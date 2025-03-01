#![allow(clippy::box_collection)]
use std::{
    cell::{RefCell, UnsafeCell},
    sync::{
        atomic::{AtomicBool, AtomicPtr, AtomicU64, Ordering},
        mpsc::{channel, Receiver, Sender},
        Arc,
    },
    time::{Duration, Instant},
};

use crossbeam_deque::{Steal, Stealer, Worker};
use libc::malloc;
use parking_lot::{Condvar, Mutex};
use rustc_hash::FxHashMap;

#[cfg(feature = "gc_profile")]
use crate::GC_INIT_TIME;
#[cfg(feature = "llvm_stackmap")]
use crate::STACK_MAP;
use crate::{
    allocator::{GlobalAllocator, ThreadLocalAllocator},
    block::{Block, LineHeaderExt, ObjectType},
    gc_is_auto_collect_enabled,
    immix_obj::ImmixObject,
    spin_until, Function, HeaderExt, SendableMarkJob, BLOCK_SIZE, CALLEE_SAVED_REG_NUM, ENABLE_EVA,
    GC_COLLECTOR_COUNT, GC_ID, GC_MARKING, GC_MARK_COND, GC_RUNNING, GC_STW_COUNT, GC_SWEEPING,
    GC_SWEEPPING_NUM, GLOBAL_ALLOCATOR, LINE_SIZE, NUM_LINES_PER_BLOCK, SHOULD_EXIT,
    USE_SHADOW_STACK,
};

pub static SLOW_PATH_COUNT: AtomicU64 = AtomicU64::new(0);

mod helpers;
use helpers::get_fn_from_frame;

/// # Collector
/// The collector is responsible for collecting garbage. It is the entry point for
/// the garbage collection process. It is also responsible for allocating new
/// objects (by using threadlocal allocator).
///
/// Each thread has a collector associated with it. The collector is thread-local.
///
/// ## Fields
///
/// * `thread_local_allocator` - thread-local allocator
/// * `roots` - gc roots
/// * `queue` - gc queue
/// * `id` - collector id
/// * `mark_histogram` - mark histogram
/// * `status` - collector status
#[repr(C)]
pub struct Collector {
    thread_local_allocator: *mut ThreadLocalAllocator,
    registers: UnsafeCell<[usize; CALLEE_SAVED_REG_NUM]>,
    former_registers: [usize; CALLEE_SAVED_REG_NUM],
    stuck_sp: *mut u8,
    low_sp: *mut u8,
    #[cfg(feature = "shadow_stack")]
    roots: rustc_hash::FxHashMap<*mut u8, ObjectType>,
    queue: Worker<SendableMarkJob>,
    id: usize,
    mark_histogram: *mut FxHashMap<usize, usize>,
    status: RefCell<CollectorStatus>,
    frames_list: AtomicPtr<Vec<(*mut libc::c_void, &'static Function)>>,
    live_set: RefCell<FxHashMap<u64, *mut u8>>,
    coro_stacks: FxHashMap<*mut u8, Vec<(*mut libc::c_void, &'static Function)>>,
    live: bool,
    stuck_stop_notify_chan: Sender<()>,
    stuck_stopped_notify_chan: (Sender<()>, Receiver<()>),
    previous_sp: RefCell<*mut u8>,
}

struct CollectorStatus {
    collecting: bool,
    total_stuck_time: Duration,
    am_i_triggered: bool,
    need_to_restore_registers: bool,
}

static TIME_TO_SAFE_POINT_US: AtomicU64 = AtomicU64::new(0);

pub type VisitFunc = unsafe extern "C" fn(&Collector, *mut u8);

pub type VtableFunc = extern "C" fn(*mut u8, &Collector, VisitFunc, VisitFunc, VisitFunc);

impl Drop for Collector {
    fn drop(&mut self) {
        log::info!("Collector {} is dropped", self.id);
        unsafe {
            if self.live {
                let mut v = GC_COLLECTOR_COUNT.lock();
                v.0 -= 1;
                v.2.remove(&self.id);
                drop(Box::from_raw(self.thread_local_allocator));
                self.live = false;
                GC_MARK_COND.notify_all();
                drop(v);
            }
            libc::free(self.mark_histogram as *mut libc::c_void);
        }
    }
}

impl Collector {
    /// # new
    /// Create a new collector.
    ///
    /// ## Parameters
    /// * `heap_size` - heap size
    pub fn new(ga: &mut GlobalAllocator) -> Self {
        let id = GC_ID.fetch_add(1, Ordering::Relaxed);
        let mut v = GC_COLLECTOR_COUNT.lock();
        if GC_RUNNING.load(Ordering::Acquire) {
            GC_MARK_COND.wait_while(&mut v, |_| GC_RUNNING.load(Ordering::Acquire));
        }
        v.0 += 1;
        let worker = Worker::new_lifo();
        v.2.insert(id, worker.stealer());
        GC_MARK_COND.notify_all();
        drop(v);
        unsafe {
            let tla = ThreadLocalAllocator::new(ga);
            let mem = Box::leak(Box::new(tla)) as *mut _;
            let memvecmap = malloc(core::mem::size_of::<FxHashMap<usize, usize>>())
                .cast::<FxHashMap<usize, usize>>();
            memvecmap.write(FxHashMap::with_capacity_and_hasher(
                NUM_LINES_PER_BLOCK,
                Default::default(),
            ));

            Self {
                thread_local_allocator: mem,
                #[cfg(feature = "shadow_stack")]
                roots: rustc_hash::FxHashMap::default(),
                id,
                mark_histogram: memvecmap,
                queue: worker,
                status: RefCell::new(CollectorStatus {
                    collecting: false,
                    total_stuck_time: Duration::default(),
                    am_i_triggered: false,
                    need_to_restore_registers: false,
                }),
                frames_list: AtomicPtr::default(),
                live_set: RefCell::new(FxHashMap::default()),
                coro_stacks: FxHashMap::default(),
                live: true,
                stuck_stop_notify_chan: channel().0,
                stuck_stopped_notify_chan: channel(),
                registers: Default::default(),
                former_registers: Default::default(),
                stuck_sp: std::ptr::null_mut(),
                low_sp: std::ptr::null_mut(),
                previous_sp: RefCell::new(std::ptr::null_mut()),
            }
        }
    }

    pub fn unregister_current_thread(&mut self) {
        let mut v = GC_COLLECTOR_COUNT.lock();
        v.0 -= 1;
        v.2.remove(&self.id);
        drop(unsafe { Box::from_raw(self.thread_local_allocator) });
        self.live = false;
        GC_MARK_COND.notify_all();
        log::info!("Collector {} is unregistered", self.id);
        drop(v);
    }

    pub fn set_low_sp(&mut self, sp: *mut u8) {
        self.low_sp = sp;
    }

    /// # get_size
    ///
    /// Get the size of allocated space.
    ///
    /// ## Return
    ///
    /// * `usize` - size
    pub fn get_size(&self) -> usize {
        self.thread_local_allocator().get_size()
    }

    /// # alloc
    ///
    /// Allocate a new object.
    ///
    /// This function is considered as a
    /// GC safepoint, which means it may trigger a GC.
    ///
    /// ## Parameters
    /// * `size` - object size
    /// * `obj_type` - object type
    ///
    /// ## Return
    /// * `ptr` - object pointer
    pub fn alloc(&self, size: usize, obj_type: ObjectType) -> *mut u8 {
        self.alloc_fast_unwind(size, obj_type, std::ptr::null_mut())
    }

    /// # alloc_fast_unwind
    ///
    /// Allocate a new object, if it trigger a GC, it will use stack pointer to walk gc frames.
    ///
    /// For more information, see [mark_fast_unwind](Collector::mark_fast_unwind)
    pub fn alloc_fast_unwind(&self, size: usize, obj_type: ObjectType, sp: *mut u8) -> *mut u8 {
        // let start = Instant::now();
        #[cfg(debug_assertions)]
        if !GC_SWEEPING.load(Ordering::Acquire) {
            self.collect_fast_unwind(sp);
        }
        if gc_is_auto_collect_enabled() {
            self.collect_if_needed_fast_unwind(sp);
        }
        let ptr = self.alloc_no_collect(size, obj_type);
        // crate::EP.fetch_add(start.elapsed().as_nanos() as u64, Ordering::Relaxed);
        if ptr.is_null() && size != 0 {
            // spin_until!(!GC_SWEEPING.load(Ordering::Acquire));
            log::info!("gc {}: OOM, start emergency gc", self.id);
            // ENABLE_EVA.store(false, Ordering::Release);
            self.collect_fast_unwind(sp);
            // ENABLE_EVA.store(true, Ordering::Release);
            return self.thread_local_allocator().alloc(size, obj_type);
        }
        // crate::EP.fetch_add(start.elapsed().as_nanos() as u64, Ordering::Relaxed);
        ptr
    }

    #[inline(always)]
    fn collect_if_needed_fast_unwind(&self, sp: *mut u8) {
        if GC_RUNNING.load(Ordering::Acquire) {
            // eprintln!("gc {}: GC is running, start gc", self.id);
            log::info!("gc {}: GC is running, start gc", self.id);
            self.collect_fast_unwind(sp);
            return;
        }

        let mut status = self.status.borrow_mut();
        if ({ self.thread_local_allocator().should_gc() } && !GC_SWEEPING.load(Ordering::Acquire)) {
            log::info!("gc {}: GC is needed, start gc", self.id);
            status.am_i_triggered = true;
            drop(status);
            self.collect_fast_unwind(sp);
        } else {
            drop(status);
        }
    }

    /// # safepoint_fast_unwind
    ///
    /// Safepoint, if will start a GC in current thread if needed,
    /// using stack pointer to walk gc frames.
    ///
    /// This function only starts GC if a GC session is already running.
    ///
    /// For more information, see [mark_fast_unwind](Collector::mark_fast_unwind)
    pub fn safepoint_fast_unwind(&self, sp: *mut u8) {
        // if GC_RUNNING.load(Ordering::Acquire) {
        //     self.collect_fast_unwind(sp);
        // }
        self.collect_if_needed_fast_unwind(sp);
    }

    /// # alloc_no_collect
    ///
    /// Allocate a new object without possibility triggering a GC.
    #[inline(always)]
    pub fn alloc_no_collect(&self, size: usize, obj_type: ObjectType) -> *mut u8 {
        if size == 0 {
            return std::ptr::null_mut();
        }
        log::info!("gc {}: alloc {} bytes", self.id, size);
        let ptr = self.thread_local_allocator().alloc(size, obj_type);
        ptr
    }

    /// # add_root
    /// Add a root to the collector.
    ///
    /// ## Parameters
    /// * `root` - root
    /// * `size` - root size
    #[cfg(feature = "shadow_stack")]
    pub fn add_root(&mut self, root: *mut u8, obj_type: ObjectType) {
        self.roots.insert(root, obj_type);
    }

    /// # remove_root
    /// Remove a root from the collector.
    ///
    /// ## Parameters
    /// * `root` - root
    #[cfg(feature = "shadow_stack")]
    pub fn remove_root(&mut self, root: *mut u8) {
        self.roots.remove(&(root));
    }

    /// # correct_ptr
    ///
    /// used to correct forward pointer in `evacuation`
    ///
    /// ## 一般情况
    ///
    /// 原本
    ///
    /// ```no_run
    /// ptr -> heap_ptr -> value
    /// ```
    ///
    /// evacuate之后
    ///
    /// ```no_run
    /// ptr -> heap_ptr -> new_ptr(forwarded) -> value
    /// ```
    ///
    /// 现在纠正为
    ///
    /// ```no_run
    /// ptr -> new_ptr(forwarded) -> value
    /// ```
    ///
    /// ## 特殊情况
    ///
    /// 有时候gc接触的指针不是原本的堆指针，他有个offset（derived pointer）
    /// 这种情况下我们需要找到原本的堆指针，然后加上一个offset，这样才能纠正
    ///
    /// ## Parameters
    ///
    /// * `ptr` - pointer which points to the evacuated heap pointer
    /// * `offset` - offset from derived pointer to heap pointer
    ///
    /// ## Return
    ///
    /// * `ptr` - corrected pointer
    unsafe fn correct_ptr(
        &self,
        father: *mut u8,
        offset: isize,
        origin_ptr: *mut u8,
    ) -> Result<*mut u8, *mut u8> {
        let father = father as *mut *mut u8;
        let ptr = AtomicPtr::new((*father).offset(-offset) as *mut *mut u8);
        let ptr = ptr.load(Ordering::SeqCst);
        let new_ptr = *ptr;
        let np = new_ptr.offset(offset);
        let atomic_father = father as *mut AtomicPtr<u8>;
        // cas store
        // 以前的指针如果变化了，代表别人和我们标记的同一个地方，而且他们已经更正了指针
        let re = atomic_father.as_mut().unwrap().compare_exchange(
            origin_ptr,
            np,
            Ordering::SeqCst,
            Ordering::SeqCst,
        );
        log::debug!(
            "gc {} correct ptr result: {:?} in {:p} from  {:p} to {:p}",
            self.id,
            re,
            father,
            origin_ptr,
            np
        );
        re
    }

    #[cfg(feature = "llvm_gc_plugin")]
    extern "C" fn mark_ptr_callback(ptr: *mut u8, _tp: *mut u8) {
        unsafe {
            crate::SPACE.with(|gc| {
                gc.get().as_ref().unwrap_unchecked().mark_ptr(ptr);
            });
        }
    }

    fn mark_conservative(&self, ptr: *mut u8) {
        unsafe {
            if self.thread_local_allocator().in_heap(ptr) {
                let obj = ImmixObject::from_unaligned_ptr(ptr);
                if obj.is_none() {
                    return;
                }
                let obj = obj.unwrap_unchecked();
                for i in 0..obj.as_ref().unwrap_unchecked().body_size() / 8 {
                    let p = (obj as *mut u8).add(i * 8 + 8);
                    self.queue
                        .push(SendableMarkJob::Object((p, ObjectType::Pointer)));
                }
            } else if self.thread_local_allocator().in_big_heap(ptr) {
                let big_obj = self.thread_local_allocator().big_obj_from_ptr(ptr);
                if let Some(_big_obj) = big_obj {
                    // scan big obj from start to end and mark all pointers
                    // | head(16byte) | data |
                    // |<------- size ------>|
                    // size % 128 == 0 always, so just scan it.
                    let mut start = (_big_obj as *mut u8).add(16);
                    let end = start.add((*_big_obj).size);
                    while start < end {
                        self.queue
                            .push(SendableMarkJob::Object((start, ObjectType::Pointer)));
                        // self.mark_ptr(start);
                        start = start.add(8);
                    }
                }
            }
        }
    }

    /// precise mark a pointer
    unsafe extern "C" fn mark_ptr(&self, ptr: *mut u8) {
        let father = ptr;
        // check pointer is valid (divided by 8)
        // immix suppose all stack pointers are aligned by 8
        // and immix base pointer itself is always aligned by 8
        // (infact aligned by 128(LINE_SIZE))
        if (ptr as usize) % 8 != 0 {
            return;
        }

        let ptr = *(ptr as *mut *mut u8);
        // eprintln!("mark ptr {:p} -> {:p}", father, ptr);
        // mark it if it is in heap
        if (ptr as usize) % 8 != 0 {
            return;
        }
        if self.thread_local_allocator().in_heap(ptr) && ptr as usize % BLOCK_SIZE > LINE_SIZE * 3 {
            // IMPORTANT: when the stack marking is conservative, the uninitialized
            // stack space may contain some heap pointers that are previously
            // collected, since they are already dead, we should not mark them.

            let block_p: *mut Block = Block::from_obj_ptr(ptr) as *mut _;

            let block = &mut *block_p;
            if block.free {
                return;
            }
            let cursor = block.get_cursor();
            let is_candidate = block.is_eva_candidate();
            let obj = ImmixObject::from_unaligned_ptr(ptr);
            if obj.is_none() {
                return;
            }
            let mut obj = obj.unwrap_unchecked();
            let mut obj_ref = obj.as_mut().unwrap_unchecked();
            let mut body = obj_ref.get_body();
            let body_size = obj_ref.body_size();
            let offset_from_head = ptr.offset_from(body);
            debug_assert!(offset_from_head >= 0);
            if obj_ref.size as usize > BLOCK_SIZE / 4 {
                return;
            }
            debug_assert!(offset_from_head < body_size as _);
            let (mut line_header, mut header_idx) = block.get_line_header_from_addr(obj as _);
            // when ptr >= cursor and the space is not used, we should not mark it
            if ptr >= cursor
                && (!line_header.get_used()
                    || (cursor.align_offset(LINE_SIZE) != 0
                        && ptr < cursor.add(cursor.align_offset(LINE_SIZE))))
            {
                return;
            }
            if !is_candidate || obj_ref.byte_header.is_pinned() {
                let block = &mut *block_p;
                block.marked = true;

                if obj_ref.is_marked() {
                    return;
                }
                obj_ref.mark();
            } else {
                // evacuation logic
                let (forward, h) = obj_ref.byte_header.get_forward_start();
                let old_h = h;
                // if forward is true or cas is failed, then it's forwarded by other thread.
                let re = obj_ref.byte_header.forward_cas(old_h);
                let shall_i_forward = !forward && re.is_ok();
                if !shall_i_forward {
                    spin_until!(obj_ref.byte_header.get_forwarded());

                    let _ = self.correct_ptr(father, offset_from_head, ptr);
                    return;
                }

                // otherwise, we shall forward it
                let atomic_ptr = body as *mut AtomicPtr<u8>;
                let new_ptr = self.alloc_no_collect(body_size, obj_ref.obj_type);
                if !new_ptr.is_null() {
                    let new_block = Block::from_obj_ptr(new_ptr);
                    let new_obj = ImmixObject::from_body_ptr(new_ptr);
                    // eprintln!("eva to block addr: {:p}", new_block);
                    debug_assert!(!new_block.is_eva_candidate());
                    debug_assert!(new_block.get_cursor() >= new_ptr.add(body_size));
                    new_block.marked = true;
                    let (new_line_header, new_header_idx) =
                        new_block.get_line_header_from_addr(new_obj as _);
                    // 将数据复制到新的地址
                    core::ptr::copy_nonoverlapping(body, new_ptr, body_size);
                    // core::ptr::copy_nonoverlapping(line_header as * const u8, new_line_header as * mut u8, line_size);
                    header_idx = new_header_idx;
                    // 将新指针写入老数据区开头
                    (*atomic_ptr).store(new_ptr, Ordering::SeqCst);
                    log::trace!("gc {}: eva {:p} to {:p}", self.id, body, new_ptr);
                    // eprintln!("gc {}: eva {:p} to {:p} size {}", self.id, body, new_ptr, obj_ref.size);
                    // debug_assert!(!new_line_header.get_marked());
                    // debug_assert!(!new_line_header.get_forwarded());
                    line_header = new_line_header;
                    body = new_ptr;
                    debug_assert!(!new_obj.as_mut().unwrap_unchecked().byte_header.get_marked());
                    debug_assert!(!new_obj
                        .as_mut()
                        .unwrap_unchecked()
                        .byte_header
                        .get_forwarded());
                    new_obj.as_mut().unwrap_unchecked().mark();
                    // eprintln!("size {}", obj_line_size*LINE_SIZE);
                    if let Err(e) = self.correct_ptr(father, offset_from_head, ptr) {
                        eprintln!("{:p} {:p}", father, e);
                        panic!("The thread evacuated pointer changed by another thread during evacuation.");
                    }
                    // 成功驱逐
                    obj_ref.byte_header.set_forwarded();
                    debug_assert!(obj_ref.byte_header.get_forwarded());
                    obj = new_obj;
                    obj_ref = new_obj.as_mut().unwrap_unchecked();
                } else {
                    // 驱逐失败
                    panic!("gc: OOM during evacuation");
                }
            }
            debug_assert!(obj_ref.is_marked());
            debug_assert!(!obj_ref.byte_header.get_forwarded());

            if obj_ref.is_small() {
                if header_idx == NUM_LINES_PER_BLOCK - 1 {
                    line_header.set_marked(true);
                } else {
                    line_header.set_marked_conservative(true);
                    debug_assert_eq!(
                        {
                            let next = (line_header as *mut u8).add(1);
                            (*next) & 0b10
                        },
                        0b10
                    );
                }
            } else {
                line_header.set_marked(true);
                let mut header_ptr = line_header as *mut u8;
                let mut cursor = obj as *mut u8;
                let end = cursor.add(body_size + 8);
                cursor = cursor.add(cursor.align_offset(LINE_SIZE));
                while cursor < end {
                    header_ptr = header_ptr.add(1);
                    (*header_ptr).set_marked(true);
                    cursor = cursor.add(LINE_SIZE);
                }
            }
            // debug_assert!(!(*ImmixObject::from_ptr(body)).is_valid());
            // let obj_type = line_header.get_obj_type();
            match obj_ref.obj_type {
                ObjectType::Atomic => {}
                // ObjectType::Trait => self.mark_trait(body),
                // ObjectType::Complex => self.mark_complex(body),
                // ObjectType::Pointer => self.mark_ptr(body),
                // ObjectType::Conservative => self.mark_conservative(body),
                _ => self.push_job(body, obj_ref.obj_type),
            }
        }
        // mark it if it is a big object
        else if self.thread_local_allocator().in_big_heap(ptr) {
            let big_obj = self.thread_local_allocator().big_obj_from_ptr(ptr);
            if let Some(big_obj) = big_obj {
                if (*big_obj).header.get_marked() {
                    return;
                }
                (*big_obj).header.set_marked(true);
                let obj_type = (*big_obj).header.get_obj_type();
                let p = (big_obj as *mut u8).add(16);
                match obj_type {
                    ObjectType::Atomic => {}
                    _ => self.push_job(p, obj_type),
                }
            }
        }
    }

    #[inline(always)]
    #[allow(clippy::mut_from_ref)]
    fn thread_local_allocator(&self) -> &mut ThreadLocalAllocator {
        unsafe { self.thread_local_allocator.as_mut().unwrap_unchecked() }
    }

    /// # push_job
    ///
    /// push a mark job to the gc work-stealing queue
    fn push_job(&self, head: *mut u8, obj_type: ObjectType) {
        self.queue.push(SendableMarkJob::Object((head, obj_type)))
    }

    /// precise mark a complex object
    ///
    /// it self does not mark the object, but mark the object's fields by calling
    /// mark_ptr
    unsafe extern "C" fn mark_complex(&self, ptr: *mut u8) {
        if ptr.is_null() {
            return;
        }
        let vptr = *(ptr as *mut *mut u8);
        // stack may contain old pointer that's collected before
        if vptr.is_null()
            || self.thread_local_allocator().in_heap(vptr)
            || self.thread_local_allocator().in_big_heap(vptr)
            || !vptr.is_aligned()
            || vptr as usize > 0x0000FFFFFFFFFFFF
        {
            return;
        }
        let vtable = *(ptr as *mut VtableFunc);
        vtable(
            ptr,
            self,
            Self::mark_ptr,
            Self::mark_complex,
            Self::mark_trait,
        );
    }
    /// precise mark a trait object
    unsafe extern "C" fn mark_trait(&self, ptr: *mut u8) {
        // the trait is not init
        if ptr.is_null() {
            return;
        }
        let loaded = ptr as *mut *mut u8;
        let ptr = loaded.offset(1);
        self.mark_ptr(ptr as *mut u8);
    }
    pub fn keep_live(&self, gc_ptr: *mut u8) -> u64 {
        let len = self.live_set.borrow().len();
        self.live_set.borrow_mut().insert(len as _, gc_ptr);
        len as _
    }
    pub fn keep_live_pinned(&self, gc_ptr: *mut u8) -> u64 {
        self.live_set.borrow_mut().insert(gc_ptr as _, gc_ptr);
        gc_ptr as _
    }
    pub fn rm_live(&self, handle: u64) {
        self.live_set.borrow_mut().remove(&handle);
    }
    pub fn print_stats(&self) {
        println!("gc {} states:", self.id);
        {
            self.thread_local_allocator().print_stats();
        }
    }
    pub fn get_id(&self) -> usize {
        self.id
    }

    pub fn iter<F>(&self, f: F)
    where
        F: FnMut(*mut u8),
    {
        self.thread_local_allocator().iter(f);
    }

    /// # mark
    ///
    /// mark using backtrace-rs
    ///
    /// for more information, see [mark_fast_unwind](Collector::mark_fast_unwind)
    pub fn mark(&self) {
        self.mark_fast_unwind(std::ptr::null_mut());
    }

    fn mark_stack_offset(&self, sp: *mut u8, offset: i32) {
        unsafe {
            let root = sp.offset(offset as isize);
            if root.is_null() {
                return;
            }
            self.push_job(root, ObjectType::Pointer);
        }
    }

    fn pin_all_callee_saved_regs(&self) {
        unsafe {
            for r in &mut *self.registers.get() {
                if self.thread_local_allocator().in_heap((*r) as *mut _) {
                    if let Some(o) = ImmixObject::from_unaligned_ptr(*r as *mut _) {
                        o.as_mut().unwrap_unchecked().byte_header.pin();
                    }
                }
            }
        }
    }

    /// # mark_fast_unwind
    ///
    ///
    /// From gc roots, mark all reachable objects.
    ///
    /// this mark function is __precise__
    ///
    /// ## Parameters
    ///
    /// * `sp` - stack pointer
    ///
    /// if the stack pointer is null, then it will use backtrace-rs to walk
    /// the stack.
    ///
    /// Stack walk using sp is lock-free and more precise(it only walks gc frames).
    ///
    /// ## Safety
    ///
    /// The fast version relies heavily on llvm generated stackmap, calling convention and
    /// made some assumptions on the stack layout, which may not work on some
    /// platforms. A known issue is it breaks on [linux x86_64][1] with
    /// late machine code optimization enabled(in llvm 16).
    ///
    /// [1]:https://github.com/llvm/llvm-project/issues/75162
    ///
    /// The backtrace-rs version works on most platforms in aot mode, but it
    /// failed on [macos aarch64 in jit mode][2], as there's a issue for llvm
    /// to emit __eh_frame section.
    ///
    /// [2]:https://github.com/llvm/llvm-project/issues/49036
    pub fn mark_fast_unwind(&self, sp: *mut u8) {
        self.pin_all_callee_saved_regs();
        let mut mtx = SWEEP_MUTEX.lock();
        SWEEP_COND.wait_while(&mut mtx, |sweeping| *sweeping);
        drop(mtx);
        // let start1 = Instant::now();
        // self.pin_all_callee_saved_regs();
        let mut v = GC_COLLECTOR_COUNT.lock();
        if v.1 == 0 {
            let mutex = STUCK_MUTEX.lock();
            GC_RUNNING.store(true, Ordering::Release);
            STUCK_COND.notify_all();
            drop(mutex);
        }
        v.1 += 1;
        let count = v.0;
        let waiting = v.1;
        log::info!(
            "gc mark {}: start, waiting: {}, count: {}",
            self.id,
            waiting,
            count
        );
        // println!("gc mark {}: waiting: {}, count: {}", self.id, waiting, count);
        let stealers = if waiting != count {
            GC_MARK_COND.wait_while(&mut v, |(c, _, _)| {
                // 线程数量变化了？
                if waiting == *c {
                    GC_MARKING.store(true, Ordering::Release);
                    GC_STW_COUNT.fetch_add(1, Ordering::SeqCst);
                    GC_MARK_COND.notify_all();
                    GC_SWEEPPING_NUM.store(*c, Ordering::Release);
                    return false;
                }
                if SHOULD_EXIT.load(Ordering::Acquire) {
                    return false;
                }
                !GC_MARKING.load(Ordering::Acquire)
            });
            if SHOULD_EXIT.load(Ordering::Acquire) {
                return;
            }
            {
                self.thread_local_allocator().get_more_works();
            }
            let stealers = v.2.values().cloned().collect::<Vec<_>>();
            drop(v);
            stealers
        } else {
            GC_MARKING.store(true, Ordering::Release);
            GC_STW_COUNT.fetch_add(1, Ordering::SeqCst);
            GC_MARK_COND.notify_all();
            {
                self.thread_local_allocator().get_more_works();
            }
            let stealers = v.2.values().cloned().collect::<Vec<_>>();
            GC_SWEEPPING_NUM.store(count, Ordering::Release);
            drop(v);
            stealers
        };
        log::info!("gc mark {}: sync done", self.id);
        {
            self.thread_local_allocator().return_prev_free_blocks();
        }
        // println!("gc mark {}: start", self.id);
        #[cfg(feature = "gc_profile")]
        eprintln!(
            "gc {} done mark sync at {:?}",
            self.id,
            GC_INIT_TIME.elapsed().as_nanos()
        );

        // let inst = Instant::now();
        #[cfg(feature = "shadow_stack")]
        {
            for (root, obj_type) in self.roots.iter() {
                match obj_type {
                    ObjectType::Atomic => {}
                    _ => self.queue.push(SendableMarkJob::Object((*root, *obj_type))),
                }
            }
        }
        log::trace!("gc {}: marking...", self.id);
        // let currsp = Self::current_sp();
        #[cfg(feature = "llvm_stackmap")]
        {
            if USE_SHADOW_STACK.load(Ordering::Relaxed) {
                #[cfg(feature = "llvm_gc_plugin")]
                unsafe {
                    crate::shadow_stack::visitGCRoots(Self::mark_ptr_callback)
                };
            } else {
                // println!("{:?}", &STACK_MAP.map.borrow());
                let fl = self.frames_list.load(Ordering::SeqCst);
                if !fl.is_null() {
                    unsafe {
                        for r in &mut *self.registers.get() {
                            let p = r as *mut _ as _;
                            self.mark_ptr(p);
                        }
                    }
                    // // self.mark_all_stucked_registers();
                    // log::trace!("gc {}: tracing stucked frames", self.id);
                    for f in unsafe { &*fl } {
                        self.queue.push(SendableMarkJob::Frame((f.0, f.1)));
                        // self.mark_frame(&(f.0 as _), &f.1);
                    }
                } else if sp.is_null() {
                    // use backtrace.rs or stored frames
                    let mut frames: Vec<(*mut libc::c_void, &'static Function)> = vec![];
                    backtrace::trace(|frame| {
                        if let Some(f) = get_fn_from_frame(frame) {
                            frames.push((frame.sp(), f));
                        }
                        true
                    });

                    self.mark_gc_frames(&frames);
                } else {
                    unsafe {
                        for r in &mut *self.registers.get() {
                            let p = r as *mut _ as _;
                            self.mark_ptr(p);
                        }
                    }
                    // self.mark_all_stucked_registers();
                    helpers::walk_gc_frames(sp, |sp, _, f| {
                        // eprintln!("gc {} mark frame {:p} {:?}", self.id,sp, f);
                        self.queue.push(SendableMarkJob::Frame((sp as _, f)));
                        // self.mark_frame(&(sp as _), &f);
                    });

                    // IMPORTANT: callee saved registers may
                    // already been pushed to stack, so we should
                    // mark the rust stack from sp to water_mark_sp
                    unsafe {
                        let mut sp1 = self.low_sp;
                        // let mut i = 0;
                        while sp1 < sp {
                            // eprintln!("gc {} mark sp {:p} {}", self.id,sp, i);
                            self.mark_ptr(sp1);
                            // i += 1;
                            sp1 = sp1.add(8);
                        }
                    }
                }
                log::debug!("gc {} global roots", self.id);
                self.mark_globals();
                log::debug!("gc {} global roots end", self.id);
                log::debug!("gc {} coro roots", self.id);
                self.mark_coro_stacks();
                log::debug!("gc {} coro roots end", self.id);
            }
        }

        for (_, live) in self.live_set.borrow_mut().iter_mut() {
            let p = live as *mut _ as _;
            self.push_job(p, ObjectType::Pointer);
        }

        self.mark_queue(&stealers);
        let mut v = GC_COLLECTOR_COUNT.lock();
        v.1 -= 1;
        if v.1 != 0 {
            log::info!(
                "gc mark {} ending: waiting for other threads waiting: {} count: {}",
                self.id,
                v.1,
                v.0
            );
            GC_MARK_COND.wait_while(&mut v, |(_, w, _)| {
                log::info!(
                    "gc mark {} ending: waiting for other threads waiting: {} ",
                    self.id,
                    *w
                );
                *w != 0
            });
        } else {
            log::info!(
                "gc mark {} ending: waiting for other threads waiting: {}",
                self.id,
                v.1
            );
            let mut mtx = SWEEP_MUTEX.lock();
            *mtx = true;
            drop(mtx);
            let g = unsafe { GLOBAL_ALLOCATOR.0.as_mut().unwrap() };

            let mut guard = g.finalizers.lock();
            let mut remove_list = vec![];
            for (i, (p, a, f)) in guard.iter_mut().enumerate() {
                // get block of p
                let head = unsafe {
                    ImmixObject::from_unaligned_ptr(*p)
                        .unwrap_unchecked()
                        .as_mut()
                        .unwrap_unchecked()
                };
                let offset_from_head = unsafe { (*p).offset_from(head.get_body()) };

                if head.byte_header.get_forwarded() {
                    unsafe {
                        _ = self.correct_ptr(p as *mut _ as _, offset_from_head, *p);
                    }
                }
                let head = unsafe {
                    ImmixObject::from_unaligned_ptr(*p)
                        .unwrap_unchecked()
                        .as_mut()
                        .unwrap_unchecked()
                };
                if !head.byte_header.get_marked() {
                    // not marked, we should remove it
                    remove_list.push(i);
                    // call finalizer
                    f(*a);
                }
            }
            for i in remove_list.iter().rev() {
                guard.swap_remove(*i);
            }
            drop(guard);

            GC_MARKING.store(false, Ordering::Release);
            GLOBAL_MARK_FLAG.store(false, Ordering::Release);
            log::info!("gc {}: notify other thread mark end", self.id);
            GC_MARK_COND.notify_all();
            GC_RUNNING.store(false, Ordering::Release);
            GC_SWEEPING.store(true, Ordering::Release);
            drop(v);
            unsafe {
                GLOBAL_ALLOCATOR
                    .0
                    .as_mut()
                    .unwrap_unchecked()
                    .sweep_big_objs()
            };
        }
        log::info!("gc mark {}: end", self.id);
    }

    fn mark_queue(&self, stealers: &[Stealer<SendableMarkJob>]) {
        // iterate through queue and mark all reachable objects
        unsafe {
            loop {
                let mut empty_num = 0;
                for stealer in stealers {
                    match stealer.steal_batch(&self.queue) {
                        Steal::Success(_) => {}
                        Steal::Empty => {
                            empty_num += 1;
                        }
                        Steal::Retry => {}
                    }
                }
                while let Some(job) = self.queue.pop() {
                    match job {
                        SendableMarkJob::Frame(f) => {
                            self.mark_frame(&f.0, &f.1);
                        }
                        SendableMarkJob::Object((obj, obj_type)) => self.mark_obj(obj_type, obj),
                    }
                }
                if empty_num == stealers.len() {
                    break;
                }
            }
        }
    }

    unsafe fn mark_obj(&self, obj_type: ObjectType, obj: *mut u8) {
        match obj_type {
            ObjectType::Atomic => {}
            ObjectType::Complex => {
                self.mark_complex(obj);
            }
            ObjectType::Trait => {
                self.mark_trait(obj);
            }
            ObjectType::Pointer => {
                self.mark_ptr(obj);
            }
            ObjectType::Conservative => self.mark_conservative(obj),
        }
    }

    /// # mark_gc_frames
    ///
    /// mark gc frames
    ///
    /// ## Parameters
    ///
    /// * `frames` - gc frames, each frame is a tuple of (ip, sp)
    fn mark_gc_frames(&self, frames: &[(*mut libc::c_void, &'static Function)]) {
        frames.iter().for_each(|(sp, f)| {
            self.mark_frame(sp, f);
        });
    }

    fn mark_frame(&self, sp: &*mut libc::c_void, f: &&Function) {
        #[cfg(not(feature = "conservative_stack_scan"))]
        f.iter_roots()
            .for_each(|offset| self.mark_stack_offset(*sp as _, offset));
        #[cfg(target_arch = "aarch64")]
        let frame_size = f.frame_size;
        #[cfg(target_arch = "x86_64")]
        let frame_size = f.frame_size + 8;
        #[cfg(feature = "conservative_stack_scan")]
        for i in 0..(frame_size + 7) / 8 {
            self.mark_stack_offset(*sp as _, i * 8);
        }
    }

    #[cfg(feature = "llvm_stackmap")]
    fn mark_globals(&self) {
        if GLOBAL_MARK_FLAG
            .compare_exchange(false, true, Ordering::SeqCst, Ordering::SeqCst)
            .is_ok()
        {
            unsafe {
                STACK_MAP
                    .global_roots
                    .as_mut()
                    .unwrap()
                    .iter()
                    .for_each(|(root, tp)| {
                        // self.push_job(*root, *tp);
                        match *tp {
                            ObjectType::Atomic => {}
                            // ObjectType::Trait => self.mark_trait(*root),
                            // ObjectType::Complex => self.mark_complex(*root),
                            // ObjectType::Pointer => self.mark_ptr(*root),
                            // ObjectType::Conservative => self.mark_conservative(*root),
                            _ => self.push_job(*root, *tp),
                        }
                    });
            }
        }
    }

    pub(crate) fn store_registers(&mut self) {
        unsafe {
            *self.registers.get() = Self::callee_saved_registers();
        }
        self.former_registers = self.registers();
    }
    pub(crate) fn registers(&self) -> [usize; CALLEE_SAVED_REG_NUM] {
        unsafe { *self.registers.get() }
    }

    pub(crate) fn get_need_restore(&self) -> bool {
        let res = self.status.borrow().need_to_restore_registers;
        self.status.borrow_mut().need_to_restore_registers = false;
        res
    }

    pub(crate) fn restore_callee_saved_registers(&self) {
        use std::arch::asm;
        if self.get_need_restore() {
            let reg = self.registers();
            unsafe {
                // compare registers with former registers, if changed, restore
                for i in 0..CALLEE_SAVED_REG_NUM {
                    if reg[i] != self.former_registers[i] {
                        #[cfg(target_arch = "aarch64")]
                        match i {
                            0 => asm!("mov x19, {0}", in(reg) reg[i]),
                            1 => asm!("mov x20, {0}", in(reg) reg[i]),
                            2 => asm!("mov x21, {0}", in(reg) reg[i]),
                            3 => asm!("mov x22, {0}", in(reg) reg[i]),
                            4 => asm!("mov x23, {0}", in(reg) reg[i]),
                            5 => asm!("mov x24, {0}", in(reg) reg[i]),
                            6 => asm!("mov x25, {0}", in(reg) reg[i]),
                            7 => asm!("mov x26, {0}", in(reg) reg[i]),
                            8 => asm!("mov x27, {0}", in(reg) reg[i]),
                            9 => asm!("mov x28, {0}", in(reg) reg[i]),
                            _ => unreachable!(),
                        }
                        #[cfg(target_arch = "x86_64")]
                        match i {
                            0 => asm!("mov rbx, {0}", in(reg) reg[i]),
                            1 => asm!("mov rbp, {0}", in(reg) reg[i]),
                            2 => asm!("mov r12, {0}", in(reg) reg[i]),
                            3 => asm!("mov r13, {0}", in(reg) reg[i]),
                            4 => asm!("mov r14, {0}", in(reg) reg[i]),
                            5 => asm!("mov r15, {0}", in(reg) reg[i]),
                            6 => asm!("mov rsi, {0}", in(reg) reg[i]),
                            7 => asm!("mov rdi, {0}", in(reg) reg[i]),
                            8 => asm!("mov rsp, {0}", in(reg) reg[i]),
                            _ => unreachable!(),
                        }
                    }
                }
            }
        }
    }

    // on aarch64 is r19…r28
    pub(crate) fn callee_saved_registers() -> [usize; CALLEE_SAVED_REG_NUM] {
        let mut regs = [0; CALLEE_SAVED_REG_NUM];
        unsafe {
            // https://github.com/ARM-software/abi-aa/blob/main/aapcs64/aapcs64.rst#611general-purpose-registers
            #[cfg(target_arch = "aarch64")]
            std::arch::asm!(
                "mov {0}, x19",
                "mov {1}, x20",
                "mov {2}, x21",
                "mov {3}, x22",
                "mov {4}, x23",
                "mov {5}, x24",
                "mov {6}, x25",
                "mov {7}, x26",
                "mov {8}, x27",
                "mov {9}, x28",
                out(reg) regs[0],
                out(reg) regs[1],
                out(reg) regs[2],
                out(reg) regs[3],
                out(reg) regs[4],
                out(reg) regs[5],
                out(reg) regs[6],
                out(reg) regs[7],
                out(reg) regs[8],
                out(reg) regs[9],
            );
            // The x64 ABI considers registers RBX, RBP, RDI, RSI, RSP, R12, R13, R14, R15, and XMM6-XMM15 nonvolatile
            // see https://learn.microsoft.com/en-us/cpp/build/x64-calling-convention?view=msvc-170#callercallee-saved-registers
            #[cfg(target_arch = "x86_64")]
            std::arch::asm!(
                "mov {0}, rbx",
                "mov {1}, rbp",
                "mov {2}, r12",
                "mov {3}, r13",
                "mov {4}, r14",
                "mov {5}, r15",
                "mov {6}, rsi",
                "mov {7}, rdi",
                "mov {8}, rsp",
                out(reg) regs[0],
                out(reg) regs[1],
                out(reg) regs[2],
                out(reg) regs[3],
                out(reg) regs[4],
                out(reg) regs[5],
                out(reg) regs[6],
                out(reg) regs[7],
                out(reg) regs[8],
            );
        }
        regs
    }
    /// # sweep
    ///
    /// since we did synchronization in mark, we don't need to do synchronization again in sweep
    pub fn sweep(&self) -> (usize, usize) {
        log::trace!("gc {}: sweeping...", self.id);
        let used = { self.thread_local_allocator().sweep(self.mark_histogram) };
        // let previous_threshold = self.status.borrow().collect_threshold;
        // let previous_remaining = self.status.borrow().last_gc_remaining;
        let used_bytes = used.0;
        {
            let ga = self.thread_local_allocator().global_allocator();
            ga.add_used(used_bytes);
        }

        #[cfg(feature = "gc_profile")]
        eprintln!(
            "gc {} done sweep at {:?}",
            self.id,
            GC_INIT_TIME.elapsed().as_nanos()
        );
        let v = GC_SWEEPPING_NUM.fetch_sub(1, Ordering::AcqRel);
        if v - 1 == 0 {
            {
                let ga = self.thread_local_allocator().global_allocator();
                ga.end_gc();
            }
            log::info!("gc {}: sweep done", self.id);
            // eprintln!("gc sweep end {}", self.id);
            GC_SWEEPING.store(false, Ordering::Release);
            let mut mtx = SWEEP_MUTEX.lock();
            *mtx = false;
            SWEEP_COND.notify_all();
        }
        used
        // used
    }

    /// # safepoint
    ///
    /// A safepoint is a point in the program where the garbage collector can
    /// safely run.
    ///
    /// Safepoint, if it trigger a GC, it will use backtrace-rs to walk gc frames.
    pub fn safepoint(&self) {
        self.safepoint_fast_unwind(std::ptr::null_mut());
    }

    /// # collect
    ///
    /// Collect garbage.
    ///
    /// This default implementation is walk stack using backtrace-rs,
    /// which is kind of slow but perfectly works on most of platforms. Backtrace-rs is
    /// using a global mutex during stack walking, which may cause
    /// performance issue.
    ///
    /// If you want to gain more performance, you can use its fast version
    /// `collect_fast_unwind`, which requires you to pass the stack pointer,
    /// and perform stack walking using frame size recorded in stackmap, which
    /// is lock-free and more precise(it only walks gc frames).
    pub fn collect(&self) {
        self.collect_fast_unwind(std::ptr::null_mut());
    }

    /// # collect_fast_unwind
    ///
    /// Collect garbage, use stack pointer to walk gc frames.
    ///
    /// ## Parameters
    ///
    /// * `sp` - stack pointer
    ///
    /// if `sp` is null, then use backtrace-rs to walk stack
    ///
    /// for more information, see [mark_fast_unwind](Collector::mark_fast_unwind)
    pub fn collect_fast_unwind(&self, sp: *mut u8) {
        #[cfg(feature = "gc_profile")]
        eprintln!(
            "gc {} start collect at {:?}",
            self.id,
            GC_INIT_TIME.elapsed().as_nanos(),
        );
        log::info!(
            "gc {} collecting... stucked: {}",
            self.id,
            !self.frames_list.load(Ordering::SeqCst).is_null()
        );
        let mut status = self.status.borrow_mut();
        if status.collecting {
            return Default::default();
        }
        status.need_to_restore_registers = true;
        status.collecting = true;
        drop(status);
        // evacuation pre process
        // 这个过程要在完成safepoint同步之前完成，因为在驱逐的情况下
        // 他要设置每个block是否是驱逐目标
        // 如果设置的时候别的线程的mark已经开始，那么将无法保证能够纠正所有被驱逐的指针
        unsafe {
            self.thread_local_allocator().correct_cursor();
            if ENABLE_EVA.load(Ordering::SeqCst) && self.thread_local_allocator().should_eva() {
                // 如果需要驱逐，首先计算驱逐阀域
                let mut eva_threshold = 0;
                let mut available_histogram: FxHashMap<usize, usize> =
                    FxHashMap::with_capacity_and_hasher(NUM_LINES_PER_BLOCK, Default::default());
                let mut available_lines = self
                    .thread_local_allocator()
                    .fill_available_histogram(&mut available_histogram);
                let mut required_lines = 0;
                let mark_histogram = &mut *self.mark_histogram;
                for threshold in (0..=(NUM_LINES_PER_BLOCK / 2)).rev() {
                    // 从洞多到洞少遍历，计算剩余空间，直到空间不足
                    // 此时洞的数量就是驱逐阀域
                    required_lines += *mark_histogram.get(&threshold).unwrap_or(&0);
                    available_lines = available_lines
                        .saturating_sub(*available_histogram.get(&threshold).unwrap_or(&0));
                    if available_lines <= required_lines {
                        eva_threshold = threshold;
                        break;
                    }
                }
                log::info!("gc {} eva threshold:{}", self.id, eva_threshold);
                // 根据驱逐阀域标记每个block是否是驱逐目标
                self.thread_local_allocator()
                    .set_eva_threshold(eva_threshold);
            }
            (*self.mark_histogram).clear();
        }
        {
            self.thread_local_allocator().set_collect_mode(true);
        }
        self.mark_fast_unwind(sp);
        if SHOULD_EXIT.load(Ordering::Acquire) {
            return;
        }
        let (_used, free) = self.sweep();
        {
            self.thread_local_allocator().set_collect_mode(false);
        }
        log::info!(
            "gc {} collect done, used heap size: {} bytes, freed {} bytes in this gc",
            self.id,
            _used,
            free
        );
        let mut status = self.status.borrow_mut();
        status.collecting = false;
    }

    #[inline(always)]
    pub(crate) fn current_sp() -> *mut u8 {
        let sp: *mut u8;
        unsafe {
            #[cfg(target_arch = "aarch64")]
            std::arch::asm!("mov {}, sp", out(reg) sp);
            #[cfg(target_arch = "x86_64")]
            std::arch::asm!("mov {}, rsp", out(reg) sp);
        }
        sp
    }
    /// # stuck
    ///
    /// tell the collector that the current thread is stucked.
    pub fn stuck(&mut self) {
        self.stuck_fast_unwind(std::ptr::null_mut());
    }

    pub fn gc_stw_duration(&self) -> Duration {
        println!(
            "total time to safepoint: {:?}",
            Duration::from_nanos(TIME_TO_SAFE_POINT_US.load(Ordering::Relaxed))
        );
        self.status.borrow().total_stuck_time
    }

    /// # stuck_fast_unwind
    ///
    /// tell the collector that the current thread is stucked.
    ///
    /// ## Parameters
    ///
    /// - `sp` - stack pointer
    ///
    /// for more information, see [mark_fast_unwind](Collector::mark_fast_unwind)
    #[inline(always)]
    pub fn stuck_fast_unwind(&mut self, sp: *mut u8) {
        if SHOULD_EXIT.load(Ordering::Relaxed) {
            return;
        }
        self.store_registers();
        self.pin_all_callee_saved_regs();
        self.stuck_sp = sp;
        log::info!("gc {}: stucking...", self.id);
        let frames = self.get_frames(sp);
        let (startsender, startrecv) = channel::<()>();
        let (endsender, endreceiver) = channel::<()>();
        self.stuck_stop_notify_chan = endsender;
        unsafe {
            let ptr = Box::leak(Box::new(frames)) as *mut _;
            self.frames_list.store(ptr, Ordering::SeqCst);
            let c: *mut Collector = self as *mut _;
            let c = c.as_mut().unwrap();
            let sender = c.stuck_stopped_notify_chan.0.clone();
            GLOBAL_ALLOCATOR.0.as_ref().unwrap().pool.execute(move || {
                crate::STUCK_COUNT.fetch_add(1, Ordering::SeqCst);
                // NOTE: **VERY ESSENCIAL** to make sure the function here will not
                // voluntarily start a new gc
                let mut first = true;
                loop {
                    if SHOULD_EXIT.load(Ordering::Relaxed) {
                        crate::STUCK_COUNT.fetch_sub(1, Ordering::SeqCst);
                        break;
                    }
                    let mut mutex = STUCK_MUTEX.lock();
                    if first {
                        first = false;
                        _ = startsender.send(());
                    }
                    if endreceiver.try_recv().is_ok() {
                        drop(mutex);
                        sender.send(()).unwrap();
                        crate::STUCK_COUNT.fetch_sub(1, Ordering::SeqCst);
                        break;
                    } else {
                        if !GC_RUNNING.load(Ordering::Acquire) {
                            STUCK_COND.wait_until(
                                &mut mutex,
                                Instant::now() + Duration::from_millis(100),
                            );
                        }
                        drop(mutex);
                        c.safepoint();
                    }
                }
            });
        }
        // in case of exit this may return error
        _ = startrecv.recv();
        STUCK_COND.notify_all();
        // FRAMES_LIST.0.lock().borrow_mut().insert( self as _,frames);
    }

    fn mark_coro_stacks(&self) {
        for (_k, frames) in self.coro_stacks.iter() {
            for (sp, f) in frames.iter() {
                self.mark_frame(sp, f);
            }
        }
    }

    pub fn add_coro_stack(&mut self, sp: *mut u8, stack: *mut u8) {
        let frames = self.get_frames(sp);
        log::debug!("gc {} add coro stack {:p} {:?}", self.id, stack, frames);
        self.coro_stacks.insert(stack, frames);
    }

    pub fn remove_coro_stack(&mut self, stack: *mut u8) {
        log::debug!("gc {} remove coro stack {:p}", self.id, stack);
        self.coro_stacks.remove(&stack);
    }

    pub fn unstuck(&mut self) {
        if SHOULD_EXIT.load(Ordering::Relaxed) {
            return;
        }
        log::info!("gc {}: unstucking...", self.id);
        _ = self.stuck_stop_notify_chan.send(());
        STUCK_COND.notify_all();
        // wait until the shadow thread exit
        _ = self.stuck_stopped_notify_chan.1.recv();

        let old = self
            .frames_list
            .swap(std::ptr::null_mut(), Ordering::SeqCst);
        if !old.is_null() {
            unsafe {
                drop(Box::from_raw(old));
            }
        }
        log::info!("gc {}: unstuck done", self.id);
        // unsafe{update_resgisters(self.former_registers, unsafe{*self.registers.get()},self.id);}
    }
    fn get_frames(&self, sp: *mut u8) -> Vec<(*mut libc::c_void, &'static Function)> {
        let mut frames = vec![];
        if sp.is_null() {
            backtrace::trace(|frame| {
                let f = get_fn_from_frame(frame);
                if let Some(f) = f {
                    frames.push((frame.sp(), f));
                }
                true
            });
        } else {
            helpers::walk_gc_frames(sp, |sp, _, f| frames.push((sp as _, f)));
        }
        frames
    }
}

static GLOBAL_MARK_FLAG: AtomicBool = AtomicBool::new(false);

// static STUCK_GCED: AtomicBool = AtomicBool::new(false);

lazy_static::lazy_static! {
    static ref STUCK_COND: Arc<Condvar> = Arc::new(Condvar::new());
    static ref STUCK_MUTEX:Mutex<()> = Mutex::new(());
    static ref SWEEP_COND: Arc<Condvar> = Arc::new(Condvar::new());
    static ref SWEEP_MUTEX:Mutex<bool> = Mutex::new(false);
}

unsafe impl Sync for Collector {}
unsafe impl Send for Collector {}
