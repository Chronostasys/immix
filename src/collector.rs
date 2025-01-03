#![allow(clippy::box_collection)]
use std::{
    cell::{RefCell, UnsafeCell},
    cmp::min,
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
    gc_is_auto_collect_enabled, spin_until, Function, HeaderExt, SendableMarkJob, ENABLE_EVA,
    FREE_SPACE_DIVISOR, GC_COLLECTOR_COUNT, GC_ID, GC_MARKING, GC_MARK_COND, GC_RUNNING,
    GC_STW_COUNT, GC_SWEEPING, GC_SWEEPPING_NUM, GLOBAL_ALLOCATOR, LINE_SIZE, NUM_LINES_PER_BLOCK,
    REMAIN_MULTIPLIER, SHOULD_EXIT, THRESHOLD_PROPORTION, USE_SHADOW_STACK,
};

pub static SLOW_PATH_COUNT: AtomicU64 = AtomicU64::new(0);

fn get_ip_from_sp(sp: *mut u8) -> *mut u8 {
    let sp = sp as *mut *mut u8;
    // check align
    unsafe {
        let p = sp.offset(-1);
        if p as usize % 8 == 0 {
            *p
        } else {
            std::ptr::null_mut()
        }
    }
}

fn walk_gc_frames(sp: *mut u8, mut walker: impl FnMut(*mut u8, *mut u8, &'static Function)) {
    let mut sp = sp;
    loop {
        let ip = get_ip_from_sp(sp);
        let frame = unsafe { STACK_MAP.map.as_ref().unwrap().get(&ip.cast_const()) };
        if let Some(frame) = frame {
            #[cfg(target_arch = "aarch64")]
            let frame_size = frame.frame_size;
            #[cfg(target_arch = "x86_64")]
            let frame_size = frame.frame_size + 8;

            walker(sp, ip, frame);
            sp = unsafe {
                #[cfg(target_arch = "aarch64")]
                {
                    sp.offset(frame_size as _)
                }
                #[cfg(target_arch = "x86_64")]
                {
                    sp.offset(frame_size as _)
                }
            };
        } else {
            break;
        }
    }
}

/// # Collector
/// The collector is responsible for collecting garbage. It is the entry point for
/// the garbage collection process. It is also responsible for allocating new
/// blocks and objects.
///
/// Each thread has a collector associated with it. The collector is thread-local.
///
/// ## Fields
/// * `thread_local_allocator` - thread-local allocator
/// * `roots` - gc roots
/// * `queue` - gc queue
/// * `id` - collector id
/// * `mark_histogram` - mark histogram
/// * `status` - collector status
#[repr(C)]
pub struct Collector {
    thread_local_allocator: *mut ThreadLocalAllocator,
    bytes_allocated_since_last_gc: UnsafeCell<usize>,
    registers: UnsafeCell<[usize; 32]>,
    former_registers: [usize; 32],
    stuck_sp: *mut u8,
    water_mark_sp: *mut u8,
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
}

struct CollectorStatus {
    /// in bytes
    collect_threshold: usize,
    /// in bytes
    last_gc_remaining: usize,
    collecting: bool,
    total_stuck_time: Duration,
    am_i_triggered: bool,
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
                bytes_allocated_since_last_gc: UnsafeCell::new(0),
                #[cfg(feature = "shadow_stack")]
                roots: rustc_hash::FxHashMap::default(),
                id,
                mark_histogram: memvecmap,
                queue: worker,
                status: RefCell::new(CollectorStatus {
                    collect_threshold: 1024 * 1024,
                    collecting: false,
                    last_gc_remaining: 0,
                    total_stuck_time: Duration::default(),
                    am_i_triggered: false,
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
                water_mark_sp: std::ptr::null_mut(),
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

    pub fn set_high_sp(&mut self, sp: *mut u8) {
        self.water_mark_sp = sp;
    }

    /// # get_size
    ///
    /// Get the size of allocated space.
    ///
    /// ## Return
    ///
    /// * `usize` - size
    pub fn get_size(&self) -> usize {
        unsafe { self.thread_local_allocator.as_mut().unwrap().get_size() }
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
        unsafe {
            self.thread_local_allocator
                .as_mut()
                .unwrap_unchecked()
                .mv_exausted_blocks();
        }
        if gc_is_auto_collect_enabled() {
            self.collect_if_needed_fast_unwind(sp);
        }
        let ptr = self.alloc_no_collect(size, obj_type);
        // crate::EP.fetch_add(start.elapsed().as_nanos() as u64, Ordering::Relaxed);
        if ptr.is_null() {
            spin_until!(!GC_SWEEPING.load(Ordering::Acquire));
            log::info!("gc {}: OOM, start emergency gc", self.id);
            ENABLE_EVA.store(false, Ordering::Release);
            self.collect_fast_unwind(sp);
            ENABLE_EVA.store(true, Ordering::Release);
            return unsafe {
                self.thread_local_allocator
                    .as_mut()
                    .unwrap()
                    .alloc(size, obj_type)
            };
        }
        // crate::EP.fetch_add(start.elapsed().as_nanos() as u64, Ordering::Relaxed);
        ptr
    }

    #[inline(always)]
    fn collect_if_needed_fast_unwind(&self, sp: *mut u8) {
        if GC_RUNNING.load(Ordering::Acquire) {
            log::info!("gc {}: GC is running, start gc", self.id);
            self.collect_fast_unwind(sp);
            return;
        }
        let mut status = self.status.borrow_mut();
        if (unsafe { *self.bytes_allocated_since_last_gc.get() }
            + status.last_gc_remaining * REMAIN_MULTIPLIER
            >= status.collect_threshold
            && !GC_SWEEPING.load(Ordering::Acquire))
            || (unsafe {
                self.thread_local_allocator
                    .as_mut()
                    .unwrap_unchecked()
                    .should_gc()
            } && !GC_SWEEPING.load(Ordering::Acquire))
        {
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
        unsafe {
            // let mut status = self.status.borrow_mut();
            *self.bytes_allocated_since_last_gc.get() += ((size - 1) / LINE_SIZE + 1) * LINE_SIZE;
            // drop(status);
            let ptr = self
                .thread_local_allocator
                .as_mut()
                .unwrap_unchecked()
                .alloc(size, obj_type);
            ptr
        }
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
        // eprintln!(
        //     "gc {} correct ptr result: {:?} in {:p} from  {:p} to {:p}",
        //     self.id,
        //     re,
        //     father,
        //     origin_ptr,
        //     np
        // );
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
            if self.thread_local_allocator.as_mut().unwrap().in_heap(ptr) {
                let block_p: *mut Block = Block::from_obj_ptr(ptr) as *mut _;

                let block = &mut *block_p;
                block.marked = true;
                let head = block.get_head_ptr(ptr);
                if head.is_null() {
                    return;
                }
                let (_, mut idx) = block.get_line_header_from_addr(head);
                // walk from head to end
                // let mut line_header = line_header;
                loop {
                    let ptr = block.get_nth_line(idx);
                    for i in 0..LINE_SIZE / 8 {
                        let p = ptr.add(i * 8);
                        self.mark_ptr(p);
                    }

                    idx += 1;
                    if idx == NUM_LINES_PER_BLOCK {
                        break;
                    }
                    let (line_header, _) = block.get_line_header_from_addr(ptr);
                    if line_header.get_is_head() {
                        break;
                    }
                }
            } else if self
                .thread_local_allocator
                .as_mut()
                .unwrap_unchecked()
                .in_big_heap(ptr)
            {
                let big_obj = self
                    .thread_local_allocator
                    .as_mut()
                    .unwrap()
                    .big_obj_from_ptr(ptr);
                if let Some(_big_obj) = big_obj {
                    // scan big obj from start to end and mark all pointers
                    // | head(16byte) | data |
                    // |<------- size ------>|
                    // size % 128 == 0 always, so just scan it.
                    let mut start = (_big_obj as *mut u8).add(16);
                    let end = start.add((*_big_obj).size - 16);
                    while start < end {
                        self.mark_ptr(start);
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
        if self
            .thread_local_allocator
            .as_mut()
            .unwrap_unchecked()
            .in_heap(ptr)
        {
            let block_p: *mut Block = Block::from_obj_ptr(ptr) as *mut _;

            let block = &mut *block_p;
            let is_candidate = block.is_eva_candidate();
            let mut head = block.get_head_ptr(ptr);
            if head.is_null() {
                return;
            }
            let offset_from_head = ptr.offset_from(head);
            let (line_header, idx) = block.get_line_header_from_addr(head);
            if !is_candidate || line_header.is_pinned() {
                let block = &mut *block_p;
                block.marked = true;

                if line_header.get_marked() {
                    return;
                }
            } else {
                // evacuation logic
                let (forward, h) = line_header.get_forward_start();
                let old_h = h;
                // if forward is true or cas is failed, then it's forwarded by other thread.
                let re = line_header.forward_cas(old_h);
                let shall_i_forward = !forward && re.is_ok();
                if !shall_i_forward {
                    spin_until!(line_header.get_forwarded());

                    let _ = self.correct_ptr(father, offset_from_head, ptr);
                    debug_assert!(line_header.get_used());
                    return;
                }

                // otherwise, we shall forward it
                let atomic_ptr = head as *mut AtomicPtr<u8>;

                let obj_line_size = line_header.get_obj_line_size(idx, Block::from_obj_ptr(head));
                let new_ptr =
                    self.alloc_no_collect(obj_line_size * LINE_SIZE, line_header.get_obj_type());
                if !new_ptr.is_null() {
                    let new_block = Block::from_obj_ptr(new_ptr);
                    // eprintln!("eva to block addr: {:p}", new_block);
                    debug_assert!(!new_block.is_eva_candidate());
                    let (new_line_header, _) = new_block.get_line_header_from_addr(new_ptr);
                    // 将数据复制到新的地址
                    core::ptr::copy_nonoverlapping(head, new_ptr, obj_line_size * LINE_SIZE);
                    // core::ptr::copy_nonoverlapping(line_header as * const u8, new_line_header as * mut u8, line_size);

                    // 将新指针写入老数据区开头
                    (*atomic_ptr).store(new_ptr, Ordering::SeqCst);
                    // eprintln!("gc {}: father {:p} eva {:p} to {:p}",self.id, father, head, new_ptr);
                    log::trace!("gc {}: eva {:p} to {:p}", self.id, head, new_ptr);
                    debug_assert!(!new_line_header.get_marked());
                    debug_assert!(!new_line_header.get_forwarded());
                    new_line_header.set_marked(true);
                    new_block.marked = true;
                    head = new_ptr;
                    self.correct_ptr(father, offset_from_head, ptr).expect(
                        "The thread evacuated pointer changed by another thread during evacuation.",
                    );
                    // 成功驱逐
                    line_header.set_forwarded();
                } else {
                    // 驱逐失败
                    panic!("gc: OOM during evacuation");
                }
            }

            line_header.set_marked(true);
            let obj_type = line_header.get_obj_type();
            match obj_type {
                ObjectType::Atomic => {}
                // ObjectType::Trait => self.mark_trait(head),
                // ObjectType::Complex => self.mark_complex(head),
                // ObjectType::Pointer => self.mark_ptr(head),
                _ => self.push_job(head, obj_type),
            }
        }
        // mark it if it is a big object
        else if self
            .thread_local_allocator
            .as_mut()
            .unwrap()
            .in_big_heap(ptr)
        {
            let big_obj = self
                .thread_local_allocator
                .as_mut()
                .unwrap()
                .big_obj_from_ptr(ptr);
            if let Some(big_obj) = big_obj {
                if (*big_obj).header.get_marked() {
                    return;
                }
                (*big_obj).header.set_marked(true);
                let obj_type = (*big_obj).header.get_obj_type();
                match obj_type {
                    ObjectType::Atomic => {}
                    _ => self.push_job(ptr, obj_type),
                }
            }
        }
    }

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
            || self.thread_local_allocator.as_mut().unwrap().in_heap(vptr)
            || self
                .thread_local_allocator
                .as_mut()
                .unwrap()
                .in_big_heap(vptr)
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
        unsafe {
            self.thread_local_allocator.as_ref().unwrap().print_stats();
        }
    }
    pub fn get_id(&self) -> usize {
        self.id
    }

    pub fn iter<F>(&self, f: F)
    where
        F: FnMut(*mut u8),
    {
        unsafe {
            self.thread_local_allocator.as_ref().unwrap().iter(f);
        }
    }

    /// # mark
    ///
    /// mark using backtrace-rs
    ///
    /// for more information, see [mark_fast_unwind](Collector::mark_fast_unwind)
    pub fn mark(&self) {
        self.mark_fast_unwind(std::ptr::null_mut());
    }

    fn mark_stack_offset(&self, sp: *mut u8, offset: i32, obj_type: ObjectType) {
        unsafe {
            let root = sp.offset(offset as isize);
            if root.is_null() {
                return;
            }
            match obj_type {
                ObjectType::Atomic => panic!("stack root shall never be atomic"),
                ObjectType::Trait => self.mark_trait(*(root as *mut *mut u8)),
                ObjectType::Complex => self.mark_complex(*(root as *mut *mut u8)),
                ObjectType::Pointer => self.mark_ptr(root),
                ObjectType::Conservative => self.mark_conservative(*(root as *mut *mut u8)),
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
        // let start1 = Instant::now();

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
                !GC_MARKING.load(Ordering::Acquire)
            });
            unsafe {
                self.thread_local_allocator
                    .as_mut()
                    .unwrap()
                    .get_more_works();
            }
            let stealers = v.2.values().cloned().collect::<Vec<_>>();
            drop(v);
            stealers
        } else {
            GC_MARKING.store(true, Ordering::Release);
            GC_STW_COUNT.fetch_add(1, Ordering::SeqCst);
            GC_MARK_COND.notify_all();
            unsafe {
                self.thread_local_allocator
                    .as_mut()
                    .unwrap()
                    .get_more_works();
            }
            let stealers = v.2.values().cloned().collect::<Vec<_>>();
            GC_SWEEPPING_NUM.store(count, Ordering::Release);
            drop(v);
            stealers
        };
        log::info!("gc mark {}: sync done", self.id);
        unsafe {
            self.thread_local_allocator
                .as_mut()
                .unwrap_unchecked()
                .return_prev_free_blocks();
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
                    // self.mark_all_stucked_registers();
                    log::trace!("gc {}: tracing stucked frames", self.id);
                    for f in unsafe { &*fl } {
                        self.queue.push(SendableMarkJob::Frame((f.0, f.1)));
                        // self.mark_frame(&(f.0 as _), &f.1);
                    }
                    // unsafe{self.mark_current_sp_to_pl_sp(self.stuck_sp,self.water_mark_sp);}
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
                    // self.mark_all_stucked_registers();
                    walk_gc_frames(sp, |sp, _, f| {
                        // eprintln!("gc {} mark frame {:p} {:?}", self.id,sp, f);
                        self.queue.push(SendableMarkJob::Frame((sp as _, f)));
                        // self.mark_frame(&(sp as _), &f);
                    });
                    // unsafe{self.mark_current_sp_to_pl_sp(sp,self.water_mark_sp);}
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
            unsafe {
                let p = live as *mut _ as _;
                self.mark_ptr(p);
            }
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
            let g = unsafe { GLOBAL_ALLOCATOR.0.as_mut().unwrap() };

            let mut guard = g.finalizers.lock();
            let mut remove_list = vec![];
            for (i, (p, a, f)) in guard.iter_mut().enumerate() {
                // get block of p
                let block = unsafe { Block::from_obj_ptr(*p) };
                let head = unsafe { block.get_head_ptr(*p) };
                let offset_from_head = unsafe { (*p).offset_from(head) };
                let (line_header, _) = unsafe { block.get_line_header_from_addr(head) };
                if line_header.get_forwarded()
                    && !line_header.is_pinned()
                    && line_header.get_marked()
                {
                    unsafe {
                        _ = self.correct_ptr(p as *mut _ as _, offset_from_head, *p);
                    }
                }
                if !line_header.get_marked() {
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
                while let Some(job) = self.queue.pop() {
                    match job {
                        SendableMarkJob::Frame(f) => {
                            self.mark_frame(&f.0, &f.1);
                        }
                        SendableMarkJob::Object((obj, obj_type)) => self.mark_obj(obj_type, obj),
                    }
                }
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
            .for_each(|offset| self.mark_stack_offset(*sp as _, offset, ObjectType::Pointer));
        #[cfg(target_arch = "aarch64")]
        let frame_size = f.frame_size;
        #[cfg(target_arch = "x86_64")]
        let frame_size = f.frame_size + 8;
        #[cfg(feature = "conservative_stack_scan")]
        for i in 0..=frame_size / 8 {
            self.mark_stack_offset(*sp as _, i * 8, ObjectType::Pointer);
        }
    }

    #[cfg(feature = "llvm_stackmap")]
    fn mark_globals(&self) {
        use int_enum::IntEnum;

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
                        log::debug!(
                            "gc {}: mark global {:p} {:p} {:p}",
                            self.id,
                            *root,
                            *((*root) as *mut *mut u8),
                            {
                                if self
                                    .thread_local_allocator
                                    .as_mut()
                                    .unwrap()
                                    .in_heap(*((*root) as *mut *mut u8) as _)
                                {
                                    **((*root) as *mut *mut *mut u8)
                                } else {
                                    std::ptr::null_mut()
                                }
                            }
                        );

                        match IntEnum::from_int(*tp).unwrap() {
                            ObjectType::Atomic => {}
                            ObjectType::Complex => {
                                self.mark_complex(*root);
                            }
                            ObjectType::Trait => {
                                self.mark_trait(*root);
                            }
                            ObjectType::Pointer => {
                                self.mark_ptr(*root);
                            }
                            ObjectType::Conservative => self.mark_conservative(*root),
                        }
                        // self.mark_ptr(*root);
                    });
            }
        }
    }

    /// # sweep
    ///
    /// since we did synchronization in mark, we don't need to do synchronization again in sweep
    pub fn sweep(&self) -> (usize, usize) {
        log::trace!("gc {}: sweeping...", self.id);
        let used = unsafe {
            self.thread_local_allocator
                .as_mut()
                .unwrap()
                .sweep(self.mark_histogram)
        };
        let previous_threshold = self.status.borrow().collect_threshold;
        // let previous_remaining = self.status.borrow().last_gc_remaining;
        let remaining = used.0;
        let this = unsafe { *self.bytes_allocated_since_last_gc.get() };
        if self.status.borrow().am_i_triggered
            && this <= (previous_threshold as f64 / FREE_SPACE_DIVISOR as f64) as usize
        {
            // eprintln!("gc {}: expand {} {} {}", self.id, this, previous_threshold, remaining);
            // expand threshold
            self.status.borrow_mut().collect_threshold = min(
                (previous_threshold as f64 * THRESHOLD_PROPORTION) as usize,
                unsafe { GLOBAL_ALLOCATOR.0.as_mut().unwrap().size() },
            );
        }
        //  else if  remaining <= (previous_threshold as f64 / crate::USED_SPACE_DIVISOR as f64) as usize {
        //         // shrink threshold
        //         self.status.borrow_mut().collect_threshold =
        //             (previous_threshold as f64 * crate::SHRINK_PROPORTION) as usize;
        //     }
        unsafe { *self.bytes_allocated_since_last_gc.get() = 0 };
        self.status.borrow_mut().last_gc_remaining = remaining;
        self.status.borrow_mut().am_i_triggered = false;

        let v = GC_SWEEPPING_NUM.fetch_sub(1, Ordering::AcqRel);
        if v - 1 == 0 {
            log::info!("gc {}: sweep done", self.id);
            // println!("gc sweep end {}", self.id);
            GC_SWEEPING.store(false, Ordering::Release);
        }
        #[cfg(feature = "gc_profile")]
        eprintln!(
            "gc {} done sweep at {:?}",
            self.id,
            GC_INIT_TIME.elapsed().as_nanos()
        );
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
        //         // Create a signpost interval for your function. The interval ends
        // // when the variable goes out of scope.
        // let _interval = signpost::begin_interval!(
        //     LOGGER,
        //     /* Interval ID */ self.id as _,
        //     /* Interval name */ "collect_fast_unwind_ex",
        // );
        #[cfg(feature = "gc_profile")]
        eprintln!(
            "gc {} start collect at {:?}",
            self.id,
            GC_INIT_TIME.elapsed().as_nanos(),
        );
        // unsafe {
        //     self.thread_local_allocator.as_ref().unwrap().verify();
        // }
        // let start = Instant::now();
        log::info!(
            "gc {} collecting... stucked: {}",
            self.id,
            !self.frames_list.load(Ordering::SeqCst).is_null()
        );
        // self.print_stats();
        let mut status = self.status.borrow_mut();
        // println!("gc {} collecting... {}", self.id,status.bytes_allocated_since_last_gc);
        if status.collecting {
            return Default::default();
        }
        status.collecting = true;
        drop(status);
        // evacuation pre process
        // 这个过程要在完成safepoint同步之前完成，因为在驱逐的情况下
        // 他要设置每个block是否是驱逐目标
        // 如果设置的时候别的线程的mark已经开始，那么将无法保证能够纠正所有被驱逐的指针
        unsafe {
            if ENABLE_EVA.load(Ordering::SeqCst)
                && self.thread_local_allocator.as_mut().unwrap().should_eva()
            {
                // 如果需要驱逐，首先计算驱逐阀域
                let mut eva_threshold = 0;
                let mut available_histogram: FxHashMap<usize, usize> =
                    FxHashMap::with_capacity_and_hasher(NUM_LINES_PER_BLOCK, Default::default());
                let mut available_lines = self
                    .thread_local_allocator
                    .as_mut()
                    .unwrap()
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
                self.thread_local_allocator
                    .as_mut()
                    .unwrap()
                    .set_eva_threshold(eva_threshold);
            }
            (*self.mark_histogram).clear();
        }
        // let time = std::time::Instant::now();
        unsafe {
            self.thread_local_allocator
                .as_mut()
                .unwrap()
                .set_collect_mode(true);
        }
        self.mark_fast_unwind(sp);
        // let mark_time = time.elapsed();
        let (_used, free) = self.sweep();
        // let sweep_time = time.elapsed() - mark_time;
        unsafe {
            self.thread_local_allocator
                .as_mut()
                .unwrap()
                .set_collect_mode(false);
        }
        log::info!(
            "gc {} collect done, used heap size: {} bytes, freed {} bytes in this gc",
            self.id,
            _used,
            free
        );
        let mut status = self.status.borrow_mut();
        // unsafe {
        //     self.thread_local_allocator.as_ref().unwrap().verify();
        // }
        status.collecting = false;
        // status.total_stuck_time += start.elapsed();
        // (Default::default(), Default::default())
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
    pub fn stuck_fast_unwind(&mut self, sp: *mut u8) {
        self.former_registers = unsafe { *self.registers.get() };
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
                // NOTE: **VERY ESSENCIAL** to make sure the function here will not
                // voluntarily start a new gc
                let mut first = true;
                loop {
                    if SHOULD_EXIT.load(Ordering::Relaxed) {
                        break;
                    }
                    let mut mutex = STUCK_MUTEX.lock();
                    if first {
                        first = false;
                        startsender.send(()).unwrap();
                    }
                    if endreceiver.try_recv().is_ok() {
                        drop(mutex);
                        sender.send(()).unwrap();
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
        startrecv.recv().unwrap();
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
        log::info!("gc {}: unstucking...", self.id);
        self.stuck_stop_notify_chan.send(()).unwrap();
        STUCK_COND.notify_all();
        // wait until the shadow thread exit
        self.stuck_stopped_notify_chan.1.recv().unwrap();

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
            walk_gc_frames(sp, |sp, _, f| frames.push((sp as _, f)));
        }
        frames
    }
}

fn get_fn_from_frame(frame: &backtrace::Frame) -> Option<&'static Function> {
    let map = unsafe { STACK_MAP.map.as_ref() }.unwrap();
    map.get(&(frame.ip().cast_const() as _))
}

static GLOBAL_MARK_FLAG: AtomicBool = AtomicBool::new(false);

// static STUCK_GCED: AtomicBool = AtomicBool::new(false);

lazy_static::lazy_static! {
    static ref STUCK_COND: Arc<Condvar> = Arc::new(Condvar::new());
    static ref STUCK_MUTEX:Mutex<()> = Mutex::new(());
}

unsafe impl Sync for Collector {}
unsafe impl Send for Collector {}
