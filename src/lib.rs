#![allow(clippy::not_unsafe_ptr_arg_deref)]
#![allow(clippy::missing_safety_doc)]
#![allow(clippy::needless_range_loop)]
#![allow(dead_code)]
use std::{
    cell::UnsafeCell,
    os::raw::c_void,
    sync::{
        atomic::{AtomicBool, AtomicUsize, Ordering},
        Arc,
    },
    time::Duration,
};

use crossbeam_deque::Stealer;
use immix_obj::ImmixObject;
pub use int_enum::IntEnum;
use lazy_static::lazy_static;
use libc::malloc;

mod allocator;
mod block;
mod collector;
mod consts;
#[cfg(feature = "llvm_stackmap")]
mod llvm_stackmap;
mod macros;
mod mmap;
mod shadow_stack;
#[cfg(feature = "llvm_stackmap")]
pub use llvm_stackmap::*;
mod bigobj;
#[cfg(feature = "c-api")]
pub mod c_api;

pub use allocator::*;
pub use block::*;
pub use collector::*;
pub use consts::*;

use parking_lot::{Condvar, Mutex};
#[cfg(feature = "llvm_stackmap")]
use rustc_hash::FxHashMap;

thread_local! {
    pub static SPACE: UnsafeCell<Collector> = unsafe {
        // gc运行中的时候不能增加线程
        let gc = Collector::new(GLOBAL_ALLOCATOR.0.as_mut().unwrap());
        UnsafeCell::new(gc)
    };
}

// pub static SPACE: Lazy<ThreadLocal< RefCell<Collector>>> = Lazy::new(|| ThreadLocal::new(|| unsafe {
//     // gc运行中的时候不能增加线程
//     let gc = Collector::new(GLOBAL_ALLOCATOR.0.as_mut().unwrap());
//     RefCell::new(gc)
// }));
#[cfg(feature = "llvm_stackmap")]
lazy_static! {
    static ref STACK_MAP: StackMapWrapper = {
        let map = Box::into_raw(Box::default());
        let global_roots = Box::into_raw(Box::default());
        StackMapWrapper { map, global_roots }
    };
}

pub fn register_global(p: *mut u8, tp: ObjectType) {
    unsafe {
        STACK_MAP.global_roots.as_mut().unwrap().push((p, tp));
    }
}

#[cfg(feature = "llvm_stackmap")]
pub struct StackMapWrapper {
    pub map: *mut FxHashMap<*const u8, Function>,
    pub global_roots: *mut Vec<(*mut u8, ObjectType)>,
}
#[cfg(feature = "llvm_stackmap")]
unsafe impl Sync for StackMapWrapper {}
#[cfg(feature = "llvm_stackmap")]
unsafe impl Send for StackMapWrapper {}
const DEFAULT_HEAP_SIZE: usize = 1024 * 1024 * 1024 * 16;
lazy_static! {
    pub static ref GLOBAL_ALLOCATOR: GAWrapper = unsafe {
        let mut heap_size = DEFAULT_HEAP_SIZE;
        if let Ok(usage) = sys_info::mem_info() {
            heap_size = usage.total as usize * 1024;
        } else {
            log::warn!(
                "Failed to get virtual memory size, use default heap size {} byte",
                heap_size
            );
        }

        if let Ok(size) = std::env::var("PL_IMMIX_HEAP_SIZE") {
            heap_size = size.parse().unwrap();
        }
        heap_size = round_n_up!(heap_size, BLOCK_SIZE);
        log::info!("heap size: {}", heap_size);
        let ga = GlobalAllocator::new(heap_size);

        let mem = malloc(core::mem::size_of::<GlobalAllocator>()).cast::<GlobalAllocator>();
        mem.write(ga);
        GAWrapper(mem)
    };
}

/// This function is used to allocate a new object on the heap.
/// The size of the object is given in bytes by the size argument.
/// The object type is specified by the obj_type argument, which is a u8.
/// This function is used to allocate all objects (except
/// for the object header) on the heap,
/// and it is used by both the GC and the user.
/// This function is used by the user in the following manner:
/// ```ignore
/// let obj = gc_malloc(size, obj_type);
/// ```
/// where obj is a pointer to the newly allocated object.
///
/// ## Behaviour
///
/// If auto gc is enabled, this function may trigger a gc if some conditions are met.
///
/// If the heap is full, this function will trigger an emergency gc and try again.
/// If the heap is still full after the emergency gc, this function will return null.
pub fn gc_malloc(size: usize, obj_type: u8) -> *mut u8 {
    SPACE.with(|gc| {
        // println!("start malloc");
        let gc = unsafe { gc.get().as_ref().unwrap() };
        // println!("malloc");
        gc.alloc(size, ObjectType::from_int(obj_type).unwrap())
    })
}

pub fn print_block_time() {
    SPACE.with(|gc| {
        let gc = unsafe { gc.get().as_ref().unwrap() };
        let duration = gc.gc_stw_duration();
        println!("gc stw duration: {:?}", duration);
    })
}

pub fn set_low_sp(sp: *mut u8) {
    SPACE.with(|gc| {
        let gc = unsafe { gc.get().as_mut().unwrap() };
        gc.set_low_sp(sp);
    })
}

pub fn current_sp() -> *mut u8 {
    Collector::current_sp()
}

/// # gc_malloc_fast_unwind
///
/// Same behavior as gc_malloc, but this function will use stack
/// pointer to perform fast unwind
///
/// If the stack pointer is not provided, this function will use
/// backtrace-rs to walk the stack.
///
/// For more information, see [mark_fast_unwind](crate::collector::Collector::mark_fast_unwind)
#[inline(always)]
pub fn gc_malloc_fast_unwind(size: usize, obj_type: u8, sp: *mut u8) -> *mut u8 {
    let me_sp = Collector::current_sp();
    let (p, gc) = SPACE.with(|gc| {
        // println!("start malloc");
        unsafe {
            gc.get().as_mut().unwrap_unchecked().set_low_sp(me_sp);
        };
        let gc = unsafe { gc.get().as_mut().unwrap_unchecked() };
        // println!("malloc");
        (
            gc.alloc_fast_unwind(size, ObjectType::from_int(obj_type).unwrap(), sp),
            gc,
        )
    });
    gc.set_low_sp(me_sp);

    p
}

#[inline(always)]
pub fn gc_malloc_fast_unwind_ex(
    mut space: *mut *mut Collector,
    size: usize,
    obj_type: u8,
    sp: *mut u8,
) -> *mut u8 {
    let me_sp = Collector::current_sp();
    // SLOW_PATH_COUNT.fetch_add(1, Ordering::Relaxed);
    // gc_malloc_fast_unwind(size, obj_type, sp)
    let re = if unsafe { *space }.is_null() {
        let re = SPACE.with(|gc1| {
            {
                let space: &mut *mut *mut Collector = &mut space;
                let gc = gc1.get();
                unsafe { **space = gc }
                // let regs = Collector::get_registers();

                // let sp = Collector::current_sp();
                unsafe {
                    gc.as_mut().unwrap_unchecked().set_low_sp(me_sp);
                };
                unsafe { gc.as_mut().unwrap_unchecked().store_registers() };
                // eprintln!("space setted {:p}", gc);
                let re = unsafe { gc.as_ref().unwrap_unchecked() }.alloc_fast_unwind(
                    size,
                    ObjectType::from_int(obj_type).unwrap(),
                    sp,
                );
                re
            }
        });
        re
    } else {
        let gc = unsafe { *space };
        // let regs = Collector::get_registers();
        // let sp = Collector::current_sp();
        unsafe {
            gc.as_mut().unwrap_unchecked().set_low_sp(me_sp);
        };
        unsafe { gc.as_mut().unwrap_unchecked().store_registers() };
        // eprintln!("space get {:p}", gc);
        let re = unsafe { gc.as_ref().unwrap_unchecked() }.alloc_fast_unwind(
            size,
            ObjectType::from_int(obj_type).unwrap(),
            sp,
        );
        re
    };
    unsafe {
        (**space).restore_callee_saved_registers();
    }
    re
}

/// # gc_malloc_no_collect
///
/// Same behavior as gc_malloc, but this function will never trigger
/// a gc.
pub fn gc_malloc_no_collect(size: usize, obj_type: u8) -> *mut u8 {
    SPACE.with(|gc| {
        // println!("start malloc");
        let gc = unsafe { gc.get().as_ref().unwrap() };
        // println!("malloc");
        gc.alloc_no_collect(size, ObjectType::from_int(obj_type).unwrap())
    })
}

/// # gc_register_finalizer
///
/// Register a finalizer for an object.
///
/// The finalizer will be called when the object is collected.
///
/// ## Parameters
///
/// * `obj` - object pointer, must be allocated by gc. Does not need to be pinned.
/// * `arg` - argument for the finalizer
/// * `f` - finalizer function
pub fn gc_register_finalizer(obj: *mut u8, arg: *mut u8, f: fn(*mut u8)) {
    unsafe {
        GLOBAL_ALLOCATOR
            .0
            .as_mut()
            .unwrap()
            .register_finalizer(obj, arg, f);
    }
}

/// This function is used to force a garbage collection.
///
/// During the collection mark phase, this function will
/// use backtrace-rs to walk the stack.
///
/// For more information, see [mark_fast_unwind](crate::collector::Collector::mark_fast_unwind)
pub fn gc_collect() {
    SPACE.with(|gc| {
        // println!("start collect");
        let gc = unsafe { gc.get().as_ref().unwrap() };
        gc.collect();
        // println!("collect")
    })
}

/// # gc_collect_fast_unwind
///
/// Same behavior as gc_collect, but this function will use stack
/// pointer to perform fast unwind.
///
/// For more information, see [mark_fast_unwind](crate::collector::Collector::mark_fast_unwind)
pub fn gc_collect_fast_unwind(sp: *mut u8) {
    SPACE.with(|gc| {
        // println!("start collect");
        let gc = unsafe { gc.get().as_ref().unwrap() };
        gc.collect_fast_unwind(sp);
        // println!("collect")
    })
}

#[cfg(feature = "shadow_stack")]
pub fn gc_add_root(root: *mut u8, obj_type: u8) {
    SPACE.with(|gc| {
        // println!("start add_root");
        let gc = unsafe { gc.get().as_mut().unwrap() };
        gc.add_root(root, ObjectType::from_int(obj_type).unwrap());
        // println!("add_root")
    })
}

pub fn gc_keep_live(gc_ptr: *mut u8) -> u64 {
    SPACE.with(|gc| {
        // println!("start add_root");
        let gc = unsafe { gc.get().as_ref().unwrap() };
        gc.keep_live(gc_ptr)
        // println!("add_root")
    })
}

pub fn gc_keep_live_pinned(gc_ptr: *mut u8) -> u64 {
    SPACE.with(|gc| {
        // println!("start add_root");
        let gc = unsafe { gc.get().as_ref().unwrap() };
        gc.keep_live_pinned(gc_ptr)
        // println!("add_root")
    })
}

pub fn gc_rm_live(handle: u64) {
    SPACE.with(|gc| {
        // println!("start add_root");
        let gc = unsafe { gc.get().as_ref().unwrap() };
        gc.rm_live(handle);
        // println!("add_root")
    })
}

#[cfg(feature = "shadow_stack")]
pub fn gc_remove_root(root: *mut u8) {
    SPACE.with(|gc| {
        // println!("start remove_root");
        let gc = unsafe { gc.get().as_mut().unwrap() };
        gc.remove_root(root);
        // println!("remove_root")
    })
}

#[inline(always)]
pub fn gc_is_auto_collect_enabled() -> bool {
    GC_AUTOCOLLECT_ENABLE
}

pub fn no_gc_thread() {
    SPACE.with(|gc| {
        unsafe { gc.get().as_mut().unwrap() }.unregister_current_thread();
    })
}

pub fn safepoint() {
    SPACE.with(|gc| {
        unsafe { gc.get().as_ref().unwrap() }.safepoint();
    })
}

pub fn safepoint_fast_unwind(sp: *mut u8) {
    SPACE.with(|gc| {
        unsafe { gc.get().as_ref().unwrap() }.safepoint_fast_unwind(sp);
    })
}

pub fn register_current_thread() -> *mut Collector {
    SPACE.with(|gc| gc.get())
}

pub fn safepoint_fast_unwind_ex(sp: *mut u8, gc: *mut Collector) {
    let me_sp = Collector::current_sp();
    unsafe {
        let gc = gc.as_mut().unwrap();
        gc.set_low_sp(me_sp);
        gc.store_registers();
    }
    unsafe { gc.as_ref().unwrap() }.safepoint_fast_unwind(sp);
}

#[cfg(feature = "llvm_stackmap")]
pub fn gc_init(ptr: *mut u8) {
    // print_stack_map(ptr);
    // println!("stackmap: {:?}", &STACK_MAP.map.borrow());
    build_root_maps(ptr, unsafe { STACK_MAP.map.as_mut().unwrap() });
    #[cfg(feature = "gc_profile")]
    eprintln!("init done {:?}", &GC_INIT_TIME.elapsed().as_nanos());
    log::info!("read stack map done");
}

/// notify gc current thread is going to stuck e.g.
/// lock a mutex or doing sync io or sleep etc.
///
/// during thread stucking, gc will start a nanny thread to
/// do gc works that original thread should do.
///
/// ## Note
///
/// During thread stucking, the stucking thread should not
/// request any memory from gc, or it will cause a panic.
pub fn thread_stuck_start() {
    // v.0 -= 1;
    SPACE.with(|gc| {
        // println!("start add_root");
        let gc = unsafe { gc.get().as_mut().unwrap() };
        gc.stuck()
        // println!("add_root")
    });
}

#[inline(always)]
pub fn thread_stuck_start_fast(sp: *mut u8) {
    // v.0 -= 1;
    let me_sp = Collector::current_sp();
    SPACE.with(|gc| {
        let gc = unsafe { gc.get().as_mut().unwrap() };
        gc.set_low_sp(me_sp);
        // let regs = Collector::get_registers();
        // gc.set_registers(regs);
        gc.stuck_fast_unwind(sp)
        // println!("add_root")
    });
}

/// notify gc current thread is not stuck anymore
///
/// if a gc is triggered during thread stucking, this function
/// will block until the gc is finished
pub fn thread_stuck_end() {
    log::trace!("unstucking...");
    // v.0 += 1;
    SPACE.with(|gc| {
        // println!("start add_root");
        let gc = unsafe { gc.get().as_mut().unwrap() };
        gc.unstuck()
        // println!("add_root")
    });
}

pub fn add_coro_stack(sp: *mut u8, stack: *mut u8) {
    SPACE.with(|gc| {
        // println!("start add_root");
        let gc = unsafe { gc.get().as_mut().unwrap() };
        gc.add_coro_stack(sp, stack)
        // println!("add_root")
    });
}

pub fn remove_coro_stack(stack: *mut u8) {
    SPACE.with(|gc| {
        // println!("start add_root");
        let gc = unsafe { gc.get().as_mut().unwrap() };
        gc.remove_coro_stack(stack)
        // println!("add_root")
    });
}

pub unsafe fn pin(obj: *mut u8) {
    let obj = ImmixObject::from_unaligned_ptr(obj).unwrap_unchecked();
    obj.as_mut().unwrap_unchecked().byte_header.pin();
}

pub unsafe fn is_pinned(obj: *mut u8) -> bool {
    let obj = ImmixObject::from_unaligned_ptr(obj).unwrap_unchecked();
    obj.as_mut().unwrap_unchecked().byte_header.is_pinned()
}

/// # set evacuation
///
/// 设置是否开启自动驱逐
///
/// 驱逐(evacuation)是immix一种去碎片化机制
///
/// 一般来说驱逐能带来更好的性能，但是请注意，驱逐会
/// 改变mutator指针的指向，正常来说这种改动是自愈的，
/// 在gc过程结束后mutator应当不会受到影响，但是如果
/// mutator中**特殊**存储了指向堆内存的指针，且该数据不被gc
/// 观测，那么驱逐可能会导致它指向错误的地址。
pub fn set_evacuation(eva: bool) {
    ENABLE_EVA.store(eva, Ordering::SeqCst);
}

pub struct GAWrapper(*mut GlobalAllocator);

impl GAWrapper {}

enum SendableMarkJob {
    Frame((*mut c_void, &'static Function)),
    Object((*mut u8, ObjectType)),
}

unsafe impl Send for SendableMarkJob {}
unsafe impl Sync for SendableMarkJob {}

lazy_static! {
/// collector count
///
/// should be the same as the number of threads
static ref GC_COLLECTOR_COUNT: Mutex<(usize, usize, FxHashMap<usize,Stealer<SendableMarkJob>>)> = {
    Mutex::new((0, 0, FxHashMap::default()))
};
}

// static GC_MARK_WAITING: AtomicUsize = AtomicUsize::new(0);

static GC_MARKING: AtomicBool = AtomicBool::new(false);

// static GC_MARK_COND: Arc< Condvar> = Arc::new( Condvar::new());

lazy_static! {
    static ref GC_MARK_COND: Arc<Condvar> = Arc::new(Condvar::new());
}

static GC_SWEEPPING_NUM: AtomicUsize = AtomicUsize::new(0);

static GC_SWEEPING: AtomicBool = AtomicBool::new(false);

static GC_RUNNING: AtomicBool = AtomicBool::new(false);

static GC_ID: AtomicUsize = AtomicUsize::new(0);

static GC_STW_COUNT: AtomicUsize = AtomicUsize::new(0);

pub(crate) static USE_SHADOW_STACK: AtomicBool = AtomicBool::new(false);

pub static ENABLE_EVA: AtomicBool = AtomicBool::new(true);

pub static SHOULD_EXIT: AtomicBool = AtomicBool::new(false);

#[cfg(feature = "gc_profile")]
lazy_static! {
    pub static ref GC_INIT_TIME: std::time::Instant = std::time::Instant::now();
}

#[cfg(feature = "auto_gc")]
const GC_AUTOCOLLECT_ENABLE: bool = true;
#[cfg(not(feature = "auto_gc"))]
const GC_AUTOCOLLECT_ENABLE: bool = false;

unsafe impl Sync for GAWrapper {}

pub fn get_gc_stw_num() -> usize {
    GC_STW_COUNT.load(Ordering::SeqCst)
}

pub fn set_shadow_stack(b: bool) {
    USE_SHADOW_STACK.store(b, Ordering::Relaxed);
}

#[cfg(feature = "llvm_gc_plugin")]
pub unsafe fn set_shadow_stack_addr(addr: *mut u8) {
    shadow_stack::SetShadowStackAddr(addr)
}

pub fn exit_block() {
    SHOULD_EXIT.store(true, Ordering::SeqCst);
    let mut v = GC_COLLECTOR_COUNT.lock();
    GC_MARK_COND.notify_all();
    GC_MARK_COND.wait_while_for(
        &mut v,
        |(c, _, _)| *c != 0 || STUCK_COUNT.load(Ordering::SeqCst) != 0,
        Duration::from_micros(100),
    );
}

pub(crate) static STUCK_COUNT: AtomicUsize = AtomicUsize::new(0);
