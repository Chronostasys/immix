use std::process::exit;

use crate::{gc_malloc_fast_unwind, gc_malloc_fast_unwind_ex, gc_malloc_no_collect, Collector};
use backtrace::Backtrace;
use log::trace;

#[no_mangle]
pub unsafe extern "C" fn immix_gc_init(ptr: *mut u8) {
    trace!("immix gc init, stackmap: {:p}", ptr);
    // crate::gc_disable_auto_collect();
    crate::gc_init(ptr)
}

struct DioGC();
impl DioGC {
    pub unsafe fn register_global(p: *mut u8, tp: u8) {
        crate::register_global(p, tp);
    }
    pub unsafe fn malloc(size: u64, obj_type: u8, rsp: *mut *mut u8) -> *mut u8 {
        trace!("malloc: {} {}", size, obj_type);
        #[cfg(any(test, debug_assertions))]
        crate::gc_collect_fast_unwind(rsp as _);
        let re = gc_malloc_fast_unwind(size as usize, obj_type, rsp as _);
        if re.is_null() && size != 0 {
            eprintln!("gc malloc failed! (OOM)");
            let bt = Backtrace::new();
            println!("{:?}", bt);
            exit(1);
        }
        re
    }
    pub unsafe fn malloc_no_collect(size: u64, obj_type: u8) -> *mut u8 {
        trace!("malloc: {} {}", size, obj_type);
        let re = gc_malloc_no_collect(size as usize, obj_type);
        if re.is_null() && size != 0 {
            eprintln!("gc malloc failed! (OOM)");
            let bt = Backtrace::new();
            println!("{:?}", bt);
            exit(1);
        }
        re
    }
    pub unsafe fn add_coro_stack(sp: *mut u8, stack: *mut u8) {
        crate::add_coro_stack(sp, stack);
    }
    pub unsafe fn remove_coro_stack(stack: *mut u8) {
        crate::remove_coro_stack(stack);
    }
    pub unsafe fn disable_auto_collect() {}
    pub unsafe fn enable_auto_collect() {}
    pub unsafe fn stuck_begin(sp: *mut u8) {
        crate::thread_stuck_start_fast(sp);
    }
    pub unsafe fn stuck_end() {
        crate::thread_stuck_end();
    }
    pub unsafe fn collect() {
        trace!("manual collect");
        crate::gc_collect()
    }
    pub fn get_stw_num() -> i64 {
        crate::get_gc_stw_num() as _
    }
    pub fn set_eva(eva: i32) {
        crate::set_evacuation(eva == 1);
    }
    pub fn safepoint(sp: *mut u8) {
        crate::safepoint_fast_unwind(sp)
    }
    pub fn about() {
        let dio = "
        ⠀⠀⠀⠀⠀⠀⠀⠀⠀⢹⡀⠀⠀⠀⠀⠀⠘⠀⣷⠋⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢠⡀⠀⠀⠀⠙⢦⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
        ⠀⠀⠀⠀⠀⠀⠀⠀⠀⡼⠃⠀⠀⠀⠀⠀⣤⠀⢏⠀⠀⠀⠀⢠⣠⡆⠀⠀⣦⡀⠀⠳⡀⠀⠀⠀⠀⠑⢄⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈
        ⠀⠀⠀⠀⠀⠀⠀⠀⠐⣇⡀⠀⠀⠀⠀⠀⠘⠂⢈⣦⠀⣀⡀⠈⣟⢷⣄⠀⠘⣷⣄⠀⠹⣆⠀⠀⠀⠀⠀⠙⢦⣀⠀⠀⠀⠀⠀⠀⠀⢤
        ⠀⠀⠀⠀⠐⣶⠦⠤⠴⠋⠁⠀⠀⠀⠀⡜⢷⣧⣸⣿⡀⡟⠹⡄⢹⠀⣹⣷⣤⡘⣄⠙⠲⢬⣿⣉⡉⠉⠉⠉⠉⢉⣥⣀⠀⠀⠀⠀⠀⠀
        ⠀⠀⠀⠀⠀⠈⠳⠤⢤⡀⠀⠀⠀⠀⠀⢹⡾⣿⠛⠉⣧⡇⠀⢱⣸⡔⢡⠏⠀⠉⢻⣦⣤⠀⠈⠹⣿⣂⡀⣠⠔⢉⡤⠾⡆⠀⠀⠀⠀⠀
        ⠀⠀⠀⠀⠀⠀⠀⢀⡞⣧⠀⠀⢠⠈⣇⢀⣿⠃⠀⠀⠸⣿⣠⣼⣟⣠⣯⣴⡿⠷⣿⠟⠁⠀⠀⠀⠀⠀⣇⡇⠀⡿⠦⡀⣇⠀⠀⠀⠀⠀
        ⠀⠀⠀⠀⠀⠀⠀⣾⡼⡇⠀⠀⠘⡇⣿⣿⣿⢦⣄⣧⠀⣯⣿⣼⣿⣿⠋⢿⣽⣶⡏⠀⠀⠀⠀⠀⠀⠀⢻⠇⢀⡇⣠⠇⢸⡄⠀⠀⠀⣠
        ⠀⠀⠀⠀⠀⠀⠀⠙⠓⠳⣤⣶⠀⣿⠛⣿⢻⣷⣮⣽⡆⠈⠿⠟⠻⠛⠉⠉⠋⠉⠀⠀⠀⠀⠀⠀⠀⠀⠙⠀⠘⢿⠃⠀⣼⠁⠀⠀⠀⡱
        ⠀⠀⠀⠀⠀⠀⠀⢀⣠⡴⣺⣿⢠⣍⡀⠘⡿⢿⡿⠿⣷⡄⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣀⡈⢀⡾⠃⠀⠀⠀⠘⢄
        ⠀⠀⠀⠀⠀⠀⠀⠀⠉⠉⠁⢸⡟⣾⡷⣄⢹⠀⠀⠀⣿⠁⣀⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⡏⡏⠉⠀⠀⠀⠀⠀⡐⠪
        ⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⠃⠈⠃⠀⠙⣇⠀⠀⠙⠦⠉⠉⠁⠀⠀⠀⠀⠀⢠⡆⠀⠀⠀⠀⠀⠀⠀⢸⠃⠹⡄⠀⠀⠀⠀⠀⠠⡀
        ⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠙⣆⠀⠀⢠⣤⣤⡤⢒⣊⣩⣽⣿⣿⠀⠀⠀⠀⠀⠀⠀⠀⢸⡄⠀⠙⣿⠀⡄⠀⠀⠀⠙
        ⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠘⢦⠀⠈⠹⣶⠛⣩⠔⠋⠉⠁⣸⠀⠀⠀⠀⠀⠀⠀⣠⢞⡁⠀⠀⡞⣸⠃⠀⠀⠀⠀
        ⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠳⣄⠀⠈⣿⣇⣀⣀⣀⢴⡿⠀⠀⠀⠀⠀⣠⠞⠁⣸⠀⢀⡼⠟⠹⡀⠀⠀⠀⠀
        ⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠈⠳⡄⠙⠲⠤⠥⢖⡋⠀⠀⠀⠀⡠⠊⠁⠀⢠⠇⠀⠀⠀⠀⠀⢹⣉⡉⢰⡎
        ⠀⣀⣤⠖⠒⢲⡀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠙⣆⠀⠛⠋⠉⠀⠀⢀⡤⠊⠀⠀⠀⠀⠞⠀⠀⠀⠀⠀⠀⠀⢳⡼⠋⠀
        ⠋⡝⠁⠀⠀⠀⢱⡀⢀⡴⠊⠉⠉⠙⣇⠀⠀⠀⠀⠀⠀⠀⠀⠀⢘⣄⣀⣀⣀⡤⠖⠋⠀⠀⠀⠀⠀⠀⠀⠀⣀⣀⠤⠤⠖⠊⢁⡠⠖⠋
        ⠉⠉⠉⠉⠙⡆⠀⢷⠋⠀⠀⢀⡴⠚⠁⠀⠀⠀⠀⠀⠀⣠⠴⣚⠭⠜⠛⢯⠀⡇⠀⠀⣀⣀⠤⠄⠒⠒⠉⠉⠀⣀⣀⠤⠔⠊⠁⠀⠀⠀
        ⠳⠄⠀⠀⠀⡇⢀⡼⢦⡀⣰⠋⠀⠀⠀⠀⠀⠀⠀⠀⢸⣏⣛⠓⠤⠤⡀⠘⡆⢇⣠⠞⢁⣠⠤⠤⠖⠒⠒⠉⠉⠀⠀⠀⠀⠀⠀⠀⠀⠀
        ⠀⠈⠀⠀⠀⡟⠋⠀⠀⣹⠇⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠹⡈⠉⠙⠢⡝⡄⠳⡼⠃⡴⠋⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
        ⠀⢀⠀⢀⡴⠃⠀⠀⡸⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢀⠇⠀⠀⠀⠙⢸⡞⢠⠞⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
        ⠀⣻⠒⠋⠀⠀⠀⡰⠃⠀⠀⠀⠀⠀⠀⠀⣀⣀⠠⠤⠤⠼⡀⠀⠀⠀⠀⡞⢠⠏⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
        ⠘⠁⠀⠀⠀⠀⡰⠁⠀⠀⢀⣠⠄⠒⠊⠉⠀⠀⠀⠀⠀⠀⠈⢢⡀⠀⢰⢡⠇⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
        ⠀⠀⠀⠀⢀⣼⣁⠤⠖⠊⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⣀⣽⣴⡾⠟⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀
        ⠀⠀⢀⣠⠞⠉⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⢠⣼⡟⠋⠁⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀⠀";
        println!("{}", dio);
        println!("        Dio gc");
    }
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__register_global(p: *mut u8, tp: u8) {
    DioGC::register_global(p, tp)
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__malloc_old(size: u64, obj_type: u8, rsp: *mut *mut u8) -> *mut u8 {
    DioGC::malloc(size, obj_type, rsp)
}

#[no_mangle]
pub unsafe extern "C" fn DioGC__malloc_slowpath(
    size: u64,
    obj_type: u8,
    rsp: *mut *mut u8,
    space: *mut *mut Collector,
) -> *mut u8 {
    gc_malloc_fast_unwind_ex(space, size as _, obj_type, rsp as _)
}

#[no_mangle]
pub unsafe extern "C" fn gc_set_handle(space: *mut *mut Collector) {
    if unsafe { *space }.is_null() {
        crate::SPACE.with(|gc1| {
            let gc = gc1.get();
            unsafe { *space = gc }
        });
    }
}

#[no_mangle]
pub unsafe extern "C" fn DioGC__keep_live_pinned(p: *mut u8) {
    crate::gc_keep_live_pinned(p);
}

#[no_mangle]
pub unsafe extern "C" fn DioGC__rm_live_pinned(p: *mut u8) {
    crate::gc_rm_live(p as _);
}

#[no_mangle]
pub unsafe extern "C" fn DioGC__pin(p: *mut u8) {
    crate::pin(p);
}

#[no_mangle]
pub unsafe extern "C" fn DioGC__is_pinned(p: *mut u8) -> i32 {
    crate::is_pinned(p) as _
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__malloc_no_collect(size: u64, obj_type: u8) -> *mut u8 {
    DioGC::malloc_no_collect(size, obj_type)
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__add_coro_stack(sp: *mut u8, stack: *mut u8) {
    DioGC::add_coro_stack(sp, stack)
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__remove_coro_stack(stack: *mut u8) {
    DioGC::remove_coro_stack(stack)
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__disable_auto_collect() {
    DioGC::disable_auto_collect()
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__enable_auto_collect() {
    DioGC::enable_auto_collect()
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__stuck_begin(sp: *mut u8) {
    DioGC::stuck_begin(sp)
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__stuck_end() {
    DioGC::stuck_end()
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__collect() {
    DioGC::collect()
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__get_stw_num() -> i64 {
    DioGC::get_stw_num()
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__set_eva(eva: i32) {
    DioGC::set_eva(eva)
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__safepoint_ex(sp: *mut u8, space: *mut Collector) {
    crate::safepoint_fast_unwind_ex(sp, space);
}
#[no_mangle]
pub unsafe extern "C" fn DioGC__about() {
    DioGC::about()
}

#[no_mangle]
pub unsafe extern "C" fn gc_exit_block() {
    crate::exit_block()
}

#[no_mangle]
pub unsafe extern "C" fn gc_print_block_time() {
    crate::print_block_time()
}

#[no_mangle]
pub unsafe extern "C" fn gc_set_high_sp(sp: *mut u8) {
    crate::set_high_sp(sp);
}

#[no_mangle]
pub unsafe extern "C" fn start_nano() -> u64 {
    use std::time::SystemTime;
    let duration_since_epoch = SystemTime::now()
        .duration_since(SystemTime::UNIX_EPOCH)
        .unwrap();
    let timestamp_nanos = duration_since_epoch.as_nanos(); // u128
    timestamp_nanos as u64
}

#[no_mangle]
pub unsafe extern "C" fn record_eplased(start: u64) {
    let end = start_nano();
    crate::EP.fetch_add(end - start, std::sync::atomic::Ordering::Relaxed);
}
