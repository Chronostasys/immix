use crate::Function;

pub(crate) fn get_fn_from_frame(frame: &backtrace::Frame) -> Option<&'static Function> {
    let map = unsafe { crate::STACK_MAP.map.as_ref() }.unwrap();
    map.get(&(frame.ip().cast_const() as _))
}

pub(crate) fn get_ip_from_sp(sp: *mut u8) -> *mut u8 {
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

pub(crate) fn walk_gc_frames(
    sp: *mut u8,
    mut walker: impl FnMut(*mut u8, *mut u8, &'static Function),
) {
    let mut sp = sp;
    loop {
        let ip = get_ip_from_sp(sp);
        let frame = unsafe { crate::STACK_MAP.map.as_ref().unwrap().get(&ip.cast_const()) };
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
