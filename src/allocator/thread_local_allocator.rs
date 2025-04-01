//! # Thread-local allocator
//!
//! This module contains the thread-local allocator, which is associated with each thread.
//!
//! Thread-local allocator get empty blocks from global allocator, and allocate objects using these blocks.
//!
//! When a thread-local allocator is dropped, it will return all blocks to global allocator.

use std::collections::VecDeque;

use rustc_hash::FxHashMap;

use crate::{
    bigobj::BigObj,
    block::{Block, ObjectType},
    consts::{BLOCK_SIZE, LINE_SIZE},
    HeaderExt, EVA_BLOCK_PROPORTION, NUM_LINES_PER_BLOCK,
};

use super::GlobalAllocator;

/// # struct ThreadLocalAllocator
///
/// Thread-local allocator, associated with each thread.
///
/// Thread-local allocator get empty blocks from global allocator, and allocate objects from these blocks.
///
/// When a thread-local allocator is dropped, it will return all blocks to global allocator.
///
/// ## Fields
///
/// * `global_allocator` - global allocator
/// * `unavailable_blocks` - unavailable blocks
/// * `current_block` - current block
/// * `recyclable_blocks` - recyclable blocks
/// * `lock` - lock
#[repr(C)]
pub struct ThreadLocalAllocator {
    curr_block: *mut Block,
    global_allocator: *mut GlobalAllocator,
    unavailable_blocks: Vec<*mut Block>,
    recyclable_blocks: VecDeque<*mut Block>,
    eva_blocks: Vec<*mut Block>,
    collect_mode: bool,
    blocks_to_return: Vec<*mut Block>,
}

impl Drop for ThreadLocalAllocator {
    fn drop(&mut self) {
        let global_allocator = unsafe { &mut *self.global_allocator };
        // here we should return all blocks to global allocator
        // however, when a thread exits, it may still hold some non-empty blocks
        // those blocks shall be stored and give to another thread latter
        // eprintln!("drop thread local allocator {} eva blocks {} un blocks {} re blocks", self.eva_blocks.len(), self.unavailable_blocks.len(), self.recyclable_blocks.len());
        global_allocator.on_thread_destroy(
            &self.eva_blocks,
            self.recyclable_blocks
                .drain(..)
                .chain(self.blocks_to_return.drain(..)),
            &self.unavailable_blocks,
        );
    }
}

impl ThreadLocalAllocator {
    // pub fn verify(&self) {
    //     self.recyclable_blocks.iter().chain(self.unavailable_blocks.iter()).for_each(|b| unsafe{
    //         assert!(b.as_ref().unwrap().cursor<300);
    //     })
    // }
    /// # new
    ///
    /// Create a new thread-local allocator.
    ///
    /// ## Parameters
    ///
    /// * `global_allocator` - global allocator
    pub fn new(global_allocator: *mut GlobalAllocator) -> Self {
        let recycle_blocks = VecDeque::new();
        // recycle_blocks.push_back(initial_block);
        Self {
            curr_block: std::ptr::null_mut(),
            global_allocator,
            unavailable_blocks: Vec::new(),
            recyclable_blocks: recycle_blocks,
            eva_blocks: Vec::new(),
            collect_mode: false,
            blocks_to_return: Vec::new(),
        }
    }

    pub fn set_collect_mode(&mut self, collect_mode: bool) {
        self.collect_mode = collect_mode;
    }

    pub fn get_more_works(&mut self) {
        unsafe {
            self.global_allocator
                .as_mut()
                .unwrap()
                .get_returned_blocks(&mut self.recyclable_blocks, &mut self.unavailable_blocks);
        }
    }
    pub fn print_stats(&self) {
        println!("unavailable blocks: {:?}", self.unavailable_blocks);
        for block in &self.unavailable_blocks {
            unsafe {
                (**block).show();
            }
        }
        println!("recyclable blocks: {:?}", self.recyclable_blocks);
        for block in &self.recyclable_blocks {
            unsafe {
                (**block).show();
            }
        }
    }

    #[cfg(debug_assertions)]
    pub fn check_block_cursor(&self) {
        for block in &self.recyclable_blocks {
            unsafe {
                debug_assert!(!(**block).get_cursor().is_null());
            }
        }
    }

    pub fn iter<F>(&self, mut f: F)
    where
        F: FnMut(*mut u8),
    {
        for &b in self
            .unavailable_blocks
            .iter()
            .chain(self.recyclable_blocks.iter())
        {
            unsafe { (*b).iter(&mut f) }
        }
    }

    /// # should_eva
    ///
    /// whether the collection should run evacuation algorithm
    pub fn should_eva(&self) -> bool {
        #[cfg(debug_assertions)]
        {
            true
        }
        #[cfg(not(debug_assertions))]
        {
            self.recyclable_blocks.len() > 1
        }
    }

    pub(crate) fn correct_cursor(&self) {
        if let Some(b) = self.recyclable_blocks.front() {
            unsafe {
                (**b).count_holes_and_avai_lines();
            }
        }
    }

    pub fn fill_available_histogram(&self, histogram: &mut FxHashMap<usize, usize>) -> usize {
        let mut total_available = 0;
        self.recyclable_blocks.iter().for_each(|block| unsafe {
            let (available, holes) = (**block).get_available_line_num_and_holes();
            if let Some(v) = histogram.get_mut(&holes) {
                *v += available;
            } else {
                histogram.insert(holes, available);
            }
            total_available += available;
        });
        total_available
    }

    pub fn set_eva_threshold(&mut self, _threshold: usize) {
        self.recyclable_blocks.iter().for_each(|block| unsafe {
            (**block).set_eva_threshold({
                #[cfg(not(debug_assertions))]
                {
                    _threshold
                }
                #[cfg(debug_assertions)]
                {
                    0
                }
            })
        });
    }

    /// # get_size
    ///
    /// Get the size of allocated space.
    ///
    /// ## Return
    ///
    /// * `usize` - size
    pub fn get_size(&self) -> usize {
        let mut size = 0;
        // println!("unavailable blocks:");
        for block in &self.unavailable_blocks {
            // unsafe{(**block).show();}
            size += unsafe { (**block).get_size() };
        }
        // println!("recyclable blocks:");
        for block in &self.recyclable_blocks {
            // unsafe{(**block).show();}
            size += unsafe { (**block).get_size() };
        }
        size
    }

    pub fn should_gc(&self) -> bool {
        unsafe {
            self.recyclable_blocks.is_empty()
                && self.blocks_to_return.is_empty()
                && (*self.global_allocator).should_gc()
            // !self.unavailable_blocks.is_empty()
        }
    }

    /// # alloc
    ///
    /// 优先从recycle blocks中分配，如果中对象分配失败，使用overflow_alloc，
    /// 每用完一个recycle block则将block从recycle列表中移除，移入unavailable blocks中。
    /// 当recycle blocks为空时，申请新的空block进行分配
    ///
    /// ## Parameters
    ///
    /// * `size` - object size
    /// * `obj_type` - object type
    ///
    /// ## Return
    ///
    /// * `*mut u8` - object pointer
    #[inline(always)]
    pub fn alloc(&mut self, size: usize, obj_type: ObjectType, can_fail: bool) -> *mut u8 {
        // big size object
        if size > ((BLOCK_SIZE / LINE_SIZE - 3) / 4 - 1) * LINE_SIZE {
            return self.big_obj_alloc(size, obj_type);
        }

        self.normal_alloc(size, obj_type, can_fail)
    }

    #[inline(always)]
    fn normal_alloc(&mut self, size: usize, obj_type: ObjectType, can_fail: bool) -> *mut u8 {
        #[cfg(debug_assertions)]
        {
            self.check_block_cursor();
        }
        // mid size object & small size object
        // 刚启动或者recycle block全用光了
        if self.recyclable_blocks.is_empty() {
            let block = self.get_new_block_cannot_fail();
            if block.is_null() {
                return std::ptr::null_mut();
            }
            debug_assert!(!unsafe { (*block).get_cursor() }.is_null());
            unsafe {
                (*block).free = false;
            }
            self.recyclable_blocks.push_back(block);
        }
        let mut f = unsafe { self.recyclable_blocks.front().unwrap_unchecked() };
        unsafe {
            while (**f).is_eva_candidate() && self.collect_mode {
                let uf = self.recyclable_blocks.pop_front().unwrap_unchecked();
                self.unavailable_blocks.push(uf);
                let ff = self.recyclable_blocks.front();
                if let Some(ff) = ff {
                    f = ff;
                } else {
                    return self.normal_alloc(size, obj_type, can_fail);
                }
            }
        }
        debug_assert!((!unsafe { f.as_ref().unwrap() }.is_eva_candidate() || !self.collect_mode));
        let res = unsafe { (**f).alloc(size, obj_type) };

        match res {
            crate::AllocResult::Success(p) => {
                self.curr_block = *f;
                // if self.collect_mode {
                //     unsafe{(**f).eva_allocated = true;}
                // }
                // eprintln!("normal alloc {:p} size {}", p, size);
                p
            }
            crate::AllocResult::Fail => {
                debug_assert!(size + 8 > LINE_SIZE);
                // mid size object alloc failed, try to overflow_alloc
                self.overflow_alloc(size, obj_type, can_fail)
            }
            crate::AllocResult::Exhausted => {
                unsafe {
                    self.unavailable_blocks
                        .push(self.recyclable_blocks.pop_front().unwrap_unchecked());
                }
                self.normal_alloc(size, obj_type, can_fail)
            }
        }
    }

    /// # overflow_alloc
    ///
    /// 从global allocator中获取新block进行分配。
    ///
    /// ## Parameters
    ///
    /// * `size` - object size
    ///
    /// ## Return
    ///
    /// * `*mut u8` - object pointer
    pub fn overflow_alloc(&mut self, size: usize, obj_type: ObjectType, can_fail: bool) -> *mut u8 {
        // eprintln!("overflow alloc");
        // 获取新block
        let new_block = self.get_new_block(can_fail);
        if new_block.is_null() {
            return std::ptr::null_mut();
        }
        unsafe {
            (*new_block).free = false;
        }
        debug_assert!(!unsafe { new_block.as_ref().unwrap() }.is_eva_candidate());
        // alloc
        let re = unsafe {
            match (*new_block).alloc(size, obj_type) {
                crate::AllocResult::Success(p) => p,
                _ => unreachable!(),
            }
        };
        unsafe {
            (*new_block).correct_overflow_avai_lines();
        }
        debug_assert!(!unsafe { (*new_block).get_cursor() }.is_null());
        self.recyclable_blocks.push_back(new_block);
        // unsafe {
        //     self.curr_block = *self.recyclable_blocks.front().unwrap_unchecked();
        // }
        re
    }
    /// # big_obj_alloc
    ///
    /// 大对象分配
    ///
    /// ## Parameters
    ///
    /// * `size` - object size
    ///
    /// ## Return
    ///
    /// * `*mut u8` - object pointer
    pub fn big_obj_alloc(&mut self, size: usize, obj_type: ObjectType) -> *mut u8 {
        let obj = unsafe { (*self.global_allocator).get_big_obj(size) };
        unsafe { (*obj).header.set_obj_type(obj_type) };
        unsafe { (*obj).header.set_used(true) };
        unsafe { (obj as *mut u8).add(16) }
    }

    pub fn big_obj_from_ptr(&mut self, ptr: *mut u8) -> Option<*mut BigObj> {
        unsafe {
            self.global_allocator
                .as_mut()
                .unwrap_unchecked()
                .big_obj_from_ptr(ptr)
        }
    }

    pub fn return_prev_free_blocks(&mut self) {
        let global_allocator = unsafe { &mut *self.global_allocator };
        global_allocator.return_blocks(self.blocks_to_return.drain(..));
    }

    /// # get_new_block
    ///
    /// get a new block from global allocator.
    ///
    /// ## Return
    ///
    /// * `*mut Block` - block pointer
    fn get_new_block_cannot_fail(&mut self) -> *mut Block {
        self.get_new_block(false)
    }
    fn get_new_block(&mut self, can_fail: bool) -> *mut Block {
        let b = if self.collect_mode && !self.eva_blocks.is_empty() {
            self.eva_blocks.pop().unwrap()
        } else if let Some(b) = self.blocks_to_return.pop() {
            b
        } else if self.collect_mode {
            unsafe { (*self.global_allocator).get_block_locked() }
        } else {
            unsafe { (*self.global_allocator).get_block(can_fail) }
        };

        unsafe {
            b.as_mut().map(|b| {
                b.reset_header();
            })
        };

        b
    }
    /// # in_heap
    pub fn in_heap(&self, ptr: *mut u8) -> bool {
        unsafe { (*self.global_allocator).in_heap(ptr) }
    }

    /// # in_big_heap
    pub fn in_big_heap(&self, ptr: *mut u8) -> bool {
        unsafe { (*self.global_allocator).in_big_heap(ptr) }
    }

    pub fn global_allocator(&mut self) -> &mut GlobalAllocator {
        unsafe { self.global_allocator.as_mut().unwrap_unchecked() }
    }

    /// # sweep
    ///
    /// Iterate all blocks, if a block is not marked, free it.
    /// Correct all remain blocks' headers, and classify them
    /// into recyclable blocks and unavailable blocks.
    pub fn sweep(&mut self, mark_histogram: *mut FxHashMap<usize, usize>) -> (usize, usize) {
        let mut recyclable_blocks = VecDeque::new();
        let mut unavailable_blocks = Vec::new();
        let mut free_blocks = Vec::new();
        let mut total_used = 0;
        let mut free_lines = 0;
        unsafe {
            for block in self
                .recyclable_blocks
                .iter()
                .chain(self.unavailable_blocks.iter())
            {
                let block = *block;
                if (*block).marked {
                    let (delta_u, delta_f) = (*block).correct_header(mark_histogram);
                    total_used += delta_u;
                    free_lines += delta_f;
                    let (line, _) = (*block).get_available_line_num_and_holes();
                    if line > 0 {
                        debug_assert!(!{ (*block).get_cursor() }.is_null());
                        recyclable_blocks.push_back(block);
                    } else {
                        unavailable_blocks.push(block);
                    }
                } else {
                    free_lines += NUM_LINES_PER_BLOCK - 3;
                    block.as_mut().unwrap_unchecked().free = true;
                    free_blocks.push(block);
                }
            }
        }

        // order recycle blocks by address
        recyclable_blocks.make_contiguous().sort_unstable();
        self.recyclable_blocks = recyclable_blocks;
        self.unavailable_blocks = unavailable_blocks;
        let total_block_num =
            self.recyclable_blocks.len() + self.unavailable_blocks.len() + self.eva_blocks.len();
        let head_room_size = (EVA_BLOCK_PROPORTION * total_block_num as f64) as usize;
        if self.eva_blocks.len() > head_room_size {
            // 把多的加到free_blocks
            let over_flow = self.eva_blocks.len() - head_room_size;
            for _ in 0..over_flow {
                unsafe {
                    let b = self.eva_blocks.pop().unwrap_unchecked();
                    free_blocks.push(b);
                }
            }
        } else {
            // 尝试把少的从free_blocks取出来
            let less = head_room_size - self.eva_blocks.len();
            for _ in 0..less {
                if let Some(block) = free_blocks.pop() {
                    self.eva_blocks.push(block);
                } else {
                    break;
                }
            }
        }
        debug_assert!(
            free_blocks
                .iter()
                .filter(|b| unsafe {
                    b.as_mut().unwrap().get_available_line_num_and_holes().0 > NUM_LINES_PER_BLOCK
                })
                .count()
                == 0
        );
        free_blocks.sort_unstable();
        debug_assert!(self.blocks_to_return.is_empty());
        self.blocks_to_return = free_blocks;
        self.eva_blocks
            .iter()
            .chain(self.blocks_to_return.iter())
            .for_each(|b| unsafe {
                (*b).as_mut().unwrap_unchecked().free = true;
            });

        let curr = self.recyclable_blocks.front().cloned();
        if curr.is_none() {
            self.curr_block = self
                .blocks_to_return
                .pop()
                .unwrap_or_else(|| self.get_new_block_cannot_fail());
            if self.curr_block.is_null() {
                panic!("OOM! GC does not free enough memory!");
            }
            unsafe {
                self.curr_block.as_mut().unwrap_unchecked().free = false;
                self.curr_block.as_mut().unwrap_unchecked().reset_header();
            }
            debug_assert!(!unsafe { self.curr_block.as_ref().unwrap().get_cursor() }.is_null());
            self.recyclable_blocks.push_back(self.curr_block);
        } else {
            self.curr_block = unsafe { curr.unwrap_unchecked() };
        }
        // self.print_stats();

        let used_lines = total_used * LINE_SIZE;
        (used_lines, free_lines * LINE_SIZE)
    }
}
