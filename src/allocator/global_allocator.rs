use std::{
    collections::VecDeque,
    sync::atomic::{AtomicU64, AtomicUsize},
};

use parking_lot::{Mutex, RwLock};

use threadpool::ThreadPool;

use crate::{
    bigobj::BigObj, block::Block, consts::BLOCK_SIZE, mmap::Mmap, round_n_down, HeaderExt,
    NUM_LINES_PER_BLOCK,
};

use super::{big_obj_allocator::BigObjAllocator, global_freelist::Freelist};

type FinalizerList = Mutex<Vec<(*mut u8, *mut u8, fn(*mut u8))>>;

pub static EP: AtomicU64 = AtomicU64::new(0);

/// # Global allocator
///
/// Only allocate blocks, shared between threads, need synchronization.
pub struct GlobalAllocator {
    /// mmap region
    mmap: Mmap,
    /// current heap pointer
    current: AtomicUsize,
    /// heap start
    heap_start: *mut u8,
    /// heap end
    heap_end: *mut u8,
    /// 所有被归还的空Block都会被放到这个Vec里面
    free_blocks: Freelist<*mut Block>,
    /// 线程被销毁时的unavailable_blocks会被暂存到这里，直到下次GC的时候被别的线程
    /// 的GC获取
    unavailable_blocks: Vec<*mut Block>,
    /// big object
    big_objs: RwLock<Vec<*mut BigObj>>,
    /// 线程被销毁时的urecycle_blocks会被暂存到这里，直到下次GC的时候被别的线程
    /// 的GC获取
    recycle_blocks: Vec<*mut Block>,
    /// lock
    lock: Mutex<()>,
    /// big object mmap
    pub big_obj_allocator: BigObjAllocator,

    // last_get_block_time: std::time::Instant,
    /// 一个周期内alloc的block数减去return的block数
    /// 大于0表示内存使用量处于增加状态，小于0表示内存使用量处于减少状态
    mem_usage_flag: i64,

    // /// 周期计数器，每个内存总体增加周期加1，每个内存总体不变/减少周期减1
    // round: i64,
    pub pool: ThreadPool,

    /// a bytemap indicates whether a block is in use
    block_bytemap: *mut u8,

    pub(crate) finalizers: FinalizerList,

    free_list_mtx: RwLock<()>,

    heap_size: usize,
    total_used: AtomicUsize,
}

unsafe impl Sync for GlobalAllocator {}

// const ROUND_THRESHOLD: i64 = 10;

// const ROUND_MIN_TIME_MILLIS: u128 = 1000;

impl Drop for GlobalAllocator {
    fn drop(&mut self) {
        unsafe { libc::free(self.block_bytemap as _) }
    }
}

impl GlobalAllocator {
    // pub fn block_stealer(&self) -> Stealer<*mut Block> {
    //     self.free_blocks.lock().stealer()
    // }
    /// Create a new global allocator.
    ///
    /// size is the max heap size
    pub fn new(size: usize) -> Self {
        let mmap = Mmap::new(size * 3 / 4);

        // mmap.commit(mmap.aligned(), BLOCK_SIZE);
        // let n_workers = available_parallelism().unwrap().get();
        let start = mmap.aligned(BLOCK_SIZE);
        let end = round_n_down!(mmap.end() as usize, BLOCK_SIZE) as *mut u8;

        // bytemap is only for immix space
        let immix_size = end as usize - start as usize;
        // we use one byte per block to avoid using lock
        let bytemap_size = immix_size / BLOCK_SIZE;
        let block_bytemap: *mut u8 = unsafe { libc::malloc(bytemap_size) } as *mut u8;
        Self {
            current: AtomicUsize::new(mmap.aligned(BLOCK_SIZE) as _),
            heap_start: start,
            heap_end: end,
            mmap,
            free_blocks: Freelist::new(bytemap_size),
            big_objs: RwLock::new(Vec::new()),
            lock: Mutex::new(()),
            big_obj_allocator: BigObjAllocator::new(size / 4),
            // last_get_block_time: std::time::Instant::now(),
            // round: 0,
            mem_usage_flag: 0,
            pool: ThreadPool::default(),
            unavailable_blocks: vec![],
            recycle_blocks: vec![],
            block_bytemap,
            finalizers: Mutex::new(Vec::new()),
            free_list_mtx: RwLock::new(()),
            heap_size: 1024 * 1024,
            total_used: AtomicUsize::new(0),
        }
    }

    pub(crate) fn add_used(&self, size: usize) {
        self.total_used
            .fetch_add(size, std::sync::atomic::Ordering::Relaxed);
    }

    pub(crate) fn end_gc(&mut self) {
        // let offset = unsafe{(self.current.load(std::sync::atomic::Ordering::Relaxed) as * mut u8).offset_from(self.heap_start) as usize};
        // if offset >= self.heap_size {
        //     self.heap_size = offset;
        // }
        let total_used = self.total_used.load(std::sync::atomic::Ordering::Relaxed);
        let should_expand = total_used > self.heap_size / 2;
        // eprintln!("total used: {}, heap size: {}", total_used, self.heap_size);
        if should_expand {
            self.heap_size = self.heap_size * 11 / 10;
        }

        self.total_used
            .store(0, std::sync::atomic::Ordering::Relaxed);
    }
    /// 从big object mmap中分配一个大对象，大小为size
    pub fn get_big_obj(&mut self, size: usize) -> *mut BigObj {
        // eprintln!("get big obj: {}", size);
        let obj = self.big_obj_allocator.get_chunk(size);
        self.big_objs.write().push(obj);
        obj
    }
    pub fn big_obj_from_ptr(&self, ptr: *mut u8) -> Option<*mut BigObj> {
        for obj in self.big_objs.read().iter() {
            // FIXME: O(n); should use a tree
            let start = unsafe { (*obj as *mut u8).add(16) };
            let end = unsafe { (*obj as *mut u8).add((*(*obj)).size) };
            if start <= ptr && end >= ptr {
                return Some(*obj);
            }
        }
        None
    }

    pub fn register_finalizer(&self, ptr: *mut u8, arg: *mut u8, finalizer: fn(*mut u8)) {
        let mut finalizers = self.finalizers.lock();
        finalizers.push((ptr, arg, finalizer));
    }

    // pub fn unmap_all(&mut self) {
    //     let _lock = self.lock.lock();
    //     self.free_blocks.iter_mut().for_each(|(block, freed)| {
    //         if *freed {
    //             return;
    //         }
    //         self.mmap.dontneed(*block as *mut u8, BLOCK_SIZE);
    //         *freed = true;
    //     });
    // }

    pub fn size(&self) -> usize {
        self.heap_end as usize - self.heap_start as usize
    }

    pub fn sweep_big_objs(&mut self) {
        // eprintln!("sweep big objs");
        let _lock = self.lock.lock();
        let mut objs = self.big_objs.write();
        let mut big_objs = Vec::new();
        for obj in objs.iter() {
            // eprintln!("sweep big obj: {:p} {} {}", *obj, unsafe { (*(*obj)).size }, unsafe { (*(*obj)).header.get_marked()});
            if unsafe { (*(*obj)).header.get_marked() } {
                big_objs.push(*obj);
            } else {
                unsafe {
                    (**obj).header = 0;
                }
                self.big_obj_allocator.return_chunk(*obj);
            }
            // big_objs.push(*obj);
            unsafe {
                (*(*obj)).header &= !0b10;
            }
        }
        *objs = big_objs;
    }

    pub(crate) fn set_block_bitmap(&self, block: *mut Block, value: bool) {
        let block_start = block as usize;
        let block_index = (block_start - self.heap_start as usize) / BLOCK_SIZE;
        unsafe {
            self.block_bytemap
                .add(block_index)
                .write(if value { 1 } else { 0 })
        }
    }

    fn get_ptr_bitmap(&self, ptr: *mut u8) -> bool {
        let ptr_start = ptr as usize;
        let block_index = (ptr_start - self.heap_start as usize) / BLOCK_SIZE;
        unsafe { self.block_bytemap.add(block_index).read() == 1 }
    }

    /// 从mmap的heap空间之中获取一个Option<* mut Block>，如果heap空间不够了，就返回None
    ///
    /// 每次分配block会让current增加一个block的大小
    fn alloc_block<const N: usize>(&self, can_fail: bool) -> Option<[*mut Block; N]> {
        let current = self.current.load(std::sync::atomic::Ordering::Relaxed) as *mut u8;

        let heap_end = self.heap_end;
        let end = unsafe { current.add(BLOCK_SIZE * N) };
        if end > heap_end {
            return None;
        }
        if end > unsafe { self.heap_start.add(self.heap_size) } && can_fail {
            return None;
        }
        // crate::SLOW_PATH_COUNT.fetch_add(1, std::sync::atomic::Ordering::Relaxed);
        let current = self
            .current
            .fetch_add(BLOCK_SIZE * N, std::sync::atomic::Ordering::Relaxed)
            as *mut u8;

        self.mmap.commit(current, BLOCK_SIZE * N);
        let blocks = unsafe {
            let mut blocks = [std::ptr::null_mut(); N];
            for i in 0..N {
                blocks[i] = current.add(i * BLOCK_SIZE) as *mut Block;
                // eprintln!("new block: {:p}", blocks[i]);
            }
            blocks
        };
        // eprintln!("total blocks allocated: {}",  (current as usize - self.heap_start as usize) / BLOCK_SIZE);
        Some(blocks)
    }

    pub fn should_gc(&self) -> bool {
        unsafe {
            let p = self.current.load(std::sync::atomic::Ordering::Relaxed) as *mut u8;
            p >= self.heap_start.add(self.heap_size) && self.free_blocks.is_empty()
        }
    }

    // pub fn out_of_space(&self) ->bool {
    //     (self.heap_end as usize - self.current as usize) < BLOCK_SIZE && self.free_blocks.len() == 0
    // }

    /// # get_returned_blocks
    ///
    /// 获取所有因为线程被销毁而被归还的非空block
    pub fn get_returned_blocks(
        &mut self,
        recycle: &mut VecDeque<*mut Block>,
        unv: &mut Vec<*mut Block>,
    ) {
        let _lock = self.lock.lock();
        recycle.extend(self.recycle_blocks.drain(..).inspect(|b| unsafe {
            b.as_mut().unwrap().set_eva_threshold(NUM_LINES_PER_BLOCK);
        }));
        unv.extend(self.unavailable_blocks.drain(..).inspect(|b| unsafe {
            b.as_mut().unwrap().set_eva_threshold(NUM_LINES_PER_BLOCK);
        }));
    }

    /// # get_block
    ///
    /// 从free_blocks中获取一个可用的block，如果没有可用的block，就从mmap的heap空间之中获取一个新block
    pub fn get_block(&mut self, can_fail: bool) -> *mut Block {
        let block = if let Some(block) = self.free_blocks.pop() {
            // eprintln!("get block from free list");
            block
        } else {
            self.alloc_block::<1>(can_fail)
                .unwrap_or([std::ptr::null_mut()])[0]
        };

        if block.is_null() {
            return block;
        }
        self.set_block_bitmap(block, true);
        #[cfg(feature = "zero_init")]
        unsafe {
            core::ptr::write_bytes(block as *mut u8, 0, BLOCK_SIZE);
        }
        block
    }

    /// # return_blocks
    ///
    /// blocks是into iterator
    ///
    /// 将blocks放回free_blocks中，所有放回的空间都可能会被dontneed，访问它虽然有时不会报错，
    /// 但是可能会造成Invalid Memory Access
    pub fn return_blocks<I>(&mut self, blocks: I)
    where
        I: IntoIterator<Item = *mut Block>,
    {
        let _lock = self.free_list_mtx.write();
        for block in blocks {
            // unsafe{assert!(!block.as_mut().unwrap_unchecked().marked)};
            self.set_block_bitmap(block, false);
            self.free_blocks.push(block);
            // self.mmap
            //     .dontneed(block as *mut Block as *mut u8, BLOCK_SIZE);
        }
    }

    pub fn get_block_locked(&mut self) -> *mut Block {
        let _lock = self.free_list_mtx.read();

        let block = if let Some(block) = self.free_blocks.pop() {
            block
        } else {
            self.alloc_block::<1>(false)
                .unwrap_or([std::ptr::null_mut()])[0]
        };

        if block.is_null() {
            return block;
        }
        self.set_block_bitmap(block, true);
        #[cfg(feature = "zero_init")]
        unsafe {
            core::ptr::write_bytes(block as *mut u8, 0, BLOCK_SIZE);
        }
        block
    }

    pub fn on_thread_destroy<I>(&mut self, eva: &[*mut Block], recycle: I, unv: &[*mut Block])
    where
        I: IntoIterator<Item = *mut Block>,
    {
        let _lock = self.lock.lock();
        self.unavailable_blocks.extend_from_slice(unv);
        self.recycle_blocks.extend(recycle);
        for block in eva {
            self.mem_usage_flag -= 1;
            self.set_block_bitmap(*block, false);
            self.free_blocks.push(*block);
        }
    }

    /// # in heap
    /// 判断一个指针是否在heap之中
    pub fn in_heap(&self, ptr: *mut u8) -> bool {
        ptr >= self.heap_start
            && ptr < (self.heap_end)
            && ptr < (self.current.load(std::sync::atomic::Ordering::Relaxed) as *mut u8)
            && self.get_ptr_bitmap(ptr)
    }

    /// # in_big_heap
    /// 判断一个指针是否是一个大对象
    pub fn in_big_heap(&self, ptr: *mut u8) -> bool {
        self.big_obj_allocator.in_heap(ptr)
    }
}
