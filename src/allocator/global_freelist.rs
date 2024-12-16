use std::{collections::VecDeque, sync::atomic::{AtomicIsize, Ordering}};

use parking_lot::RwLock;

use crate::Block;


/// A structure used in the global allocator
/// to store the free list of objects
/// 
/// The free list is mostly used when the thread local allocator
/// try to get a new block from the global allocator, and they
/// only return the block to the global allocator just after the GC,
/// so we must ensure that the pop(get_block) operation is fast.
#[derive(Debug)]
pub struct Freelist<T> {
    inner:  Inner<T>,
}

impl <T:Copy> Freelist<T> {
    pub fn new(init_size: usize) -> Self {
        Freelist {
            inner: Inner::new(init_size),
        }
    }
    pub fn push(&mut self, item: T) {
        let inner = &mut self.inner;
        let cursor = inner.cursor.load(Ordering::Relaxed);
        if cursor < 0 {
            inner.buf[0] = item;
            inner.cursor.store(0, Ordering::Relaxed);
        } else {
            let cursor = cursor as usize + 1;
            inner.buf[cursor] = item;
            inner.cursor.store(cursor as isize, Ordering::Relaxed);
        }
    }

    pub fn pop(&self) -> Option<T> {
        let inner = & self.inner;
        let cursor = inner.cursor.fetch_sub(1, Ordering::Relaxed);
        if cursor < 0 {
            None
        } else {
            let cursor = cursor as usize;
            let item = unsafe{*inner.buf.get_unchecked(cursor)};
            Some(item)
        }
    }

    pub fn pop_n<const N:usize>(&self, dest: &mut VecDeque<T>) -> Result<(),()> {
        let inner = & self.inner;
        let cursor = inner.cursor.fetch_sub(N as isize, Ordering::Relaxed);
        for i in 0..N {
            let cursor = cursor - i as isize;
            if cursor < 0 {
                if i == 0 {
                    return Err(());
                }
                break;
            }
            let cursor = cursor as usize;
            let item = unsafe{*inner.buf.get_unchecked(cursor)};
            dest.push_back(item);
            
        }
        Ok(())
    }
    
    
}


#[derive(Debug)]
struct Inner<T> {
    buf: Box< [T]>,
    cursor: AtomicIsize,
}


impl <T> Inner<T> {
    fn new(init_size: usize) -> Self {
        let mut buf = Vec::<T>::with_capacity(init_size);
        unsafe {
            buf.set_len(init_size);
        }
        Inner {
            buf: buf.into_boxed_slice(),
            cursor: AtomicIsize::new(-1),
        }
    }
}



