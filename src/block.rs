use std::sync::atomic::{AtomicU8, Ordering};

use int_enum::IntEnum;
use rustc_hash::FxHashMap;

use crate::consts::{BLOCK_SIZE, LINE_SIZE, NUM_LINES_PER_BLOCK};

/// # Object type
///
/// Object types. Used to support precise GC.
///
/// need 2 bits to represent.
#[repr(u8)]
#[derive(Debug, Clone, Copy, PartialEq, Eq, IntEnum)]
pub enum ObjectType {
    /// Atomic object, means the object does not contain any pointers.
    Atomic = 0,
    /// Trait object, only contains one heap pointer at offset 1.
    Trait = 1,
    /// Complex object, contains multiple heap pointers.
    ///
    /// A complex object must provide a `visit` method to iterate through all heap pointers.
    Complex = 2,
    /// Pointer object, contains one heap pointer.
    Pointer = 3,
    /// Conservative object
    Conservative = 4,
}

#[derive(Debug, Clone, Copy, PartialEq, Eq)]
pub enum AllocResult {
    Success(*mut u8),
    Fail,
    Exauted
}

type LineHeader = u8;

pub trait HeaderExt {
    fn get_used(&self) -> bool;
    fn get_marked(&self) -> bool;
    fn get_obj_type(&self) -> ObjectType;
    fn set_used(&mut self, used: bool);
    fn set_marked(&mut self, marked: bool);
    fn set_obj_type(&mut self, obj_type: ObjectType);
}

pub trait LineHeaderExt {
    fn is_medium_body(&mut self) -> bool;
    fn set_forwarded(&mut self);
    fn get_forwarded(&self) -> bool;
    fn get_forward_start(&self) -> (bool, LineHeader);
    fn forward_cas(&mut self, old: u8) -> Result<u8, u8>;
    fn is_pinned(&self) -> bool;
    fn pin(&mut self);
    fn set_medium(&mut self);
}

#[inline(always)]
fn count_next_zeros(line_map: &[u8; 256], idx: usize) -> usize {
    let mut len = 0;
    for i in line_map.iter().take(NUM_LINES_PER_BLOCK).skip(idx) {
        if i & 1 == 0 {
            len += 1;
        } else {
            break;
        }
    }
    len
}

/// A block is a 32KB memory region.
///
/// A block is divided into 256 lines, each line is 128 bytes.
///
/// **the leading 3 lines are reserved for metadata.**
#[repr(C)]
pub struct Block {
    /// 第一个hole的起始地址
    cursor: * mut u8,
    hole_end: * mut u8,
    available_line_num: usize,
    /// 洞的数量
    hole_num: usize,
    end: * mut u8,
    /// |                           LINE HEADER(1 byte)                         |
    /// |    7   |    6   |    5   |    4   |    3   |    2   |    1   |    0   |
    /// | medium |   eva  |  evaed |        -----------       | marked |  used  |
    ///
    /// When the evaed bit is set and eva is not, the line is pinned.
    line_map: [LineHeader; NUM_LINES_PER_BLOCK],
    /// 是否被标记
    pub marked: bool,
    eva_target: bool,
}

impl HeaderExt for u8 {
    #[inline]
    fn get_used(&self) -> bool {
        self & 0b1 == 0b1
    }
    #[inline]
    fn get_marked(&self) -> bool {
        self & 0b10 == 0b10
    }
    #[inline]
    fn get_obj_type(&self) -> ObjectType {
        ObjectType::from_int((self >> 2) & 0b111).expect("invalid object type")
    }
    #[inline]
    fn set_used(&mut self, used: bool) {
        if used {
            *self |= 0b1;
        } else {
            *self &= !0b1;
        }
    }
    #[inline]
    fn set_obj_type(&mut self, obj_type: ObjectType) {
        // *self &= !0b110;
        *self |= (obj_type as u8) << 2;
    }
    #[inline]
    fn set_marked(&mut self, marked: bool) {
        if marked {
            *self |= 0b10;
        } else {
            *self &= !0b10;
        }
    }
}
impl LineHeaderExt for LineHeader {
    #[inline]
    fn set_forwarded(&mut self) {
        let atom_self = self as *mut u8 as *mut AtomicU8;
        unsafe {
            let value = (*atom_self).load(Ordering::SeqCst);
            let forwarded = value | 0b100000;
            (*atom_self).store(forwarded, Ordering::Release);
        }
    }
    fn set_medium(&mut self) {
        *self |= 0b10000000;
    }
    fn is_medium_body(&mut self) -> bool {
        *self & 0b10000000 == 0b10000000
    }
    #[inline]
    fn get_forward_start(&self) -> (bool, LineHeader) {
        let atom_self = self as *const u8 as *const AtomicU8;
        let load = unsafe { (*atom_self).load(Ordering::Acquire) };
        (load & 0b1000000 == 0b1000000, load)
    }

    #[inline]
    fn get_forwarded(&self) -> bool {
        let atom_self = self as *const u8 as *const AtomicU8;
        let load = unsafe { (*atom_self).load(Ordering::Acquire) };
        load & 0b100000 == 0b100000
    }
    #[inline]
    fn forward_cas(&mut self, old: u8) -> Result<u8, u8> {
        let atom_self = self as *mut u8 as *mut AtomicU8;
        unsafe {
            (*atom_self).compare_exchange(old, old | 0b1000000, Ordering::SeqCst, Ordering::SeqCst)
        }
    }




    fn is_pinned(&self) -> bool {
        self & 0b1100000 == 0b0100000
    }

    fn pin(&mut self) {
        *self |= 0b100000;
        *self &= !0b1000000;
    }
}

impl Block {
    /// Create a new block.
    ///
    /// at must be a `BLOCK_SIZE` aligned pointer.
    pub fn new(at: *mut u8) -> &'static mut Self {
        unsafe {
            let ptr = at as *mut Self;
            debug_assert!(ptr as usize % BLOCK_SIZE == 0);
            ptr.write(Self {
                line_map: [0; NUM_LINES_PER_BLOCK],
                cursor: (ptr as *mut u8).offset((LINE_SIZE*3) as _), // 跳过前三行，都用来放metadata。浪费一点空间（metadata从0.8%->1.2%）
                hole_end: (ptr as *mut u8).offset(BLOCK_SIZE as _),
                end: (ptr as *mut u8).offset(BLOCK_SIZE as _),
                marked: false,
                hole_num: 1,
                available_line_num: NUM_LINES_PER_BLOCK - 3,
                eva_target: false,
            });

            &mut *ptr
        }
    }

    pub fn get_available_line_num_and_holes(&self) -> (usize, usize) {
        (self.available_line_num, self.hole_num)
    }

    pub fn show(&self) {
        println!("size: {}", self.get_size());
        println!("first_hole_line_idx: {:?}", self.cursor);
        println!("marked: {}", self.marked);
        println!("hole_num: {}", self.hole_num);
        println!("available_line_num: {}", self.available_line_num);
        println!("line_map: {:?}", self.line_map);
    }


    pub fn get_obj_line_size(&mut  self, idx: usize) -> usize {
        // 往后遍历获取自身大小
        let mut line_size = 1;
        while idx + line_size < NUM_LINES_PER_BLOCK
            && self.line_map[idx + line_size].is_medium_body()
        {
            line_size += 1;
        }
        line_size
    }

    /// return the used size of the block
    pub fn get_size(&self) -> usize {
        self.line_map[3..NUM_LINES_PER_BLOCK]
            .iter()
            .filter(|&&x| x & 1 == 1)
            .map(|_| 1)
            .sum::<usize>()
    }

    pub fn iter<F>(&mut self, mut f: F)
    where
        F: FnMut(*mut u8),
    {
        let ptr = self as *mut Self as *mut u8;
        self.line_map[0..NUM_LINES_PER_BLOCK]
            .iter()
            .enumerate()
            .filter(|(_, x)| **x & 1 == 1)
            .for_each(|(i, _)| unsafe { f(ptr.add(i * LINE_SIZE)) })
    }
    pub fn reset_header(&mut self) {
        let ptr = self as *mut Self as *mut u8;
        self.cursor = unsafe{ptr.add(LINE_SIZE * 3)};
        self.line_map = [0; NUM_LINES_PER_BLOCK];
        self.marked = false;
        self.hole_num = 1;
        self.available_line_num = NUM_LINES_PER_BLOCK - 3;
        self.eva_target = false;
        self.hole_end = unsafe{ptr.add(BLOCK_SIZE)};
        self.end = unsafe {(ptr as *mut u8).offset(BLOCK_SIZE as _)};
    }

    pub fn get_cursor(&self) -> *mut u8 {
        self.cursor
    }

    /// # correct_header
    /// 回收的最后阶段，重置block的header
    pub unsafe fn correct_header(
        &mut self,
        mark_histogram: *mut FxHashMap<usize, usize>,
    ) -> (usize, usize) {
        let mut idx = 3;
        let mut used_lines = 0;
        let mut hole_num = 0;
        let mut hole_flag = false;
        let mut cursor = None;
        let mut hole_end = None;
        while idx < NUM_LINES_PER_BLOCK {
            if !self.line_map[idx].is_pinned() {
                if self.line_map[idx].get_forwarded() && self.line_map[idx].get_marked() {
                    self.line_map[idx].set_marked(false);
                }
                // 如果pin了，需要把记号一直保留，这里没pin所以直接清除
                self.line_map[idx] &= !0b1100000; // unset forward bits
            }
            if self.line_map[idx].get_marked() {
                if cursor.is_some() && hole_end.is_none() {
                    hole_end = Some(self.get_nth_line(idx));
                }
                hole_flag = false;
                // unset mark bit, set used bit
                self.line_map[idx] &= !0b10;
                self.line_map[idx] |= 0b1;

                used_lines += 1;
                // get next line, check is medium flag
                idx += 1;
                while idx < NUM_LINES_PER_BLOCK && self.line_map[idx] & 0b10000000 == 0b10000000 {
                    // set used bit
                    self.line_map[idx] &= !0b10;
                    self.line_map[idx] |= 0b1;
                    used_lines += 1;
                    idx += 1;
                }
            } else {
                if cursor.is_none() {
                    cursor = Some(self.get_nth_line(idx));
                }
                if !hole_flag {
                    hole_num += 1;
                    hole_flag = true;
                }
                self.line_map[idx] &= 0;
                idx += 1;
            }
            
        }

        if let Some(cursor) = cursor {
            self.cursor = cursor;
            self.hole_end = hole_end.unwrap_or(self.end);
        }
        self.available_line_num = NUM_LINES_PER_BLOCK - 3 - used_lines;
        self.hole_num = hole_num;
        self.marked = false;
        self.eva_target = false;
        if let Some(count) = (*mark_histogram).get_mut(&self.hole_num) {
            *count += used_lines;
        } else {
            (*mark_histogram).insert(self.hole_num, used_lines);
        }
        (used_lines, self.available_line_num)
    }

    /// # find_next_hole
    ///
    /// input a tuple (u8, u8) representing previous hole
    ///
    /// Find the next hole in the block.
    ///
    /// Return the start line index and the length of the hole (u8, u8).
    ///
    /// If no hole found, return `None`.
    #[inline(always)]
    pub fn find_next_hole(
        &self,
        prev_hole: (usize, usize),
        size_line: usize,
    ) -> Option<(usize, usize)> {
        let mut idx = prev_hole.0 + prev_hole.1;
        let mut len = 0;
        let line_map: &[u8; 256] = &self.line_map;

        while idx < NUM_LINES_PER_BLOCK {
            if line_map[idx] & 1 == 0 {
                len += 1;
                if len >= size_line {
                    return Some((idx - len + 1, len + count_next_zeros(line_map, idx + 1)));
                }
            } else {
                if len >= size_line {
                    return Some((idx - len, len + count_next_zeros(line_map, idx)));
                } else if len > 0 {
                    return None;
                }
                len = 0;
            }

            idx += 1;
        }

        None
    }

    /// # get_nth_line
    ///
    /// get the line at nth index as * mut u8
    ///
    /// # Safety
    ///
    /// The caller must ensure that the index is valid.
    pub unsafe fn get_nth_line(&mut self, idx: usize) -> *mut u8 {
        debug_assert!(idx < NUM_LINES_PER_BLOCK);
        (self as *mut Self as *mut u8).add(idx * LINE_SIZE)
    }

    /// # from_obj_ptr
    ///
    /// get the block from a pointer
    ///
    /// note that the pointer does not need to be exactly at the start of the block
    ///
    /// # Safety
    ///
    /// The caller must ensure that the pointer is valid.
    pub unsafe fn from_obj_ptr(ptr: *mut u8) -> &'static mut Self {
        // ptr may not be at the start of the block
        // the block start address is the nearest multiple of BLOCK_SIZE
        // get the block start address
        let ptr = ptr as usize;
        let block_start = ptr - (ptr % BLOCK_SIZE);
        &mut *(block_start as *mut Self)
    }

    /// # get_head_ptr
    ///
    /// A pointer in the graph may not point to the start position of the
    /// space we allocated for it. Consider the following example:
    ///
    /// ```pl
    ///
    /// struct A {
    ///     a: u8;
    ///     b: u8;
    /// }
    ///
    /// let a = A { a: 1, b: 2 };
    /// let ptr = &a.b; // where ptr is a pointer to the field b, what we want is a pointer to the struct A
    /// ```
    ///
    /// This function is used to get the pointer to the start position of the space we allocated for the object,
    /// from a pointer in the graph. e.g. in the above example, we want to get a pointer to the struct A, by
    /// passing the pointer to the field b.
    pub unsafe fn get_head_ptr(&mut self, ptr: *mut u8) -> *mut u8 {
        let mut idx = self.get_line_idx_from_addr(ptr);
        debug_assert!(idx >= 3);
        let mut header = self.get_nth_line_header(idx);
        // 如果是head，直接返回
        if !header.is_medium_body() {
            return self.get_nth_line(idx);
        }
        idx -= 1;
        header = self.get_nth_line_header(idx);
        // 否则往前找到head
        while header.is_medium_body() {
            debug_assert!(idx >= 3);
            header = self.get_nth_line_header(idx - 1);
            idx -= 1;
        }
        // 返回head的地址
        self.get_nth_line(idx)
    }

    pub unsafe fn get_line_header_from_addr(&mut self, addr: *mut u8) -> (&mut LineHeader, usize) {
        let idx = self.get_line_idx_from_addr(addr);
        (self.get_nth_line_header(idx), idx)
    }

    pub unsafe fn get_nth_line_header(&mut self, idx: usize) -> &mut LineHeader {
        debug_assert!(idx < NUM_LINES_PER_BLOCK);
        self.line_map.get_unchecked_mut(idx)
    }

    /// # get_line_idx_from_addr
    ///
    /// get the line index from the given address
    ///
    /// # Safety
    ///
    /// The caller must ensure that the address is in the block.
    unsafe fn get_line_idx_from_addr(&self, addr: *mut u8) -> usize {
        debug_assert!(addr as *const u8 >= self as *const Self as *const u8);
        debug_assert!((addr as *const u8) < (self as *const Self as *const u8).add(BLOCK_SIZE));
        (addr as usize - self as *const Self as usize) / LINE_SIZE
    }

    pub fn get_obj_from_header_ptr(&mut self, header: *mut LineHeader) -> *mut u8 {
        // from header get index in line map
        let idx =
            (header as usize - self.line_map.as_ptr() as usize) / std::mem::size_of::<LineHeader>();
        // from index get line

        unsafe { self.get_nth_line(idx) }
    }

    /// # set_eva_threshold
    ///
    /// set the eva_target flag to true if the block's hole number is greater than the threshold
    pub fn set_eva_threshold(&mut self, threshold: usize) {
        self.eva_target = self.hole_num > threshold;
    }

    pub fn is_eva_candidate(&self) -> bool {
        self.eva_target
    }





    pub unsafe fn bump_next_hole(&mut self) ->Option<()> {
        // update cursor, hole_end to the next hole, if there is no hole, set cursor to the end
        // decrease hole_num
        let next_idx = self.get_line_idx_from_addr(self.hole_end);
        for i in next_idx..NUM_LINES_PER_BLOCK {
            let header = self.line_map.get_unchecked(i);
            if !header.get_used() {
                self.cursor = self.get_nth_line(i);
                // find the end of the hole
                for j in i..NUM_LINES_PER_BLOCK {
                    let header = self.line_map.get_unchecked_mut(j);
                    if header.get_used() {
                        self.hole_end = self.get_nth_line(j);
                        return Some(());
                    }
                }
                self.hole_end = self.end;
                return Some(());
            }
        }
        return None;
    }


    pub unsafe fn correct_overflow_avai_lines(&mut self) {
        self.available_line_num = NUM_LINES_PER_BLOCK- self.get_line_idx_from_addr(self.cursor);
    }


    pub fn count_holes_and_avai_lines(&mut self) {
        // count from cursor to the end
        let alined_cursor = unsafe{self.cursor.add(self.cursor.align_offset(LINE_SIZE))};
        let idx = unsafe{self.get_line_idx_from_addr(alined_cursor)};
        let mut holes = 0;
        let mut avai = 0;
        let mut i = idx;
        while  i < NUM_LINES_PER_BLOCK {
            let header = self.line_map[i];
            if !header.get_used() {
                holes += 1;
                i += 1;
                avai += 1;
                while i < NUM_LINES_PER_BLOCK && !self.line_map[i].get_used() {
                    i += 1;
                    avai += 1;
                }
            }
            i += 1;
        }
        self.hole_num = holes;
        self.available_line_num = avai;
    }

    pub unsafe fn alloc(&mut self, size: usize) -> AllocResult {
        // doing a bump allocation
        // real alloc size must be a multiple of 8 bytes
        let size = (size + 7) / 8 * 8;
        // check if is small object
        let is_small = size <= LINE_SIZE;
        if is_small {
            // if small, check if it exceeds current line
            let current_line_remains = self.cursor.align_offset(LINE_SIZE);
            if current_line_remains < size {
                // if exceeds, move cursor to next line
                self.cursor = self.cursor.add(current_line_remains);
                if self.cursor >= self.hole_end && self.bump_next_hole().is_none() {
                    return AllocResult::Exauted;
                }
            }
            // bump allocation
            let ptr = self.cursor;
            self.cursor = self.cursor.add(size);
            return AllocResult::Success(ptr);
        }
        let cursor = self.cursor.add(self.cursor.align_offset(LINE_SIZE));
        // check if current hole is enough
        if cursor.add(size) >= self.hole_end {
            return AllocResult::Fail;
        }
        // bump allocation
        let ptr = cursor;
        // set all lines except the first one medium flag
        let idx = self.get_line_idx_from_addr(ptr);
        for i in 1..=size / LINE_SIZE {
            let header = self.line_map.get_unchecked_mut(idx + i);
            header.set_medium();
        }
        self.cursor = cursor.add(size);
        AllocResult::Success(ptr)
    }

}

#[cfg(test)]
mod tests {
    use crate::{allocator::GlobalAllocator, BLOCK_SIZE, NUM_LINES_PER_BLOCK};

    #[test]
    fn test_block_alloc() {
        unsafe {
            let mut ga = GlobalAllocator::new(BLOCK_SIZE * 20);
            let block = &mut *ga.get_block();
            
            block.cursor = block.cursor.add(64);
            block.count_holes_and_avai_lines();
            assert_eq!(block.hole_num, 1);
            assert_eq!(block.available_line_num, NUM_LINES_PER_BLOCK - 3 - 1);
            let l = block.get_nth_line_header(100);
            *l = 0b1;
            block.count_holes_and_avai_lines();
            assert_eq!(block.hole_num, 2);
            assert_eq!(block.available_line_num, NUM_LINES_PER_BLOCK - 3 - 1 - 1);
            let l = block.get_nth_line_header(101);
            *l = 0b1;
            block.count_holes_and_avai_lines();
            assert_eq!(block.hole_num, 2);
            assert_eq!(block.available_line_num, NUM_LINES_PER_BLOCK - 3 - 1 - 2);
            let l = block.get_nth_line_header(103);
            *l = 0b1;
            block.count_holes_and_avai_lines();
            assert_eq!(block.hole_num, 3);
            assert_eq!(block.available_line_num, NUM_LINES_PER_BLOCK - 3 - 1 - 3);
        };
    }

    #[test]
    fn test_correct_header() {
        unsafe {
            let mut ga = GlobalAllocator::new(BLOCK_SIZE * 20);
            let block = &mut *ga.get_block();
            block.cursor = block.cursor.add(64);
            let l = block.get_nth_line_header(100);
            *l = 0b10;
            let l = block.get_nth_line_header(101);
            *l = 0b10000000;
            let l = block.get_nth_line_header(103);
            *l = 0b10;
            let mut gram = Default::default();
            block.correct_header(&mut gram);
            assert_eq!(block.hole_num, 3);
            assert_eq!(block.available_line_num, NUM_LINES_PER_BLOCK - 3 - 3);
            let cursor = block.cursor;
            assert_eq!(cursor, block.get_nth_line(3));
            assert_eq!(gram.get(&3), Some(&3));
        };
    }

    #[test]
    fn test_get_head_ptr() {
        unsafe {
            let mut ga = GlobalAllocator::new(BLOCK_SIZE * 20);
            let block = &mut *ga.get_block();
            block.cursor = block.cursor.add(64);
            let l = block.get_nth_line_header(100);
            *l = 0b10;
            let l = block.get_nth_line_header(101);
            *l = 0b10000000;
            let l = block.get_nth_line_header(103);
            *l = 0b10;
            let ptr = block.get_nth_line(101).add(8);
            let head = block.get_head_ptr(ptr);
            assert_eq!(head, block.get_nth_line(100));
        };
    }

}
