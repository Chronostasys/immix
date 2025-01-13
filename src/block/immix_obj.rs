use std::marker::PhantomData;

use crate::BLOCK_SIZE;
use crate::LINE_SIZE;

use super::HeaderExt;
use super::LineHeaderExt;
use super::ObjectType;

use super::LineHeader;

#[repr(C)]
#[derive(Debug, Clone, Copy)]
pub(crate) struct ImmixObject {
    /// |                           LINE HEADER(1 byte)                         |
    /// |    7   |    6   |    5   |    4   |    3   |    2   |    1   |    0   |
    /// | medium |   eva  |  evaed |        -----------       | marked |  used  |
    ///
    /// When the evaed bit is set and eva is not, the line is pinned.
    pub(crate) byte_header: LineHeader,
    pub(crate) obj_type: ObjectType,
    pub(crate) size: u16, // size of object, include header
    pub(crate) addr_low: u32,
    body: PhantomData<[u8]>,
}

impl ImmixObject {
    pub(crate) unsafe fn new(addr: *mut u8, size: u16, obj_type: ObjectType) -> *mut Self {
        let obj = addr as *mut ImmixObject;
        (*obj).byte_header = 0;
        (*obj).obj_type = obj_type;
        (*obj).size = size;
        // get low 32 bit of addr
        (*obj).addr_low = addr as u32;
        // eprintln!("addr_low: {:x}", (*obj).addr_low);
        obj
    }

    pub(crate) unsafe fn from_unaligned_ptr(addr: *mut u8) -> Option<*mut Self> {
        // ptr is pointed to body, so we need to get the start addr of object
        // as immix object must be aligned to 8 bytes, start from addr,
        // going 8 bytes back to get the start addr of object
        let mut header_addr = ((addr as usize - 1) & (!0x7)) as *mut ImmixObject;

        // shall not cross block boundary
        let block_start =
            (header_addr as usize - header_addr as usize % BLOCK_SIZE) as *mut ImmixObject;

        // check if it's valid
        while !(*header_addr).is_valid() {
            // if not valid, go back 8 bytes
            header_addr = header_addr.offset(-1);
            if header_addr < block_start {
                return None;
            }
        }
        // check if addr in body
        let body = (*header_addr).get_body();
        let body_end = body.add((*header_addr).body_size());
        if addr < body || addr >= body_end {
            return None;
        }
        // now we get the start addr of object
        Some(header_addr)
    }

    pub(crate) fn from_body_ptr(addr: *mut u8) -> *mut Self {
        // ptr is pointed to body, so we need to get the start addr of object
        // as immix object must be aligned to 8 bytes, start from addr,
        // going 8 bytes back to get the start addr of object

        // now we get the start addr of object
        (addr as usize - 8) as *mut ImmixObject
    }

    pub(crate) fn is_valid(&self) -> bool {
        // check addr_low
        self.addr_low == self as *const _ as u32 && self.size > 8 && self.obj_type as u8 <= 4
    }

    pub(crate) fn from_ptr(addr: *mut u8) -> *mut Self {
        addr as *mut ImmixObject
    }

    pub(crate) fn get_body(&self) -> *mut u8 {
        &self.body as *const _ as *mut u8
    }
    pub(crate) fn body_size(&self) -> usize {
        self.size as usize - 8
    }
    pub(crate) fn is_small(&self) -> bool {
        self.size <= LINE_SIZE as _
    }
    pub(crate) fn mark(&mut self) {
        self.byte_header.set_marked(true);
    }
    pub(crate) fn is_marked(&self) -> bool {
        self.byte_header.get_marked()
    }
    pub(crate) fn correct_header(&mut self) {
        if self.byte_header.is_pinned() {
            self.byte_header = 1;
            self.byte_header.pin();
        } else {
            self.byte_header = 1;
        }
    }
}
