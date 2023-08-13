use libc::{c_void, c_char, c_int};

use std::ptr::{null, null_mut};

pub const FUTHARK_SUCCESS: c_int = 0;
pub const FUTHARK_OUT_OF_MEMORY: c_int = 2;
pub const FUTHARK_PROGRAM_ERROR: c_int = 3;

#[repr(C)]
pub struct futhark_context_config([u8; 0]);

#[repr(C)]
pub struct futhark_context([u8; 0]);

pub trait MemFFI: Copy {
  type Ptr: Copy;

  fn _get_refcount(&self) -> *mut i32;
  fn _get_ptr(&self) -> Self::Ptr;
  fn _get_size(&self) -> usize;
  fn _get_tag(&self) -> *const c_char;
  fn _set_refcount(&mut self, new_refc: *mut i32);
  fn _set_ptr(&mut self, new_ptr: Self::Ptr);
  fn _set_size(&mut self, new_sz: usize);
  fn _set_tag(&mut self, new_tag: *const c_char);
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct memblock {
  pub refcount: *mut c_int,
  pub mem_ptr:  *mut c_void,
  pub mem_size: usize,
  pub tag:      *const c_char,
}

impl Default for memblock {
  fn default() -> memblock {
    memblock{
      refcount: null_mut(),
      mem_ptr:  null_mut(),
      mem_size: 0,
      tag:      null(),
    }
  }
}

impl MemFFI for memblock {
  type Ptr = *mut c_void;

  fn _get_refcount(&self) -> *mut i32 {
    self.refcount
  }

  fn _get_ptr(&self) -> *mut c_void {
    self.mem_ptr
  }

  fn _get_size(&self) -> usize {
    self.mem_size
  }

  fn _get_tag(&self) -> *const c_char {
    self.tag
  }

  fn _set_refcount(&mut self, new_refc: *mut i32) {
    self.refcount = new_refc;
  }

  fn _set_ptr(&mut self, new_ptr: *mut c_void) {
    self.mem_ptr = new_ptr;
  }

  fn _set_size(&mut self, new_sz: usize) {
    self.mem_size = new_sz;
  }

  fn _set_tag(&mut self, new_tag: *const c_char) {
    self.tag = new_tag;
  }
}

#[derive(Clone, Copy)]
#[repr(C)]
pub struct memblock_dev {
  pub refcount: *mut c_int,
  pub mem_dptr: u64,
  pub mem_size: usize,
  pub tag:      *const c_char,
}

impl Default for memblock_dev {
  fn default() -> memblock_dev {
    memblock_dev{
      refcount: null_mut(),
      mem_dptr: 0,
      mem_size: 0,
      tag:      null(),
    }
  }
}

impl MemFFI for memblock_dev {
  type Ptr = u64;

  fn _get_refcount(&self) -> *mut i32 {
    self.refcount
  }

  fn _get_ptr(&self) -> u64 {
    self.mem_dptr
  }

  fn _get_size(&self) -> usize {
    self.mem_size
  }

  fn _get_tag(&self) -> *const c_char {
    self.tag
  }

  fn _set_refcount(&mut self, new_refc: *mut i32) {
    self.refcount = new_refc;
  }

  fn _set_ptr(&mut self, new_dptr: u64) {
    self.mem_dptr = new_dptr;
  }

  fn _set_size(&mut self, new_sz: usize) {
    self.mem_size = new_sz;
  }

  fn _set_tag(&mut self, new_tag: *const c_char) {
    self.tag = new_tag;
  }
}

/*#[derive(Default)]
#[repr(C)]
pub struct array_1d {
  pub mem: memblock,
  pub shape: [i64; 1],
}

#[derive(Default)]
#[repr(C)]
pub struct array_2d {
  pub mem: memblock,
  pub shape: [i64; 2],
}

#[derive(Default)]
#[repr(C)]
pub struct array_3d {
  pub mem: memblock,
  pub shape: [i64; 3],
}

#[derive(Default)]
#[repr(C)]
pub struct array_4d {
  pub mem: memblock,
  pub shape: [i64; 4],
}

#[derive(Default)]
#[repr(C)]
pub struct array_1d_dev {
  pub mem: memblock_dev,
  pub shape: [i64; 1],
}

#[derive(Default)]
#[repr(C)]
pub struct array_2d_dev {
  pub mem: memblock_dev,
  pub shape: [i64; 2],
}

#[derive(Default)]
#[repr(C)]
pub struct array_3d_dev {
  pub mem: memblock_dev,
  pub shape: [i64; 3],
}

#[derive(Default)]
#[repr(C)]
pub struct array_4d_dev {
  pub mem: memblock_dev,
  pub shape: [i64; 4],
}*/
