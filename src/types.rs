use libc::{c_void, c_char, c_int};

use std::ptr::{null, null_mut};

pub const FUTHARK_SUCCESS: c_int = 0;
pub const FUTHARK_OUT_OF_MEMORY: c_int = 2;
pub const FUTHARK_PROGRAM_ERROR: c_int = 3;

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
}

#[repr(C)]
pub struct futhark_context_config([u8; 0]);

#[repr(C)]
pub struct futhark_context([u8; 0]);
