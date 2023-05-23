use libc::{c_char, c_uchar, c_int};

#[repr(C)]
pub struct memblock {
  pub refcount: *mut c_int,
  pub mem_ptr: *mut c_uchar,
  pub mem_size: usize,
  pub tag: *const c_char,
}

#[repr(C)]
pub struct memblock_dev {
  pub refcount: *mut c_int,
  pub mem_dptr: u64,
  pub mem_size: usize,
  pub tag: *const c_char,
}

#[repr(C)]
pub struct array_1d_dev {
  pub mem: memblock_dev,
  pub shape: [i64; 1],
}

#[repr(C)]
pub struct array_2d_dev {
  pub mem: memblock_dev,
  pub shape: [i64; 2],
}

#[repr(C)]
pub struct array_3d_dev {
  pub mem: memblock_dev,
  pub shape: [i64; 3],
}

#[repr(C)]
pub struct array_4d_dev {
  pub mem: memblock_dev,
  pub shape: [i64; 4],
}

#[repr(C)]
pub struct futhark_context_config([u8; 0]);

#[repr(C)]
pub struct futhark_context([u8; 0]);
