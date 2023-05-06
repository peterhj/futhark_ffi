extern crate cc;
extern crate libc;
extern crate libloading;
extern crate rustc_serialize;
//extern crate tempfile;

use self::blake2s::{Blake2s};

use libc::{c_int};
use libloading::os::unix::{Library, Symbol};
//use potato::{Blake2s};
use rustc_serialize::hex::{ToHex};
//use tempfile::{Builder as TempBuilder};

use std::env;
use std::fs;
//use std::io::{Write};
use std::path::{Path, PathBuf};
use std::process::{};

pub mod blake2s;
//pub mod temp;

// This "FFI" really just calls the futhark executable.

// TODO

#[repr(C)]
pub struct futhark_context_config([u8; 0]);

#[repr(C)]
pub struct futhark_context([u8; 0]);

#[derive(Default)]
pub struct ObjectFFI {
  _inner:       Option<Library>,
  ctx_cfg_new:  Option<Symbol<extern "C" fn () -> *mut futhark_context_config>>,
  ctx_cfg_free: Option<Symbol<extern "C" fn (*mut futhark_context_config)>>,
  ctx_new:      Option<Symbol<extern "C" fn (*mut futhark_context_config) -> *mut futhark_context>>,
  ctx_free:     Option<Symbol<extern "C" fn (*mut futhark_context)>>,
  ctx_may_fail: Option<Symbol<extern "C" fn (*mut futhark_context) -> c_int>>,
  ctx_sync:     Option<Symbol<extern "C" fn (*mut futhark_context) -> c_int>>,
  /*new_f32_1d:   Option<Symbol<extern "C" fn () -> ()>>,
  new_i32_1d:   Option<Symbol<extern "C" fn () -> ()>>,
  new_u32_1d:   Option<Symbol<extern "C" fn () -> ()>>,
  new_f16_1d:   Option<Symbol<extern "C" fn () -> ()>>,
  new_u16_1d:   Option<Symbol<extern "C" fn () -> ()>>,
  new_u8_1d:    Option<Symbol<extern "C" fn () -> ()>>,*/
  // TODO
  entry:        Option<Symbol<extern "C" fn () -> ()>>,
}

impl Drop for ObjectFFI {
  fn drop(&mut self) {
    let inner = self._inner.take();
    assert!(inner.is_some());
    *self = Default::default();
    drop(inner.unwrap());
  }
}
impl ObjectFFI {
  unsafe fn load_symbols(&mut self) {
    let inner = self._inner.as_ref().unwrap();
    self.ctx_cfg_new = inner.get(b"futhark_context_config_new").ok();
    self.ctx_cfg_free = inner.get(b"futhark_context_config_free").ok();
    self.ctx_new = inner.get(b"futhark_context_new").ok();
    self.ctx_free = inner.get(b"futhark_context_free").ok();
    self.ctx_may_fail = inner.get(b"futhark_context_may_fail").ok();
    self.ctx_sync = inner.get(b"futhark_context_sync").ok();
    // TODO
    self.entry = inner.get(b"futhark_enter_kernel").ok();
  }
}

pub struct Object {
  ffi:  ObjectFFI,
}

impl Object {
  pub fn cached_or_new_cuda(src_buf: &[u8]) -> Result<Object, ()> {
    let mut srchash = Blake2s::new_hash();
    srchash.hash_bytes(b"--! futhark cuda\n");
    srchash.hash_bytes(src_buf);
    let h = srchash.finalize();
    let x = h.to_hex();
    let stem = format!("futhark_obj_{}", x);
    unimplemented!();
  }
}

pub struct ObjectBuild {
  work_dir: PathBuf,
  srchash:  Blake2s,
  source:   Vec<u8>,
  output:   Option<PathBuf>,
}

impl ObjectBuild {
  pub fn new_cuda() -> ObjectBuild {
    let mut work_dir = env::home_dir().unwrap();
    work_dir.push(".futhark_ffi");
    work_dir.push("cache");
    fs::create_dir_all(&work_dir).ok();
    let mut srchash = Blake2s::new_hash();
    srchash.hash_bytes(b"--! futhark cuda\n");
    ObjectBuild{
      work_dir,
      srchash,
      source:   Vec::new(),
      output:   None,
    }
  }

  pub fn work_dir<P: AsRef<Path>>(&mut self, p: P) -> &mut ObjectBuild {
    self.work_dir = p.as_ref().to_owned();
    self
  }

  pub fn source(&mut self, buf: &[u8]) -> &mut ObjectBuild {
    self.srchash.hash_bytes(buf);
    self.source.extend_from_slice(buf);
    self
  }

  pub fn build(&mut self) -> Result<Object, ()> {
    let h = self.srchash.finalize();
    let x = h.to_hex();
    let stem = format!("futhark_obj_{}", x);
    let mut f_path = self.work_dir.clone();
    f_path.push(&stem);
    f_path.set_extension("fut");
    unimplemented!();
    /*
    let f = TempBuilder::new().suffix(".fut").tempfile_in(&self.work_dir).unwrap();
    f.write_all(&self.source).unwrap();
    //let fut_path = f.into_temp_path();
    // FIXME: run futhark cuda.
    let mut c_path = f_path.clone();
    let mut h_path = f_path.clone();
    let mut so_path = f_path.clone();
    c_path.set_extension("c");
    h_path.set_extension("h");
    match so_path.file_name() {
      None => panic!("bug"),
      Some(s) => {
        so_path.set_file_name(&format!("lib{}", s));
      }
    }
    so_path.set_extension("so");
    // FIXME: run cc.
    let mut c = cc::Build::new()
      .shared_flag(true)
      .static_flag(false)
      .opt_level(2)
      .include(&self.work_dir)
      .file(&c_path)
      .compile(&stem);
    let inner = Library::new(&so_path).map_err(|_| ())?;
    */
  }
}
