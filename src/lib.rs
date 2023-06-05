extern crate cc;
extern crate libc;
extern crate libloading;
extern crate rustc_serialize;
extern crate ryu;
//extern crate tempfile;

use self::blake2s::{Blake2s};
use self::bindings::{ObjectFFI};
use self::types::*;

use libc::{c_void, malloc, free};
//use potato::{Blake2s};
use rustc_serialize::{Decodable};
use rustc_serialize::hex::{ToHex};
use rustc_serialize::json::{Decoder as JsonDecoder, Json};
use ryu::{Buffer as RyuBuffer};
//use tempfile::{Builder as TempBuilder};

//use std::alloc::{Layout, alloc, dealloc};
use std::cell::{RefCell};
use std::collections::{BTreeMap};
//use std::env;
use std::ffi::{OsStr};
use std::fs::{File, OpenOptions, create_dir_all};
use std::io::{Read, Write};
use std::marker::{PhantomData};
use std::mem::{size_of, swap};
use std::path::{Path, PathBuf};
use std::process::{Command};
use std::ptr::{copy_nonoverlapping, null_mut, write};
use std::slice::{from_raw_parts};
use std::str::{from_utf8};

pub mod bindings;
pub mod blake2s;
pub mod build_env;
pub mod types;
//pub mod temp;

#[derive(Default)]
pub struct FutharkFloatFormatter {
  buf:  RefCell<RyuBuffer>,
}

impl Clone for FutharkFloatFormatter {
  fn clone(&self) -> FutharkFloatFormatter {
    FutharkFloatFormatter::default()
  }
}

impl FutharkFloatFormatter {
  pub fn format_f32(&self, x: f32) -> String {
    let mut s = String::new();
    self.write_f32(&mut s, x);
    s
  }

  pub fn write_f32(&self, s: &mut String, x: f32) {
    if x.is_nan() {
      s.push_str("f32.nan");
    } else if !x.is_finite() {
      // FIXME FIXME: double check this api.
      if x.is_sign_negative() {
        s.push_str("-");
      }
      s.push_str("f32.inf");
    } else {
      s.push_str(self.buf.borrow_mut().format_finite(x));
      s.push_str("f32");
    }
  }
}

#[derive(Clone, Default, Debug)]
pub struct Config {
  // TODO
  pub cachedir: PathBuf,
  pub futhark:  PathBuf,
  pub include:  PathBuf,
  pub target:   Option<String>,
}

impl Config {
  pub fn target(&self) -> &str {
    self.target.as_ref().map(|s| s.as_ref()).unwrap_or(crate::build_env::TARGET)
  }
}

// NB: This "FFI" really just calls the futhark executable.

#[derive(Clone, Copy, Debug)]
pub enum BuildError {
  Cache,
  FutharkCommand,
  Futhark(Option<i32>),
  /*JsonPath,
  JsonUtf8,
  JsonFromStr,
  JsonDecode,*/
  Json,
  Cc,
  DylibPath,
  DylibHash,
  Dylib,
}

pub trait Backend {
  // TODO
  //fn cmd_arg() -> &'static [u8];
  fn cmd_arg() -> &'static str;
}

pub enum MulticoreBackend {}

impl Backend for MulticoreBackend {
  fn cmd_arg() -> &'static str {
    "multicore"
  }
}

pub enum CudaBackend {}

impl Backend for CudaBackend {
  fn cmd_arg() -> &'static str {
    "cuda"
  }
}

/*//#[derive(RustcDecodable)]
pub enum BackendType {
  Multicore,
  Cuda,
}*/

#[derive(RustcDecodable, Debug)]
pub struct ObjectManifestTypeOps {
  pub free:         String,
  pub new:          String,
  pub shape:        String,
  pub values:       String,
}

#[derive(RustcDecodable, Debug)]
pub struct ObjectManifestType {
  pub ctype:        String,
  pub elemtype:     String,
  pub kind:         String,
  pub ops:          ObjectManifestTypeOps,
  pub rank:         i64,
}

#[derive(RustcDecodable, Debug)]
pub struct ObjectManifestInput {
  pub name:         String,
  pub type_:        String,
  pub unique:       bool,
}

#[derive(RustcDecodable, Debug)]
pub struct ObjectManifestOutput {
  pub type_:        String,
  pub unique:       bool,
}

#[derive(RustcDecodable, Debug)]
pub struct ObjectManifestEntry {
  pub cfun:         String,
  pub inputs:       Vec<ObjectManifestInput>,
  pub outputs:      Vec<ObjectManifestOutput>,
  pub tuning_params: Vec<String>,
}

#[derive(RustcDecodable, Debug)]
pub struct ObjectManifestSingleEntry {
  pub kernel:       ObjectManifestEntry,
}

#[derive(RustcDecodable, Debug)]
pub struct ObjectManifest {
  pub backend:      String,
  pub entry_points: ObjectManifestSingleEntry,
  pub types:        BTreeMap<String, ObjectManifestType>,
  pub version:      String,
}

pub fn fixup_json_manifest(j: Json) -> Json {
  match j {
    Json::Object(kvs) => {
      let mut new_kvs = BTreeMap::new();
      for (k, v) in kvs.into_iter() {
        let new_k = if &k == "type" {
          "type_".into()
        } else {
          k
        };
        let old_v = new_kvs.insert(new_k, fixup_json_manifest(v));
        assert!(old_v.is_none());
      }
      Json::Object(new_kvs)
    }
    Json::Array(xs) => {
      Json::Array(xs.into_iter().map(|x| fixup_json_manifest(x)).collect())
    }
    _ => j
  }
}

impl ObjectManifest {
  pub fn open_with_hash<P: AsRef<Path>>(json_path: P) -> Result<(ObjectManifest, String), ()> {
    match OpenOptions::new().read(true).write(false).create(false).open(json_path) {
      Err(_) => return Err(()),
      Ok(mut json_f) => {
        let mut json_buf = Vec::new();
        match json_f.read_to_end(&mut json_buf) {
          Err(_) => panic!("bug"),
          Ok(_) => {}
        }
        let mut h = Blake2s::new_hash();
        h.hash_bytes(&json_buf);
        let h = h.finalize();
        let hx = h.to_hex();
        let j = match Json::from_str(from_utf8(&json_buf).map_err(|_| ())?) {
          Err(_) => return Err(()),
          Ok(j) => j
        };
        match Decodable::decode(&mut JsonDecoder::new(fixup_json_manifest(j))) {
          Err(_) => return Err(()),
          Ok(m) => Ok((m, hx))
        }
      }
    }
  }
}

pub struct Object<B: Backend> {
  pub manifest: ObjectManifest,
  pub ffi:  ObjectFFI,
  pub cfg:  *mut futhark_context_config,
  pub ctx:  *mut futhark_context,
  _mrk: PhantomData<B>,
}

impl<B: Backend> Drop for Object<B> {
  fn drop(&mut self) {
    if !self.ctx.is_null() {
      (self.ffi.ctx_free.as_ref().unwrap())(self.ctx);
    }
    if !self.cfg.is_null() {
      (self.ffi.ctx_cfg_free.as_ref().unwrap())(self.cfg);
    }
  }
}

impl<B: Backend> Object<B> {
  pub fn open<P: AsRef<OsStr>>(manifest: ObjectManifest, dylib_path: P) -> Result<Object<B>, ()> {
    let ffi = unsafe { ObjectFFI::open(dylib_path).map_err(|_| ())? };
    Ok(Object{
      manifest,
      ffi,
      cfg:  null_mut(),
      ctx:  null_mut(),
      _mrk: PhantomData,
    })
  }
}

impl Config {
  pub fn cached_or_new_object<B: Backend>(&self, src_buf: &[u8]) -> Result<Object<B>, BuildError> {
    let mut srchash = Blake2s::new_hash();
    srchash.hash_bytes(src_buf);
    let h = srchash.finalize();
    let hx = h.to_hex();
    let stem = format!("futhark_obj_{}_{}", B::cmd_arg(), hx);
    create_dir_all(&self.cachedir).ok();
    let mut f_path = self.cachedir.clone();
    f_path.push(&stem);
    f_path.set_extension("fut");
    let mut c_path = f_path.clone();
    let mut h_path = f_path.clone();
    let mut json_path = f_path.clone();
    let mut dylib_path = f_path.clone();
    let mut hash_path = f_path.clone();
    c_path.set_extension("c");
    h_path.set_extension("h");
    json_path.set_extension("json");
    hash_path.set_extension("hash");
    // FIXME FIXME: os-specific dylib path.
    match dylib_path.file_name() {
      None => panic!("bug"),
      Some(s) => {
        dylib_path.set_file_name(&format!("lib{}", s.to_str().unwrap()));
      }
    }
    dylib_path.set_extension("so");
    //println!("DEBUG: futhark_ffi::Config::cached_or_new_object: target: {}", crate::build_env::TARGET);
    //println!("DEBUG: futhark_ffi::Config::cached_or_new_object: dylib path: {}", dylib_path.to_str().unwrap());
    //println!("DEBUG: futhark_ffi::Config::cached_or_new_object: dylib file: {}", dylib_path.file_name().unwrap().to_str().unwrap());
    match (ObjectManifest::open_with_hash(&json_path),
           OpenOptions::new().read(true).write(false).create(false).open(&dylib_path),
           OpenOptions::new().read(true).write(false).create(false).open(&hash_path))
    {
      (Ok((manifest, json_hx)), Ok(mut dylib_f), Ok(mut hash_f)) => {
        let mut hx_buf = Vec::new();
        hx_buf.extend_from_slice(json_hx.as_bytes());
        let mut dylib_buf = Vec::new();
        dylib_f.read_to_end(&mut dylib_buf).unwrap();
        let mut dylib_h = Blake2s::new_hash();
        dylib_h.hash_bytes(&dylib_buf);
        let dylib_h = dylib_h.finalize();
        let dylib_hx = dylib_h.to_hex();
        hx_buf.extend_from_slice(dylib_hx.as_bytes());
        let mut hash_buf = Vec::new();
        hash_f.read_to_end(&mut hash_buf).unwrap();
        if hash_buf.len() >= hx_buf.len() &&
           &hx_buf == &hash_buf[ .. hx_buf.len()]
        {
          println!("DEBUG: futhark_ffi::Config::cached_or_new_object: load cached...");
          return Object::open(manifest, &dylib_path).map_err(|_| BuildError::Dylib);
        }
      }
      _ => {}
    }
    match OpenOptions::new().read(false).write(true).create(true).truncate(true).open(&f_path) {
      Err(_) => return Err(BuildError::Cache),
      Ok(mut f) => {
        f.write_all(src_buf).unwrap();
      }
    }
    match Command::new(&self.futhark)
      //.arg(from_utf8(B::cmd_arg()).unwrap())
      .arg(B::cmd_arg())
      .arg("--library")
      .arg(&f_path)
      .status()
    {
      Err(_) => return Err(BuildError::FutharkCommand),
      Ok(status) => {
        if !status.success() {
          return Err(BuildError::Futhark(status.code()));
        }
      }
    }
    let (manifest, json_hx) = match ObjectManifest::open_with_hash(&json_path) {
      Err(_) => return Err(BuildError::Json),
      Ok((m, hx)) => (m, hx)
    };
    if &manifest.backend != B::cmd_arg() {
      panic!("bug");
    }
    match cc::Build::new()
      // NB: We have to set `out_dir`, `target`, `host`, `debug`, and `opt_level`;
      // normally they are read from env vars passed by cargo to the build script.
      .out_dir(&self.cachedir)
      .target(self.target())
      .host(self.target())
      .debug(false)
      .opt_level(2)
      .pic(true)
      .include(&self.cachedir)
      .include(&self.include)
      .file(&c_path)
      .object_prefix_hash(false)
      .archive(false)
      .dylib(true)
      .silent(true)
      //.try_compile(dylib_path.file_name().unwrap().to_str().unwrap())
      .try_compile(&stem)
    {
      Err(e) => {
        println!("WARNING: futhark_ffi::Config::cached_or_new_object: cc build error: {}", e);
        return Err(BuildError::Cc);
      }
      Ok(_) => {}
    }
    match OpenOptions::new().read(true).write(false).create(false).open(&dylib_path) {
      Err(_) => return Err(BuildError::DylibPath),
      Ok(mut dylib_f) => {
        let mut buf = Vec::new();
        dylib_f.read_to_end(&mut buf).unwrap();
        let mut h = Blake2s::new_hash();
        h.hash_bytes(&buf);
        let h = h.finalize();
        let hx = h.to_hex();
        match OpenOptions::new().read(false).write(true).create(true).truncate(true).open(&hash_path) {
          Err(_) => return Err(BuildError::DylibHash),
          Ok(mut hash_f) => {
            hash_f.write_all(json_hx.as_bytes()).unwrap();
            hash_f.write_all(hx.as_bytes()).unwrap();
          }
        }
      }
    }
    println!("DEBUG: futhark_ffi::Config::cached_or_new_object: new build done!");
    Object::open(manifest, &dylib_path).map_err(|_| BuildError::Dylib)
  }
}

impl<B: Backend> Object<B> {
  /*pub fn setup(&self, ) {
    unimplemented!();
  }*/

  pub fn reset(&self, ) {
    (self.ffi.ctx_reset.as_ref().unwrap())(self.ctx);
  }

  pub fn may_fail(&self) -> bool {
    let ret = (self.ffi.ctx_may_fail.as_ref().unwrap())(self.ctx);
    ret != 0
  }

  pub fn sync(&self) -> Result<(), i32> {
    let ret = (self.ffi.ctx_sync.as_ref().unwrap())(self.ctx);
    if ret != FUTHARK_SUCCESS {
      return Err(ret);
    }
    Ok(())
  }
}

pub trait ObjectExt {
  type Array;
  type RawArray;

  fn enter_kernel(&mut self, arityin: u16, arityout: u16, arg_arr: &[Self::Array], out_raw_arr: &mut [Self::RawArray]) -> Result<(), i32>;
}

impl ObjectExt for Object<CudaBackend> {
  type Array = ArrayDev;
  type RawArray = *mut memblock_dev;

  fn enter_kernel(&mut self, arityin: u16, arityout: u16, arg_arr: &[ArrayDev], out_raw_arr: &mut [*mut memblock_dev]) -> Result<(), i32> {
    // FIXME FIXME
    let out_raw_arr_buf_len = out_raw_arr.len();
    let out_raw_arr_buf = out_raw_arr.as_mut_ptr();
    assert_eq!(arg_arr.len(), arityin as usize);
    assert_eq!(out_raw_arr_buf_len, arityout as usize);
    unsafe { self.ffi.load_entry_symbol(arityin, arityout, true); }
    let ret = match (arityin, arityout) {
      (0, 1) => (self.ffi.entry_0_1_dev.as_ref().unwrap())(self.ctx, out_raw_arr_buf),
      (1, 1) => (self.ffi.entry_1_1_dev.as_ref().unwrap())(self.ctx, out_raw_arr_buf, arg_arr[0].as_ptr()),
      (2, 1) => (self.ffi.entry_2_1_dev.as_ref().unwrap())(self.ctx, out_raw_arr_buf, arg_arr[0].as_ptr(), arg_arr[1].as_ptr()),
      (3, 1) => (self.ffi.entry_3_1_dev.as_ref().unwrap())(self.ctx, out_raw_arr_buf, arg_arr[0].as_ptr(), arg_arr[1].as_ptr(), arg_arr[2].as_ptr()),
      (4, 1) => (self.ffi.entry_4_1_dev.as_ref().unwrap())(self.ctx, out_raw_arr_buf, arg_arr[0].as_ptr(), arg_arr[1].as_ptr(), arg_arr[2].as_ptr(), arg_arr[3].as_ptr()),
      _ => panic!("bug: Object::<CudaBackend>::enter_kernel: unimplemented: arityin={} arityout={}", arityin, arityout)
    };
    if ret != FUTHARK_SUCCESS {
      return Err(ret);
    }
    Ok(())
  }
}

pub struct ArrayDev {
  raw:  usize,
}

impl Drop for ArrayDev {
  fn drop(&mut self) {
    let ptr = self.as_ptr();
    if ptr.is_null() {
      return;
    }
    match self.dec_refcount() {
      Some(0) => {
        // FIXME FIXME: first, unref.
        match self.raw & 7 {
          1 | 2 | 3 | 4 => unsafe { free(ptr as *mut _) },
          _ => unreachable!()
        }
      }
      Some(_) | None => {}
    }
  }
}

impl ArrayDev {
  pub fn from_raw(ptr: *mut memblock_dev, ndim: u8) -> ArrayDev {
    assert!(!ptr.is_null());
    let raw_ptr = ptr as usize;
    assert_eq!(raw_ptr & 7, 0);
    let raw = match ndim {
      1 | 2 | 3 | 4 => raw_ptr | (ndim as usize),
      _ => unreachable!()
    };
    ArrayDev{raw}
  }

  pub fn alloc_1d() -> ArrayDev {
    assert_eq!(size_of::<array_1d_dev>(), size_of::<memblock_dev>() + 8);
    let ptr = unsafe { malloc(size_of::<array_1d_dev>()) } as *mut _;
    ArrayDev::from_raw(ptr, 1)
  }

  pub fn alloc_2d() -> ArrayDev {
    assert_eq!(size_of::<array_2d_dev>(), size_of::<memblock_dev>() + 8 * 2);
    let ptr = unsafe { malloc(size_of::<array_2d_dev>()) } as *mut _;
    ArrayDev::from_raw(ptr, 2)
  }

  pub fn alloc_3d() -> ArrayDev {
    assert_eq!(size_of::<array_3d_dev>(), size_of::<memblock_dev>() + 8 * 3);
    let ptr = unsafe { malloc(size_of::<array_3d_dev>()) } as *mut _;
    ArrayDev::from_raw(ptr, 3)
  }

  pub fn alloc_4d() -> ArrayDev {
    assert_eq!(size_of::<array_4d_dev>(), size_of::<memblock_dev>() + 8 * 4);
    let ptr = unsafe { malloc(size_of::<array_4d_dev>()) } as *mut _;
    ArrayDev::from_raw(ptr, 4)
  }

  /*pub fn into_raw(self) -> (*mut memblock_dev, u8) {
    // FIXME: this still drops b/c raw is Copy.
    let ArrayDev{raw} = self;
    let ptr = (raw & (!7)) as *mut _;
    let ndim = (raw & 7) as _;
    (ptr, ndim)
  }*/

  pub fn take_ptr(&mut self) -> *mut memblock_dev {
    let mask = (self.raw & 7);
    self.raw &= (!7);
    let nil: *mut memblock_dev = null_mut();
    let mut out = nil as usize;
    swap(&mut out, &mut self.raw);
    self.raw |= mask;
    let ptr = out as *mut _;
    ptr
  }

  pub fn as_ptr(&self) -> *mut memblock_dev {
    (self.raw & (!7)) as *mut _
  }

  pub fn ndim(&self) -> u8 {
    (self.raw & 7) as _
  }

  pub fn refcount(&self) -> Option<i32> {
    unsafe {
      let mem = self.as_ptr() as *const memblock_dev;
      if mem.is_null() {
        return None;
      }
      let c = (&*mem).refcount as *const i32;
      if c.is_null() {
        return None;
      }
      Some(*c)
    }
  }

  pub fn dec_refcount(&self) -> Option<i32> {
    unsafe {
      let mem = self.as_ptr();
      if mem.is_null() {
        return None;
      }
      let c = (&*mem).refcount as *mut i32;
      if c.is_null() {
        return None;
      }
      let prev_c = *c;
      assert!(prev_c >= 1);
      let new_c = prev_c - 1;
      write(c, new_c);
      Some(new_c)
    }
  }

  pub fn parts(&self) -> Option<(u64, usize)> {
    unsafe {
      let mem = self.as_ptr() as *const memblock_dev;
      if mem.is_null() {
        return None;
      }
      let mem = &*mem;
      Some((mem.mem_dptr, mem.mem_size))
    }
  }

  pub unsafe fn shape(&self) -> Option<&[i64]> {
    let ndim = self.raw & 7;
    if ndim == 0 {
      return None;
    }
    let ptr = self.as_ptr() as *const u8;
    if ptr.is_null() {
      return None;
    }
    let buf = ptr.offset(size_of::<memblock_dev>() as _) as *const i64;
    Some(from_raw_parts(buf, ndim))
  }

  pub fn set_shape(&self, shape: &[i64]) {
    let ndim = self.raw & 7;
    assert!(ndim != 0);
    assert_eq!(ndim, shape.len());
    unsafe {
      let ptr = self.as_ptr() as *mut u8;
      assert!(!ptr.is_null());
      let buf = ptr.offset(size_of::<memblock_dev>() as _) as *mut i64;
      // FIXME FIXME: check that we can do copy_nonoverlapping.
      copy_nonoverlapping(shape.as_ptr(), buf, ndim);
    }
  }
}
