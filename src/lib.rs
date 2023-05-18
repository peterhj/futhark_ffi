extern crate cc;
extern crate home;
extern crate libc;
extern crate libloading;
extern crate rustc_serialize;
extern crate ryu;
//extern crate tempfile;

use self::blake2s::{Blake2s};

use home::{home_dir};
use libc::{c_int, c_void};
use libloading::nonsafe::{Library, Symbol};
//use potato::{Blake2s};
use rustc_serialize::{Decodable};
use rustc_serialize::hex::{ToHex};
use rustc_serialize::json::{Decoder as JsonDecoder, Json};
use ryu::{Buffer as RyuBuffer};
//use tempfile::{Builder as TempBuilder};

use std::cell::{RefCell};
use std::collections::{BTreeMap};
//use std::env;
use std::fs::{File, OpenOptions, create_dir_all};
use std::io::{Read, Write};
use std::marker::{PhantomData};
use std::path::{Path, PathBuf};
use std::process::{Command};
use std::ptr::{null_mut};
use std::str::{from_utf8};

pub mod blake2s;
pub mod build_env;
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
        s.push_str("-f32.inf");
      } else {
        s.push_str("f32.inf");
      }
    } else {
      s.push_str(self.buf.borrow_mut().format_finite(x));
      s.push_str("f32");
    }
  }
}

#[derive(Clone, Debug)]
pub struct Config {
  // TODO
  pub work_dir: PathBuf,
  pub futhark:  PathBuf,
}

impl Default for Config {
  fn default() -> Config {
    let mut work_dir = home_dir().unwrap();
    work_dir.push(".futhark_ffi");
    work_dir.push("cache");
    let futhark = PathBuf::from("../futhark_ffi/futhark");
    Config{
      work_dir,
      futhark,
    }
  }
}

// NB: This "FFI" really just calls the futhark executable.

#[derive(Clone, Copy, Debug)]
pub enum BuildError {
  Cache,
  FutharkCommand,
  Futhark(Option<i32>),
  JsonPath,
  JsonUtf8,
  JsonFromStr,
  JsonDecode,
  Cc,
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

#[repr(C)]
pub struct futhark_context_config([u8; 0]);

#[repr(C)]
pub struct futhark_context([u8; 0]);

#[allow(non_snake_case)]
#[derive(Default)]
pub struct ObjectFFI {
  pub _inner:       Option<Library>,
  pub ctx_cfg_new:  Option<Symbol<extern "C" fn () -> *mut futhark_context_config>>,
  pub ctx_cfg_free: Option<Symbol<extern "C" fn (*mut futhark_context_config)>>,
  // TODO TODO
  pub ctx_cfg_set_cuGetErrorString:         Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuInit:                   Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuDeviceGetCount:         Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuDeviceGetName:          Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuDeviceGet:              Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuDeviceGetAttribute:     Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuCtxCreate:              Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuCtxDestroy:             Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuCtxPopCurrent:          Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuCtxPushCurrent:         Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuCtxSynchronize:         Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuMemAlloc:               Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuMemFree:                Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuMemcpy:                 Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuMemcpyHtoD:             Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuMemcpyDtoH:             Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuMemcpyAsync:            Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuMemcpyHtoDAsync:        Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuMemcpyDtoHAsync:        Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cudaEventCreate:          Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cudaEventDestroy:         Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cudaEventRecord:          Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cudaEventElapsedTime:     Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_nvrtcGetErrorString:      Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_nvrtcCreateProgram:       Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_nvrtcDestroyProgram:      Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_nvrtcCompileProgram:      Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_nvrtcGetProgramLogSize:   Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_nvrtcGetProgramLog:       Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_nvrtcGetPTXSize:          Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_nvrtcGetPTX:              Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuModuleLoadData:         Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuModuleUnload:           Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuModuleGetFunction:      Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuFuncGetAttribute:       Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuLaunchKernel:           Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_new:      Option<Symbol<extern "C" fn (*mut futhark_context_config) -> *mut futhark_context>>,
  pub ctx_free:     Option<Symbol<extern "C" fn (*mut futhark_context)>>,
  pub ctx_set_max_block_size:       Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_max_grid_size:        Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_max_tile_size:        Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_max_threshold:        Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_max_shared_memory:    Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_max_bespoke:          Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_lockstep_width:       Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_device:       Option<Symbol<extern "C" fn (*mut futhark_context, c_int) -> c_int>>,
  pub ctx_set_stream:       Option<Symbol<extern "C" fn (*mut futhark_context, *mut c_void) -> *mut c_void>>,
  pub ctx_may_fail: Option<Symbol<extern "C" fn (*mut futhark_context) -> c_int>>,
  pub ctx_sync:     Option<Symbol<extern "C" fn (*mut futhark_context) -> c_int>>,
  /*new_f32_1d:   Option<Symbol<extern "C" fn () -> ()>>,
  new_i32_1d:   Option<Symbol<extern "C" fn () -> ()>>,
  new_u32_1d:   Option<Symbol<extern "C" fn () -> ()>>,
  new_f16_1d:   Option<Symbol<extern "C" fn () -> ()>>,
  new_u16_1d:   Option<Symbol<extern "C" fn () -> ()>>,
  new_u8_1d:    Option<Symbol<extern "C" fn () -> ()>>,*/
  // TODO
  pub entry:  Option<Symbol<extern "C" fn () -> ()>>,
}

impl Drop for ObjectFFI {
  fn drop(&mut self) {
    let inner = self._inner.take();
    *self = Default::default();
    if let Some(inner) = inner {
      drop(inner);
    }
  }
}

impl ObjectFFI {
  pub unsafe fn load_symbols(&mut self) {
    let inner = self._inner.as_ref().unwrap();
    self.ctx_cfg_new = inner.get(b"futhark_context_config_new").ok();
    self.ctx_cfg_free = inner.get(b"futhark_context_config_free").ok();
    self.ctx_cfg_set_cuGetErrorString = inner.get(b"futhark_context_config_set_cuGetErrorString").ok();
    self.ctx_cfg_set_cuInit = inner.get(b"futhark_context_config_set_cuInit").ok();
    self.ctx_cfg_set_cuDeviceGetCount = inner.get(b"futhark_context_config_set_cuDeviceGetCount").ok();
    self.ctx_cfg_set_cuDeviceGetName = inner.get(b"futhark_context_config_set_cuDeviceGetName").ok();
    self.ctx_cfg_set_cuDeviceGet = inner.get(b"futhark_context_config_set_cuDeviceGet").ok();
    self.ctx_cfg_set_cuDeviceGetAttribute = inner.get(b"futhark_context_config_set_cuDeviceGetAttribute").ok();
    self.ctx_cfg_set_cuCtxCreate = inner.get(b"futhark_context_config_set_cuCtxCreate").ok();
    self.ctx_cfg_set_cuCtxDestroy = inner.get(b"futhark_context_config_set_cuCtxDestroy").ok();
    self.ctx_cfg_set_cuCtxPopCurrent = inner.get(b"futhark_context_config_set_cuCtxPopCurrent").ok();
    self.ctx_cfg_set_cuCtxPushCurrent = inner.get(b"futhark_context_config_set_cuCtxPushCurrent").ok();
    self.ctx_cfg_set_cuCtxSynchronize = inner.get(b"futhark_context_config_set_cuCtxSynchronize").ok();
    self.ctx_cfg_set_cuMemAlloc = inner.get(b"futhark_context_config_set_cuMemAlloc").ok();
    self.ctx_cfg_set_cuMemFree = inner.get(b"futhark_context_config_set_cuMemFree").ok();
    self.ctx_cfg_set_cuMemcpy = inner.get(b"futhark_context_config_set_cuMemcpy").ok();
    self.ctx_cfg_set_cuMemcpyHtoD = inner.get(b"futhark_context_config_set_cuMemcpyHtoD").ok();
    self.ctx_cfg_set_cuMemcpyDtoH = inner.get(b"futhark_context_config_set_cuMemcpyDtoH").ok();
    self.ctx_cfg_set_cuMemcpyAsync = inner.get(b"futhark_context_config_set_cuMemcpyAsync").ok();
    self.ctx_cfg_set_cuMemcpyHtoDAsync = inner.get(b"futhark_context_config_set_cuMemcpyHtoDAsync").ok();
    self.ctx_cfg_set_cuMemcpyDtoHAsync = inner.get(b"futhark_context_config_set_cuMemcpyDtoHAsync").ok();
    self.ctx_cfg_set_cudaEventCreate = inner.get(b"futhark_context_config_set_cudaEventCreate").ok();
    self.ctx_cfg_set_cudaEventDestroy = inner.get(b"futhark_context_config_set_cudaEventDestroy").ok();
    self.ctx_cfg_set_cudaEventRecord = inner.get(b"futhark_context_config_set_cudaEventRecord").ok();
    self.ctx_cfg_set_cudaEventElapsedTime = inner.get(b"futhark_context_config_set_cudaEventElapsedTime").ok();
    self.ctx_cfg_set_nvrtcGetErrorString = inner.get(b"futhark_context_config_set_nvrtcGetErrorString").ok();
    self.ctx_cfg_set_nvrtcCreateProgram = inner.get(b"futhark_context_config_set_nvrtcCreateProgram").ok();
    self.ctx_cfg_set_nvrtcDestroyProgram = inner.get(b"futhark_context_config_set_nvrtcDestroyProgram").ok();
    self.ctx_cfg_set_nvrtcCompileProgram = inner.get(b"futhark_context_config_set_nvrtcCompileProgram").ok();
    self.ctx_cfg_set_nvrtcGetProgramLogSize = inner.get(b"futhark_context_config_set_nvrtcGetProgramLogSize").ok();
    self.ctx_cfg_set_nvrtcGetProgramLog = inner.get(b"futhark_context_config_set_nvrtcGetProgramLog").ok();
    self.ctx_cfg_set_nvrtcGetPTXSize = inner.get(b"futhark_context_config_set_nvrtcGetPTXSize").ok();
    self.ctx_cfg_set_nvrtcGetPTX = inner.get(b"futhark_context_config_set_nvrtcGetPTX").ok();
    self.ctx_cfg_set_cuModuleLoadData = inner.get(b"futhark_context_config_set_cuModuleLoadData").ok();
    self.ctx_cfg_set_cuModuleUnload = inner.get(b"futhark_context_config_set_cuModuleUnload").ok();
    self.ctx_cfg_set_cuModuleGetFunction = inner.get(b"futhark_context_config_set_cuModuleGetFunction").ok();
    self.ctx_cfg_set_cuFuncGetAttribute = inner.get(b"futhark_context_config_set_cuFuncGetAttribute").ok();
    self.ctx_cfg_set_cuLaunchKernel = inner.get(b"futhark_context_config_set_cuLaunchKernel").ok();
    self.ctx_new = inner.get(b"futhark_context_new").ok();
    self.ctx_free = inner.get(b"futhark_context_free").ok();
    self.ctx_set_max_block_size = inner.get(b"futhark_context_set_max_block_size").ok();
    self.ctx_set_max_grid_size = inner.get(b"futhark_context_set_max_grid_size").ok();
    self.ctx_set_max_tile_size = inner.get(b"futhark_context_set_max_tile_size").ok();
    self.ctx_set_max_threshold = inner.get(b"futhark_context_set_max_threshold").ok();
    self.ctx_set_max_shared_memory = inner.get(b"futhark_context_set_max_shared_memory").ok();
    self.ctx_set_max_bespoke = inner.get(b"futhark_context_set_max_bespoke").ok();
    self.ctx_set_lockstep_width = inner.get(b"futhark_context_set_lockstep_width").ok();
    self.ctx_set_device = inner.get(b"futhark_context_set_device").ok();
    self.ctx_set_stream = inner.get(b"futhark_context_set_stream").ok();
    self.ctx_may_fail = inner.get(b"futhark_context_may_fail").ok();
    self.ctx_sync = inner.get(b"futhark_context_sync").ok();
    // TODO
    self.entry = inner.get(b"futhark_enter_kernel").ok();
    // TODO
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

impl Config {
  pub fn cached_or_new_object<B: Backend>(&self, src_buf: &[u8]) -> Result<Object<B>, BuildError> {
    let mut srchash = Blake2s::new_hash();
    srchash.hash_bytes(src_buf);
    let h = srchash.finalize();
    let hx = h.to_hex();
    let stem = format!("futhark_obj_{}_{}", B::cmd_arg(), hx);
    create_dir_all(&self.work_dir).ok();
    let mut f_path = self.work_dir.clone();
    f_path.push(&stem);
    f_path.set_extension("fut");
    let mut c_path = f_path.clone();
    let mut h_path = f_path.clone();
    let mut json_path = f_path.clone();
    let mut dylib_path = f_path.clone();
    c_path.set_extension("c");
    h_path.set_extension("h");
    json_path.set_extension("json");
    // FIXME FIXME: os-specific dylib path.
    match dylib_path.file_name() {
      None => panic!("bug"),
      Some(s) => {
        dylib_path.set_file_name(&format!("lib{}", s.to_str().unwrap()));
      }
    }
    dylib_path.set_extension("so");
    // FIXME FIXME: caching.
    match OpenOptions::new().write(true).create(true).truncate(true).open(&f_path) {
      Err(_) => return Err(BuildError::Cache),
      Ok(ref mut f) => {
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
    let manifest: ObjectManifest = match File::open(&json_path) {
      Err(_) => return Err(BuildError::JsonPath),
      Ok(mut json_f) => {
        let mut json_buf = Vec::new();
        match json_f.read_to_end(&mut json_buf) {
          Err(_) => panic!("bug"),
          Ok(_) => {}
        }
        let j = match Json::from_str(from_utf8(&json_buf).map_err(|_| BuildError::JsonUtf8)?) {
          Err(_) => return Err(BuildError::JsonFromStr),
          Ok(j) => j
        };
        match Decodable::decode(&mut JsonDecoder::new(fixup_json_manifest(j))) {
          Err(_) => return Err(BuildError::JsonDecode),
          Ok(m) => m
        }
      }
    };
    if &manifest.backend != B::cmd_arg() {
      panic!("bug");
    }
    println!("DEBUG: futhark_ffi::Config::cached_or_new_object: target: {}", self::build_env::TARGET);
    println!("DEBUG: futhark_ffi::Config::cached_or_new_object: dylib path: {}", dylib_path.to_str().unwrap());
    println!("DEBUG: futhark_ffi::Config::cached_or_new_object: dylib file: {}", dylib_path.file_name().unwrap().to_str().unwrap());
    match cc::Build::new()
      // NB: We have to set `out_dir`, `target`, `host`, `debug`, and `opt_level`;
      // normally they are read from env vars passed by cargo to the build script.
      .out_dir(&self.work_dir)
      .target(self::build_env::TARGET)
      .host(self::build_env::TARGET)
      .debug(false)
      .opt_level(2)
      .pic(true)
      .include(&self.work_dir)
      .include("../virtcuda")
      .file(&c_path)
      .object_prefix_hash(false)
      .archive(false)
      .dylib(true)
      //.try_compile(dylib_path.file_name().unwrap().to_str().unwrap())
      .try_compile(&stem)
    {
      Err(e) => {
        println!("WARNING: futhark_ffi::Config::cached_or_new_object: cc build error: {}", e);
        return Err(BuildError::Cc);
      }
      Ok(_) => {}
    }
    let mut ffi = ObjectFFI::default();
    unsafe {
      ffi._inner = Some(match Library::new(&dylib_path) {
        Err(_) => return Err(BuildError::Dylib),
        Ok(dylib) => dylib
      });
      ffi.load_symbols();
    }
    Ok(Object{
      manifest,
      ffi,
      cfg:  null_mut(),
      ctx:  null_mut(),
      _mrk: PhantomData,
    })
  }
}
