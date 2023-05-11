extern crate cc;
extern crate home;
extern crate libc;
extern crate libloading;
extern crate rustc_serialize;
//extern crate tempfile;

use self::blake2s::{Blake2s};

use home::{home_dir};
use libc::{c_int, c_void};
use libloading::os::unix::{Library, Symbol};
//use potato::{Blake2s};
use rustc_serialize::{Decodable};
use rustc_serialize::hex::{ToHex};
use rustc_serialize::json::{Decoder as JsonDecoder, Json};
//use tempfile::{Builder as TempBuilder};

use std::collections::{BTreeMap};
//use std::env;
use std::fs::{File, create_dir_all};
use std::io::{Read};
use std::marker::{PhantomData};
use std::path::{Path, PathBuf};
use std::process::{Command};
use std::ptr::{null_mut};
use std::str::{from_utf8};

pub mod blake2s;
//pub mod temp;

// NB: This "FFI" really just calls the futhark executable.

#[derive(Clone, Copy, Debug)]
pub enum BuildError {
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

#[derive(Default)]
pub struct ObjectFFI {
  pub _inner:       Option<Library>,
  pub ctx_cfg_new:  Option<Symbol<extern "C" fn () -> *mut futhark_context_config>>,
  pub ctx_cfg_free: Option<Symbol<extern "C" fn (*mut futhark_context_config)>>,
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
  pub ctx_cfg_set_cuFuncGetAttr:            Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuLaunchKernel:           Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_new:      Option<Symbol<extern "C" fn (*mut futhark_context_config) -> *mut futhark_context>>,
  pub ctx_free:     Option<Symbol<extern "C" fn (*mut futhark_context)>>,
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
    assert!(inner.is_some());
    *self = Default::default();
    drop(inner.unwrap());
  }
}

impl ObjectFFI {
  pub unsafe fn load_symbols(&mut self) {
    let inner = self._inner.as_ref().unwrap();
    self.ctx_cfg_new = inner.get(b"futhark_context_config_new").ok();
    self.ctx_cfg_free = inner.get(b"futhark_context_config_free").ok();
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
    self.ctx_cfg_set_cuFuncGetAttr = inner.get(b"futhark_context_config_set_cuFuncGetAttr").ok();
    self.ctx_cfg_set_cuLaunchKernel = inner.get(b"futhark_context_config_set_cuLaunchKernel").ok();
    self.ctx_new = inner.get(b"futhark_context_new").ok();
    self.ctx_free = inner.get(b"futhark_context_free").ok();
    self.ctx_may_fail = inner.get(b"futhark_context_may_fail").ok();
    self.ctx_sync = inner.get(b"futhark_context_sync").ok();
    // TODO
    self.entry = inner.get(b"futhark_enter_kernel").ok();
    // TODO
  }
}

pub struct Object<B: Backend> {
  manifest: ObjectManifest,
  ffi:  ObjectFFI,
  cfg:  *mut futhark_context_config,
  ctx:  *mut futhark_context,
  _mrk: PhantomData<B>,
}

impl<B: Backend> Object<B> {
  pub fn cached_or_new(src_buf: &[u8]) -> Result<Object<B>, BuildError> {
    let mut srchash = Blake2s::new_hash();
    srchash.hash_bytes(src_buf);
    let h = srchash.finalize();
    let hx = h.to_hex();
    let stem = format!("futhark_obj_{}_{}", B::cmd_arg(), hx);
    let mut work_dir = home_dir().unwrap();
    work_dir.push(".futhark_ffi");
    work_dir.push("cache");
    create_dir_all(&work_dir).ok();
    let mut f_path = work_dir.clone();
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
    match Command::new("futhark")
      //.arg(from_utf8(B::cmd_arg()).unwrap())
      .arg(B::cmd_arg())
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
    match cc::Build::new()
      .shared_flag(true)
      .static_flag(false)
      .opt_level(2)
      .include(&work_dir)
      .file(&c_path)
      .try_compile(dylib_path.to_str().unwrap())
    {
      Err(_) => {
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
