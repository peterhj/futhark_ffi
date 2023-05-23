extern crate cc;
extern crate home;
extern crate libc;
extern crate libloading;
extern crate rustc_serialize;
extern crate ryu;
//extern crate tempfile;

use self::blake2s::{Blake2s};
use self::bindings::{ObjectFFI};
use self::types::*;

use home::{home_dir};
//use potato::{Blake2s};
use rustc_serialize::{Decodable};
use rustc_serialize::hex::{ToHex};
use rustc_serialize::json::{Decoder as JsonDecoder, Json};
use ryu::{Buffer as RyuBuffer};
//use tempfile::{Builder as TempBuilder};

use std::cell::{RefCell};
use std::collections::{BTreeMap};
//use std::env;
use std::ffi::{OsStr};
use std::fs::{File, OpenOptions, create_dir_all};
use std::io::{Read, Write};
use std::marker::{PhantomData};
use std::path::{Path, PathBuf};
use std::process::{Command};
use std::ptr::{null_mut};
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
  pub cachedir: PathBuf,
  pub futhark:  PathBuf,
  pub target:   Option<String>,
}

impl Default for Config {
  fn default() -> Config {
    let mut cachedir = home_dir().unwrap();
    cachedir.push(".futhark_ffi");
    cachedir.push("cache");
    // FIXME FIXME: figure out how to package this.
    let futhark = PathBuf::from("../futhark_ffi/cacti-futhark");
    let target = None;
    Config{
      cachedir,
      futhark,
      target,
    }
  }
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
      .include("../virtcuda")
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
