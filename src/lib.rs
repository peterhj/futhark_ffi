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
use std::fmt::{Debug, Formatter, Result as FmtResult, Write as FmtWrite};
use std::fs::{File, OpenOptions, create_dir_all};
use std::io::{Read, Write, BufReader, BufWriter, Seek, SeekFrom};
use std::marker::{PhantomData};
use std::mem::{size_of, swap};
use std::os::unix::fs::{MetadataExt};
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

#[derive(Clone, Copy, Debug)]
pub enum AbiScalar {
  Empty,
  F64(f64),
  F32(f32),
  F16(u16),
  Bf16(u16),
  I64(i64),
  I32(i32),
  I16(i16),
  I8(i8),
  U64(u64),
  U32(u32),
  U16(u16),
  U8(u8),
}

impl AbiScalar {
  pub fn into_f32(&self) -> f32 {
    match self {
      &AbiScalar::F32(x) => x,
      _ => panic!("bug: AbiScalar::into_f32: actual={:?}", self.type_())
    }
  }

  pub fn into_i64(&self) -> i64 {
    match self {
      &AbiScalar::I64(x) => x,
      _ => panic!("bug: AbiScalar::into_i64: actual={:?}", self.type_())
    }
  }

  pub fn type_(&self) -> AbiScalarType {
    match self {
      &AbiScalar::Empty     => AbiScalarType::Empty,
      &AbiScalar::F64(..)   => AbiScalarType::F64,
      &AbiScalar::F32(..)   => AbiScalarType::F32,
      &AbiScalar::F16(..)   => AbiScalarType::F16,
      &AbiScalar::Bf16(..)  => AbiScalarType::Bf16,
      &AbiScalar::I64(..)   => AbiScalarType::I64,
      &AbiScalar::I32(..)   => AbiScalarType::I32,
      &AbiScalar::I16(..)   => AbiScalarType::I16,
      &AbiScalar::I8(..)    => AbiScalarType::I8,
      &AbiScalar::U64(..)   => AbiScalarType::U64,
      &AbiScalar::U32(..)   => AbiScalarType::U32,
      &AbiScalar::U16(..)   => AbiScalarType::U16,
      &AbiScalar::U8(..)    => AbiScalarType::U8,
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum AbiScalarType {
  Empty,
  F64,
  F32,
  F16,
  Bf16,
  I64,
  I32,
  I16,
  I8,
  U64,
  U32,
  U16,
  U8,
}

impl Default for AbiScalarType {
  fn default() -> AbiScalarType {
    AbiScalarType::Empty
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum AbiSpace {
  NotSpecified,
  Default,
  Device,
}

impl Default for AbiSpace {
  fn default() -> AbiSpace {
    AbiSpace::NotSpecified
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Default, Debug)]
pub struct Abi {
  pub arityout: u16,
  pub arityin:  u16,
  // FIXME: param buf len.
  pub param_ty: [AbiScalarType; 1],
  pub space:    AbiSpace,
}

impl Abi {
  pub fn num_param(&self) -> usize {
    let mut np = 0;
    for i in 0 .. self.param_ty.len() {
      if self.param_ty[i] == AbiScalarType::Empty {
        break;
      }
      np += 1;
    }
    np
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
  C,
  H,
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
  pub eabi: Option<Abi>,
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
      eabi: None,
      cfg:  null_mut(),
      ctx:  null_mut(),
      _mrk: PhantomData,
    })
  }
}

#[derive(Default)]
pub struct StageMem {
  pub f: Option<Vec<u8>>,
  pub c: Option<Vec<u8>>,
  pub h: Option<Vec<u8>>,
  pub j: Option<Vec<u8>>,
  pub d: Option<Vec<u8>>,
  pub manifest: Option<ObjectManifest>,
}

impl StageMem {
  pub fn reset(&mut self) {
    self.f = None;
    self.c = None;
    self.h = None;
    self.j = None;
    self.d = None;
    self.manifest = None;
  }
}

#[derive(Clone, Copy, Debug)]
#[repr(u8)]
pub enum StageIOErr {
  Eof,
  Corrupt,
  ReadFail,
  WriteFail,
}

pub enum StageLock {
  N,
  R(BufReader<File>),
  W(BufWriter<File>),
}

impl StageLock {
  pub fn is_none(&self) -> bool {
    match self {
      &StageLock::N => true,
      _ => false
    }
  }

  pub fn reader(&mut self) -> &mut BufReader<File> {
    match self {
      &mut StageLock::R(ref mut reader) => reader,
      _ => panic!("bug")
    }
  }

  pub fn writer(&mut self) -> &mut BufWriter<File> {
    match self {
      &mut StageLock::W(ref mut writer) => writer,
      _ => panic!("bug")
    }
  }
}

pub struct StageFile {
  path: PathBuf,
  lock: StageLock,
}

impl StageFile {
  pub fn new(path: PathBuf) -> StageFile {
    StageFile{
      path,
      lock: StageLock::N,
    }
  }

  pub fn reset(&mut self) {
    self.lock = StageLock::N;
    let file = OpenOptions::new().read(true).write(true).create(true).truncate(true).open(&self.path).unwrap();
    let size = file.metadata().unwrap().size();
    assert_eq!(size, 0);
  }

  pub fn unlock(&mut self) {
    self.lock = StageLock::N;
  }

  pub fn _read_next<R: Read>(reader: &mut R) -> Result<(u8, Vec<u8>), StageIOErr> {
    let mut prefix_buf = [0u8; 3];
    match reader.read(&mut prefix_buf as &mut [_]) {
      Ok(3) => {}
      Ok(0) => {
        return Err(StageIOErr::Eof);
      }
      // FIXME
      Ok(_) => unimplemented!(),
      Err(_) => {
        return Err(StageIOErr::ReadFail);
      }
    }
    if !(prefix_buf[0] == b'\n' && prefix_buf[2] == b':') {
      return Err(StageIOErr::Corrupt);
    }
    let mut hash_buf = Vec::with_capacity(64);
    hash_buf.resize(64, 0);
    reader.read_exact(&mut hash_buf as &mut [_]).map_err(|_| StageIOErr::Corrupt)?;
    Ok((prefix_buf[1], hash_buf))
  }

  pub fn get_next(&mut self) -> Result<(u8, Vec<u8>), StageIOErr> {
    if self.lock.is_none() {
      let mut file = match OpenOptions::new().read(true).open(&self.path) {
        Err(_) => return Err(StageIOErr::Eof),
        Ok(f) => f
      };
      let size = file.metadata().unwrap().size();
      if size % 67 != 0 {
        return Err(StageIOErr::Corrupt);
      }
      //file.seek(SeekFrom::Start(size as _)).unwrap();
      self.lock = StageLock::R(BufReader::new(file));
    }
    Self::_read_next(self.lock.reader())
  }

  pub fn _write_next<W: Write>(key: u8, hx_buf: &[u8], writer: &mut W) -> Result<(), StageIOErr> {
    assert_eq!(hx_buf.len(), 64);
    writer.write_all(&[b'\n', key, b':']).map_err(|_| StageIOErr::WriteFail)?;
    writer.write_all(hx_buf).map_err(|_| StageIOErr::WriteFail)?;
    Ok(())
  }

  pub fn put_next(&mut self, key: u8, hx_buf: &[u8]) -> Result<(), StageIOErr> {
    if self.lock.is_none() {
      let mut file = OpenOptions::new().read(true).write(true).create(true).open(&self.path).unwrap();
      let size = file.metadata().unwrap().size();
      if size % 67 != 0 {
        return Err(StageIOErr::Corrupt);
      }
      file.seek(SeekFrom::Start(size as _)).unwrap();
      self.lock = StageLock::W(BufWriter::new(file));
    }
    Self::_write_next(key, hx_buf, self.lock.writer())
  }
}

#[derive(Clone, Copy, PartialEq, Eq, PartialOrd, Ord, Debug)]
#[repr(u8)]
pub enum Stage {
  _Top = 0,
  Fut = 1,
  C = 2,
  Dylib = 3,
}

impl Config {
  pub fn build<B: Backend>(&self, stage: Stage, src_buf: &[u8]) -> Result<Option<Object<B>>, BuildError> {
    let mut srchash = Blake2s::new_hash();
    srchash.hash_bytes(src_buf);
    let src_h = srchash.finalize();
    let src_hx = src_h.to_hex();
    let stem = format!("futhark_obj_{}_{}", B::cmd_arg(), src_hx);
    create_dir_all(&self.cachedir).ok();
    let mut f_path = self.cachedir.clone();
    f_path.push(&stem);
    f_path.set_extension("fut");
    let mut c_path = f_path.clone();
    let mut h_path = f_path.clone();
    let mut json_path = f_path.clone();
    let mut dylib_path = f_path.clone();
    //let mut hash_path = f_path.clone();
    let mut stage_path = f_path.clone();
    c_path.set_extension("c");
    h_path.set_extension("h");
    json_path.set_extension("json");
    //hash_path.set_extension("hash");
    stage_path.set_extension("stage");
    // FIXME FIXME: os-specific dylib path.
    match dylib_path.file_name() {
      None => panic!("bug"),
      Some(s) => {
        dylib_path.set_file_name(&format!("lib{}", s.to_str().unwrap()));
      }
    }
    dylib_path.set_extension("so");
    //println!("DEBUG: futhark_ffi::Config::build: target: {}", crate::build_env::TARGET);
    //println!("DEBUG: futhark_ffi::Config::build: dylib path: {}", dylib_path.to_str().unwrap());
    //println!("DEBUG: futhark_ffi::Config::build: dylib file: {}", dylib_path.file_name().unwrap().to_str().unwrap());
    /*match (ObjectManifest::open_with_hash(&json_path),
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
          println!("DEBUG: futhark_ffi::Config::build: load cached...");
          return Object::open(manifest, &dylib_path).map_err(|_| BuildError::Dylib).map(|obj| Some(obj));
        }
      }
      _ => {}
    }*/
    let mut stage_mem = StageMem::default();
    let mut stagefile = StageFile::new(stage_path);
    loop {
      match stagefile.get_next() {
        Err(StageIOErr::Eof) => {
          stagefile.unlock();
          break;
        }
        Err(_) => {
          stage_mem.reset();
          stagefile.reset();
        }
        Ok((b'f', hv)) => stage_mem.f = Some(hv),
        Ok((b'c', hv)) => stage_mem.c = Some(hv),
        Ok((b'h', hv)) => stage_mem.h = Some(hv),
        Ok((b'j', hv)) => stage_mem.j = Some(hv),
        Ok((b'd', hv)) => stage_mem.d = Some(hv),
        Ok(_) => {}
      }
    }
    let mut retry = false;
    loop {
      if stage == Stage::_Top {
        return Ok(None);
      }
      if stage >= Stage::Fut {
        if stage_mem.f.is_none() {
          match OpenOptions::new().read(false).write(true).create(true).truncate(true).open(&f_path) {
            Err(_) => return Err(BuildError::Cache),
            Ok(mut f) => {
              f.write_all(src_buf).unwrap();
            }
          }
          match stagefile.put_next(b'f', src_hx.as_bytes()) {
            Err(_) => {
              stagefile.reset();
              return Err(BuildError::Cache);
            }
            Ok(_) => {}
          }
          stage_mem.f = Some(src_hx.as_bytes().to_owned());
        }
        if src_hx.as_bytes() != stage_mem.f.as_ref().unwrap() {
          stagefile.reset();
          if retry {
            return Err(BuildError::Cache);
          }
          retry = true;
          continue;
        }
      }
      if stage == Stage::Fut {
        return Ok(None);
      }
      if stage >= Stage::C {
        if stage_mem.c.is_none() {
          match Command::new(&self.futhark)
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
          let c_hx = match OpenOptions::new().read(true).write(false).create(false).open(&c_path) {
            Err(_) => return Err(BuildError::C),
            Ok(mut file) => {
              let mut buf = Vec::new();
              file.read_to_end(&mut buf).unwrap();
              let mut h = Blake2s::new_hash();
              h.hash_bytes(&buf);
              let h = h.finalize();
              h.to_hex()
            }
          };
          let h_hx = match OpenOptions::new().read(true).write(false).create(false).open(&h_path) {
            Err(_) => return Err(BuildError::H),
            Ok(mut file) => {
              let mut buf = Vec::new();
              file.read_to_end(&mut buf).unwrap();
              let mut h = Blake2s::new_hash();
              h.hash_bytes(&buf);
              let h = h.finalize();
              h.to_hex()
            }
          };
          let (manifest, json_hx) = match ObjectManifest::open_with_hash(&json_path) {
            Err(_) => return Err(BuildError::Json),
            Ok((m, hx)) => (m, hx)
          };
          if &manifest.backend != B::cmd_arg() {
            panic!("bug");
          }
          match stagefile.put_next(b'c', c_hx.as_bytes()) {
            Err(_) => {
              stagefile.reset();
              return Err(BuildError::Cache);
            }
            Ok(_) => {}
          }
          match stagefile.put_next(b'h', h_hx.as_bytes()) {
            Err(_) => {
              stagefile.reset();
              return Err(BuildError::Cache);
            }
            Ok(_) => {}
          }
          match stagefile.put_next(b'j', json_hx.as_bytes()) {
            Err(_) => {
              stagefile.reset();
              return Err(BuildError::Cache);
            }
            Ok(_) => {}
          }
          stage_mem.c = Some(c_hx.as_bytes().to_owned());
          stage_mem.h = Some(h_hx.as_bytes().to_owned());
          stage_mem.j = Some(json_hx.as_bytes().to_owned());
          stage_mem.manifest = Some(manifest);
        }
        if stage_mem.manifest.is_none() {
          match ObjectManifest::open_with_hash(&json_path) {
            Err(_) => {
              stagefile.reset();
              if retry {
                return Err(BuildError::Cache);
              }
              retry = true;
              continue;
            }
            Ok((manifest, json_hx)) => {
              if stage_mem.j.as_ref().map(|buf| buf as &[_]) != Some(json_hx.as_bytes()) {
                stagefile.reset();
                if retry {
                  return Err(BuildError::Cache);
                }
                retry = true;
                continue;
              }
              stage_mem.manifest = Some(manifest);
            }
          }
        }
      }
      if stage == Stage::C {
        return Ok(None);
      }
      if stage >= Stage::Dylib {
        if stage_mem.d.is_none() {
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
              println!("WARNING: futhark_ffi::Config::build: cc build error: {}", e);
              return Err(BuildError::Cc);
            }
            Ok(_) => {}
          }
          let dylib_hx = match OpenOptions::new().read(true).write(false).create(false).open(&dylib_path) {
            Err(_) => return Err(BuildError::DylibPath),
            Ok(mut file) => {
              let mut buf = Vec::new();
              file.read_to_end(&mut buf).unwrap();
              let mut h = Blake2s::new_hash();
              h.hash_bytes(&buf);
              let h = h.finalize();
              h.to_hex()
            }
          };
          match stagefile.put_next(b'd', dylib_hx.as_bytes()) {
            Err(_) => {
              stagefile.reset();
              return Err(BuildError::Cache);
            }
            Ok(_) => {}
          }
          stage_mem.d = Some(dylib_hx.as_bytes().to_owned());
          println!("DEBUG: futhark_ffi::Config::build: new build done!");
        } else {
          println!("DEBUG: futhark_ffi::Config::build: load cached...");
        }
      }
      if stage == Stage::Dylib {
        let manifest = stage_mem.manifest.unwrap();
        return Object::open(manifest, &dylib_path).map_err(|_| BuildError::Dylib).map(|obj| Some(obj));
      }
      unreachable!();
    }
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
  //type RawArray;

  fn enter_kernel(&mut self, arityin: u16, arityout: u16, param: &[AbiScalar], arg_arr: &[Self::Array], out_arr: &mut [Self::Array]) -> Result<(), i32>;
}

impl ObjectExt for Object<CudaBackend> {
  type Array = ArrayDev;
  //type RawArray = *mut memblock_dev;

  fn enter_kernel(&mut self, arityin: u16, arityout: u16, param: &[AbiScalar], arg_arr: &[ArrayDev], out_arr: &mut [ArrayDev]) -> Result<(), i32> {
    // FIXME FIXME
    //let out_raw_arr_buf_len = out_raw_arr.len();
    //let out_raw_arr_buf = out_raw_arr.as_mut_ptr();
    //assert_eq!(out_raw_arr_buf_len, arityout as usize);
    assert_eq!(out_arr.len(), arityout as usize);
    assert_eq!(arg_arr.len(), arityin as usize);
    let np = param.len();
    let mut param_ty = Vec::with_capacity(np);
    for p in param.iter() {
      param_ty.push(p.type_());
    }
    assert_eq!(param_ty.len(), np);
    for _ in np .. 1 {
      param_ty.push(AbiScalarType::Empty);
    }
    match self.eabi.as_ref() {
      None => {
        let ret = unsafe { self.ffi.load_entry_symbol(AbiSpace::Device, arityin, arityout, &param_ty[ .. np]) };
        assert!(ret.is_some());
        let abi = Abi{
          arityout,
          arityin,
          param_ty: [param_ty[0]],
          space: AbiSpace::Device,
        };
        self.eabi = Some(abi);
      }
      Some(e_abi) => {
        assert_eq!(e_abi.space, AbiSpace::Device);
        assert_eq!(e_abi.arityin, arityin);
        assert_eq!(e_abi.arityout, arityout);
        assert_eq!(&e_abi.param_ty[..], &param_ty);
      }
    }
    let ret = match (arityout, arityin) {
      (1, 0) => {
        if &param_ty[ .. np] == &[AbiScalarType::F32] {
          (self.ffi.entry_1_0_p_f32_dev.as_ref().unwrap())(self.ctx, out_arr[0]._as_mut_ptr(), param[0].into_f32())
        } else if &param_ty[ .. np] == &[AbiScalarType::I64] {
          (self.ffi.entry_1_0_p_i64_dev.as_ref().unwrap())(self.ctx, out_arr[0]._as_mut_ptr(), param[0].into_i64())
        } else if &param_ty[ .. np] == &[] {
          (self.ffi.entry_1_0_dev.as_ref().unwrap())(self.ctx, out_arr[0]._as_mut_ptr())
        } else {
          unimplemented!();
        }
      }
      (1, 1) => {
        if &param_ty[ .. np] == &[AbiScalarType::F32] {
          (self.ffi.entry_1_1_p_f32_dev.as_ref().unwrap())(self.ctx, out_arr[0]._as_mut_ptr(), arg_arr[0].as_ptr(), param[0].into_f32())
        } else if &param_ty[ .. np] == &[AbiScalarType::I64] {
          (self.ffi.entry_1_1_p_i64_dev.as_ref().unwrap())(self.ctx, out_arr[0]._as_mut_ptr(), arg_arr[0].as_ptr(), param[0].into_i64())
        } else if &param_ty[ .. np] == &[] {
          (self.ffi.entry_1_1_dev.as_ref().unwrap())(self.ctx, out_arr[0]._as_mut_ptr(), arg_arr[0].as_ptr())
        } else {
          unimplemented!();
        }
      }
      (1, 2) => (self.ffi.entry_1_2_dev.as_ref().unwrap())(self.ctx, out_arr[0]._as_mut_ptr(), arg_arr[0].as_ptr(), arg_arr[1].as_ptr()),
      (1, 3) => (self.ffi.entry_1_3_dev.as_ref().unwrap())(self.ctx, out_arr[0]._as_mut_ptr(), arg_arr[0].as_ptr(), arg_arr[1].as_ptr(), arg_arr[2].as_ptr()),
      (1, 4) => (self.ffi.entry_1_4_dev.as_ref().unwrap())(self.ctx, out_arr[0]._as_mut_ptr(), arg_arr[0].as_ptr(), arg_arr[1].as_ptr(), arg_arr[2].as_ptr(), arg_arr[3].as_ptr()),
      _ => {
        panic!("bug: Object::<CudaBackend>::enter_kernel: unimplemented: arityin={} arityout={} param={:?}", arityin, arityout, &param_ty);
      }
    };
    if ret != FUTHARK_SUCCESS {
      return Err(ret);
    }
    Ok(())
  }
}

#[repr(transparent)]
pub struct ArrayDev {
  pub raw:  usize,
}

impl Debug for ArrayDev {
  fn fmt(&self, f: &mut Formatter) -> FmtResult {
    let ndim = self._ndim();
    let mem = self.as_ptr();
    if mem.is_null() {
      return write!(f, "ArrayDev({} | null)", ndim);
    }
    unsafe {
      let c = (&*mem).refcount as usize;
      let dptr = (&*mem).mem_dptr as usize;
      let size = (&*mem).mem_size as usize;
      let tag = (&*mem).tag as usize;
      write!(f, "ArrayDev({} | 0x{:016x} -> {{ refcount: 0x{:016x}",
          ndim, mem as usize, c)?;
      if c == 0 {
      } else {
        let cd = *(c as *const i32);
        write!(f, " -> {}", cd)?;
      }
      write!(f, ", mem_dptr: 0x{:016x}, mem_size: {}", dptr, size)?;
      if tag == 0 {
        write!(f, ", tag: null")?;
      } else {
        write!(f, ", tag: 0x{:016x}", tag)?;
      }
      if ndim == 0 {
        write!(f, " }})")?;
      } else {
        let buf = mem as *const u8;
        let shape_buf = buf.offset(size_of::<memblock_dev>() as _) as *const i64;
        let shape = from_raw_parts(shape_buf, ndim as usize);
        write!(f, ", shape: {:?} }})", shape)?;
      }
    }
    Ok(())
  }
}

impl Drop for ArrayDev {
  fn drop(&mut self) {
    let ptr = self.as_ptr();
    if ptr.is_null() {
      return;
    }
    match self._dec_refcount() {
      Some(0) => {
        // FIXME FIXME: first, unref.
        match self._ndim() {
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

  pub fn null() -> ArrayDev {
    let ptr: *mut memblock_dev = null_mut();
    let raw = ptr as usize;
    ArrayDev{raw}
  }

  pub fn new_1d() -> ArrayDev {
    assert_eq!(size_of::<array_1d_dev>(), size_of::<memblock_dev>() + 8);
    let ptr = unsafe { malloc(size_of::<array_1d_dev>()) } as *mut _;
    let this = ArrayDev::from_raw(ptr, 1);
    unsafe { this._init(); }
    this
  }

  pub fn new_2d() -> ArrayDev {
    assert_eq!(size_of::<array_2d_dev>(), size_of::<memblock_dev>() + 8 * 2);
    let ptr = unsafe { malloc(size_of::<array_2d_dev>()) } as *mut _;
    let this = ArrayDev::from_raw(ptr, 2);
    unsafe { this._init(); }
    this
  }

  pub fn new_3d() -> ArrayDev {
    assert_eq!(size_of::<array_3d_dev>(), size_of::<memblock_dev>() + 8 * 3);
    let ptr = unsafe { malloc(size_of::<array_3d_dev>()) } as *mut _;
    let this = ArrayDev::from_raw(ptr, 3);
    unsafe { this._init(); }
    this
  }

  pub fn new_4d() -> ArrayDev {
    assert_eq!(size_of::<array_4d_dev>(), size_of::<memblock_dev>() + 8 * 4);
    let ptr = unsafe { malloc(size_of::<array_4d_dev>()) } as *mut _;
    let this = ArrayDev::from_raw(ptr, 4);
    unsafe { this._init(); }
    this
  }

  pub unsafe fn _init(&self) {
    let mem = self.as_ptr();
    assert!(!mem.is_null());
    (&mut *mem).refcount = malloc(size_of::<i32>()) as *mut i32;
    *(&mut *mem).refcount = 1;
    (&mut *mem).mem_dptr = 0;
    (&mut *mem).mem_size = 0;
    (&mut *mem).tag = null_mut();
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

  pub fn _as_mut_ptr(&mut self) -> *mut *mut memblock_dev {
    &mut self.raw as *mut usize as *mut *mut memblock_dev
  }

  pub fn _ndim(&self) -> u8 {
    (self.raw & 7) as u8
  }

  pub fn ndim(&self) -> Option<u8> {
    let nd = (self.raw & 7) as u8;
    if nd == 0 {
      return None;
    }
    Some(nd)
  }

  pub fn _set_ndim(&mut self, nd: u8) {
    assert_eq!(0, self._ndim());
    assert!(nd > 0);
    assert!(nd <= 7);
    self.raw |= (nd as usize);
  }

  pub fn refcount(&self) -> Option<i32> {
    let mem = self.as_ptr() as *const memblock_dev;
    if mem.is_null() {
      return None;
    }
    unsafe {
      let c = (&*mem).refcount as *const i32;
      if c.is_null() {
        return None;
      }
      Some(*c)
    }
  }

  pub fn _dec_refcount(&self) -> Option<i32> {
    let mem = self.as_ptr();
    if mem.is_null() {
      return None;
    }
    //println!("DEBUG: ArrayDev::_dec_refcount: memptr=0x{:016x}", mem as usize);
    unsafe {
      let c = (&*mem).refcount as *mut i32;
      if c.is_null() {
        return None;
      }
      //println!("DEBUG: ArrayDev::_dec_refcount:   refc=0x{:016x}", c as usize);
      //println!("DEBUG: ArrayDev::_dec_refcount:   dptr=0x{:016x}", (&*mem).mem_dptr);
      //println!("DEBUG: ArrayDev::_dec_refcount:   size=0x{:016x}", (&*mem).mem_size);
      let prev_c = *c;
      assert!(prev_c >= 1);
      let new_c = prev_c - 1;
      write(c, new_c);
      Some(new_c)
    }
  }

  pub fn mem_parts(&self) -> Option<(u64, usize)> {
    let mem = self.as_ptr() as *const memblock_dev;
    if mem.is_null() {
      return None;
    }
    unsafe {
      let mem = &*mem;
      Some((mem.mem_dptr, mem.mem_size))
    }
  }

  pub fn set_mem_parts(&self, dptr: u64, size: usize) {
    let mem = self.as_ptr();
    assert!(!mem.is_null());
    unsafe {
      (&mut *mem).mem_dptr = dptr;
      (&mut *mem).mem_size = size;
    }
  }

  pub fn shape(&self) -> Option<&[i64]> {
    let ndim = self._ndim();
    if ndim == 0 {
      return None;
    }
    unsafe {
      let buf = self.as_ptr() as *const u8;
      if buf.is_null() {
        return None;
      }
      let shape_buf = buf.offset(size_of::<memblock_dev>() as _) as *const i64;
      Some(from_raw_parts(shape_buf, ndim as usize))
    }
  }

  pub fn set_shape(&self, new_shape: &[i64]) {
    let ndim = self._ndim();
    assert!(ndim != 0);
    assert_eq!(ndim as usize, new_shape.len());
    unsafe {
      let buf = self.as_ptr() as *mut u8;
      assert!(!buf.is_null());
      let shape_buf = buf.offset(size_of::<memblock_dev>() as _) as *mut i64;
      // FIXME FIXME: check that we can do copy_nonoverlapping.
      copy_nonoverlapping(new_shape.as_ptr(), shape_buf, ndim as usize);
    }
  }
}
