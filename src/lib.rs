extern crate cc;
extern crate libc;
extern crate libloading;
extern crate rustc_serialize;
extern crate ryu;

use self::blake2s::{Blake2s};
use self::bindings::*;
use self::types::*;

use libc::{malloc, free, c_void};
//use potato::{Blake2s};
use rustc_serialize::{Decodable};
use rustc_serialize::hex::{ToHex};
use rustc_serialize::json::{Decoder as JsonDecoder, Json};
use ryu::{Buffer as RyuBuffer};

use std::cell::{Cell, RefCell, UnsafeCell};
use std::cmp::{max};
use std::collections::{BTreeMap};
use std::ffi::{CStr, CString, OsStr};
use std::fmt::{Debug, Formatter, Result as FmtResult, Write as FmtWrite};
use std::fs::{File, OpenOptions, create_dir_all};
use std::hash::{Hash, Hasher};
use std::io::{Read, Write, BufReader, BufWriter, Seek, SeekFrom};
use std::mem::{size_of, swap};
use std::os::unix::fs::{MetadataExt};
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};
use std::ptr::{copy_nonoverlapping, null_mut, write};
use std::slice::{from_raw_parts};
use std::str::{from_utf8};

pub mod bindings;
pub mod blake2s;
pub mod build_env;
pub mod types;

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

/*#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum AbiOutput {
  Unspec = 0,
  Pure = 1,
  ImplicitInPlace = 2,
  //ExplicitInPlace,
  Unique = 3,
}

impl Default for AbiOutput {
  fn default() -> AbiOutput {
    AbiOutput::Unspec
  }
}

impl AbiOutput {
  pub fn from_bits(x: u8) -> AbiOutput {
    match x {
      0 => AbiOutput::Unspec,
      1 => AbiOutput::Pure,
      2 => AbiOutput::ImplicitInPlace,
      //3 => AbiOutput::ExplicitInPlace,
      3 => AbiOutput::Unique,
      _ => panic!("bug")
    }
  }

  pub fn to_bits(self) -> u8 {
    self as u8
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum AbiInput {
  Unspec = 0,
  Shared = 1,
  Consumed = 3,
}

impl Default for AbiInput {
  fn default() -> AbiInput {
    AbiInput::Unspec
  }
}

impl AbiInput {
  pub fn from_bits(x: u8) -> AbiInput {
    match x {
      0 => AbiInput::Unspec,
      1 => AbiInput::Shared,
      3 => AbiInput::Consumed,
      _ => panic!("bug")
    }
  }

  pub fn to_bits(self) -> u8 {
    self as u8
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum AbiParam {
  Unspec = 0,
  //ImplicitOutShape,
  //Explicit,
  // TODO
}

impl Default for AbiParam {
  fn default() -> AbiParam {
    AbiParam::Unspec
  }
}

impl AbiParam {
  pub fn from_bits(x: u8) -> AbiParam {
    match x {
      0 => AbiParam::Unspec,
      _ => panic!("bug")
    }
  }

  pub fn to_bits(self) -> u8 {
    self as u8
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum AbiArrayRepr {
  Unspec = 0,
  //Unit,
  //Flat,
  Nd,
}

impl Default for AbiArrayRepr {
  fn default() -> AbiArrayRepr {
    AbiArrayRepr::Unspec
  }
}

impl AbiArrayRepr {
  pub fn from_bits(x: u8) -> AbiArrayRepr {
    match x {
      0 => AbiArrayRepr::Unspec,
      //1 => AbiArrayRepr::Unit,
      //2 => AbiArrayRepr::Flat,
      1 => AbiArrayRepr::Nd,
      _ => panic!("bug")
    }
  }

  pub fn to_bits(self) -> u8 {
    self as u8
  }
}*/

#[derive(Clone, Debug)]
//#[derive(Clone, Copy, Debug)]
pub enum AbiScalar {
  Unspec,
  F64(Cell<f64>),
  F32(Cell<f32>),
  I64(Cell<i64>),
  I32(Cell<i32>),
  I16(Cell<i16>),
  I8(Cell<i8>),
  U64(Cell<u64>),
  U32(Cell<u32>),
  U16(Cell<u16>),
  U8(Cell<u8>),
  F16(Cell<u16>),
  //Bf16(Cell<u16>),
}

impl AbiScalar {
  pub fn _get_ptr(&self) -> *mut c_void {
    match self {
      &AbiScalar::Unspec        => panic!("bug"),
      &AbiScalar::F64(ref x)    => x.as_ptr() as *mut c_void,
      &AbiScalar::F32(ref x)    => x.as_ptr() as *mut c_void,
      &AbiScalar::I64(ref x)    => x.as_ptr() as *mut c_void,
      &AbiScalar::I32(ref x)    => x.as_ptr() as *mut c_void,
      &AbiScalar::I16(ref x)    => x.as_ptr() as *mut c_void,
      &AbiScalar::I8(ref x)     => x.as_ptr() as *mut c_void,
      &AbiScalar::U64(ref x)    => x.as_ptr() as *mut c_void,
      &AbiScalar::U32(ref x)    => x.as_ptr() as *mut c_void,
      &AbiScalar::U16(ref x)    => x.as_ptr() as *mut c_void,
      &AbiScalar::U8(ref x)     => x.as_ptr() as *mut c_void,
      &AbiScalar::F16(ref x)    => x.as_ptr() as *mut c_void,
      //&AbiScalar::Bf16(ref x)   => x.as_ptr() as *mut c_void,
    }
  }

  pub fn into_f32(&self) -> f32 {
    match self {
      &AbiScalar::F32(ref x) => x.get(),
      _ => panic!("bug: AbiScalar::into_f32: actual={:?}", self.type_())
    }
  }

  pub fn into_i64(&self) -> i64 {
    match self {
      &AbiScalar::I64(ref x) => x.get(),
      _ => panic!("bug: AbiScalar::into_i64: actual={:?}", self.type_())
    }
  }

  pub fn type_(&self) -> AbiScalarType {
    match self {
      &AbiScalar::Unspec    => AbiScalarType::Unspec,
      &AbiScalar::F64(..)   => AbiScalarType::F64,
      &AbiScalar::F32(..)   => AbiScalarType::F32,
      &AbiScalar::I64(..)   => AbiScalarType::I64,
      &AbiScalar::I32(..)   => AbiScalarType::I32,
      &AbiScalar::I16(..)   => AbiScalarType::I16,
      &AbiScalar::I8(..)    => AbiScalarType::I8,
      &AbiScalar::U64(..)   => AbiScalarType::U64,
      &AbiScalar::U32(..)   => AbiScalarType::U32,
      &AbiScalar::U16(..)   => AbiScalarType::U16,
      &AbiScalar::U8(..)    => AbiScalarType::U8,
      &AbiScalar::F16(..)   => AbiScalarType::F16,
      //&AbiScalar::Bf16(..)  => AbiScalarType::Bf16,
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Debug)]
#[repr(u8)]
pub enum AbiScalarType {
  Unspec = 0,
  F64,
  F32,
  I64,
  I32,
  I16,
  I8,
  U64,
  U32,
  U16,
  U8,
  F16,
  //Bf16,
}

impl Default for AbiScalarType {
  fn default() -> AbiScalarType {
    AbiScalarType::Unspec
  }
}

impl AbiScalarType {
  pub fn from_bits(x: u8) -> AbiScalarType {
    match x {
      0   => AbiScalarType::Unspec,
      1   => AbiScalarType::F64,
      2   => AbiScalarType::F32,
      3   => AbiScalarType::I64,
      4   => AbiScalarType::I32,
      5   => AbiScalarType::I16,
      6   => AbiScalarType::I8,
      7   => AbiScalarType::U64,
      8   => AbiScalarType::U32,
      9   => AbiScalarType::U16,
      10  => AbiScalarType::U8,
      11  => AbiScalarType::F16,
      //12  => AbiScalarType::Bf16,
      _   => panic!("bug")
    }
  }

  pub fn to_bits(self) -> u8 {
    self as u8
  }

  pub fn format_futhark(self) -> &'static str {
    match self {
      AbiScalarType::Unspec => panic!("bug"),
      AbiScalarType::F64   => "f64",
      AbiScalarType::F32   => "f32",
      AbiScalarType::I64   => "i64",
      AbiScalarType::I32   => "i32",
      AbiScalarType::I16   => "i16",
      AbiScalarType::I8    => "i8",
      AbiScalarType::U64   => "u64",
      AbiScalarType::U32   => "u32",
      AbiScalarType::U16   => "u16",
      AbiScalarType::U8    => "u8",
      AbiScalarType::F16   => "f16",
    }
  }
}

#[derive(Clone, Copy, PartialEq, Eq, Hash, Debug)]
#[repr(u8)]
pub enum AbiSpace {
  Unspec = 0,
  Default,
  Device,
}

impl Default for AbiSpace {
  fn default() -> AbiSpace {
    AbiSpace::Unspec
  }
}

/*#[derive(Clone, PartialEq, Eq, Default, Debug)]
pub struct Abi {
  pub arityout: u16,
  pub arityin:  u16,
  pub param_ct: Cell<u16>,
  //pub output:   AbiOutput,
  pub space:    AbiSpace,
  // FIXME
  /*pub out_repr: [AbiArrayRepr; 1],
  pub arg_repr: [AbiArrayRepr; 5],
  pub param_ty: [AbiScalarType; 1],*/
  pub bits_buf: RefCell<Vec<u8>>,
}

impl Hash for Abi {
  fn hash<H: Hasher>(&self, state: &mut H) {
    self.arityout.hash(state);
    self.arityin.hash(state);
    self.param_ct.get().hash(state);
    self.space.hash(state);
    self.bits_buf.borrow().hash(state);
  }
}

impl Abi {
  pub fn num_param(&self) -> usize {
    /*let mut np = 0;
    for i in 0 .. self.param_ty.len() {
      if self.param_ty[i] == AbiScalarType::Unspec {
        break;
      }
      np += 1;
    }
    np*/
    self.param_ct.get() as usize
  }

  pub fn get_out_arr(&self, idx: u16) -> (AbiOutput, AbiArrayRepr, AbiScalarType) {
    assert!(idx < self.arityout);
    let val = self.bits_buf.borrow()[idx as usize];
    let out = AbiOutput::from_bits(val >> 6);
    let rep = AbiArrayRepr::from_bits((val >> 4) & 3);
    let dty = AbiScalarType::from_bits(val & 15);
    (out, rep, dty)
  }

  pub fn set_out_arr(&self, idx: u16, out: AbiOutput, rep: AbiArrayRepr, dty: AbiScalarType) {
    assert!(idx < self.arityout);
    let val = (out.to_bits() << 6) | (rep.to_bits() << 4) | dty.to_bits();
    if idx as usize == self.bits_buf.borrow().len() {
      self.bits_buf.borrow_mut().push(val);
    } else {
      self.bits_buf.borrow_mut()[idx as usize] = val;
    }
  }

  pub fn push_out_arr(&self, idx: u16, out: AbiOutput, rep: AbiArrayRepr, dty: AbiScalarType) {
    self.set_out_arr(idx, out, rep, dty)
  }

  /*pub fn push_out_arr(&self, idx: u16, out: AbiOutput, rep: AbiArrayRepr, dty: AbiScalarType) {
    let val = (out.to_bits() << 6) | (rep.to_bits() << 4) | dty.to_bits();
    assert_eq!(self.bits_buf.borrow().len(), idx as usize);
    self.bits_buf.borrow_mut().push(val);
  }*/

  pub fn get_arg_arr(&self, idx: u16) -> (AbiInput, AbiArrayRepr, AbiScalarType) {
    assert!(idx < self.arityin);
    let val = self.bits_buf.borrow_mut()[(self.arityout + idx) as usize];
    let in_ = AbiInput::from_bits(val >> 6);
    let rep = AbiArrayRepr::from_bits((val >> 4) & 3);
    let dty = AbiScalarType::from_bits(val & 15);
    (in_, rep, dty)
  }

  pub fn set_arg_arr(&self, idx: u16, in_: AbiInput, rep: AbiArrayRepr, dty: AbiScalarType) {
    assert!(idx < self.arityin);
    let val = (in_.to_bits() << 6) | (rep.to_bits() << 4) | dty.to_bits();
    if (self.arityout + idx) as usize == self.bits_buf.borrow().len() {
      self.bits_buf.borrow_mut().push(val);
    } else {
      self.bits_buf.borrow_mut()[(self.arityout + idx) as usize] = val;
    }
  }

  pub fn push_arg_arr(&self, idx: u16, in_: AbiInput, rep: AbiArrayRepr, dty: AbiScalarType) {
    self.set_arg_arr(idx, in_, rep, dty)
  }

  /*pub fn push_arg_arr(&self, idx: u16, rep: AbiArrayRepr, dty: AbiScalarType) {
    let val = (rep.to_bits() << 4) | dty.to_bits();
    assert_eq!(self.bits_buf.borrow().len(), self.arityout as usize + idx as usize);
    self.bits_buf.borrow_mut().push(val);
  }*/

  pub fn get_param(&self, idx: u16) -> AbiScalarType {
    assert!(idx < self.param_ct.get());
    let val = self.bits_buf.borrow_mut()[(self.arityout + self.arityin + idx) as usize];
    let dty = AbiScalarType::from_bits(val);
    dty
  }

  pub fn set_param(&self, idx: u16, dty: AbiScalarType) {
    assert!(idx < self.param_ct.get());
    let val = dty.to_bits();
    self.bits_buf.borrow_mut()[(self.arityout + self.arityin + idx) as usize] = val;
  }

  pub fn push_param(&self, idx: u16, dty: AbiScalarType) {
    assert_eq!(idx, self.param_ct.get());
    self.param_ct.set(idx + 1);
    let val = dty.to_bits();
    assert_eq!(self.bits_buf.borrow().len(), (self.arityout + self.arityin + idx) as usize);
    self.bits_buf.borrow_mut().push(val);
  }

  pub fn push_implicit_out_shape_param(&self, out_idx: u16, ndim: i8) {
    // FIXME
    unimplemented!();
  }
}*/

#[derive(Clone, PartialEq, Eq, Hash, Default, Debug)]
pub struct EntryAbi {
  pub arityout: u16,
  pub arityin:  u16,
  pub param_ct: u16,
  pub space:    AbiSpace,
  pub data:     Vec<u8>,
}

impl EntryAbi {
  pub fn get_param(&self, idx: u16) -> AbiScalarType {
    assert!(idx < self.param_ct);
    let u = self.data[idx as usize];
    AbiScalarType::from_bits(u)
  }

  pub fn set_param(&mut self, idx: u16, sty: AbiScalarType) {
    assert!(idx < self.param_ct);
    if self.data.len() <= idx as usize {
      self.data.resize(idx as usize + 1, 0);
    }
    let u = sty.to_bits();
    self.data[idx as usize] = u;
  }
}

#[derive(Clone, Default, Debug)]
pub struct Config {
  // TODO
  pub cachedir: PathBuf,
  pub futhark:  PathBuf,
  pub include:  PathBuf,
  pub target:   Option<String>,
  pub verbose:  bool,
  pub debug:    bool,
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
  type FFI: ObjectFFI;

  fn cmd_arg() -> &'static str;
}

pub enum MulticoreBackend {}

impl Backend for MulticoreBackend {
  type FFI = MulticoreObjectFFI;

  fn cmd_arg() -> &'static str {
    "multicore"
  }
}

pub enum CudaBackend {}

impl Backend for CudaBackend {
  type FFI = CudaObjectFFI;

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
  pub src_hash: String,
  pub fut_path: PathBuf,
  pub debug:    bool,
  pub manifest: ObjectManifest,
  //pub eabi: Option<Abi>,
  pub eabi: Option<EntryAbi>,
  pub cfg:  *mut futhark_context_config,
  pub ctx:  *mut futhark_context,
  pub ffi:  <B as Backend>::FFI,
}

impl<B: Backend> Drop for Object<B> {
  fn drop(&mut self) {
    if !self.ctx.is_null() {
      (self.ffi.base().ctx_free.as_ref().unwrap())(self.ctx);
    }
    if !self.cfg.is_null() {
      let cbuf = (self.ffi.base().ctx_cfg_set_cache_file.as_ref().unwrap())(self.cfg, null_mut());
      if !cbuf.is_null() {
        unsafe {
          let _cpath = CString::from_raw(cbuf);
        }
      }
      (self.ffi.base().ctx_cfg_free.as_ref().unwrap())(self.cfg);
    }
  }
}

impl<B: Backend> Object<B> {
  pub fn open<P: AsRef<OsStr>>(src_hash: String, fut_path: PathBuf, manifest: ObjectManifest, dylib_path: P) -> Result<Object<B>, ()> {
    let ffi = unsafe { <<B as Backend>::FFI as ObjectFFI>::open(dylib_path).map_err(|_| ())? };
    Ok(Object{
      src_hash,
      fut_path,
      debug: false,
      manifest,
      eabi: None,
      cfg:  null_mut(),
      ctx:  null_mut(),
      ffi,
    })
  }

  pub fn kcache_path(&self) -> Option<PathBuf> {
    let mut kcache_path = self.fut_path.clone();
    kcache_path.set_extension("kcache");
    Some(kcache_path)
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
  pub fn build<B: Backend>(&self, stage: Stage, name: Option<&str>, source: &[String]) -> Result<Option<Object<B>>, BuildError> {
    let mut srchash = Blake2s::new_hash();
    for s in source.iter() {
      srchash.hash_bytes(s.as_bytes());
      srchash.hash_bytes(b"\n");
    }
    let src_h = srchash.finalize();
    let src_hx = src_h.to_hex();
    let stem = format!("futhark_obj_{}_{}", B::cmd_arg(), src_hx);
    create_dir_all(&self.cachedir).ok();
    let mut f_path = self.cachedir.clone();
    f_path.push(&stem);
    f_path.set_extension("fut");
    let f_path_str = f_path.to_str().unwrap();
    for &c in f_path_str.as_bytes() {
      // FIXME: sanitize path.
      if c == b'\"' {
        panic!("bug");
      }
    }
    let mut name_path = f_path.clone();
    let mut c_path = f_path.clone();
    let mut h_path = f_path.clone();
    let mut json_path = f_path.clone();
    let mut dylib_path = f_path.clone();
    //let mut hash_path = f_path.clone();
    let mut stage_path = f_path.clone();
    name_path.set_extension("name");
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
              for s in source.iter() {
                f.write_all(s.as_bytes()).unwrap();
                f.write_all(b"\n").unwrap();
              }
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
          if let Some(name) = name {
            match OpenOptions::new().read(false).write(true).create(true).truncate(true).open(&name_path) {
              Err(_) => return Err(BuildError::Cache),
              Ok(mut f) => {
                f.write_all(name.as_bytes()).unwrap();
              }
            }
          }
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
            .stdout(Stdio::piped())
            .stderr(Stdio::piped())
            .output()
          {
            Err(_) => return Err(BuildError::FutharkCommand),
            Ok(output) => {
              if !output.status.success() {
                let code = output.status.code();
                println!("DEBUG: futhark_ffi::Config::build: build failed with error code: {:?}", code);
                //println!("{:?}", output);
                println!("DEBUG: futhark_ffi::Config::build: ----- stderr below -----");
                println!("{}", from_utf8(&output.stderr).unwrap());
                println!("DEBUG: futhark_ffi::Config::build: ----- stderr above -----");
                return Err(BuildError::Futhark(code));
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
            .debug(true)
            .opt_level(2)
            .pic(true)
            .define("FUTHARK_SOURCE_FILE", &format!("\"{}\"", f_path_str) as &str)
            .include(&self.cachedir)
            .include(&self.include)
            .file(&c_path)
            .object_prefix_hash(false)
            .archive(false)
            .dylib(true)
            .silent(!self.verbose)
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
          if self.debug { println!("DEBUG: futhark_ffi::Config::build: new build done!"); }
        } else {
          if self.debug { println!("DEBUG: futhark_ffi::Config::build: load cached..."); }
        }
      }
      if stage == Stage::Dylib {
        let manifest = stage_mem.manifest.unwrap();
        return Object::open(src_hx, f_path, manifest, &dylib_path)
              .map_err(|_| BuildError::Dylib)
              .map(|mut obj| {
                obj.debug = self.debug;
                Some(obj)
              });
      }
      unreachable!();
    }
  }
}

impl<B: Backend> Object<B> {
  pub fn new_config(&mut self) {
    self.cfg = (self.ffi.base().ctx_cfg_new.as_ref().unwrap())();
  }

  pub fn set_cache_file<Q: Into<Option<P>>, P: AsRef<Path>>(&mut self, cache_path: Q) {
    match cache_path.into() {
      None => {
        (self.ffi.base().ctx_cfg_set_cache_file.as_ref().unwrap())(self.cfg, null_mut());
      }
      Some(cache_path) => {
        let mut buf = cache_path.as_ref().to_str().unwrap().as_bytes().to_owned();
        buf.push(b'\0');
        //println!("DEBUG: Object::set_cache_file: path buf={:?}", &buf);
        let cpath = CString::from_vec_with_nul(buf).unwrap();
        (self.ffi.base().ctx_cfg_set_cache_file.as_ref().unwrap())(self.cfg, cpath.into_raw());
      }
    }
  }

  pub fn new_context(&mut self) {
    self.ctx = (self.ffi.base().ctx_new.as_ref().unwrap())(self.cfg);
  }

  pub fn may_fail(&self) -> bool {
    let ret = (self.ffi.base().ctx_may_fail.as_ref().unwrap())(self.ctx);
    ret != 0
  }

  pub fn sync(&self) -> Result<(), i32> {
    let ret = (self.ffi.base().ctx_sync.as_ref().unwrap())(self.ctx);
    if ret != FUTHARK_SUCCESS {
      return Err(ret);
    }
    Ok(())
  }

  pub fn error(&self) -> Option<&CStr> {
    let err = (self.ffi.base().ctx_error.as_ref().unwrap())(self.ctx);
    if err.is_null() {
      return None;
    }
    unsafe {
      Some(CStr::from_ptr(err))
    }
  }

  pub fn reset(&self, ) {
    (self.ffi.base().ctx_reset.as_ref().unwrap())(self.ctx);
  }

  pub fn release(&self, ) {
    (self.ffi.base().ctx_release.as_ref().unwrap())(self.ctx);
  }
}

impl Object<MulticoreBackend> {
  pub fn set_num_threads(&self, n: i32) {
    (self.ffi.ctx_cfg_set_num_threads.as_ref().unwrap())(self.cfg, n);
  }
}

impl Object<CudaBackend> {
  pub fn set_setup_device(&self, dev: i32) {
    (self.ffi.ctx_cfg_set_setup_device.as_ref().unwrap())(self.cfg, dev);
  }

  pub fn set_setup_stream(&self, raw_stream: *mut c_void) {
    (self.ffi.ctx_cfg_set_setup_stream.as_ref().unwrap())(self.cfg, raw_stream);
  }

  pub fn set_stream(&self, raw_stream: *mut c_void) {
    (self.ffi.ctx_set_stream.as_ref().unwrap())(self.ctx, raw_stream);
  }
}

pub trait ObjectExt {
  type Array;

  fn enter_kernel(&mut self, /*arityin: u16, arityout: u16,*/ /*abi: &Abi,*/ eabi: EntryAbi, param: &[AbiScalar], arg_arr: &[UnsafeCell<Self::Array>], out_arr: &[UnsafeCell<Self::Array>]) -> Result<(), i32>;
}

impl ObjectExt for Object<MulticoreBackend> {
  type Array = Array;

  fn enter_kernel(&mut self, eabi: EntryAbi, param: &[AbiScalar], arg_arr: &[UnsafeCell<Array>], out_arr: &[UnsafeCell<Array>]) -> Result<(), i32> {
    let np = param.len();
    let mut param_ty = Vec::with_capacity(np);
    for p in param.iter() {
      param_ty.push(p.type_());
    }
    if self.debug {
    println!("DEBUG: Object::<MulticoreBackend>::enter_kernel: manifest.out.len={}",
        self.manifest.entry_points.kernel.outputs.len());
    println!("DEBUG: Object::<MulticoreBackend>::enter_kernel: manifest.in.len={}",
        self.manifest.entry_points.kernel.inputs.len());
    println!("DEBUG: Object::<MulticoreBackend>::enter_kernel: out={} in={} param_ty={:?} param={:?}",
        eabi.arityout, eabi.arityin, &param_ty, param);
    }
    assert_eq!(out_arr.len(), eabi.arityout as usize);
    assert_eq!(arg_arr.len(), eabi.arityin as usize);
    assert_eq!(np, param_ty.len());
    assert_eq!(np, eabi.param_ct as usize);
    if self.manifest.entry_points.kernel.outputs.len() != eabi.arityout as usize {
      println!("ERROR: Object::<MulticoreBackend>::enter_kernel: eabi mismatch v. manifest (outputs)");
      println!("ERROR: Object::<MulticoreBackend>::enter_kernel:   manifest outputs len={}",
          self.manifest.entry_points.kernel.outputs.len());
      println!("ERROR: Object::<MulticoreBackend>::enter_kernel:   eabi arity out={}",
          eabi.arityout);
      panic!();
    }
    if self.manifest.entry_points.kernel.inputs.len() != (eabi.arityin + eabi.param_ct) as usize {
      println!("ERROR: Object::<MulticoreBackend>::enter_kernel: eabi mismatch v. manifest (inputs)");
      println!("ERROR: Object::<MulticoreBackend>::enter_kernel:   manifest inputs len={}",
          self.manifest.entry_points.kernel.inputs.len());
      println!("ERROR: Object::<MulticoreBackend>::enter_kernel:   eabi arity in={}",
          eabi.arityin);
      println!("ERROR: Object::<MulticoreBackend>::enter_kernel:   eabi param ct={}",
          eabi.param_ct);
      panic!();
    }
    // FIXME: we can also compare the eabi and manifest types.
    match self.eabi.as_ref() {
      None => {
        assert_eq!(eabi.space, AbiSpace::Default);
        self.eabi = Some(eabi);
      }
      Some(e_abi) => {
        assert_eq!(e_abi.space, AbiSpace::Default);
        assert_eq!(e_abi.space, eabi.space);
        assert_eq!(e_abi.param_ct, eabi.param_ct);
        assert_eq!(e_abi.arityin, eabi.arityin);
        assert_eq!(e_abi.arityout, eabi.arityout);
        // FIXME: compare eabi types.
        //assert_eq!(&e_abi.param_ty[..], &param_ty);
      }
    }
    let mut raw_out: Vec<*mut c_void> = Vec::with_capacity(self.manifest.entry_points.kernel.outputs.len());
    let mut raw_arg: Vec<*mut c_void> = Vec::with_capacity(self.manifest.entry_points.kernel.inputs.len());
    for k in 0 .. out_arr.len() {
      raw_out.push(out_arr[k as usize].get() as *mut c_void);
    }
    assert_eq!(raw_out.len(), self.manifest.entry_points.kernel.outputs.len());
    for k in 0 .. arg_arr.len() {
      raw_arg.push(arg_arr[k as usize].get() as *mut c_void);
    }
    for k in 0 .. param.len() {
      raw_arg.push(param[k]._get_ptr());
    }
    assert_eq!(raw_arg.len(), self.manifest.entry_points.kernel.inputs.len());
    let ret = (self.ffi.base().call_kernel.as_ref().unwrap())(self.ctx, raw_out.as_mut_ptr(), raw_arg.as_mut_ptr());
    if ret != FUTHARK_SUCCESS {
      return Err(ret);
    }
    Ok(())
  }
}

impl ObjectExt for Object<CudaBackend> {
  type Array = ArrayDev;

  //fn enter_kernel(&mut self, abi: &Abi, param: &[AbiScalar], arg_arr: &[ArrayDev], out_arr: &mut [ArrayDev]) -> Result<(), i32> {}
  fn enter_kernel(&mut self, /*_abi: &Abi,*/ eabi: EntryAbi, param: &[AbiScalar], arg_arr: &[UnsafeCell<ArrayDev>], out_arr: &[UnsafeCell<ArrayDev>]) -> Result<(), i32> {
    /*assert_eq!(out_arr.len(), abi.arityout as usize);
    // FIXME
    if let (AbiOutput::ImplicitInPlace, _, _) = abi.get_out_arr(0) {
      assert_eq!(arg_arr.len(), (abi.arityin + 1) as usize);
    } else {
      assert_eq!(arg_arr.len(), abi.arityin as usize);
    }*/
    let np = param.len();
    let mut param_ty = Vec::with_capacity(np);
    for p in param.iter() {
      param_ty.push(p.type_());
    }
    /*assert_eq!(abi.num_param(), np);*/
    /*for _ in np .. 1 {
      param_ty.push(AbiScalarType::Unspec);
    }*/
    if self.debug {
    println!("DEBUG: Object::<CudaBackend>::enter_kernel: manifest.out.len={}",
        self.manifest.entry_points.kernel.outputs.len());
    println!("DEBUG: Object::<CudaBackend>::enter_kernel: manifest.in.len={}",
        self.manifest.entry_points.kernel.inputs.len());
    /*println!("DEBUG: Object::<CudaBackend>::enter_kernel: out={} in={} param_ty={:?} param={:?}",
        abi.arityout, abi.arityin, &param_ty, param);*/
    println!("DEBUG: Object::<CudaBackend>::enter_kernel: out={} in={} param_ty={:?} param={:?}",
        eabi.arityout, eabi.arityin, &param_ty, param);
    }
    assert_eq!(out_arr.len(), eabi.arityout as usize);
    assert_eq!(arg_arr.len(), eabi.arityin as usize);
    assert_eq!(np, param_ty.len());
    assert_eq!(np, eabi.param_ct as usize);
    /*if let (AbiOutput::ImplicitInPlace, _, _) = abi.get_out_arr(0) {
      if self.manifest.entry_points.kernel.inputs.len() != (abi.arityin + 1) as usize + abi.num_param() {
        panic!("ERROR: Object::<CudaBackend>::enter_kernel: abi mismatch v. manifest");
      }
    } else {
      if self.manifest.entry_points.kernel.inputs.len() != abi.arityin as usize + abi.num_param() {
        panic!("ERROR: Object::<CudaBackend>::enter_kernel: abi mismatch v. manifest");
      }
    }
    if param_ty.len() != abi.num_param() {
      panic!("ERROR: Object::<CudaBackend>::enter_kernel: abi mismatch v. param ty buf");
    }
    if param.len() != abi.num_param() {
      panic!("ERROR: Object::<CudaBackend>::enter_kernel: abi mismatch v. param buf");
    }*/
    if self.manifest.entry_points.kernel.outputs.len() != eabi.arityout as usize {
      println!("ERROR: Object::<CudaBackend>::enter_kernel: eabi mismatch v. manifest (outputs)");
      println!("ERROR: Object::<CudaBackend>::enter_kernel:   manifest outputs len={}",
          self.manifest.entry_points.kernel.outputs.len());
      println!("ERROR: Object::<CudaBackend>::enter_kernel:   eabi arity out={}",
          eabi.arityout);
      panic!();
    }
    if self.manifest.entry_points.kernel.inputs.len() != (eabi.arityin + eabi.param_ct) as usize {
      println!("ERROR: Object::<CudaBackend>::enter_kernel: eabi mismatch v. manifest (inputs)");
      println!("ERROR: Object::<CudaBackend>::enter_kernel:   manifest inputs len={}",
          self.manifest.entry_points.kernel.inputs.len());
      println!("ERROR: Object::<CudaBackend>::enter_kernel:   eabi arity in={}",
          eabi.arityin);
      println!("ERROR: Object::<CudaBackend>::enter_kernel:   eabi param ct={}",
          eabi.param_ct);
      panic!();
    }
    // FIXME: we can also compare the eabi and manifest types.
    match self.eabi.as_ref() {
      None => {
        //let ret = unsafe { self.ffi.load_entry_symbol(AbiSpace::Device, abi.arityin, abi.arityout, &param_ty[ .. np]) };
        //assert!(ret.is_some());
        /*let e_abi = Abi{
          arityout,
          arityin,
          // FIXME FIXME
          param_ct: Cell::new(param.len() as _),
          //output:   Default::default(),
          space:    AbiSpace::Device,
          /*out_repr: Default::default(),
          arg_repr: Default::default(),
          param_ty: [param_ty[0]],*/
          bits_buf: RefCell::new(Vec::new()),
        };*/
        /*let mut e_abi = abi.clone();
        e_abi.space = AbiSpace::Device;
        self.eabi = Some(e_abi);*/
        assert_eq!(eabi.space, AbiSpace::Device);
        self.eabi = Some(eabi);
      }
      Some(e_abi) => {
        /*assert_eq!(e_abi.space, AbiSpace::Device);
        assert_eq!(e_abi.num_param(), abi.num_param());
        assert_eq!(e_abi.arityin, abi.arityin);
        assert_eq!(e_abi.arityout, abi.arityout);*/
        assert_eq!(e_abi.space, AbiSpace::Device);
        assert_eq!(e_abi.space, eabi.space);
        assert_eq!(e_abi.param_ct, eabi.param_ct);
        assert_eq!(e_abi.arityin, eabi.arityin);
        assert_eq!(e_abi.arityout, eabi.arityout);
        // FIXME: compare eabi types.
        //assert_eq!(&e_abi.param_ty[..], &param_ty);
      }
    }
    let mut raw_out: Vec<*mut c_void> = Vec::with_capacity(self.manifest.entry_points.kernel.outputs.len());
    let mut raw_arg: Vec<*mut c_void> = Vec::with_capacity(self.manifest.entry_points.kernel.inputs.len());
    for k in 0 .. out_arr.len() {
      raw_out.push(out_arr[k as usize].get() as *mut c_void);
    }
    assert_eq!(raw_out.len(), self.manifest.entry_points.kernel.outputs.len());
    for k in 0 .. arg_arr.len() {
      raw_arg.push(arg_arr[k as usize].get() as *mut c_void);
    }
    for k in 0 .. param.len() {
      raw_arg.push(param[k]._get_ptr());
    }
    assert_eq!(raw_arg.len(), self.manifest.entry_points.kernel.inputs.len());
    let ret = (self.ffi.base().call_kernel.as_ref().unwrap())(self.ctx, raw_out.as_mut_ptr(), raw_arg.as_mut_ptr());
    if ret != FUTHARK_SUCCESS {
      return Err(ret);
    }
    Ok(())
  }
}

#[repr(transparent)]
pub struct Array {
  pub raw:  usize,
}

impl Debug for Array {
  fn fmt(&self, f: &mut Formatter) -> FmtResult {
    let ndim = self._ndim();
    let mem = self.as_ptr();
    if mem.is_null() {
      return write!(f, "Array({} | null)", ndim);
    }
    unsafe {
      let c = (&*mem).refcount as usize;
      let ptr = (&*mem).mem_ptr as usize;
      let size = (&*mem).mem_size as usize;
      let tag = (&*mem).tag as usize;
      write!(f, "Array({} | 0x{:016x} -> {{ refcount: 0x{:016x}",
          ndim, mem as usize, c)?;
      if c == 0 {
      } else {
        let cd = *(c as *const i32);
        write!(f, " -> {}", cd)?;
      }
      write!(f, ", mem_ptr: 0x{:016x}, mem_size: {}", ptr, size)?;
      if tag == 0 {
        write!(f, ", tag: null")?;
      } else {
        write!(f, ", tag: 0x{:016x}", tag)?;
      }
      if ndim == 0 {
        write!(f, " }})")?;
      } else {
        let buf = mem as *const u8;
        let shape_buf = buf.offset(size_of::<memblock>() as _) as *const i64;
        let shape = from_raw_parts(shape_buf, ndim as usize);
        write!(f, ", shape: {:?} }})", shape)?;
      }
    }
    Ok(())
  }
}

impl Clone for Array {
  fn clone(&self) -> Array {
    let o_mem = self.as_ptr();
    if o_mem.is_null() {
      return Array::null();
    }
    let ndim = self._ndim();
    assert!(ndim >= 1);
    assert!(ndim <= 4);
    self._inc_refcount();
    let mem_sz = size_of::<memblock>() + 8 * (ndim as usize);
    let ptr = unsafe {
      let mem = malloc(mem_sz) as *mut memblock;
      assert!(!mem.is_null());
      // FIXME FIXME: check that we can do copy_nonoverlapping.
      copy_nonoverlapping(o_mem as *const _ as *const u8, mem as *mut u8, mem_sz);
      mem
    };
    Array::from_raw(ptr, ndim)
  }
}

impl Drop for Array {
  fn drop(&mut self) {
    let ptr = self.as_ptr();
    if ptr.is_null() {
      return;
    }
    match self._dec_refcount() {
      Some(0) => {
        unsafe {
          // FIXME: sticky refcount.
          let refc_ptr = (&*ptr).refcount;
          assert!(!refc_ptr.is_null());
          free(refc_ptr as *mut _);
        }
      }
      None | Some(_) => {}
    }
    match self._ndim() {
      1 | 2 | 3 | 4 => unsafe { free(ptr as *mut _) },
      _ => unreachable!()
    }
  }
}

impl Array {
  pub fn from_raw(ptr: *mut memblock, ndim: i8) -> Array {
    assert!(!ptr.is_null());
    let raw_ptr = ptr as usize;
    assert_eq!(raw_ptr & 7, 0);
    let raw = match ndim {
      1 | 2 | 3 | 4 => raw_ptr | (ndim as usize),
      _ => unreachable!()
    };
    Array{raw}
  }

  pub fn null() -> Array {
    let ptr: *mut memblock = null_mut();
    let raw = ptr as usize;
    Array{raw}
  }

  pub fn new_1d() -> Array {
    assert_eq!(size_of::<array_1d>(), size_of::<memblock>() + 8);
    let ptr = unsafe { malloc(size_of::<array_1d>()) } as *mut _;
    let this = Array::from_raw(ptr, 1);
    unsafe { this._init(); }
    this
  }

  pub fn new_2d() -> Array {
    assert_eq!(size_of::<array_2d>(), size_of::<memblock>() + 8 * 2);
    let ptr = unsafe { malloc(size_of::<array_2d>()) } as *mut _;
    let this = Array::from_raw(ptr, 2);
    unsafe { this._init(); }
    this
  }

  pub fn new_3d() -> Array {
    assert_eq!(size_of::<array_3d>(), size_of::<memblock>() + 8 * 3);
    let ptr = unsafe { malloc(size_of::<array_3d>()) } as *mut _;
    let this = Array::from_raw(ptr, 3);
    unsafe { this._init(); }
    this
  }

  pub fn new_4d() -> Array {
    assert_eq!(size_of::<array_4d>(), size_of::<memblock>() + 8 * 4);
    let ptr = unsafe { malloc(size_of::<array_4d>()) } as *mut _;
    let this = Array::from_raw(ptr, 4);
    unsafe { this._init(); }
    this
  }

  pub unsafe fn _init(&self) {
    let mem = self.as_ptr();
    assert!(!mem.is_null());
    (&mut *mem).refcount = malloc(size_of::<i32>() * 2) as *mut i32;
    write((&mut *mem).refcount, 1);
    write((&mut *mem).refcount.offset(1), 0);
    (&mut *mem).mem_ptr = null_mut();
    (&mut *mem).mem_size = 0;
    (&mut *mem).tag = null_mut();
  }

  pub fn take_ptr(&mut self) -> *mut memblock {
    let mask = (self.raw & 7);
    self.raw &= (!7);
    let nil: *mut memblock = null_mut();
    let mut out = nil as usize;
    swap(&mut out, &mut self.raw);
    self.raw |= mask;
    let ptr = out as *mut _;
    ptr
  }

  pub fn as_ptr(&self) -> *mut memblock {
    (self.raw & (!7)) as *mut _
  }

  /*pub fn _as_mut_ptr(&mut self) -> *mut *mut memblock {
    &mut self.raw as *mut usize as *mut *mut memblock
  }*/

  pub fn _ndim(&self) -> i8 {
    (self.raw & 7) as i8
  }

  pub fn ndim(&self) -> Option<i8> {
    let nd = self._ndim();
    assert!(nd >= 0);
    assert!(nd <= 7);
    if nd == 0 {
      return None;
    }
    Some(nd)
  }

  pub fn _set_ndim(&mut self, nd: i8) {
    assert_eq!(0, self._ndim());
    assert!(nd > 0);
    assert!(nd <= 7);
    self.raw |= (nd as usize);
  }

  pub fn _unset_ndim(&mut self) -> i8 {
    let nd = self._ndim();
    assert!(nd > 0);
    assert!(nd <= 7);
    self.raw &= (!7);
    nd
  }

  pub fn refcount(&self) -> Option<i32> {
    let mem = self.as_ptr() as *const memblock;
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
    //println!("DEBUG: Array::_dec_refcount: memptr=0x{:016x}", mem as usize);
    unsafe {
      let c = (&*mem).refcount as *mut i32;
      if c.is_null() {
        return None;
      }
      //println!("DEBUG: Array::_dec_refcount:   refc=0x{:016x}", c as usize);
      //println!("DEBUG: Array::_dec_refcount:   ptr =0x{:016x}", (&*mem).mem_ptr as usize);
      //println!("DEBUG: Array::_dec_refcount:   size=0x{:016x}", (&*mem).mem_size);
      let prev_c = *c;
      assert!(prev_c >= 1);
      let new_c = prev_c - 1;
      write(c, new_c);
      Some(new_c)
    }
  }

  pub fn _inc_refcount(&self) -> i32 {
    let mem = self.as_ptr();
    assert!(!mem.is_null());
    unsafe {
      let c = (&*mem).refcount as *mut i32;
      assert!(!c.is_null());
      let prev_c = *c;
      assert!(prev_c >= 1);
      let new_c = prev_c + 1;
      write(c, new_c);
      new_c
    }
  }

  pub fn sticky(&self) -> Option<i32> {
    let mem = self.as_ptr() as *const memblock;
    if mem.is_null() {
      return None;
    }
    unsafe {
      let c = (&*mem).refcount as *const i32;
      if c.is_null() {
        return None;
      }
      Some(*(c.offset(1)))
    }
  }

  pub fn _set_sticky(&self, sticky: i32) {
    let mem = self.as_ptr() as *const memblock;
    assert!(!mem.is_null());
    unsafe {
      let c = (&*mem).refcount as *mut i32;
      assert!(!c.is_null());
      let prev_sticky = *(c.offset(1));
      let new_sticky = max(prev_sticky, sticky);
      write(c.offset(1), new_sticky);
    }
  }

  pub fn mem_parts(&self) -> Option<(*mut c_void, usize)> {
    let mem = self.as_ptr() as *const memblock;
    if mem.is_null() {
      return None;
    }
    unsafe {
      let mem = &*mem;
      Some((mem.mem_ptr, mem.mem_size))
    }
  }

  pub fn set_mem_parts(&self, ptr: *mut c_void, size: usize) {
    let mem = self.as_ptr();
    assert!(!mem.is_null());
    unsafe {
      (&mut *mem).mem_ptr = ptr;
      (&mut *mem).mem_size = size;
    }
  }

  pub fn tag(&self) -> Option<&CStr> {
    let mem = self.as_ptr();
    assert!(!mem.is_null());
    unsafe {
      let raw_tag = (&*mem).tag;
      if raw_tag.is_null() {
        None
      } else {
        Some(CStr::from_ptr(raw_tag))
      }
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
      let shape_buf = buf.offset(size_of::<memblock>() as _) as *const i64;
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
      let shape_buf = buf.offset(size_of::<memblock>() as _) as *mut i64;
      // FIXME FIXME: check that we can do copy_nonoverlapping.
      copy_nonoverlapping(new_shape.as_ptr(), shape_buf, ndim as usize);
    }
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

impl Clone for ArrayDev {
  fn clone(&self) -> ArrayDev {
    let o_mem = self.as_ptr();
    if o_mem.is_null() {
      return ArrayDev::null();
    }
    let ndim = self._ndim();
    assert!(ndim >= 1);
    assert!(ndim <= 4);
    self._inc_refcount();
    let mem_sz = size_of::<memblock_dev>() + 8 * (ndim as usize);
    let ptr = unsafe {
      let mem = malloc(mem_sz) as *mut memblock_dev;
      assert!(!mem.is_null());
      // FIXME FIXME: check that we can do copy_nonoverlapping.
      copy_nonoverlapping(o_mem as *const _ as *const u8, mem as *mut u8, mem_sz);
      mem
    };
    ArrayDev::from_raw(ptr, ndim)
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
        unsafe {
          // FIXME: sticky refcount.
          let refc_ptr = (&*ptr).refcount;
          assert!(!refc_ptr.is_null());
          free(refc_ptr as *mut _);
        }
      }
      None | Some(_) => {}
    }
    match self._ndim() {
      1 | 2 | 3 | 4 => unsafe { free(ptr as *mut _) },
      _ => unreachable!()
    }
  }
}

impl ArrayDev {
  pub fn from_raw(ptr: *mut memblock_dev, ndim: i8) -> ArrayDev {
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
    (&mut *mem).refcount = malloc(size_of::<i32>() * 2) as *mut i32;
    write((&mut *mem).refcount, 1);
    write((&mut *mem).refcount.offset(1), 0);
    (&mut *mem).mem_dptr = 0;
    (&mut *mem).mem_size = 0;
    (&mut *mem).tag = null_mut();
  }

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

  /*pub fn _as_mut_ptr(&mut self) -> *mut *mut memblock_dev {
    &mut self.raw as *mut usize as *mut *mut memblock_dev
  }*/

  pub fn _ndim(&self) -> i8 {
    (self.raw & 7) as i8
  }

  pub fn ndim(&self) -> Option<i8> {
    let nd = self._ndim();
    assert!(nd >= 0);
    assert!(nd <= 7);
    if nd == 0 {
      return None;
    }
    Some(nd)
  }

  pub fn _set_ndim(&mut self, nd: i8) {
    assert_eq!(0, self._ndim());
    assert!(nd > 0);
    assert!(nd <= 7);
    self.raw |= (nd as usize);
  }

  pub fn _unset_ndim(&mut self) -> i8 {
    let nd = self._ndim();
    assert!(nd > 0);
    assert!(nd <= 7);
    self.raw &= (!7);
    nd
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

  pub fn _inc_refcount(&self) -> i32 {
    let mem = self.as_ptr();
    assert!(!mem.is_null());
    unsafe {
      let c = (&*mem).refcount as *mut i32;
      assert!(!c.is_null());
      let prev_c = *c;
      assert!(prev_c >= 1);
      let new_c = prev_c + 1;
      write(c, new_c);
      new_c
    }
  }

  pub fn sticky(&self) -> Option<i32> {
    let mem = self.as_ptr() as *const memblock_dev;
    if mem.is_null() {
      return None;
    }
    unsafe {
      let c = (&*mem).refcount as *const i32;
      if c.is_null() {
        return None;
      }
      Some(*(c.offset(1)))
    }
  }

  pub fn _set_sticky(&self, sticky: i32) {
    let mem = self.as_ptr() as *const memblock_dev;
    assert!(!mem.is_null());
    unsafe {
      let c = (&*mem).refcount as *mut i32;
      assert!(!c.is_null());
      let prev_sticky = *(c.offset(1));
      let new_sticky = max(prev_sticky, sticky);
      write(c.offset(1), new_sticky);
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

  pub fn tag(&self) -> Option<&CStr> {
    let mem = self.as_ptr();
    assert!(!mem.is_null());
    unsafe {
      let raw_tag = (&*mem).tag;
      if raw_tag.is_null() {
        None
      } else {
        Some(CStr::from_ptr(raw_tag))
      }
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
