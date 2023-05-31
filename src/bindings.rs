use crate::types::*;

use libc::{c_int, c_void};
use libloading::nonsafe::{Library, Symbol};

use std::ffi::{OsStr};
use std::mem::{align_of};

#[allow(non_snake_case)]
#[derive(Default)]
pub struct ObjectFFI {
  pub _inner:       Option<Library>,
  pub ctx_cfg_new:  Option<Symbol<extern "C" fn () -> *mut futhark_context_config>>,
  pub ctx_cfg_free: Option<Symbol<extern "C" fn (*mut futhark_context_config)>>,
  // TODO TODO
  pub ctx_cfg_set_gpu_alloc:                Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_gpu_free:                 Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_gpu_back_alloc:           Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_gpu_back_free:            Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  // TODO TODO
  pub ctx_cfg_set_cuGetErrorString:         Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuInit:                   Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuDeviceGetCount:         Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuDeviceGetName:          Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuDeviceGet:              Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuDeviceGetAttribute:     Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuDevicePrimaryCtxRetain: Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
  pub ctx_cfg_set_cuDevicePrimaryCtxRelease: Option<Symbol<extern "C" fn (*mut futhark_context_config, *mut c_void)>>,
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
  pub ctx_new:              Option<Symbol<extern "C" fn (*mut futhark_context_config) -> *mut futhark_context>>,
  pub ctx_free:             Option<Symbol<extern "C" fn (*mut futhark_context)>>,
  pub ctx_reset:            Option<Symbol<extern "C" fn (*mut futhark_context)>>,
  pub ctx_set_max_block_size:       Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_max_grid_size:        Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_max_tile_size:        Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_max_threshold:        Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_max_shared_memory:    Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_max_bespoke:          Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_lockstep_width:       Option<Symbol<extern "C" fn (*mut futhark_context, usize)>>,
  pub ctx_set_device:       Option<Symbol<extern "C" fn (*mut futhark_context, c_int) -> c_int>>,
  pub ctx_set_stream:       Option<Symbol<extern "C" fn (*mut futhark_context, *mut c_void) -> *mut c_void>>,
  pub ctx_may_fail:         Option<Symbol<extern "C" fn (*mut futhark_context) -> c_int>>,
  pub ctx_sync:             Option<Symbol<extern "C" fn (*mut futhark_context) -> c_int>>,
  // TODO
  // FIXME FIXME: how to handle polymorphic entry point signature?
  //pub entry:  Option<Symbol<extern "C" fn () -> ()>>,
  pub entry_0_1_dev:        Option<Symbol<extern "C" fn (*mut futhark_context, *mut *mut memblock_dev) -> c_int>>,
  pub entry_1_1_dev:        Option<Symbol<extern "C" fn (*mut futhark_context, *mut *mut memblock_dev, *mut memblock_dev) -> c_int>>,
  pub entry_2_1_dev:        Option<Symbol<extern "C" fn (*mut futhark_context, *mut *mut memblock_dev, *mut memblock_dev, *mut memblock_dev) -> c_int>>,
  pub entry_3_1_dev:        Option<Symbol<extern "C" fn (*mut futhark_context, *mut *mut memblock_dev, *mut memblock_dev, *mut memblock_dev, *mut memblock_dev) -> c_int>>,
  pub entry_4_1_dev:        Option<Symbol<extern "C" fn (*mut futhark_context, *mut *mut memblock_dev, *mut memblock_dev, *mut memblock_dev, *mut memblock_dev, *mut memblock_dev) -> c_int>>,
  pub entry: Option<(u16, u16, bool)>,
}

impl Drop for ObjectFFI {
  fn drop(&mut self) {
    let inner = self._inner.take();
    if let Some(inner) = inner {
      *self = Default::default();
      drop(inner);
    }
  }
}

impl ObjectFFI {
  pub unsafe fn open<P: AsRef<OsStr>>(dylib_path: P) -> Result<ObjectFFI, ()> {
    let mut ffi = ObjectFFI::default();
    ffi._inner = Some(match Library::new(dylib_path) {
      Err(_) => return Err(()),
      Ok(dylib) => dylib
    });
    ffi.load_symbols();
    Ok(ffi)
  }

  pub unsafe fn load_symbols(&mut self) {
    // FIXME FIXME: why put these checks here? why not!
    assert_eq!(align_of::<memblock_dev>(), align_of::<array_1d_dev>());
    assert_eq!(align_of::<memblock_dev>(), align_of::<array_2d_dev>());
    assert_eq!(align_of::<memblock_dev>(), align_of::<array_3d_dev>());
    assert_eq!(align_of::<memblock_dev>(), align_of::<array_4d_dev>());
    let inner = self._inner.as_ref().unwrap();
    self.ctx_cfg_new = inner.get(b"futhark_context_config_new").ok();
    self.ctx_cfg_free = inner.get(b"futhark_context_config_free").ok();
    // TODO TODO
    self.ctx_cfg_set_gpu_alloc = inner.get(b"futhark_context_config_set_gpu_alloc").ok();
    self.ctx_cfg_set_gpu_free = inner.get(b"futhark_context_config_set_gpu_free").ok();
    self.ctx_cfg_set_gpu_back_alloc = inner.get(b"futhark_context_config_set_gpu_back_alloc").ok();
    self.ctx_cfg_set_gpu_back_free = inner.get(b"futhark_context_config_set_gpu_back_free").ok();
    // TODO TODO
    self.ctx_cfg_set_cuGetErrorString = inner.get(b"futhark_context_config_set_cuGetErrorString").ok();
    self.ctx_cfg_set_cuInit = inner.get(b"futhark_context_config_set_cuInit").ok();
    self.ctx_cfg_set_cuDeviceGetCount = inner.get(b"futhark_context_config_set_cuDeviceGetCount").ok();
    self.ctx_cfg_set_cuDeviceGetName = inner.get(b"futhark_context_config_set_cuDeviceGetName").ok();
    self.ctx_cfg_set_cuDeviceGet = inner.get(b"futhark_context_config_set_cuDeviceGet").ok();
    self.ctx_cfg_set_cuDeviceGetAttribute = inner.get(b"futhark_context_config_set_cuDeviceGetAttribute").ok();
    self.ctx_cfg_set_cuDevicePrimaryCtxRetain = inner.get(b"futhark_context_config_set_cuDevicePrimaryCtxRetain").ok();
    self.ctx_cfg_set_cuDevicePrimaryCtxRelease = inner.get(b"futhark_context_config_set_cuDevicePrimaryCtxRelease").ok();
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
    self.ctx_reset = inner.get(b"futhark_context_reset").ok();
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
  }

  pub unsafe fn load_entry_symbol(&mut self, arityin: u16, arityout: u16, dev: bool) {
    match self.entry {
      None => {}
      Some(e) => {
        assert_eq!(e, (arityin, arityout, dev));
        return;
      }
    }
    let inner = self._inner.as_ref().unwrap();
    match (arityin, arityout, dev) {
      (0, 1, true) => {
        self.entry_0_1_dev = inner.get(b"futhark_entry_kernel").ok();
      }
      (1, 1, true) => {
        self.entry_1_1_dev = inner.get(b"futhark_entry_kernel").ok();
      }
      (2, 1, true) => {
        self.entry_2_1_dev = inner.get(b"futhark_entry_kernel").ok();
      }
      (3, 1, true) => {
        self.entry_3_1_dev = inner.get(b"futhark_entry_kernel").ok();
      }
      (4, 1, true) => {
        self.entry_4_1_dev = inner.get(b"futhark_entry_kernel").ok();
      }
      _ => unimplemented!()
    }
    self.entry = Some((arityin, arityout, dev));
  }
}
