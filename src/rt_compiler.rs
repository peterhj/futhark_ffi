use cc::{Build, Object};

use std::io::{BufRead, Write, BufReader, stdout};
use std::path::{PathBuf};
use std::process::{Command, Stdio};
use std::thread::{spawn};

pub struct IspcCompile {
}

impl IspcCompile {
  pub fn try_compile(/*cc_build: &Build,*/ silent: bool, sources: &[PathBuf]) -> Result<Vec<Object>, ()> {
    //let dst_dir = cc_build.get_out_dir().unwrap();
    let mut objects = Vec::new();
    for src in sources.iter() {
      let mut dst = src.clone();
      match dst.extension() {
        None => panic!("bug"),
        Some(s) => {
          assert_eq!(s, "ispc");
        }
      }
      dst.set_extension("o");
      let mut cmd = Command::new("ispc");
      // FIXME: env vars.
      cmd.arg("-g");
      cmd.arg("--pic");
      cmd.arg("--addressing=32");
      cmd.arg("-O3");
      cmd.arg("--emit-obj");
      cmd.arg("-o");
      cmd.arg(&dst);
      cmd.arg(src);
      let mut child = cmd.stderr(Stdio::piped()).spawn().map_err(|_| ())?;
      let stderr = BufReader::new(child.stderr.take().unwrap());
      let handle = spawn(move || {
        for line in stderr.split(b'\n').filter_map(|line| line.ok()) {
          if !silent {
            print!("cargo:warning=");
            stdout().write_all(&line).unwrap();
            println!();
          } else {
            drop(line);
          }
        }
      });
      let status = child.wait().map_err(|_| ())?;
      handle.join().unwrap();
      if !status.success() {
        return Err(());
      }
      objects.push(Object{src: src.clone(), dst});
    }
    Ok(objects)
  }
}

pub struct CcLink {
}

impl CcLink {
  pub fn emit_dylib(cc_build: &Build, silent: bool, objects: &[Object], output: &str) -> Result<(), ()> {
    //let silent = cc_build.get_silent();
    let dst_dir = cc_build.get_out_dir().unwrap();
    let target = cc_build.get_target().unwrap();
    let tool = cc_build.try_get_compiler().unwrap();
    let (lib_name, gnu_lib_name) = if output.starts_with("lib") && output.ends_with(".so") {
      (&output[3..output.len() - 3], output.to_owned())
    } else {
      let mut gnu = String::with_capacity(6 + output.len());
      gnu.push_str("lib");
      gnu.push_str(&output);
      gnu.push_str(".so");
      (output, gnu)
    };
    let dst = dst_dir.join(gnu_lib_name);
    let mut cmd = tool.to_command();
    // FIXME: env vars.
    if target.contains("linux")
    || target.contains("freebsd")
    || target.contains("netbsd")
    || target.contains("openbsd") {
      cmd.arg("-shared");
      cmd.arg(&format!("-Wl,-soname,lib{}.so.0", lib_name));
      cmd.arg("-o");
      cmd.arg(dst);
      for obj in objects.iter() {
        cmd.arg(&obj.dst);
      }
      let mut child = cmd.stderr(Stdio::piped()).spawn().map_err(|_| ())?;
      let stderr = BufReader::new(child.stderr.take().unwrap());
      let handle = spawn(move || {
        for line in stderr.split(b'\n').filter_map(|line| line.ok()) {
          if !silent {
            print!("cargo:warning=");
            stdout().write_all(&line).unwrap();
            println!();
          } else {
            drop(line);
          }
        }
      });
      let status = child.wait().map_err(|_| ())?;
      handle.join().unwrap();
      if !status.success() {
        return Err(());
      }
    } else {
      unimplemented!();
    }
    Ok(())
  }
}
