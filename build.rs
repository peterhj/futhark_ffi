use std::env;
use std::fs::{OpenOptions};
use std::io::{Write, BufWriter};
use std::path::{PathBuf};

fn main() {
  println!("cargo:rerun-if-changed=build.rs");
  println!("cargo:rerun-if-env-changed=TARGET");
  let target = env::var("TARGET").unwrap();
  let out_dir = PathBuf::from(env::var("OUT_DIR").unwrap());
  let mut output_path = out_dir;
  output_path.push("build_env.rs");
  let output_file = OpenOptions::new()
    .write(true).create(true).truncate(true)
    .open(output_path).unwrap();
  let mut output_file = BufWriter::new(output_file);
  write!(&mut output_file, "/* automatically generated by build script */\n").unwrap();
  write!(&mut output_file, "pub const TARGET: &'static str = \"").unwrap();
  for c in target.escape_default() {
    write!(&mut output_file, "{}", c).unwrap();
  }
  write!(&mut output_file, "\";\n").unwrap();
}
