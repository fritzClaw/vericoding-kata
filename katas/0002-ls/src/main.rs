//! `vls` — the TRUSTED shell around the verified core in lib.rs.
//! Intent: intents/0002-ls.md (D3, D8, D9, D19).
//!
//! This file is NOT verified by Verus. Its only job: parse argv, ask the OS
//! for facts (metadata, read_dir), build an `ls::Request`, call `ls::run`,
//! write `Response.stdout`/`stderr` lines (each followed by "\n") and exit
//! with `Response.exit`. No sorting, filtering, escaping or formatting here.
//! The skeleton is locked; the region is written in the vericode stage and
//! reviewed by a human.

#[allow(unused_imports)]
use vstd::prelude::*;  // required by Verus for every crate root

fn main() {
    // <vc-shell>
    use std::ffi::OsStr;
    use std::io::Write;
    use std::os::unix::ffi::{OsStrExt, OsStringExt};

    // OS error text without Rust's " (os error N)" suffix, as raw bytes.
    fn os_message(e: &std::io::Error) -> Vec<u8> {
        let mut text = e.to_string();
        if let Some(code) = e.raw_os_error() {
            let suffix = format!(" (os error {code})");
            if text.ends_with(&suffix) {
                text.truncate(text.len() - suffix.len());
            }
        }
        text.into_bytes()
    }

    // D19: clustered short flags anywhere, `--` ends flags, lone `-` is an operand.
    let mut all = false;
    let mut reverse = false;
    let mut names: Vec<Vec<u8>> = Vec::new();
    let mut flags_done = false;
    for arg in std::env::args_os().skip(1) {
        let arg = arg.into_vec();
        if !flags_done && arg == b"--" {
            flags_done = true;
        } else if !flags_done && arg.len() > 1 && arg[0] == b'-' {
            for &c in &arg[1..] {
                match c {
                    b'a' => all = true,
                    b'r' => reverse = true,
                    _ => {
                        eprintln!("vls: invalid option -- '{}'", (c as char).escape_default());
                        eprintln!("usage: vls [-a] [-r] [PATH...]");
                        std::process::exit(2);
                    }
                }
            }
        } else {
            names.push(arg);
        }
    }
    // D8: no operand means `.`.
    if names.is_empty() {
        names.push(b".".to_vec());
    }

    // D9: classify each operand; directories are read, entries never stat'd.
    let mut operands = Vec::new();
    for name in names {
        let path = std::path::Path::new(OsStr::from_bytes(&name));
        let outcome = match std::fs::metadata(path) {
            Err(e) => ls::Outcome::Missing(os_message(&e)),
            Ok(meta) if meta.is_dir() => match std::fs::read_dir(path) {
                Err(e) => ls::Outcome::Unreadable(os_message(&e)),
                Ok(entries) => {
                    let collected: Result<Vec<Vec<u8>>, std::io::Error> =
                        entries.map(|entry| entry.map(|e| e.file_name().into_vec())).collect();
                    match collected {
                        Ok(names) => ls::Outcome::Dir(names),
                        Err(e) => ls::Outcome::Unreadable(os_message(&e)),
                    }
                }
            },
            Ok(_) => ls::Outcome::File,
        };
        operands.push(ls::Operand { name, outcome });
    }

    // The verified core decides every byte of output and the exit status.
    let res = ls::run(&ls::Request { all, reverse, operands });

    fn write_lines(w: &mut impl Write, lines: &[Vec<u8>]) -> std::io::Result<()> {
        for line in lines {
            w.write_all(line)?;
            w.write_all(b"\n")?;
        }
        w.flush()
    }
    let stderr_ok = write_lines(&mut std::io::stderr().lock(), &res.stderr).is_ok();
    let stdout_ok = write_lines(&mut std::io::BufWriter::new(std::io::stdout().lock()), &res.stdout).is_ok();
    let exit = if stdout_ok && stderr_ok { res.exit as i32 } else { 2 };
    std::process::exit(exit);
    // </vc-shell>
}
