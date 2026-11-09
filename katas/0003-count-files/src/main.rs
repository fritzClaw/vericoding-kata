//! `vwc` — the TRUSTED shell around the verified counting core in lib.rs.
//! Intent: intents/0003-count-files.md (D4, D5, D13).
//!
//! This file is NOT verified by Verus. Its only job: accept exactly `-l`,
//! read stdin in chunks, fold them with `count_files::count_chunk`, print the
//! count in decimal followed by "\n", and map overflow / read errors /
//! bad arguments to a message on stderr and exit 2. The skeleton is locked;
//! the region is written in the vericode stage and reviewed by a human.

#[allow(unused_imports)]
use vstd::prelude::*;  // required by Verus for every crate root

fn main() {
    // <vc-shell>
    use std::io::{Read, Write};

    // D4: exactly `vwc -l`.
    let args: Vec<std::ffi::OsString> = std::env::args_os().skip(1).collect();
    if args.len() != 1 || args[0] != "-l" {
        eprintln!("usage: vwc -l");
        std::process::exit(2);
    }

    // D5, D12: fold stdin chunk by chunk with the verified core.
    let mut stdin = std::io::stdin().lock();
    let mut buf = vec![0u8; 64 * 1024];
    let mut count: u64 = 0;
    loop {
        let n = match stdin.read(&mut buf) {
            Ok(0) => break,
            Ok(n) => n,
            Err(e) if e.kind() == std::io::ErrorKind::Interrupted => continue,
            Err(e) => {
                eprintln!("vwc: read error: {e}");
                std::process::exit(2);
            }
        };
        match count_files::count_chunk(count, &buf[..n].to_vec()) {
            Some(c) => count = c,
            None => {
                eprintln!("vwc: count overflows u64");
                std::process::exit(2);
            }
        }
    }

    // D13: decimal + LF, no padding.
    let mut out = std::io::stdout().lock();
    if writeln!(out, "{count}").and_then(|_| out.flush()).is_err() {
        std::process::exit(2);
    }
    // </vc-shell>
}
