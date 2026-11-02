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
    // </vc-shell>
}
