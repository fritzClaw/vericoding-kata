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
    // </vc-shell>
}
