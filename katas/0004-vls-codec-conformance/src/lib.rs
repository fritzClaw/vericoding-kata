//! Kata 0004 — vls conforms to lib-security-property.
//! Intent: intents/0004-vls-codec-conformance.md
//!
//! Proves that vls's escape table is a valid `security_property::Codec` and
//! that vls's output *is* the library's unparser, so the library's
//! guarantees apply to `vls` and `vls DIR | vwc -l`.
//! Ghost items of other crates are referenced by full path (they are erased
//! in normal builds, so they are not imported).
//!
//! Everything OUTSIDE the `<vc-helpers>` / `<vc-code>` regions is the frozen,
//! human-approved specification (hashed in specs.lock.json).
#![forbid(unsafe_code)]

use security_property::Codec;
use vstd::prelude::*;

verus! {

/// vls's own table (kata 0002), delimiter LF, header marker `:`.
pub struct VlsCodec;

impl Codec for VlsCodec {
    open spec fn code(b: u8) -> Seq<u8> {
        ls::escape_byte(b)
    }

    open spec fn delim() -> u8 {
        10
    }

    open spec fn marker() -> u8 {
        58
    }

    fn delim_exec() -> (r: u8) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn marker_exec() -> (r: u8) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn push_code(out: &mut Vec<u8>, b: u8) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    /// D1
    proof fn lemma_codec_ok() {
        // <vc-code>
        assume(false);
        // </vc-code>
    }
}

/// D1: vls's table is exactly the library's ready-made `BackslashEscape`.
pub proof fn theorem_vls_table_is_backslash(b: u8)
    ensures
        ls::escape_byte(b) == <security_property::BackslashEscape as Codec>::code(b),
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

/// D2: same encoding.
pub proof fn theorem_same_encoding(s: Seq<u8>)
    ensures
        ls::escape(s) == security_property::encode::<VlsCodec>(s),
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

/// Kata 0003's AST as the library's AST (same shape).
pub open spec fn to_lib(x: Seq<count_files::GroupS>) -> Seq<security_property::GroupS> {
    Seq::new(x.len(), |i: int| security_property::GroupS { header: x[i].header, names: x[i].names })
}

/// D3: the same documents are well formed.
pub proof fn theorem_same_wf(x: Seq<count_files::GroupS>)
    ensures
        count_files::wf(x) == security_property::wf_document(to_lib(x)),
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

/// D3: kata 0003's unparser is the library's, for vls's codec.
pub proof fn theorem_same_document(x: Seq<count_files::GroupS>)
    ensures
        count_files::unparse(x) == security_property::unparse_document::<VlsCodec>(to_lib(x)),
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

/// D3: vls's stdout bytes are the library's unparse of vls's AST.
pub proof fn theorem_vls_output_is_library_unparse(req: ls::RequestS)
    ensures
        count_files::lines_bytes(ls::ls(req).stdout) == security_property::unparse_document::<VlsCodec>(
            to_lib(count_files::ast_of(req)),
        ),
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

/// D4: vwc's count is the library's delimiter count.
pub proof fn theorem_same_count(s: Seq<u8>)
    ensures
        count_files::count_newlines(s) == security_property::count_byte(s, 10),
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

// <vc-helpers>
// </vc-helpers>

// ===========================================================================
// Spec tests. Checked by Verus; they never run.
// ===========================================================================

/// E2 / D5: vls's pre-fix table (`:` as itself) violates C4.
proof fn spec_e2_prefix_table_rejected() {
    let pre = |b: u8| if b == 58 { seq![58u8] } else { ls::escape_byte(b) };
    assert(!security_property::codec_conditions(pre, 10, 58)) by {
        assert(pre(58u8)[0] == 58u8);
    }
}

/// E3: `a:b` encodes as `a\:b` in both views.
proof fn spec_e3_encode() {
    assert(ls::escape(seq![97u8, 58, 98]) == seq![97u8, 92, 58, 98]) by (compute_only);
    assert(security_property::encode::<VlsCodec>(seq![97u8, 58, 98]) =~= seq![97u8, 92, 58, 98]) by (compute);
}

} // verus!

// Runtime tests (cargo test): the library's verified exec code on real vls output.
#[cfg(test)]
mod tests {
    use super::*;

    #[test]
    fn library_decodes_and_counts_real_vls_output() {
        let operands = vec![
            ls::Operand { name: b"d".to_vec(), outcome: ls::Outcome::Dir(vec![b"b:".to_vec(), b"a\nb".to_vec()]) },
            ls::Operand { name: b"x:".to_vec(), outcome: ls::Outcome::File },
        ];
        let res = ls::run(&ls::Request { all: false, reverse: false, operands });
        let bytes: Vec<u8> = res.stdout.iter().flat_map(|l| l.iter().copied().chain([b'\n'])).collect();
        let doc = security_property::decode_document::<VlsCodec>(&bytes).expect("vls output decodes");
        assert_eq!(doc.len(), 2);
        assert_eq!(doc[0].names, vec![b"x:".to_vec()]);
        assert_eq!(doc[1].header, Some(b"d".to_vec()));
        assert_eq!(doc[1].names, vec![b"a\nb".to_vec(), b"b:".to_vec()]);
        assert_eq!(security_property::unparse_document_exec::<VlsCodec>(&doc), bytes);
        assert_eq!(security_property::count_delims::<VlsCodec>(0, &bytes), Some(5));
    }
}
