//! Kata 0003 — counting files with `vls DIR | vwc -l`, and vls as a correct
//! unparser (parse(unparse(x)) = x, Hermerschmidt et al., IEEE SPW 2015).
//! Intent: intents/0003-count-files.md
//!
//! Everything OUTSIDE the `<vc-helpers>` / `<vc-code>` regions is the frozen,
//! human-approved specification (hashed in specs.lock.json). Theorems are
//! frozen statements; their proofs are `<vc-code>` regions.
#![forbid(unsafe_code)]

use ls::{
    OperandS, OutcomeS, RequestS, dir_ops, entries_of, escape, escape_all, file_ops, headers_on,
    join_groups, lines_view, listed_names, ls, op_names, sort_ops, sort_unique,
};
use vstd::prelude::*;

verus! {

// ===========================================================================
// vwc -l (D3, D5, D12)
// ===========================================================================

/// D3: the number of newline bytes (0x0A).
#[verifier::memoize]
pub open spec fn count_newlines(s: Seq<u8>) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == 10 {
            1nat
        } else {
            0nat
        }) + count_newlines(s.subrange(1, s.len() as int))
    }
}

// ===========================================================================
// The document language vls writes (D7, D8)
// ===========================================================================

/// One group of the document: an optional `NAME:` header and the names.
pub struct GroupS {
    pub header: Option<Seq<u8>>,
    pub names: Seq<Seq<u8>>,
}

pub open spec fn has_header(g: GroupS) -> bool {
    match g.header {
        Some(_) => true,
        None => false,
    }
}

/// D8: the ASTs vls can build.
pub open spec fn wf(doc: Seq<GroupS>) -> bool {
    // all names are non-empty
    &&& forall|i: int, j: int|
        0 <= i < doc.len() && 0 <= j < doc[i].names.len() ==> (#[trigger] doc[i].names[j]).len() > 0
    // only the first group may lack a header
    &&& forall|i: int| 0 < i < doc.len() ==> has_header(#[trigger] doc[i])
    // a headerless group is never empty
    &&& (doc.len() > 0 && !has_header(doc[0])) ==> doc[0].names.len() > 0
}

/// The bytes of a list of lines: each line followed by LF. This is exactly
/// what vls's shell writes for `Response.stdout` (kata 0002, trusted there).
#[verifier::memoize]
pub open spec fn lines_bytes(lines: Seq<Seq<u8>>) -> Seq<u8>
    decreases lines.len(),
{
    if lines.len() == 0 {
        seq![]
    } else {
        lines[0] + seq![10u8] + lines_bytes(lines.subrange(1, lines.len() as int))
    }
}

/// A group's lines: `escape(header):` (if any), then the escaped names.
pub open spec fn group_lines(g: GroupS) -> Seq<Seq<u8>> {
    (match g.header {
        Some(h) => seq![escape(h) + seq![58u8]],
        None => seq![],
    }) + escape_all(g.names)
}

#[verifier::memoize]
pub open spec fn groups_lines(doc: Seq<GroupS>) -> Seq<Seq<Seq<u8>>>
    decreases doc.len(),
{
    if doc.len() == 0 {
        seq![]
    } else {
        seq![group_lines(doc[0])] + groups_lines(doc.subrange(1, doc.len() as int))
    }
}

/// The unparser: groups separated by one empty line (kata 0002's `join_groups`).
pub open spec fn unparse(doc: Seq<GroupS>) -> Seq<u8> {
    lines_bytes(join_groups(groups_lines(doc)))
}

// ---- the AST vls builds for a request (D9) ---------------------------------

pub open spec fn dir_group_ast(op: OperandS, req: RequestS) -> GroupS {
    GroupS {
        header: if headers_on(req) {
            Some(op.name)
        } else {
            None
        },
        names: sort_unique(listed_names(entries_of(op.outcome), req.all), req.reverse),
    }
}

#[verifier::memoize]
pub open spec fn dir_groups_ast(dirs: Seq<OperandS>, req: RequestS) -> Seq<GroupS>
    decreases dirs.len(),
{
    if dirs.len() == 0 {
        seq![]
    } else {
        seq![dir_group_ast(dirs[0], req)] + dir_groups_ast(dirs.subrange(1, dirs.len() as int), req)
    }
}

pub open spec fn ast_of(req: RequestS) -> Seq<GroupS> {
    let files = file_ops(req.operands);
    let all = (if files.len() > 0 {
        seq![GroupS { header: None, names: op_names(sort_ops(files, req.reverse)) }]
    } else {
        seq![]
    }) + dir_groups_ast(sort_ops(dir_ops(req.operands), req.reverse), req);
    // A headerless empty group prints nothing (`vls EMPTYDIR`): it is not in the AST.
    if all.len() == 1 && !has_header(all[0]) && all[0].names.len() == 0 {
        seq![]
    } else {
        all
    }
}

// ===========================================================================
// Executable interface
// ===========================================================================

pub struct Group {
    pub header: Option<Vec<u8>>,
    pub names: Vec<Vec<u8>>,
}

impl View for Group {
    type V = GroupS;

    open spec fn view(&self) -> GroupS {
        GroupS {
            header: match &self.header {
                Some(h) => Some(h@),
                None => None,
            },
            names: lines_view(self.names@),
        }
    }
}

pub open spec fn doc_view(d: Seq<Group>) -> Seq<GroupS> {
    Seq::new(d.len(), |i: int| d[i]@)
}

// <vc-helpers>
// </vc-helpers>

/// D5: add the newlines of `chunk` to `acc`; `None` on u64 overflow.
pub fn count_chunk(acc: u64, chunk: &Vec<u8>) -> (r: Option<u64>)
    ensures
        r == (if acc + count_newlines(chunk@) <= u64::MAX {
            Some((acc + count_newlines(chunk@)) as u64)
        } else {
            None::<u64>
        }),
{
    // <vc-code>
    assume(false);
    unreached()
    // </vc-code>
}

/// D10: strict decoder. `Some(d)` iff `input` is the unparse of a well-formed
/// AST, and then `d` is that (unique) AST: round trip + strictness (P1, P2).
pub fn decode(input: &Vec<u8>) -> (r: Option<Vec<Group>>)
    ensures
        match r {
            Some(d) => {
                &&& wf(doc_view(d@))
                &&& unparse(doc_view(d@)) == input@
                &&& forall|x: Seq<GroupS>| wf(x) && #[trigger] unparse(x) == input@ ==> x == doc_view(d@)
            },
            None => forall|x: Seq<GroupS>| wf(x) ==> #[trigger] unparse(x) != input@,
        },
{
    // <vc-code>
    assume(false);
    unreached()
    // </vc-code>
}

// ===========================================================================
// Theorems (statements frozen; proofs are vericode)
// ===========================================================================

/// P1 (paper): the unparser is injective on well-formed ASTs, so
/// parse(unparse(x)) = x is well defined: data can't forge structure.
pub proof fn theorem_unparse_injective(x: Seq<GroupS>, y: Seq<GroupS>)
    requires
        wf(x),
        wf(y),
        unparse(x) == unparse(y),
    ensures
        x == y,
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

/// P3 (D9): vls's stdout bytes are exactly the unparse of its AST.
pub proof fn theorem_vls_unparses(req: RequestS)
    ensures
        lines_bytes(ls(req).stdout) == unparse(ast_of(req)),
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

/// P4 (D9): vls only builds well-formed ASTs (file operands have non-empty
/// names; the OS never yields an empty path).
pub proof fn theorem_vls_ast_wf(req: RequestS)
    requires
        forall|i: int|
            0 <= i < req.operands.len() && ls::is_file((#[trigger] req.operands[i]).outcome) ==> req.operands[i].name.len()
                > 0,
    ensures
        wf(ast_of(req)),
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

/// P5 (D11): `vls DIR | vwc -l` counts exactly the listed names.
pub proof fn theorem_count_files(req: RequestS)
    requires
        req.operands.len() == 1,
        ls::is_dir(req.operands[0].outcome),
    ensures
        count_newlines(lines_bytes(ls(req).stdout)) == sort_unique(
            listed_names(entries_of(req.operands[0].outcome), req.all),
            req.reverse,
        ).len(),
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

/// P5 (D12): counting chunk by chunk gives the count of the whole input.
pub proof fn theorem_count_concat(a: Seq<u8>, b: Seq<u8>)
    ensures
        count_newlines(a + b) == count_newlines(a) + count_newlines(b),
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

// ===========================================================================
// Spec tests: the intent's examples, checked by compute. They never run.
// ===========================================================================

spec fn n_a() -> Seq<u8> { seq![97u8] }               // a
spec fn n_b() -> Seq<u8> { seq![98u8] }               // b
spec fn n_c() -> Seq<u8> { seq![99u8] }               // c
spec fn n_dot_h() -> Seq<u8> { seq![46u8, 104] }      // .h
spec fn n_bang_x() -> Seq<u8> { seq![33u8, 120] }     // !x
spec fn n_d1() -> Seq<u8> { seq![100u8, 49] }         // d1
spec fn n_f1() -> Seq<u8> { seq![102u8, 49] }         // f1
spec fn n_x_colon() -> Seq<u8> { seq![120u8, 58] }    // x:
spec fn n_b_colon() -> Seq<u8> { seq![98u8, 58] }     // b:
spec fn n_a_lf_b() -> Seq<u8> { seq![97u8, 10, 98] }  // a<LF>b

spec fn d1_dir() -> OutcomeS { OutcomeS::Dir(seq![n_b(), n_a(), n_dot_h(), n_bang_x()]) }
spec fn op(name: Seq<u8>, outcome: OutcomeS) -> OperandS { OperandS { name, outcome } }
spec fn req(all: bool, reverse: bool, operands: Seq<OperandS>) -> RequestS { RequestS { all, reverse, operands } }
spec fn vls_count(r: RequestS) -> nat { count_newlines(lines_bytes(ls(r).stdout)) }

spec fn e1_r() -> RequestS { req(false, false, seq![op(n_d1(), d1_dir())]) }
spec fn e2_r() -> RequestS { req(false, false, seq![op(n_d1(), OutcomeS::Dir(seq![n_a_lf_b(), n_c()]))]) }
spec fn e3_r() -> RequestS { req(true, false, seq![op(n_d1(), d1_dir())]) }
spec fn e4_r() -> RequestS { req(false, false, seq![op(n_d1(), OutcomeS::Dir(seq![]))]) }
spec fn e5_r() -> RequestS { req(false, false, seq![op(n_d1(), OutcomeS::Missing(n_a()))]) }

proof fn spec_e1_to_e5_counts() {
    assert(vls_count(e1_r()) == 3) by (compute_only);  // reject 4 (counting .h)
    assert(vls_count(e2_r()) == 2) by (compute_only);  // reject 3 (ls | wc -l)
    assert(vls_count(e3_r()) == 6) by (compute_only);  // with . and ..
    assert(vls_count(e4_r()) == 0) by (compute_only);
    assert(vls_count(e5_r()) == 0) by (compute_only);  // pass-through (D6)
}

spec fn e6_doc() -> Seq<GroupS> {
    seq![
        GroupS { header: None, names: seq![n_a()] },
        GroupS { header: Some(n_x_colon()), names: seq![n_b_colon()] },
    ]
}

/// The injection the `:` escape prevents: header `x`, then a name `:`.
spec fn e6_forged() -> Seq<GroupS> {
    seq![
        GroupS { header: None, names: seq![n_a()] },
        GroupS { header: Some(seq![120u8]), names: seq![seq![58u8]] },
    ]
}

proof fn spec_e6_unparse() {
    // a | | x\:: | b\:
    assert(unparse(e6_doc()) == seq![97u8, 10, 10, 120, 92, 58, 58, 10, 98, 92, 58, 10]) by (compute_only);
    assert(unparse(e6_forged()) != unparse(e6_doc())) by (compute_only);
    assert(wf(e6_doc())) by {
        assert(e6_doc()[1].names[0] == n_b_colon());
    }
}

proof fn spec_e8_count() {
    assert(count_newlines(seq![97u8, 10, 98]) == 1) by (compute_only);  // a<LF>b; reject 2
}

// D9 sanity: the bridge theorem's statement holds on the examples.
spec fn multi_r() -> RequestS {
    req(false, true, seq![op(n_d1(), d1_dir()), op(n_f1(), OutcomeS::File), op(n_x_colon(), OutcomeS::File)])
}

proof fn spec_d9_bridge_instances() {
    assert(lines_bytes(ls(e1_r()).stdout) == unparse(ast_of(e1_r()))) by (compute_only);
    assert(lines_bytes(ls(e4_r()).stdout) == unparse(ast_of(e4_r()))) by (compute_only);
    assert(lines_bytes(ls(multi_r()).stdout) == unparse(ast_of(multi_r()))) by (compute_only);
    assert(ast_of(e4_r()) == Seq::<GroupS>::empty()) by (compute_only);
}

} // verus!

// Runtime tests (cargo test) for the executable parts.
#[cfg(test)]
mod tests {
    use super::*;

    fn count(bytes: &[u8]) -> Option<u64> {
        count_chunk(0, &bytes.to_vec())
    }

    #[test]
    fn e8_count_chunk() {
        assert_eq!(count(b"a\nb"), Some(1));
        assert_eq!(count(b""), Some(0));
        assert_eq!(count_chunk(u64::MAX, &b"x".to_vec()), Some(u64::MAX));
        assert_eq!(count_chunk(u64::MAX, &b"\n".to_vec()), None);  // D5 overflow
    }

    fn g(header: Option<&[u8]>, names: &[&[u8]]) -> (Option<Vec<u8>>, Vec<Vec<u8>>) {
        (header.map(|h| h.to_vec()), names.iter().map(|n| n.to_vec()).collect())
    }

    fn dec(bytes: &[u8]) -> Option<Vec<(Option<Vec<u8>>, Vec<Vec<u8>>)>> {
        decode(&bytes.to_vec()).map(|d| d.into_iter().map(|g| (g.header, g.names)).collect())
    }

    #[test]
    fn e6_round_trip() {
        assert_eq!(dec(b"a\n\nx\\::\nb\\:\n"), Some(vec![g(None, &[b"a"]), g(Some(b"x:"), &[b"b:"])]));
        assert_eq!(dec(b""), Some(vec![]));
        assert_eq!(dec(b"d:\n"), Some(vec![g(Some(b"d"), &[])]));
        assert_eq!(dec(b"a\\nb\ncaf\\xc3\\xa9\n"), Some(vec![g(None, &[b"a\nb", "caf\u{e9}".as_bytes()])]));
    }

    #[test]
    fn e7_strict() {
        for bad in [&b"a"[..], b"\\q\n", b"\\x41\n", b"\n", b"\\xC3\n", b"a\n\nb\n", b"a:b\n", b"\x01\n"] {
            assert_eq!(dec(bad), None, "accepted {:?}", String::from_utf8_lossy(bad));
        }
    }

    #[test]
    fn decodes_real_vls_output() {
        let operands = vec![
            ls::Operand { name: b"d".to_vec(), outcome: ls::Outcome::Dir(vec![b"b:".to_vec(), b"a\nb".to_vec()]) },
            ls::Operand { name: b"x:".to_vec(), outcome: ls::Outcome::File },
        ];
        let res = ls::run(&ls::Request { all: false, reverse: false, operands });
        let bytes: Vec<u8> = res.stdout.iter().flat_map(|l| l.iter().copied().chain([b'\n'])).collect();
        assert_eq!(dec(&bytes), Some(vec![g(None, &[b"x:"]), g(Some(b"d"), &[b"a\nb", b"b:"])]));
    }
}
