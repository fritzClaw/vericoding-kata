//! Kata 0003 — counting files with `vls DIR | vwc -l`, and vls as a correct
//! unparser (parse(unparse(x)) = x, Hermerschmidt et al., IEEE SPW 2015).
//! Intent: intents/0003-count-files.md
//!
//! Everything OUTSIDE the `<vc-helpers>` / `<vc-code>` regions is the frozen,
//! human-approved specification (hashed in specs.lock.json). Theorems are
//! frozen statements; their proofs are `<vc-code>` regions.
#![forbid(unsafe_code)]

// Ghost items only: erased in normal builds (Verus guide, "Ghost Erasure").
#[cfg(verus_only)]
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

// ===== part 1: counting ======================================================

proof fn lemma_count_concat(a: Seq<u8>, b: Seq<u8>)
    ensures
        count_newlines(a + b) == count_newlines(a) + count_newlines(b),
    decreases a.len(),
{
    if a.len() > 0 {
        let t = a.subrange(1, a.len() as int);
        lemma_count_concat(t, b);
        assert((a + b).subrange(1, (a + b).len() as int) =~= t + b);
        assert((a + b)[0] == a[0]);
    } else {
        assert(a + b =~= b);
    }
}

proof fn lemma_count_zero(s: Seq<u8>)
    requires
        forall|i: int| 0 <= i < s.len() ==> s[i] != 10,
    ensures
        count_newlines(s) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.subrange(1, s.len() as int);
        assert forall|i: int| 0 <= i < t.len() implies t[i] != 10 by {
            assert(t[i] == s[i + 1]);
        }
        lemma_count_zero(t);
    }
}

pub open spec fn no_lf(l: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < l.len() ==> l[i] != 10
}

proof fn lemma_count_lines_bytes(lines: Seq<Seq<u8>>)
    requires
        forall|k: int| 0 <= k < lines.len() ==> no_lf(#[trigger] lines[k]),
    ensures
        count_newlines(lines_bytes(lines)) == lines.len(),
    decreases lines.len(),
{
    if lines.len() > 0 {
        let t = lines.subrange(1, lines.len() as int);
        assert forall|k: int| 0 <= k < t.len() implies no_lf(#[trigger] t[k]) by {
            assert(t[k] == lines[k + 1]);
        }
        lemma_count_lines_bytes(t);
        assert(no_lf(lines[0]));
        lemma_count_zero(lines[0]);
        lemma_count_concat(lines[0] + seq![10u8], lines_bytes(t));
        lemma_count_concat(lines[0], seq![10u8]);
        assert(count_newlines(seq![10u8]) == 1) by {
            assert(seq![10u8].subrange(1, 1) =~= Seq::<u8>::empty());
            assert(count_newlines(Seq::<u8>::empty()) == 0);
        }
    }
}

// ===== escaping facts (kata 0002's own lemmas are private to that crate) ======

proof fn lemma_escape_byte_printable(b: u8)
    ensures
        escape_byte_len(b) == ls::escape_byte(b).len(),
        forall|i: int| 0 <= i < ls::escape_byte(b).len() ==> 32 <= #[trigger] ls::escape_byte(b)[i] <= 126,
{
}

pub open spec fn escape_byte_len(b: u8) -> nat {
    ls::escape_byte(b).len()
}

proof fn lemma_escape_printable(s: Seq<u8>)
    ensures
        forall|i: int| 0 <= i < escape(s).len() ==> 32 <= #[trigger] escape(s)[i] <= 126,
        s.len() > 0 ==> escape(s).len() > 0,
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.subrange(1, s.len() as int);
        lemma_escape_printable(t);
        lemma_escape_byte_printable(s[0]);
        let e = escape(s);
        let h = ls::escape_byte(s[0]);
        assert(e == h + escape(t));
        assert forall|i: int| 0 <= i < e.len() implies 32 <= #[trigger] e[i] <= 126 by {
            if i < h.len() {
                assert(e[i] == h[i]);
            } else {
                assert(e[i] == escape(t)[i - h.len()]);
            }
        }
    }
}

proof fn lemma_escape_no_lf(s: Seq<u8>)
    ensures
        no_lf(escape(s)),
{
    lemma_escape_printable(s);
}

proof fn lemma_escape_all_index(names: Seq<Seq<u8>>)
    ensures
        escape_all(names).len() == names.len(),
        forall|i: int| 0 <= i < names.len() ==> #[trigger] escape_all(names)[i] == escape(names[i]),
    decreases names.len(),
{
    if names.len() > 0 {
        let t = names.subrange(1, names.len() as int);
        lemma_escape_all_index(t);
        assert forall|i: int| 0 <= i < names.len() implies #[trigger] escape_all(names)[i] == escape(names[i]) by {
            if i > 0 {
                assert(t[i - 1] == names[i]);
            }
        }
    }
}

// ===== part 2: vls output structure ==========================================

proof fn lemma_single_dir_groups(req: RequestS)
    requires
        req.operands.len() == 1,
        ls::is_dir(req.operands[0].outcome),
    ensures
        file_ops(req.operands) == Seq::<OperandS>::empty(),
        dir_ops(req.operands) == seq![req.operands[0]],
        sort_ops(dir_ops(req.operands), req.reverse) == seq![req.operands[0]],
        ls::groups(req) == seq![ls::dir_group(req.operands[0], req)],
        !headers_on(req),
{
    let ops = req.operands;
    let o = ops[0];
    assert(ops.subrange(1, 1) =~= Seq::<OperandS>::empty());
    assert(file_ops(ops.subrange(1, 1)) == Seq::<OperandS>::empty());
    assert(file_ops(ops) =~= Seq::<OperandS>::empty());
    assert(dir_ops(ops.subrange(1, 1)) == Seq::<OperandS>::empty());
    assert(dir_ops(ops) =~= seq![o]);
    let s1 = seq![o];
    assert(s1.subrange(0, 0) =~= Seq::<OperandS>::empty());
    assert(sort_ops(s1.subrange(0, 0), req.reverse) == Seq::<OperandS>::empty());
    assert(ls::insert_op(o, Seq::<OperandS>::empty(), req.reverse) == s1);
    assert(sort_ops(s1, req.reverse) == s1);
    assert(s1.subrange(1, 1) =~= Seq::<OperandS>::empty());
    assert(ls::dir_groups(s1.subrange(1, 1), req) == Seq::<Seq<Seq<u8>>>::empty());
    assert(ls::dir_groups(s1, req) =~= seq![ls::dir_group(o, req)]);
    assert(ls::groups(req) =~= seq![ls::dir_group(o, req)]);
}

proof fn lemma_groups_lines_add(a: Seq<GroupS>, b: Seq<GroupS>)
    ensures
        groups_lines(a + b) == groups_lines(a) + groups_lines(b),
    decreases a.len(),
{
    if a.len() > 0 {
        let t = a.subrange(1, a.len() as int);
        lemma_groups_lines_add(t, b);
        assert((a + b).subrange(1, (a + b).len() as int) =~= t + b);
        assert((a + b)[0] == a[0]);
        assert(groups_lines(a + b) =~= groups_lines(a) + groups_lines(b));
    } else {
        assert(a + b =~= b);
        assert(groups_lines(a) =~= Seq::<Seq<Seq<u8>>>::empty());
        assert(groups_lines(a) + groups_lines(b) =~= groups_lines(b));
    }
}

proof fn lemma_dir_groups_lines(dirs: Seq<OperandS>, req: RequestS)
    ensures
        groups_lines(dir_groups_ast(dirs, req)) == ls::dir_groups(dirs, req),
    decreases dirs.len(),
{
    if dirs.len() > 0 {
        let t = dirs.subrange(1, dirs.len() as int);
        lemma_dir_groups_lines(t, req);
        let g = dir_group_ast(dirs[0], req);
        let rest = dir_groups_ast(t, req);
        assert(dir_groups_ast(dirs, req) == seq![g] + rest);
        lemma_groups_lines_add(seq![g], rest);
        assert(seq![g].subrange(1, 1) =~= Seq::<GroupS>::empty());
        assert(groups_lines(Seq::<GroupS>::empty()) == Seq::<Seq<Seq<u8>>>::empty());
        assert(groups_lines(seq![g]) =~= seq![group_lines(g)]);
        assert(group_lines(g) =~= ls::dir_group(dirs[0], req));
    } else {
        assert(dir_groups_ast(dirs, req) =~= Seq::<GroupS>::empty());
        assert(groups_lines(Seq::<GroupS>::empty()) =~= Seq::<Seq<Seq<u8>>>::empty());
        assert(ls::dir_groups(dirs, req) =~= Seq::<Seq<Seq<u8>>>::empty());
    }
}

proof fn lemma_vls_unparses(req: RequestS)
    ensures
        lines_bytes(ls(req).stdout) == unparse(ast_of(req)),
{
    let files = file_ops(req.operands);
    let fg: Seq<GroupS> = if files.len() > 0 {
        seq![GroupS { header: None, names: op_names(sort_ops(files, req.reverse)) }]
    } else {
        seq![]
    };
    let sd = sort_ops(dir_ops(req.operands), req.reverse);
    let dga = dir_groups_ast(sd, req);
    let all = fg + dga;
    lemma_groups_lines_add(fg, dga);
    lemma_dir_groups_lines(sd, req);
    if files.len() > 0 {
        let g0 = fg[0];
        assert(fg.subrange(1, 1) =~= Seq::<GroupS>::empty());
        assert(groups_lines(Seq::<GroupS>::empty()) == Seq::<Seq<Seq<u8>>>::empty());
        assert(groups_lines(fg) =~= seq![group_lines(g0)]);
        assert(group_lines(g0) =~= ls::file_group(req));
    } else {
        assert(groups_lines(fg) =~= Seq::<Seq<Seq<u8>>>::empty());
    }
    assert(groups_lines(all) =~= ls::groups(req));
    if all.len() == 1 && !has_header(all[0]) && all[0].names.len() == 0 {
        assert(all.subrange(1, 1) =~= Seq::<GroupS>::empty());
        assert(groups_lines(all) =~= seq![group_lines(all[0])]);
        assert(escape_all(all[0].names) =~= Seq::<Seq<u8>>::empty());
        assert(group_lines(all[0]) =~= Seq::<Seq<u8>>::empty());
        assert(join_groups(ls::groups(req)) =~= Seq::<Seq<u8>>::empty());
        assert(ast_of(req) == Seq::<GroupS>::empty());
        assert(groups_lines(Seq::<GroupS>::empty()) =~= Seq::<Seq<Seq<u8>>>::empty());
        assert(join_groups(Seq::<Seq<Seq<u8>>>::empty()) =~= Seq::<Seq<u8>>::empty());
    } else {
        assert(ast_of(req) == all);
    }
}

// ===== part 3: well-formedness of vls's AST ==================================

proof fn lemma_insert_op_elems(x: OperandS, s: Seq<OperandS>, reverse: bool)
    ensures
        ls::insert_op(x, s, reverse).len() == s.len() + 1,
        forall|k: int|
            0 <= k < ls::insert_op(x, s, reverse).len() ==> (#[trigger] ls::insert_op(x, s, reverse)[k] == x
                || s.contains(ls::insert_op(x, s, reverse)[k])),
    decreases s.len(),
{
    let r = ls::insert_op(x, s, reverse);
    if s.len() > 0 {
        let t = s.subrange(1, s.len() as int);
        lemma_insert_op_elems(x, t, reverse);
        assert forall|k: int| 0 <= k < r.len() implies (#[trigger] r[k] == x || s.contains(r[k])) by {
            if ls::before(x.name, s[0].name, reverse) {
                if k > 0 {
                    assert(r[k] == s[k - 1]);
                }
            } else {
                if k == 0 {
                    assert(r[0] == s[0]);
                } else {
                    let rt = ls::insert_op(x, t, reverse);
                    assert(r[k] == rt[k - 1]);
                    if rt[k - 1] != x {
                        let m = choose|m: int| 0 <= m < t.len() && t[m] == rt[k - 1];
                        assert(s[m + 1] == t[m]);
                    }
                }
            }
        }
    }
}

proof fn lemma_sort_ops_elems(s: Seq<OperandS>, reverse: bool)
    ensures
        sort_ops(s, reverse).len() == s.len(),
        forall|k: int| 0 <= k < s.len() ==> s.contains(#[trigger] sort_ops(s, reverse)[k]),
    decreases s.len(),
{
    if s.len() > 0 {
        let p = s.subrange(0, s.len() - 1);
        let x = s[s.len() - 1];
        lemma_sort_ops_elems(p, reverse);
        lemma_insert_op_elems(x, sort_ops(p, reverse), reverse);
        let r = sort_ops(s, reverse);
        assert forall|k: int| 0 <= k < s.len() implies s.contains(#[trigger] sort_ops(s, reverse)[k]) by {
            if r[k] == x {
                assert(s[s.len() - 1] == x);
            } else {
                let sp = sort_ops(p, reverse);
                let m = choose|m: int| 0 <= m < sp.len() && sp[m] == r[k];
                let j = choose|j: int| 0 <= j < p.len() && p[j] == sp[m];
                assert(s[j] == p[j]);
            }
        }
    }
}

proof fn lemma_file_ops_elems(ops: Seq<OperandS>)
    ensures
        forall|k: int|
            0 <= k < file_ops(ops).len() ==> ops.contains(#[trigger] file_ops(ops)[k]) && ls::is_file(
                file_ops(ops)[k].outcome,
            ),
        file_ops(ops).len() + dir_ops(ops).len() <= ops.len(),
    decreases ops.len(),
{
    if ops.len() > 0 {
        let t = ops.subrange(1, ops.len() as int);
        lemma_file_ops_elems(t);
        let head: Seq<OperandS> = if ls::is_file(ops[0].outcome) { seq![ops[0]] } else { seq![] };
        assert(file_ops(ops) == head + file_ops(t));
        assert forall|k: int|
            0 <= k < file_ops(ops).len() implies ops.contains(#[trigger] file_ops(ops)[k]) && ls::is_file(
            file_ops(ops)[k].outcome,
        ) by {
            if k < head.len() {
                assert(file_ops(ops)[k] == ops[0]);
            } else {
                let y = file_ops(t)[k - head.len()];
                assert(file_ops(ops)[k] == y);
                let m = choose|m: int| 0 <= m < t.len() && t[m] == y;
                assert(ops[m + 1] == y);
            }
        }
    } else {
        assert(file_ops(ops) =~= Seq::<OperandS>::empty());
        assert(dir_ops(ops) =~= Seq::<OperandS>::empty());
    }
}

proof fn lemma_dir_groups_ast(dirs: Seq<OperandS>, req: RequestS)
    ensures
        dir_groups_ast(dirs, req).len() == dirs.len(),
        forall|k: int| 0 <= k < dirs.len() ==> #[trigger] dir_groups_ast(dirs, req)[k] == dir_group_ast(dirs[k], req),
    decreases dirs.len(),
{
    if dirs.len() > 0 {
        let t = dirs.subrange(1, dirs.len() as int);
        lemma_dir_groups_ast(t, req);
        assert forall|k: int| 0 <= k < dirs.len() implies #[trigger] dir_groups_ast(dirs, req)[k] == dir_group_ast(dirs[k], req) by {
            if k > 0 {
                assert(t[k - 1] == dirs[k]);
            }
        }
    }
}

proof fn lemma_op_names_index(s: Seq<OperandS>)
    ensures
        op_names(s).len() == s.len(),
        forall|k: int| 0 <= k < s.len() ==> #[trigger] op_names(s)[k] == s[k].name,
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.subrange(1, s.len() as int);
        lemma_op_names_index(t);
        assert forall|k: int| 0 <= k < s.len() implies #[trigger] op_names(s)[k] == s[k].name by {
            if k > 0 {
                assert(t[k - 1] == s[k]);
            }
        }
    }
}

pub open spec fn all_nonempty(s: Seq<Seq<u8>>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> (#[trigger] s[k]).len() > 0
}

proof fn lemma_insert_unique_nonempty(x: Seq<u8>, s: Seq<Seq<u8>>, reverse: bool)
    requires
        x.len() > 0,
        all_nonempty(s),
    ensures
        all_nonempty(ls::insert_unique(x, s, reverse)),
    decreases s.len(),
{
    let r = ls::insert_unique(x, s, reverse);
    if s.len() > 0 {
        let t = s.subrange(1, s.len() as int);
        assert(all_nonempty(t)) by {
            assert forall|k: int| 0 <= k < t.len() implies (#[trigger] t[k]).len() > 0 by {
                assert(t[k] == s[k + 1]);
            }
        }
        lemma_insert_unique_nonempty(x, t, reverse);
        if x == s[0] {
        } else if ls::before(x, s[0], reverse) {
            assert forall|k: int| 0 <= k < r.len() implies (#[trigger] r[k]).len() > 0 by {
                if k > 0 {
                    assert(r[k] == s[k - 1]);
                }
            }
        } else {
            let rt = ls::insert_unique(x, t, reverse);
            assert forall|k: int| 0 <= k < r.len() implies (#[trigger] r[k]).len() > 0 by {
                if k > 0 {
                    assert(r[k] == rt[k - 1]);
                }
            }
        }
    } else {
        assert(r =~= seq![x]);
    }
}

proof fn lemma_sort_unique_nonempty(s: Seq<Seq<u8>>, reverse: bool)
    requires
        all_nonempty(s),
    ensures
        all_nonempty(sort_unique(s, reverse)),
    decreases s.len(),
{
    if s.len() > 0 {
        let p = s.subrange(0, s.len() - 1);
        assert(all_nonempty(p)) by {
            assert forall|k: int| 0 <= k < p.len() implies (#[trigger] p[k]).len() > 0 by {
                assert(p[k] == s[k]);
            }
        }
        lemma_sort_unique_nonempty(p, reverse);
        assert(s[s.len() - 1].len() > 0);
        lemma_insert_unique_nonempty(s[s.len() - 1], sort_unique(p, reverse), reverse);
    } else {
        assert(sort_unique(s, reverse) =~= Seq::<Seq<u8>>::empty());
    }
}

proof fn lemma_shown_entries_nonempty(es: Seq<Seq<u8>>, all: bool)
    ensures
        all_nonempty(ls::shown_entries(es, all)),
    decreases es.len(),
{
    if es.len() > 0 {
        let t = es.subrange(1, es.len() as int);
        lemma_shown_entries_nonempty(t, all);
        let head: Seq<Seq<u8>> = if ls::shown(es[0], all) { seq![es[0]] } else { seq![] };
        let r = ls::shown_entries(es, all);
        assert(r == head + ls::shown_entries(t, all));
        assert forall|k: int| 0 <= k < r.len() implies (#[trigger] r[k]).len() > 0 by {
            if k >= head.len() {
                assert(r[k] == ls::shown_entries(t, all)[k - head.len()]);
            }
        }
    } else {
        assert(ls::shown_entries(es, all) =~= Seq::<Seq<u8>>::empty());
    }
}

proof fn lemma_listed_nonempty(es: Seq<Seq<u8>>, all: bool, reverse: bool)
    ensures
        all_nonempty(sort_unique(listed_names(es, all), reverse)),
{
    lemma_shown_entries_nonempty(es, all);
    let se = ls::shown_entries(es, all);
    let l = listed_names(es, all);
    assert(all_nonempty(l)) by {
        assert forall|k: int| 0 <= k < l.len() implies (#[trigger] l[k]).len() > 0 by {
            if all && k >= se.len() {
                if k == se.len() {
                    assert(l[k] == ls::dot());
                } else {
                    assert(l[k] == ls::dotdot());
                }
            } else {
                assert(l[k] == se[k]);
            }
        }
    }
    lemma_sort_unique_nonempty(l, reverse);
}

proof fn lemma_vls_ast_wf(req: RequestS)
    requires
        forall|i: int|
            0 <= i < req.operands.len() && ls::is_file((#[trigger] req.operands[i]).outcome) ==> req.operands[i].name.len()
                > 0,
    ensures
        wf(ast_of(req)),
{
    let ops = req.operands;
    let files = file_ops(ops);
    let sf = sort_ops(files, req.reverse);
    let fg: Seq<GroupS> = if files.len() > 0 {
        seq![GroupS { header: None, names: op_names(sf) }]
    } else {
        seq![]
    };
    let sd = sort_ops(dir_ops(ops), req.reverse);
    let dga = dir_groups_ast(sd, req);
    let all = fg + dga;
    lemma_file_ops_elems(ops);
    lemma_sort_ops_elems(files, req.reverse);
    lemma_sort_ops_elems(dir_ops(ops), req.reverse);
    lemma_dir_groups_ast(sd, req);
    lemma_op_names_index(sf);
    // names of every group are non-empty
    assert forall|i: int, j: int|
        0 <= i < all.len() && 0 <= j < all[i].names.len() implies (#[trigger] all[i].names[j]).len() > 0 by {
        if i < fg.len() {
            assert(all[i] == fg[0]);
            assert(op_names(sf)[j] == sf[j].name);
            assert(files.contains(sf[j]));
            let m = choose|m: int| 0 <= m < files.len() && files[m] == sf[j];
            assert(ops.contains(files[m]) && ls::is_file(files[m].outcome));
            let q = choose|q: int| 0 <= q < ops.len() && ops[q] == files[m];
            assert(ops[q].name.len() > 0);
        } else {
            let k = i - fg.len();
            assert(all[i] == dga[k]);
            assert(dga[k] == dir_group_ast(sd[k], req));
            lemma_listed_nonempty(entries_of(sd[k].outcome), req.all, req.reverse);
        }
    }
    // only the first group may be headerless
    assert forall|i: int| 0 < i < all.len() implies has_header(#[trigger] all[i]) by {
        if headers_on(req) {
            let k = i - fg.len();
            assert(all[i] == dga[k]);
            assert(dga[k] == dir_group_ast(sd[k], req));
        } else {
            assert(all.len() <= 1);
        }
    }
    if all.len() == 1 && !has_header(all[0]) && all[0].names.len() == 0 {
        assert(ast_of(req) =~= Seq::<GroupS>::empty());
    } else {
        assert(ast_of(req) == all);
        if all.len() > 0 && !has_header(all[0]) {
            if fg.len() > 0 {
                assert(all[0] == fg[0]);
                assert(op_names(sf).len() == files.len());
            } else {
                assert(all.len() == 1 || headers_on(req));
                if headers_on(req) {
                    assert(all[0] == dga[0]);
                    assert(dga[0] == dir_group_ast(sd[0], req));
                }
            }
        }
    }
}

proof fn lemma_count_files(req: RequestS)
    requires
        req.operands.len() == 1,
        ls::is_dir(req.operands[0].outcome),
    ensures
        count_newlines(lines_bytes(ls(req).stdout)) == sort_unique(
            listed_names(entries_of(req.operands[0].outcome), req.all),
            req.reverse,
        ).len(),
{
    lemma_single_dir_groups(req);
    let o = req.operands[0];
    let s = sort_unique(listed_names(entries_of(o.outcome), req.all), req.reverse);
    assert(ls::dir_group(o, req) =~= escape_all(s));
    let gs = ls::groups(req);
    assert(join_groups(gs) == gs[0]);
    assert(ls(req).stdout == escape_all(s));
    lemma_escape_all_index(s);
    let l = escape_all(s);
    assert forall|k: int| 0 <= k < l.len() implies no_lf(#[trigger] l[k]) by {
        lemma_escape_no_lf(s[k]);
    }
    lemma_count_lines_bytes(l);
}

// ===== part 4: the parser (spec), as a byte fold, a line decoder, a line fold

// ---- split into lines (byte fold) ----
pub struct SplitS {
    pub lines: Seq<Seq<u8>>,
    pub cur: Seq<u8>,
}

pub open spec fn split_init() -> SplitS {
    SplitS { lines: seq![], cur: seq![] }
}

pub open spec fn split_step(st: SplitS, b: u8) -> SplitS {
    if b == 10 {
        SplitS { lines: st.lines.push(st.cur), cur: seq![] }
    } else {
        SplitS { lines: st.lines, cur: st.cur.push(b) }
    }
}

pub open spec fn split_run(st: SplitS, s: Seq<u8>) -> SplitS
    decreases s.len(),
{
    if s.len() == 0 {
        st
    } else {
        split_step(split_run(st, s.subrange(0, s.len() - 1)), s[s.len() - 1])
    }
}

pub open spec fn split_lines(s: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    let st = split_run(split_init(), s);
    if st.cur.len() == 0 {
        Some(st.lines)
    } else {
        None
    }
}

proof fn lemma_split_run_add(st: SplitS, a: Seq<u8>, b: Seq<u8>)
    ensures
        split_run(st, a + b) == split_run(split_run(st, a), b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        let bp = b.subrange(0, b.len() - 1);
        lemma_split_run_add(st, a, bp);
        assert((a + b).subrange(0, (a + b).len() - 1) =~= a + bp);
        assert((a + b)[(a + b).len() - 1] == b[b.len() - 1]);
    }
}

proof fn lemma_split_run_plain(st: SplitS, l: Seq<u8>)
    requires
        no_lf(l),
    ensures
        split_run(st, l) == (SplitS { lines: st.lines, cur: st.cur + l }),
    decreases l.len(),
{
    if l.len() == 0 {
        assert(st.cur + l =~= st.cur);
    } else {
        let lp = l.subrange(0, l.len() - 1);
        assert(no_lf(lp)) by {
            assert forall|i: int| 0 <= i < lp.len() implies lp[i] != 10 by {
                assert(lp[i] == l[i]);
            }
        }
        lemma_split_run_plain(st, lp);
        assert(l[l.len() - 1] != 10);
        assert((st.cur + lp).push(l[l.len() - 1]) =~= st.cur + l);
    }
}

proof fn lemma_split_lines_bytes(ls0: Seq<Seq<u8>>, lines: Seq<Seq<u8>>)
    requires
        forall|k: int| 0 <= k < lines.len() ==> no_lf(#[trigger] lines[k]),
    ensures
        split_run(SplitS { lines: ls0, cur: seq![] }, lines_bytes(lines)) == (SplitS { lines: ls0 + lines, cur: seq![] }),
    decreases lines.len(),
{
    let st = SplitS { lines: ls0, cur: seq![] };
    if lines.len() == 0 {
        assert(ls0 + lines =~= ls0);
    } else {
        let t = lines.subrange(1, lines.len() as int);
        assert forall|k: int| 0 <= k < t.len() implies no_lf(#[trigger] t[k]) by {
            assert(t[k] == lines[k + 1]);
        }
        let l0 = lines[0];
        assert(no_lf(l0));
        lemma_split_run_add(st, l0 + seq![10u8], lines_bytes(t));
        lemma_split_run_add(st, l0, seq![10u8]);
        lemma_split_run_plain(st, l0);
        assert(seq![] + l0 =~= l0);
        assert(seq![10u8].subrange(0, 0) =~= Seq::<u8>::empty());
        let s1 = split_run(st, l0);
        assert(s1.cur =~= l0);
        assert(split_run(s1, Seq::<u8>::empty()) == s1);
        assert(split_run(s1, seq![10u8]) == split_step(s1, 10u8));
        assert(split_run(split_run(st, l0), seq![10u8]) == (SplitS { lines: ls0.push(l0), cur: seq![] }));
        lemma_split_lines_bytes(ls0.push(l0), t);
        assert(ls0.push(l0) + t =~= ls0 + lines);
    }
}

proof fn lemma_lines_bytes_push(lines: Seq<Seq<u8>>, l: Seq<u8>)
    ensures
        lines_bytes(lines.push(l)) == lines_bytes(lines) + l + seq![10u8],
    decreases lines.len(),
{
    if lines.len() == 0 {
        assert(lines.push(l).subrange(1, 1) =~= Seq::<Seq<u8>>::empty());
        assert(lines_bytes(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
        assert(lines_bytes(lines.push(l)) =~= lines_bytes(lines) + l + seq![10u8]);
    } else {
        let t = lines.subrange(1, lines.len() as int);
        lemma_lines_bytes_push(t, l);
        assert(lines.push(l).subrange(1, lines.len() as int + 1) =~= t.push(l));
        assert(lines_bytes(lines.push(l)) =~= lines_bytes(lines) + l + seq![10u8]);
    }
}

proof fn lemma_split_reverse(s: Seq<u8>)
    ensures
        s == lines_bytes(split_run(split_init(), s).lines) + split_run(split_init(), s).cur,
        forall|k: int|
            0 <= k < split_run(split_init(), s).lines.len() ==> no_lf(#[trigger] split_run(split_init(), s).lines[k]),
        no_lf(split_run(split_init(), s).cur),
    decreases s.len(),
{
    if s.len() == 0 {
        assert(lines_bytes(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
        assert(s =~= lines_bytes(Seq::<Seq<u8>>::empty()) + Seq::<u8>::empty());
    } else {
        let p = s.subrange(0, s.len() - 1);
        let b = s[s.len() - 1];
        lemma_split_reverse(p);
        let st = split_run(split_init(), p);
        if b == 10 {
            lemma_lines_bytes_push(st.lines, st.cur);
            assert(s =~= lines_bytes(st.lines.push(st.cur)) + Seq::<u8>::empty());
            let nl = st.lines.push(st.cur);
            assert forall|k: int| 0 <= k < nl.len() implies no_lf(#[trigger] nl[k]) by {
                if k < st.lines.len() {
                    assert(nl[k] == st.lines[k]);
                }
            }
        } else {
            assert(s =~= p.push(b));
            assert(s =~= lines_bytes(st.lines) + st.cur.push(b));
            let nc = st.cur.push(b);
            assert forall|i: int| 0 <= i < nc.len() implies nc[i] != 10 by {
                if i < st.cur.len() {
                    assert(nc[i] == st.cur[i]);
                }
            }
        }
    }
}

// ---- decode one line ----
pub open spec fn is_hex_digit(c: u8) -> bool {
    (48 <= c && c <= 57) || (97 <= c && c <= 102)
}

pub open spec fn unhex(c: u8) -> u8 {
    if c <= 57 {
        (c - 48) as u8
    } else {
        (c - 87) as u8
    }
}

pub open spec fn hex_value(h: u8, l: u8) -> u8 {
    (unhex(h) * 16 + unhex(l)) as u8
}

/// The canonical token at the start of `l`: (byte, length). A token is
/// accepted only if `escape_byte` of its byte reproduces it exactly (strict).
pub open spec fn token(l: Seq<u8>) -> Option<(u8, nat)> {
    if l.len() == 0 {
        None
    } else if l[0] == 92 {
        if l.len() >= 2 && l[1] == 92 {
            Some((92u8, 2nat))
        } else if l.len() >= 2 && l[1] == 110 {
            Some((10u8, 2nat))
        } else if l.len() >= 2 && l[1] == 116 {
            Some((9u8, 2nat))
        } else if l.len() >= 2 && l[1] == 58 {
            Some((58u8, 2nat))
        } else if l.len() >= 4 && l[1] == 120 && is_hex_digit(l[2]) && is_hex_digit(l[3])
            && ls::escape_byte(hex_value(l[2], l[3])) == l.subrange(0, 4) {
            Some((hex_value(l[2], l[3]), 4nat))
        } else {
            None
        }
    } else if l[0] != 58 && ls::escape_byte(l[0]) == seq![l[0]] {
        Some((l[0], 1nat))
    } else {
        None
    }
}

pub open spec fn dec_line(l: Seq<u8>) -> Option<(Seq<u8>, bool)>
    decreases l.len(),
{
    if l.len() == 0 {
        Some((seq![], false))
    } else if l.len() == 1 && l[0] == 58 {
        Some((seq![], true))
    } else {
        match token(l) {
            None => None,
            Some((b, n)) => if 0 < n && n <= l.len() {
                match dec_line(l.subrange(n as int, l.len() as int)) {
                    None => None,
                    Some((v, h)) => Some((seq![b] + v, h)),
                }
            } else {
                None
            },
        }
    }
}

proof fn lemma_token_shape(l: Seq<u8>)
    ensures
        token(l) matches Some((b, n)) ==> 0 < n <= l.len() && l.subrange(0, n as int) == ls::escape_byte(b),
{
    if let Some((b, n)) = token(l) {
        if l[0] == 92 {
            if n == 2 {
                assert(l.subrange(0, 2) =~= ls::escape_byte(b));
            }
        } else {
            assert(l.subrange(0, 1) =~= ls::escape_byte(b));
        }
    }
}

proof fn lemma_hex_round(b: u8)
    requires
        !(b == 92 || b == 10 || b == 9 || b == 58 || (32 <= b && b <= 126)),
    ensures
        is_hex_digit(ls::hex_digit(b / 16)),
        is_hex_digit(ls::hex_digit(b % 16)),
        hex_value(ls::hex_digit(b / 16), ls::hex_digit(b % 16)) == b,
{
    let hi = b / 16;
    let lo = b % 16;
    assert(hi < 16 && lo < 16);
    assert(unhex(ls::hex_digit(hi)) == hi);
    assert(unhex(ls::hex_digit(lo)) == lo);
    assert(hi * 16 + lo == b) by (nonlinear_arith)
        requires
            hi == b / 16,
            lo == b % 16,
    ;
}

proof fn lemma_token_escape_byte(b: u8, t: Seq<u8>)
    ensures
        token(ls::escape_byte(b) + t) == Some((b, ls::escape_byte(b).len())),
{
    let e = ls::escape_byte(b);
    let l = e + t;
    assert(l.subrange(0, e.len() as int) =~= e);
    if !(b == 92 || b == 10 || b == 9 || b == 58 || (32 <= b && b <= 126)) {
        lemma_hex_round(b);
        assert(l[2] == e[2] && l[3] == e[3]);
        assert(l.subrange(0, 4) =~= e);
    } else {
        assert(l[0] == e[0]);
        if e.len() > 1 {
            assert(l[1] == e[1]);
        }
    }
}

pub open spec fn suffix(header: bool) -> Seq<u8> {
    if header {
        seq![58u8]
    } else {
        seq![]
    }
}

proof fn lemma_dec_escape(v: Seq<u8>, h: bool)
    ensures
        dec_line(escape(v) + suffix(h)) == Some((v, h)),
    decreases v.len(),
{
    if v.len() == 0 {
        assert(escape(v) + suffix(h) =~= suffix(h));
    } else {
        let rest = v.subrange(1, v.len() as int);
        let e = ls::escape_byte(v[0]);
        let l = escape(v) + suffix(h);
        assert(l =~= e + (escape(rest) + suffix(h)));
        lemma_token_escape_byte(v[0], escape(rest) + suffix(h));
        lemma_escape_byte_printable(v[0]);
        if l.len() == 1 {
            assert(l[0] == e[0]);
        }
        assert(l.subrange(e.len() as int, l.len() as int) =~= escape(rest) + suffix(h));
        lemma_dec_escape(rest, h);
        assert(seq![v[0]] + rest =~= v);
    }
}

proof fn lemma_dec_reverse(l: Seq<u8>)
    ensures
        dec_line(l) matches Some((v, h)) ==> l == escape(v) + suffix(h),
    decreases l.len(),
{
    if let Some((v, h)) = dec_line(l) {
        if l.len() == 0 {
            assert(escape(v) + suffix(h) =~= l);
        } else if l.len() == 1 && l[0] == 58 {
            assert(escape(v) + suffix(h) =~= l);
        } else {
            lemma_token_shape(l);
            let (b, n) = token(l).unwrap();
            let rest = l.subrange(n as int, l.len() as int);
            lemma_dec_reverse(rest);
            let (v2, h2) = dec_line(rest).unwrap();
            assert(v == seq![b] + v2 && h == h2);
            assert((seq![b] + v2).subrange(1, v.len() as int) =~= v2);
            assert(escape(v) == ls::escape_byte(b) + escape(v2));
            assert(l =~= l.subrange(0, n as int) + rest);
            assert(l =~= escape(v) + suffix(h));
        }
    }
}

// ---- lines -> document (line fold) ----
pub struct PState {
    pub ok: bool,
    pub doc: Seq<GroupS>,
    pub fresh: bool,
}

pub open spec fn pinit() -> PState {
    PState { ok: true, doc: seq![], fresh: true }
}

pub open spec fn pfail() -> PState {
    PState { ok: false, doc: seq![], fresh: true }
}

pub open spec fn add_name(doc: Seq<GroupS>, v: Seq<u8>) -> Seq<GroupS> {
    doc.update(
        doc.len() - 1,
        GroupS { header: doc[doc.len() - 1].header, names: doc[doc.len() - 1].names.push(v) },
    )
}

pub open spec fn pstep(st: PState, line: Seq<u8>) -> PState {
    if !st.ok {
        st
    } else if line.len() == 0 {
        if st.fresh {
            pfail()
        } else {
            PState { ok: true, doc: st.doc, fresh: true }
        }
    } else {
        match dec_line(line) {
            None => pfail(),
            Some((v, h)) => if h {
                if st.fresh {
                    PState { ok: true, doc: st.doc.push(GroupS { header: Some(v), names: seq![] }), fresh: false }
                } else {
                    pfail()
                }
            } else if st.fresh {
                if st.doc.len() == 0 {
                    PState { ok: true, doc: seq![GroupS { header: None, names: seq![v] }], fresh: false }
                } else {
                    pfail()
                }
            } else {
                PState { ok: true, doc: add_name(st.doc, v), fresh: false }
            },
        }
    }
}

pub open spec fn prun(st: PState, lines: Seq<Seq<u8>>) -> PState
    decreases lines.len(),
{
    if lines.len() == 0 {
        st
    } else {
        pstep(prun(st, lines.subrange(0, lines.len() - 1)), lines[lines.len() - 1])
    }
}

pub open spec fn parse_lines(lines: Seq<Seq<u8>>) -> Option<Seq<GroupS>> {
    let st = prun(pinit(), lines);
    if st.ok && !(st.fresh && st.doc.len() > 0) {
        Some(st.doc)
    } else {
        None
    }
}

pub open spec fn parse_doc(s: Seq<u8>) -> Option<Seq<GroupS>> {
    match split_lines(s) {
        Some(lines) => parse_lines(lines),
        None => None,
    }
}

proof fn lemma_prun_add(st: PState, a: Seq<Seq<u8>>, b: Seq<Seq<u8>>)
    ensures
        prun(st, a + b) == prun(prun(st, a), b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        let bp = b.subrange(0, b.len() - 1);
        lemma_prun_add(st, a, bp);
        assert((a + b).subrange(0, (a + b).len() - 1) =~= a + bp);
        assert((a + b)[(a + b).len() - 1] == b[b.len() - 1]);
    }
}

proof fn lemma_prun_one(st: PState, l: Seq<u8>)
    ensures
        prun(st, seq![l]) == pstep(st, l),
{
    assert(seq![l].subrange(0, 0) =~= Seq::<Seq<u8>>::empty());
    assert(prun(st, Seq::<Seq<u8>>::empty()) == st);
    assert(seq![l][0] == l);
}

proof fn lemma_escape_all_push(m: Seq<Seq<u8>>, v: Seq<u8>)
    ensures
        escape_all(m.push(v)) == escape_all(m) + seq![escape(v)],
    decreases m.len(),
{
    if m.len() == 0 {
        assert(m.push(v).subrange(1, 1) =~= Seq::<Seq<u8>>::empty());
        assert(escape_all(Seq::<Seq<u8>>::empty()) == Seq::<Seq<u8>>::empty());
        assert(escape_all(m.push(v)) =~= escape_all(m) + seq![escape(v)]);
    } else {
        let t = m.subrange(1, m.len() as int);
        lemma_escape_all_push(t, v);
        assert(m.push(v).subrange(1, m.len() as int + 1) =~= t.push(v));
        assert(escape_all(m.push(v)) =~= escape_all(m) + seq![escape(v)]);
    }
}

/// Appending escaped names to the open last group.
proof fn lemma_prun_names(st: PState, m: Seq<Seq<u8>>)
    requires
        st.ok,
        !st.fresh,
        st.doc.len() > 0,
        all_nonempty(m),
    ensures
        prun(st, escape_all(m)) == (PState {
            ok: true,
            doc: st.doc.update(
                st.doc.len() - 1,
                GroupS { header: st.doc[st.doc.len() - 1].header, names: st.doc[st.doc.len() - 1].names + m },
            ),
            fresh: false,
        }),
    decreases m.len(),
{
    let last = st.doc[st.doc.len() - 1];
    if m.len() == 0 {
        assert(escape_all(m) =~= Seq::<Seq<u8>>::empty());
        assert(last.names + m =~= last.names);
        assert(st.doc.update(st.doc.len() - 1, GroupS { header: last.header, names: last.names + m }) =~= st.doc);
    } else {
        let mp = m.subrange(0, m.len() - 1);
        let v = m[m.len() - 1];
        assert(all_nonempty(mp)) by {
            assert forall|k: int| 0 <= k < mp.len() implies (#[trigger] mp[k]).len() > 0 by {
                assert(mp[k] == m[k]);
            }
        }
        lemma_prun_names(st, mp);
        assert(mp.push(v) =~= m);
        lemma_escape_all_push(mp, v);
        lemma_prun_add(st, escape_all(mp), seq![escape(v)]);
        let mid = prun(st, escape_all(mp));
        lemma_prun_one(mid, escape(v));
        assert(v.len() > 0);
        lemma_escape_printable(v);
        lemma_dec_escape(v, false);
        assert(escape(v) + suffix(false) =~= escape(v));
        assert(mid.doc[mid.doc.len() - 1].names.push(v) =~= last.names + m);
        assert(add_name(mid.doc, v) =~= st.doc.update(
            st.doc.len() - 1,
            GroupS { header: last.header, names: last.names + m },
        ));
    }
}

/// A group with a header, started from a fresh state.
proof fn lemma_prun_header_group(st: PState, g: GroupS)
    requires
        st.ok,
        st.fresh,
        has_header(g),
        all_nonempty(g.names),
    ensures
        prun(st, group_lines(g)) == (PState { ok: true, doc: st.doc.push(g), fresh: false }),
{
    let h = g.header.unwrap();
    let hl = escape(h) + seq![58u8];
    assert(group_lines(g) == seq![hl] + escape_all(g.names));
    lemma_prun_add(st, seq![hl], escape_all(g.names));
    lemma_prun_one(st, hl);
    lemma_dec_escape(h, true);
    let s1 = PState { ok: true, doc: st.doc.push(GroupS { header: Some(h), names: seq![] }), fresh: false };
    assert(pstep(st, hl) == s1);
    lemma_prun_names(s1, g.names);
    assert(Seq::<Seq<u8>>::empty() + g.names =~= g.names);
    assert(s1.doc.update(s1.doc.len() - 1, GroupS { header: Some(h), names: Seq::<Seq<u8>>::empty() + g.names })
        =~= st.doc.push(g));
}

/// A headerless (hence first, non-empty) group, from the initial state.
proof fn lemma_prun_first_plain_group(g: GroupS)
    requires
        !has_header(g),
        g.names.len() > 0,
        all_nonempty(g.names),
    ensures
        prun(pinit(), group_lines(g)) == (PState { ok: true, doc: seq![g], fresh: false }),
{
    let m = g.names;
    let rest = m.subrange(1, m.len() as int);
    assert(group_lines(g) =~= escape_all(m));
    assert(escape_all(m) == seq![escape(m[0])] + escape_all(rest));
    lemma_prun_add(pinit(), seq![escape(m[0])], escape_all(rest));
    lemma_prun_one(pinit(), escape(m[0]));
    lemma_escape_printable(m[0]);
    lemma_dec_escape(m[0], false);
    assert(escape(m[0]) + suffix(false) =~= escape(m[0]));
    let s1 = PState { ok: true, doc: seq![GroupS { header: None, names: seq![m[0]] }], fresh: false };
    assert(pstep(pinit(), escape(m[0])) == s1);
    assert(all_nonempty(rest)) by {
        assert forall|k: int| 0 <= k < rest.len() implies (#[trigger] rest[k]).len() > 0 by {
            assert(rest[k] == m[k + 1]);
        }
    }
    lemma_prun_names(s1, rest);
    assert(seq![m[0]] + rest =~= m);
    assert(g.header == None::<Seq<u8>>);
    assert(s1.doc.update(0, GroupS { header: None, names: seq![m[0]] + rest }) =~= seq![g]);
}

proof fn lemma_groups_lines_push(x: Seq<GroupS>, g: GroupS)
    ensures
        groups_lines(x.push(g)) == groups_lines(x).push(group_lines(g)),
{
    lemma_groups_lines_add(x, seq![g]);
    assert(x.push(g) =~= x + seq![g]);
    assert(seq![g].subrange(1, 1) =~= Seq::<GroupS>::empty());
    assert(groups_lines(Seq::<GroupS>::empty()) == Seq::<Seq<Seq<u8>>>::empty());
    assert(groups_lines(seq![g]) =~= seq![group_lines(g)]);
    assert(groups_lines(x) + seq![group_lines(g)] =~= groups_lines(x).push(group_lines(g)));
}

proof fn lemma_groups_lines_len(x: Seq<GroupS>)
    ensures
        groups_lines(x).len() == x.len(),
    decreases x.len(),
{
    if x.len() > 0 {
        lemma_groups_lines_len(x.subrange(1, x.len() as int));
    }
}

proof fn lemma_wf_prefix(x: Seq<GroupS>)
    requires
        wf(x),
        x.len() > 0,
    ensures
        wf(x.subrange(0, x.len() - 1)),
        forall|j: int| 0 <= j < x.len() ==> all_nonempty(#[trigger] x[j].names),
{
    let p = x.subrange(0, x.len() - 1);
    assert forall|i: int, j: int| 0 <= i < p.len() && 0 <= j < p[i].names.len() implies (#[trigger] p[i].names[j]).len()
        > 0 by {
        assert(p[i] == x[i]);
        assert(x[i].names[j].len() > 0);
    }
    assert forall|i: int| 0 < i < p.len() implies has_header(#[trigger] p[i]) by {
        assert(p[i] == x[i]);
    }
    if p.len() > 0 {
        assert(p[0] == x[0]);
    }
    assert forall|j: int| 0 <= j < x.len() implies all_nonempty(#[trigger] x[j].names) by {
        assert forall|k: int| 0 <= k < x[j].names.len() implies (#[trigger] x[j].names[k]).len() > 0 by {
            assert(x[j].names[k].len() > 0);
        }
    }
}

/// Forward direction for the line fold.
proof fn lemma_prun_doc(x: Seq<GroupS>)
    requires
        wf(x),
        x.len() > 0,
    ensures
        prun(pinit(), join_groups(groups_lines(x))) == (PState { ok: true, doc: x, fresh: false }),
    decreases x.len(),
{
    lemma_wf_prefix(x);
    lemma_groups_lines_len(x);
    let k = x.len();
    let g = x[k - 1];
    let p = x.subrange(0, k - 1);
    assert(x =~= p.push(g));
    lemma_groups_lines_push(p, g);
    let gl = groups_lines(x);
    if k == 1 {
        assert(join_groups(gl) == gl[0]);
        assert(gl[0] == group_lines(g));
        if has_header(g) {
            lemma_prun_header_group(pinit(), g);
            assert(Seq::<GroupS>::empty().push(g) =~= x);
        } else {
            lemma_prun_first_plain_group(g);
            assert(seq![g] =~= x);
        }
    } else {
        lemma_prun_doc(p);
        lemma_groups_lines_len(p);
        assert(gl.subrange(0, gl.len() - 1) =~= groups_lines(p));
        assert(join_groups(gl) == join_groups(groups_lines(p)) + seq![Seq::<u8>::empty()] + group_lines(g));
        let s1 = PState { ok: true, doc: p, fresh: false };
        lemma_prun_add(pinit(), join_groups(groups_lines(p)) + seq![Seq::<u8>::empty()], group_lines(g));
        lemma_prun_add(pinit(), join_groups(groups_lines(p)), seq![Seq::<u8>::empty()]);
        lemma_prun_one(s1, Seq::<u8>::empty());
        let s2 = PState { ok: true, doc: p, fresh: true };
        assert(pstep(s1, Seq::<u8>::empty()) == s2);
        assert(has_header(x[k - 1]));
        lemma_prun_header_group(s2, g);
    }
}

proof fn lemma_group_lines_no_lf(g: GroupS)
    ensures
        forall|k: int| 0 <= k < group_lines(g).len() ==> no_lf(#[trigger] group_lines(g)[k]),
{
    lemma_escape_all_index(g.names);
    let gl = group_lines(g);
    assert forall|k: int| 0 <= k < gl.len() implies no_lf(#[trigger] gl[k]) by {
        match g.header {
            Some(h) => {
                if k == 0 {
                    lemma_escape_printable(h);
                    let hl = escape(h) + seq![58u8];
                    assert(gl[0] == hl);
                    assert forall|i: int| 0 <= i < hl.len() implies hl[i] != 10 by {
                        if i < escape(h).len() {
                            assert(hl[i] == escape(h)[i]);
                        }
                    }
                } else {
                    assert(gl[k] == escape_all(g.names)[k - 1]);
                    lemma_escape_no_lf(g.names[k - 1]);
                }
            },
            None => {
                assert(gl[k] == escape_all(g.names)[k]);
                lemma_escape_no_lf(g.names[k]);
            },
        }
    }
}

proof fn lemma_join_no_lf(gs: Seq<Seq<Seq<u8>>>)
    requires
        forall|i: int, k: int| 0 <= i < gs.len() && 0 <= k < gs[i].len() ==> no_lf(#[trigger] gs[i][k]),
    ensures
        forall|k: int| 0 <= k < join_groups(gs).len() ==> no_lf(#[trigger] join_groups(gs)[k]),
    decreases gs.len(),
{
    let j = join_groups(gs);
    if gs.len() == 1 {
        assert forall|k: int| 0 <= k < j.len() implies no_lf(#[trigger] j[k]) by {
            assert(j[k] == gs[0][k]);
        }
    } else if gs.len() > 1 {
        let p = gs.subrange(0, gs.len() - 1);
        lemma_join_no_lf(p);
        let jp = join_groups(p);
        let last = gs[gs.len() - 1];
        assert(j == jp + seq![Seq::<u8>::empty()] + last);
        assert forall|k: int| 0 <= k < j.len() implies no_lf(#[trigger] j[k]) by {
            if k < jp.len() {
                assert(j[k] == jp[k]);
            } else if k == jp.len() {
                assert(j[k] == Seq::<u8>::empty());
            } else {
                assert(j[k] == last[k - jp.len() - 1]);
            }
        }
    }
}

proof fn lemma_unparse_lines_no_lf(x: Seq<GroupS>)
    ensures
        forall|k: int|
            0 <= k < join_groups(groups_lines(x)).len() ==> no_lf(#[trigger] join_groups(groups_lines(x))[k]),
{
    let gs = groups_lines(x);
    lemma_groups_lines_len(x);
    assert forall|i: int, k: int| 0 <= i < gs.len() && 0 <= k < gs[i].len() implies no_lf(#[trigger] gs[i][k]) by {
        lemma_groups_lines_index(x, i);
        lemma_group_lines_no_lf(x[i]);
    }
    lemma_join_no_lf(gs);
}

proof fn lemma_groups_lines_index(x: Seq<GroupS>, i: int)
    requires
        0 <= i < x.len(),
    ensures
        groups_lines(x)[i] == group_lines(x[i]),
    decreases x.len(),
{
    let t = x.subrange(1, x.len() as int);
    assert(groups_lines(x) == seq![group_lines(x[0])] + groups_lines(t));
    lemma_groups_lines_len(t);
    if i > 0 {
        lemma_groups_lines_index(t, i - 1);
        assert(t[i - 1] == x[i]);
        assert(groups_lines(x)[i] == groups_lines(t)[i - 1]);
    }
}

/// The paper's round trip, at spec level: parse(unparse(x)) = x.
proof fn lemma_round_trip(x: Seq<GroupS>)
    requires
        wf(x),
    ensures
        parse_doc(unparse(x)) == Some(x),
{
    let lines = join_groups(groups_lines(x));
    lemma_unparse_lines_no_lf(x);
    lemma_split_lines_bytes(Seq::<Seq<u8>>::empty(), lines);
    assert(Seq::<Seq<u8>>::empty() + lines =~= lines);
    assert(split_init() == (SplitS { lines: Seq::<Seq<u8>>::empty(), cur: Seq::<u8>::empty() }));
    assert(split_lines(unparse(x)) == Some(lines));
    if x.len() > 0 {
        lemma_prun_doc(x);
    } else {
        assert(groups_lines(x) =~= Seq::<Seq<Seq<u8>>>::empty());
        assert(lines =~= Seq::<Seq<u8>>::empty());
    }
}

// ---- reverse direction: whatever parses, unparses back (strictness) ----

proof fn lemma_join_extend(gs: Seq<Seq<Seq<u8>>>, l: Seq<u8>)
    requires
        gs.len() > 0,
    ensures
        join_groups(gs.update(gs.len() - 1, gs[gs.len() - 1].push(l))) == join_groups(gs).push(l),
{
    let gs2 = gs.update(gs.len() - 1, gs[gs.len() - 1].push(l));
    if gs.len() == 1 {
        assert(join_groups(gs2) == gs2[0]);
    } else {
        assert(gs2.subrange(0, gs2.len() - 1) =~= gs.subrange(0, gs.len() - 1));
        assert(join_groups(gs2) =~= join_groups(gs).push(l));
    }
}

proof fn lemma_join_push(gs: Seq<Seq<Seq<u8>>>, g: Seq<Seq<u8>>)
    ensures
        join_groups(gs.push(g)) == if gs.len() == 0 {
            g
        } else {
            join_groups(gs) + seq![Seq::<u8>::empty()] + g
        },
{
    let gs2 = gs.push(g);
    if gs.len() > 0 {
        assert(gs2.subrange(0, gs2.len() - 1) =~= gs);
    }
}

pub open spec fn prun_inv(lines: Seq<Seq<u8>>, st: PState) -> bool {
    &&& wf(st.doc)
    &&& st.doc.len() == 0 ==> lines.len() == 0 && st.fresh
    &&& st.doc.len() > 0 ==> lines == join_groups(groups_lines(st.doc)) + (if st.fresh {
        seq![Seq::<u8>::empty()]
    } else {
        Seq::<Seq<u8>>::empty()
    })
}

proof fn lemma_prun_reverse(lines: Seq<Seq<u8>>)
    ensures
        prun(pinit(), lines).ok ==> prun_inv(lines, prun(pinit(), lines)),
    decreases lines.len(),
{
    let st = prun(pinit(), lines);
    if lines.len() == 0 || !st.ok {
        return;
    }
    let p = lines.subrange(0, lines.len() - 1);
    let l = lines[lines.len() - 1];
    lemma_prun_reverse(p);
    let s0 = prun(pinit(), p);
    assert(lines =~= p.push(l));
    assert(st == pstep(s0, l));
    assert(s0.ok);
    lemma_groups_lines_len(s0.doc);
    if l.len() == 0 {
        assert(!s0.fresh && s0.doc.len() > 0);
        assert(p =~= join_groups(groups_lines(s0.doc)));
        assert(l =~= Seq::<u8>::empty());
        assert(lines =~= join_groups(groups_lines(s0.doc)) + seq![Seq::<u8>::empty()]);
    } else {
        lemma_dec_reverse(l);
        let (v, h) = dec_line(l).unwrap();
        assert(l == escape(v) + suffix(h));
        if h {
            let g = GroupS { header: Some(v), names: seq![] };
            assert(st.doc == s0.doc.push(g));
            lemma_groups_lines_push(s0.doc, g);
            lemma_join_push(groups_lines(s0.doc), group_lines(g));
            assert(escape_all(Seq::<Seq<u8>>::empty()) == Seq::<Seq<u8>>::empty());
            assert(group_lines(g) =~= seq![l]);
            if s0.doc.len() == 0 {
                assert(lines =~= seq![l]);
                assert(join_groups(groups_lines(st.doc)) =~= seq![l]);
            } else {
                assert(lines =~= join_groups(groups_lines(st.doc)));
            }
            assert(wf(st.doc)) by {
                assert forall|i: int, j: int|
                    0 <= i < st.doc.len() && 0 <= j < st.doc[i].names.len() implies (#[trigger] st.doc[i].names[j]).len()
                    > 0 by {
                    assert(st.doc[i] == s0.doc[i]);
                }
                assert forall|i: int| 0 < i < st.doc.len() implies has_header(#[trigger] st.doc[i]) by {
                    if i < s0.doc.len() {
                        assert(st.doc[i] == s0.doc[i]);
                    }
                }
                if s0.doc.len() > 0 {
                    assert(st.doc[0] == s0.doc[0]);
                }
            }
        } else {
            assert(v.len() > 0) by {
                if v.len() == 0 {
                    assert(escape(v) =~= Seq::<u8>::empty());
                    assert(l =~= Seq::<u8>::empty());
                }
            }
            assert(l =~= escape(v));
            if s0.fresh {
                let g = GroupS { header: None, names: seq![v] };
                assert(s0.doc.len() == 0 && p.len() == 0);
                assert(st.doc == seq![g]);
                assert(seq![g] =~= Seq::<GroupS>::empty().push(g));
                lemma_groups_lines_push(Seq::<GroupS>::empty(), g);
                assert(groups_lines(Seq::<GroupS>::empty()) == Seq::<Seq<Seq<u8>>>::empty());
                lemma_join_push(Seq::<Seq<Seq<u8>>>::empty(), group_lines(g));
                lemma_escape_all_push(Seq::<Seq<u8>>::empty(), v);
                assert(Seq::<Seq<u8>>::empty().push(v) =~= seq![v]);
                assert(escape_all(Seq::<Seq<u8>>::empty()) == Seq::<Seq<u8>>::empty());
                assert(group_lines(g) =~= seq![l]);
                assert(lines =~= seq![l]);
                assert(wf(st.doc)) by {
                    assert forall|i: int, j: int|
                        0 <= i < st.doc.len() && 0 <= j < st.doc[i].names.len() implies (#[trigger] st.doc[i].names[j]).len()
                        > 0 by {
                        assert(st.doc[i] == g);
                    }
                }
            } else {
                let d = s0.doc;
                let last = d[d.len() - 1];
                let last2 = GroupS { header: last.header, names: last.names.push(v) };
                assert(st.doc == d.update(d.len() - 1, last2));
                lemma_escape_all_push(last.names, v);
                assert(group_lines(last2) =~= group_lines(last).push(l));
                let gl = groups_lines(d);
                lemma_groups_lines_index(d, d.len() - 1);
                assert(groups_lines(st.doc) =~= gl.update(gl.len() - 1, gl[gl.len() - 1].push(l))) by {
                    lemma_groups_lines_len(st.doc);
                    assert forall|i: int| 0 <= i < gl.len() implies #[trigger] groups_lines(st.doc)[i] == gl.update(
                        gl.len() - 1,
                        gl[gl.len() - 1].push(l),
                    )[i] by {
                        lemma_groups_lines_index(st.doc, i);
                        lemma_groups_lines_index(d, i);
                    }
                }
                lemma_join_extend(gl, l);
                assert(lines =~= join_groups(groups_lines(st.doc)) + Seq::<Seq<u8>>::empty());
                assert(wf(st.doc)) by {
                    assert forall|i: int, j: int|
                        0 <= i < st.doc.len() && 0 <= j < st.doc[i].names.len() implies (#[trigger] st.doc[i].names[j]).len()
                        > 0 by {
                        if i < d.len() - 1 {
                            assert(st.doc[i] == d[i]);
                        } else if j < last.names.len() {
                            assert(st.doc[i].names[j] == last.names[j]);
                        }
                    }
                    assert forall|i: int| 0 < i < st.doc.len() implies has_header(#[trigger] st.doc[i]) by {
                        if i < d.len() - 1 {
                            assert(st.doc[i] == d[i]);
                        }
                    }
                }
            }
        }
    }
}

proof fn lemma_parse_reverse(s: Seq<u8>)
    ensures
        parse_doc(s) matches Some(d) ==> wf(d) && unparse(d) == s,
{
    if let Some(d) = parse_doc(s) {
        lemma_split_reverse(s);
        let st = split_run(split_init(), s);
        assert(st.cur.len() == 0);
        assert(s =~= lines_bytes(st.lines));
        lemma_prun_reverse(st.lines);
        let ps = prun(pinit(), st.lines);
        if ps.doc.len() == 0 {
            assert(st.lines.len() == 0);
            assert(groups_lines(d) =~= Seq::<Seq<Seq<u8>>>::empty());
            assert(join_groups(groups_lines(d)) =~= st.lines);
        } else {
            assert(st.lines =~= join_groups(groups_lines(d)));
        }
    }
}

proof fn lemma_unparse_injective(x: Seq<GroupS>, y: Seq<GroupS>)
    requires
        wf(x),
        wf(y),
        unparse(x) == unparse(y),
    ensures
        x == y,
{
    lemma_round_trip(x);
    lemma_round_trip(y);
}
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
    let mut n: u64 = acc;
    let mut i: usize = 0;
    assert(chunk@.subrange(0, chunk@.len() as int) =~= chunk@);
    while i < chunk.len()
        invariant
            i <= chunk.len(),
            n + count_newlines(chunk@.subrange(i as int, chunk@.len() as int)) == acc + count_newlines(chunk@),
        decreases chunk.len() - i,
    {
        let ghost t = chunk@.subrange(i as int, chunk@.len() as int);
        assert(t.subrange(1, t.len() as int) =~= chunk@.subrange(i + 1, chunk@.len() as int));
        assert(t[0] == chunk@[i as int]);
        if chunk[i] == 10 {
            if n == u64::MAX {
                return None;
            }
            n = n + 1;
        }
        i += 1;
    }
    assert(chunk@.subrange(chunk@.len() as int, chunk@.len() as int) =~= Seq::<u8>::empty());
    Some(n)
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
    lemma_unparse_injective(x, y);
    // </vc-code>
}

/// P3 (D9): vls's stdout bytes are exactly the unparse of its AST.
pub proof fn theorem_vls_unparses(req: RequestS)
    ensures
        lines_bytes(ls(req).stdout) == unparse(ast_of(req)),
{
    // <vc-code>
    lemma_vls_unparses(req);
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
    lemma_vls_ast_wf(req);
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
    lemma_count_files(req);
    // </vc-code>
}

/// P5 (D12): counting chunk by chunk gives the count of the whole input.
pub proof fn theorem_count_concat(a: Seq<u8>, b: Seq<u8>)
    ensures
        count_newlines(a + b) == count_newlines(a) + count_newlines(b),
{
    // <vc-code>
    lemma_count_concat(a, b);
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
