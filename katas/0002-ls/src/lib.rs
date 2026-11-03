//! Kata 0002 — `vls`, a verified replacement for `ls`: the verified core.
//! Intent: intents/0002-ls.md
//!
//! The trusted shell (src/main.rs) gathers facts from the OS into a
//! `Request`; `run` turns it into every stdout line, every stderr line and
//! the exit code. `run` is specified as an exact function: `ls(req@)`.
//!
//! Everything OUTSIDE the `<vc-helpers>` / `<vc-code>` regions is the frozen,
//! human-approved specification (hashed in specs.lock.json).
#![forbid(unsafe_code)]

use vstd::prelude::*;

verus! {

// ===========================================================================
// Interface (exec types) and their mathematical views
// ===========================================================================

/// What the shell found for one command-line operand (D9).
pub enum Outcome {
    /// `metadata()` failed; the OS error text.
    Missing(Vec<u8>),
    /// A directory that could not be read; the OS error text.
    Unreadable(Vec<u8>),
    /// Anything that is not a directory.
    File,
    /// A directory and the raw names `read_dir` returned (any order).
    Dir(Vec<Vec<u8>>),
}

pub struct Operand {
    /// The operand exactly as typed, as raw bytes (D13).
    pub name: Vec<u8>,
    pub outcome: Outcome,
}

pub struct Request {
    /// `-a` (D5)
    pub all: bool,
    /// `-r` (D7)
    pub reverse: bool,
    /// In argument order; the shell substitutes `.` if none were given (D8).
    pub operands: Vec<Operand>,
}

pub struct Response {
    /// Lines to write to stdout, each followed by "\n".
    pub stdout: Vec<Vec<u8>>,
    /// Lines to write to stderr, each followed by "\n".
    pub stderr: Vec<Vec<u8>>,
    pub exit: u8,
}

pub enum OutcomeS {
    Missing(Seq<u8>),
    Unreadable(Seq<u8>),
    File,
    Dir(Seq<Seq<u8>>),
}

pub struct OperandS {
    pub name: Seq<u8>,
    pub outcome: OutcomeS,
}

pub struct RequestS {
    pub all: bool,
    pub reverse: bool,
    pub operands: Seq<OperandS>,
}

pub struct ResponseS {
    pub stdout: Seq<Seq<u8>>,
    pub stderr: Seq<Seq<u8>>,
    pub exit: u8,
}

pub open spec fn lines_view(v: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    Seq::new(v.len(), |i: int| v[i]@)
}

impl View for Outcome {
    type V = OutcomeS;

    open spec fn view(&self) -> OutcomeS {
        match self {
            Outcome::Missing(m) => OutcomeS::Missing(m@),
            Outcome::Unreadable(m) => OutcomeS::Unreadable(m@),
            Outcome::File => OutcomeS::File,
            Outcome::Dir(es) => OutcomeS::Dir(lines_view(es@)),
        }
    }
}

impl View for Operand {
    type V = OperandS;

    open spec fn view(&self) -> OperandS {
        OperandS { name: self.name@, outcome: self.outcome@ }
    }
}

impl View for Request {
    type V = RequestS;

    open spec fn view(&self) -> RequestS {
        RequestS {
            all: self.all,
            reverse: self.reverse,
            operands: Seq::new(self.operands@.len(), |i: int| self.operands@[i]@),
        }
    }
}

impl View for Response {
    type V = ResponseS;

    open spec fn view(&self) -> ResponseS {
        ResponseS { stdout: lines_view(self.stdout@), stderr: lines_view(self.stderr@), exit: self.exit }
    }
}

// ===========================================================================
// Specification
// ===========================================================================

// ---- D4: raw bytes, lexicographic byte order ------------------------------

/// `a` sorts strictly before `b` (bytewise; a proper prefix sorts first).
#[verifier::memoize]
pub open spec fn lex_lt(a: Seq<u8>, b: Seq<u8>) -> bool
    decreases a.len(),
{
    if b.len() == 0 {
        false
    } else if a.len() == 0 {
        true
    } else if a[0] != b[0] {
        a[0] < b[0]
    } else {
        lex_lt(a.subrange(1, a.len() as int), b.subrange(1, b.len() as int))
    }
}

/// D7: `-r` reverses every ordering.
pub open spec fn before(a: Seq<u8>, b: Seq<u8>, reverse: bool) -> bool {
    if reverse {
        lex_lt(b, a)
    } else {
        lex_lt(a, b)
    }
}

// ---- D12: escaping ---------------------------------------------------------

pub open spec fn hex_digit(d: u8) -> u8 {
    if d < 10 {
        (48 + d) as u8  // '0'..'9'
    } else {
        (87 + d) as u8  // 'a'..'f'  (97 + d - 10)
    }
}

pub open spec fn escape_byte(b: u8) -> Seq<u8> {
    if b == 92 {
        seq![92u8, 92u8]  // `\` -> `\\`
    } else if b == 10 {
        seq![92u8, 110u8]  // LF -> `\n`
    } else if b == 9 {
        seq![92u8, 116u8]  // TAB -> `\t`
    } else if 32 <= b && b <= 126 {
        seq![b]  // printable ASCII
    } else {
        seq![92u8, 120u8, hex_digit(b / 16), hex_digit(b % 16)]  // `\xHH`
    }
}

#[verifier::memoize]
pub open spec fn escape(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![]
    } else {
        escape_byte(s[0]) + escape(s.subrange(1, s.len() as int))
    }
}

#[verifier::memoize]
pub open spec fn escape_all(names: Seq<Seq<u8>>) -> Seq<Seq<u8>>
    decreases names.len(),
{
    if names.len() == 0 {
        seq![]
    } else {
        seq![escape(names[0])] + escape_all(names.subrange(1, names.len() as int))
    }
}

// ---- D5, D10: which names a directory listing shows ------------------------

pub open spec fn dot() -> Seq<u8> {
    seq![46u8]
}

pub open spec fn dotdot() -> Seq<u8> {
    seq![46u8, 46u8]
}

pub open spec fn is_hidden(n: Seq<u8>) -> bool {
    n.len() > 0 && n[0] == 46
}

/// A received entry is shown iff it is a real name (D10) and not hidden,
/// unless `-a` (D5).
pub open spec fn shown(n: Seq<u8>, all: bool) -> bool {
    &&& n.len() > 0  // D10: drop empty names
    &&& n != dot()  // D10: drop received `.`
    &&& n != dotdot()  // D10: drop received `..`
    &&& (all || !is_hidden(n))  // D5
}

#[verifier::memoize]
pub open spec fn shown_entries(es: Seq<Seq<u8>>, all: bool) -> Seq<Seq<u8>>
    decreases es.len(),
{
    if es.len() == 0 {
        seq![]
    } else {
        (if shown(es[0], all) {
            seq![es[0]]
        } else {
            seq![]
        }) + shown_entries(es.subrange(1, es.len() as int), all)
    }
}

/// D5: `-a` adds `.` and `..`.
pub open spec fn listed_names(es: Seq<Seq<u8>>, all: bool) -> Seq<Seq<u8>> {
    if all {
        shown_entries(es, true) + seq![dot(), dotdot()]
    } else {
        shown_entries(es, false)
    }
}

// ---- D4, D6, D7, D10: sorting -----------------------------------------------

/// Insert into a sorted list; an equal name is collapsed (D10).
#[verifier::memoize]
pub open spec fn insert_unique(x: Seq<u8>, s: Seq<Seq<u8>>, reverse: bool) -> Seq<Seq<u8>>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![x]
    } else if x == s[0] {
        s
    } else if before(x, s[0], reverse) {
        seq![x] + s
    } else {
        seq![s[0]] + insert_unique(x, s.subrange(1, s.len() as int), reverse)
    }
}

/// The distinct names of `s`, in strictly increasing order (decreasing with `-r`).
#[verifier::memoize]
pub open spec fn sort_unique(s: Seq<Seq<u8>>, reverse: bool) -> Seq<Seq<u8>>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![]
    } else {
        insert_unique(s[s.len() - 1], sort_unique(s.subrange(0, s.len() - 1), reverse), reverse)
    }
}

/// Insert after every operand that does not sort strictly after `x`:
/// equal names keep argument order (D14).
#[verifier::memoize]
pub open spec fn insert_op(x: OperandS, s: Seq<OperandS>, reverse: bool) -> Seq<OperandS>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![x]
    } else if before(x.name, s[0].name, reverse) {
        seq![x] + s
    } else {
        seq![s[0]] + insert_op(x, s.subrange(1, s.len() as int), reverse)
    }
}

/// Stable sort of operands by name (D13, D14, D7).
#[verifier::memoize]
pub open spec fn sort_ops(s: Seq<OperandS>, reverse: bool) -> Seq<OperandS>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![]
    } else {
        insert_op(s[s.len() - 1], sort_ops(s.subrange(0, s.len() - 1), reverse), reverse)
    }
}

// ---- D13, D14: operand groups ---------------------------------------------

pub open spec fn is_file(o: OutcomeS) -> bool {
    match o {
        OutcomeS::File => true,
        _ => false,
    }
}

pub open spec fn is_dir(o: OutcomeS) -> bool {
    match o {
        OutcomeS::Dir(_) => true,
        _ => false,
    }
}

pub open spec fn entries_of(o: OutcomeS) -> Seq<Seq<u8>> {
    match o {
        OutcomeS::Dir(es) => es,
        _ => seq![],
    }
}

#[verifier::memoize]
pub open spec fn file_ops(ops: Seq<OperandS>) -> Seq<OperandS>
    decreases ops.len(),
{
    if ops.len() == 0 {
        seq![]
    } else {
        (if is_file(ops[0].outcome) {
            seq![ops[0]]
        } else {
            seq![]
        }) + file_ops(ops.subrange(1, ops.len() as int))
    }
}

#[verifier::memoize]
pub open spec fn dir_ops(ops: Seq<OperandS>) -> Seq<OperandS>
    decreases ops.len(),
{
    if ops.len() == 0 {
        seq![]
    } else {
        (if is_dir(ops[0].outcome) {
            seq![ops[0]]
        } else {
            seq![]
        }) + dir_ops(ops.subrange(1, ops.len() as int))
    }
}

#[verifier::memoize]
pub open spec fn op_names(ops: Seq<OperandS>) -> Seq<Seq<u8>>
    decreases ops.len(),
{
    if ops.len() == 0 {
        seq![]
    } else {
        seq![ops[0].name] + op_names(ops.subrange(1, ops.len() as int))
    }
}

/// D13: all file operands, as typed, sorted (duplicates kept), escaped.
pub open spec fn file_group(req: RequestS) -> Seq<Seq<u8>> {
    escape_all(op_names(sort_ops(file_ops(req.operands), req.reverse)))
}

/// D15: headers iff 2 or more operands were given (failed ones count).
pub open spec fn headers_on(req: RequestS) -> bool {
    req.operands.len() >= 2
}

/// D15, D5, D10, D4/D7, D12: one directory's group.
pub open spec fn dir_group(op: OperandS, req: RequestS) -> Seq<Seq<u8>> {
    (if headers_on(req) {
        seq![escape(op.name) + seq![58u8]]  // `NAME:`
    } else {
        seq![]
    }) + escape_all(sort_unique(listed_names(entries_of(op.outcome), req.all), req.reverse))
}

#[verifier::memoize]
pub open spec fn dir_groups(dirs: Seq<OperandS>, req: RequestS) -> Seq<Seq<Seq<u8>>>
    decreases dirs.len(),
{
    if dirs.len() == 0 {
        seq![]
    } else {
        seq![dir_group(dirs[0], req)] + dir_groups(dirs.subrange(1, dirs.len() as int), req)
    }
}

/// D13, D14: the file group (if any file operand) first, then one group per
/// directory operand in sorted order. Missing/unreadable operands: none (D17).
pub open spec fn groups(req: RequestS) -> Seq<Seq<Seq<u8>>> {
    (if file_ops(req.operands).len() > 0 {
        seq![file_group(req)]
    } else {
        seq![]
    }) + dir_groups(sort_ops(dir_ops(req.operands), req.reverse), req)
}

/// D16: exactly one empty line between consecutive groups.
#[verifier::memoize]
pub open spec fn join_groups(gs: Seq<Seq<Seq<u8>>>) -> Seq<Seq<u8>>
    decreases gs.len(),
{
    if gs.len() == 0 {
        seq![]
    } else if gs.len() == 1 {
        gs[0]
    } else {
        join_groups(gs.subrange(0, gs.len() - 1)) + seq![seq![]] + gs[gs.len() - 1]
    }
}

// ---- D17, D18: errors and exit status --------------------------------------

/// `vls: cannot access `
pub open spec fn msg_cannot_access() -> Seq<u8> {
    seq![118u8, 108, 115, 58, 32, 99, 97, 110, 110, 111, 116, 32, 97, 99, 99, 101, 115, 115, 32]
}

/// `vls: cannot open directory `
pub open spec fn msg_cannot_open() -> Seq<u8> {
    seq![
        118u8, 108, 115, 58, 32, 99, 97, 110, 110, 111, 116, 32, 111, 112, 101, 110, 32, 100, 105,
        114, 101, 99, 116, 111, 114, 121, 32,
    ]
}

/// `: `
pub open spec fn colon_space() -> Seq<u8> {
    seq![58u8, 32u8]
}

pub open spec fn error_line(op: OperandS) -> Seq<Seq<u8>> {
    match op.outcome {
        OutcomeS::Missing(m) => seq![msg_cannot_access() + escape(op.name) + colon_space() + escape(m)],
        OutcomeS::Unreadable(m) => seq![msg_cannot_open() + escape(op.name) + colon_space() + escape(m)],
        _ => seq![],
    }
}

/// D17: one line per failed operand, in argument order.
#[verifier::memoize]
pub open spec fn error_lines(ops: Seq<OperandS>) -> Seq<Seq<u8>>
    decreases ops.len(),
{
    if ops.len() == 0 {
        seq![]
    } else {
        error_line(ops[0]) + error_lines(ops.subrange(1, ops.len() as int))
    }
}

pub open spec fn failed(o: OutcomeS) -> bool {
    match o {
        OutcomeS::Missing(_) | OutcomeS::Unreadable(_) => true,
        _ => false,
    }
}

#[verifier::memoize]
pub open spec fn any_failed(ops: Seq<OperandS>) -> bool
    decreases ops.len(),
{
    ops.len() > 0 && (failed(ops[0].outcome) || any_failed(ops.subrange(1, ops.len() as int)))
}

// ---- The whole run ---------------------------------------------------------

/// D2: the complete observable behaviour of `vls`.
pub open spec fn ls(req: RequestS) -> ResponseS {
    ResponseS {
        stdout: join_groups(groups(req)),  // D11-D16
        stderr: error_lines(req.operands),  // D17
        exit: if any_failed(req.operands) {
            2
        } else {
            0
        },  // D18
    }
}

// <vc-helpers>
// </vc-helpers>

/// D2, D20: total, never panics, output exactly `ls(req@)`.
pub fn run(req: &Request) -> (res: Response)
    ensures
        res@ == ls(req@),
{
    // <vc-code>
    assume(false);
    unreached()
    // </vc-code>
}

// ===========================================================================
// Spec tests: pin the spec to the intent's examples and properties.
// Checked by Verus; they never run.
// ===========================================================================

// ---- fixtures (names from the intent's Examples section) -------------------

spec fn n_a() -> Seq<u8> { seq![97u8] }               // a
spec fn n_b() -> Seq<u8> { seq![98u8] }               // b
spec fn n_z() -> Seq<u8> { seq![122u8] }              // z
spec fn n_dot_h() -> Seq<u8> { seq![46u8, 104] }      // .h
spec fn n_bang_x() -> Seq<u8> { seq![33u8, 120] }     // !x
spec fn n_d1() -> Seq<u8> { seq![100u8, 49] }         // d1
spec fn n_d2() -> Seq<u8> { seq![100u8, 50] }         // d2
spec fn n_d3() -> Seq<u8> { seq![100u8, 51] }         // d3
spec fn n_f1() -> Seq<u8> { seq![102u8, 49] }         // f1
spec fn n_dot_hid() -> Seq<u8> { seq![46u8, 104, 105, 100] }  // .hid
spec fn n_missing() -> Seq<u8> { seq![109u8, 105, 115, 115, 105, 110, 103] }  // missing
spec fn m_enoent() -> Seq<u8> { seq![69u8, 78, 79, 69, 78, 84] }  // ENOENT (stand-in OS text)

spec fn header(n: Seq<u8>) -> Seq<u8> { n + seq![58u8] }  // NAME:

spec fn d1_entries() -> Seq<Seq<u8>> { seq![n_b(), n_a(), n_dot_h(), n_bang_x()] }

spec fn op(name: Seq<u8>, outcome: OutcomeS) -> OperandS { OperandS { name, outcome } }
spec fn d1() -> OperandS { op(n_d1(), OutcomeS::Dir(d1_entries())) }
spec fn d2() -> OperandS { op(n_d2(), OutcomeS::Dir(seq![n_z()])) }
spec fn d3() -> OperandS { op(n_d3(), OutcomeS::Dir(seq![])) }
spec fn f1() -> OperandS { op(n_f1(), OutcomeS::File) }
spec fn hid() -> OperandS { op(n_dot_hid(), OutcomeS::File) }
spec fn missing() -> OperandS { op(n_missing(), OutcomeS::Missing(m_enoent())) }

spec fn req(all: bool, reverse: bool, operands: Seq<OperandS>) -> RequestS {
    RequestS { all, reverse, operands }
}

spec fn ok(stdout: Seq<Seq<u8>>) -> ResponseS { ResponseS { stdout, stderr: seq![], exit: 0 } }

// ---- Examples ----------------------------------------------------------------

proof fn spec_e1_bytewise_hidden() {
    // `vls d1` -> !x a b
    assert(ls(req(false, false, seq![d1()])) == ok(seq![n_bang_x(), n_a(), n_b()])) by (compute_only);
    // reject: alphabetic order; showing .h
    assert(ls(req(false, false, seq![d1()])).stdout != seq![n_a(), n_b(), n_bang_x()]) by (compute_only);
    assert(ls(req(false, false, seq![d1()])).stdout != seq![n_bang_x(), n_dot_h(), n_a(), n_b()]) by (compute_only);
}

proof fn spec_e2_all() {
    // `vls -a d1` -> !x . .. .h a b
    assert(ls(req(true, false, seq![d1()])) == ok(seq![n_bang_x(), dot(), dotdot(), n_dot_h(), n_a(), n_b()]))
        by (compute_only);
    // reject: dots forced first
    assert(ls(req(true, false, seq![d1()])).stdout != seq![dot(), dotdot(), n_bang_x(), n_dot_h(), n_a(), n_b()])
        by (compute_only);
}

proof fn spec_e3_all_reverse() {
    // `vls -ar d1` -> b a .h .. . !x
    assert(ls(req(true, true, seq![d1()])) == ok(seq![n_b(), n_a(), n_dot_h(), dotdot(), dot(), n_bang_x()]))
        by (compute_only);
    // reject: . and .. left unreversed
    assert(ls(req(true, true, seq![d1()])).stdout != seq![n_b(), n_a(), n_dot_h(), dot(), dotdot(), n_bang_x()])
        by (compute_only);
}

spec fn spec_e4_reverse_operands_r() -> RequestS { req(false, true, seq![d1(), d2(), f1()]) }

proof fn spec_e4_reverse_operands() {
    // `vls -r d1 d2 f1` -> f1 | d2: z | d1: b a !x
    assert(ls(spec_e4_reverse_operands_r()) == ok(seq![
        n_f1(), seq![],
        header(n_d2()), n_z(), seq![],
        header(n_d1()), n_b(), n_a(), n_bang_x(),
    ])) by (compute_only);
    // reject: dir groups in argument order
    assert(ls(spec_e4_reverse_operands_r()).stdout != seq![
        n_f1(), seq![],
        header(n_d1()), n_b(), n_a(), n_bang_x(), seq![],
        header(n_d2()), n_z(),
    ]) by (compute_only);
    // reject: file group last
    assert(ls(spec_e4_reverse_operands_r()).stdout != seq![
        header(n_d2()), n_z(), seq![],
        header(n_d1()), n_b(), n_a(), n_bang_x(), seq![],
        n_f1(),
    ]) by (compute_only);
}

spec fn spec_e5_files_and_empty_dir_r() -> RequestS { req(false, false, seq![f1(), hid(), d2(), d3()]) }

proof fn spec_e5_files_and_empty_dir() {
    // `vls f1 .hid d2 d3` -> .hid f1 | d2: z | d3:
    assert(ls(spec_e5_files_and_empty_dir_r()) == ok(seq![
        n_dot_hid(), n_f1(), seq![],
        header(n_d2()), n_z(), seq![],
        header(n_d3()),
    ])) by (compute_only);
    // reject: .hid hidden; no header for empty d3; trailing blank line
    assert(ls(spec_e5_files_and_empty_dir_r()).stdout != seq![n_f1(), seq![], header(n_d2()), n_z(), seq![], header(n_d3())]) by (compute_only);
    assert(ls(spec_e5_files_and_empty_dir_r()).stdout != seq![n_dot_hid(), n_f1(), seq![], header(n_d2()), n_z()]) by (compute_only);
    assert(ls(spec_e5_files_and_empty_dir_r()).stdout != seq![
        n_dot_hid(), n_f1(), seq![], header(n_d2()), n_z(), seq![], header(n_d3()), seq![],
    ]) by (compute_only);
}

spec fn spec_e6_missing_counts_for_headers_r() -> RequestS { req(false, false, seq![d1(), missing()]) }
spec fn spec_e6_missing_counts_for_headers_err() -> Seq<u8> { msg_cannot_access() + n_missing() + colon_space() + m_enoent() }

proof fn spec_e6_missing_counts_for_headers() {
    // `vls d1 missing` -> d1: !x a b ; stderr one line ; exit 2
    assert(ls(spec_e6_missing_counts_for_headers_r()) == ResponseS {
        stdout: seq![header(n_d1()), n_bang_x(), n_a(), n_b()],
        stderr: seq![spec_e6_missing_counts_for_headers_err()],
        exit: 2,
    }) by (compute_only);
    // reject: no header; exit 0
    assert(ls(spec_e6_missing_counts_for_headers_r()).stdout != seq![n_bang_x(), n_a(), n_b()]) by (compute_only);
    assert(ls(spec_e6_missing_counts_for_headers_r()).exit != 0) by (compute_only);
}

spec fn spec_e7_only_missing_r() -> RequestS { req(false, false, seq![missing()]) }

proof fn spec_e7_only_missing() {
    // `vls missing` -> nothing on stdout, one error, exit 2
    assert(ls(spec_e7_only_missing_r()).stdout == Seq::<Seq<u8>>::empty()) by (compute_only);
    assert(ls(spec_e7_only_missing_r()).stderr.len() == 1) by (compute_only);
    assert(ls(spec_e7_only_missing_r()).exit == 2) by (compute_only);
}

spec fn spec_e8_duplicate_operands_r() -> RequestS { req(false, false, seq![d1(), d1()]) }

proof fn spec_e8_duplicate_operands() {
    // `vls d1 d1` -> listed twice
    assert(ls(spec_e8_duplicate_operands_r()) == ok(seq![
        header(n_d1()), n_bang_x(), n_a(), n_b(), seq![],
        header(n_d1()), n_bang_x(), n_a(), n_b(),
    ])) by (compute_only);
    // reject: listed once
    assert(ls(spec_e8_duplicate_operands_r()).stdout != seq![header(n_d1()), n_bang_x(), n_a(), n_b()]) by (compute_only);
}

spec fn spec_e9_escaping_lf() -> Seq<u8> { seq![97u8, 10, 98] }  // a LF b
spec fn spec_e9_escaping_bs() -> Seq<u8> { seq![97u8, 92, 98] }  // a \ b
spec fn spec_e9_escaping_cafe() -> Seq<u8> { seq![99u8, 97, 102, 0xc3, 0xa9] }
spec fn spec_e9_escaping_r() -> RequestS { req(false, false, seq![op(n_d1(), OutcomeS::Dir(seq![spec_e9_escaping_lf(), spec_e9_escaping_bs(), spec_e9_escaping_cafe()]))]) }
    // raw order: a<LF>b < a\b (0x0a < 0x5c) < café ('a' < 'c')

proof fn spec_e9_escaping() {
    // entries `a<LF>b`, `back\slash`-like `a\b`, `café` (c a f 0xc3 0xa9)
    assert(ls(spec_e9_escaping_r()) == ok(seq![
        seq![97u8, 92, 110, 98],  // a\nb
        seq![97u8, 92, 92, 98],  // a\\b
        seq![99u8, 97, 102, 92, 120, 99, 51, 92, 120, 97, 57],  // caf\xc3\xa9
    ])) by (compute_only);
    // reject: raw newline inside a line
    assert(ls(spec_e9_escaping_r()).stdout[0] != spec_e9_escaping_lf()) by (compute_only);
    // reject: `\` unescaped: then `a<LF>b` and the literal name `a\nb` collide
    assert(escape(spec_e9_escaping_lf()) != escape(seq![97u8, 92, 110, 98])) by (compute_only);
}

spec fn spec_e10_robust_entries_r() -> RequestS { req(false, false, seq![op(n_d1(), OutcomeS::Dir(seq![n_a(), n_a(), dot(), seq![], n_b()]))]) }

proof fn spec_e10_robust_entries() {
    // core receives ["a","a",".","","b"] -> a b
    assert(ls(spec_e10_robust_entries_r()) == ok(seq![n_a(), n_b()])) by (compute_only);
    // reject: duplicate kept; empty line
    assert(ls(spec_e10_robust_entries_r()).stdout != seq![n_a(), n_a(), n_b()]) by (compute_only);
    assert(ls(spec_e10_robust_entries_r()).stdout != seq![n_a(), seq![], n_b()]) by (compute_only);
}

spec fn spec_d14_equal_names_keep_argument_order_first() -> OperandS { op(n_d1(), OutcomeS::Dir(seq![n_a()])) }
spec fn spec_d14_equal_names_keep_argument_order_second() -> OperandS { op(n_d1(), OutcomeS::Dir(seq![n_b()])) }

proof fn spec_d14_equal_names_keep_argument_order() {
    // two operands named d1 with different contents keep argument order, also with -r
    assert(ls(req(false, false, seq![spec_d14_equal_names_keep_argument_order_first(), spec_d14_equal_names_keep_argument_order_second()])).stdout == seq![
        header(n_d1()), n_a(), seq![], header(n_d1()), n_b(),
    ]) by (compute_only);
    assert(ls(req(false, true, seq![spec_d14_equal_names_keep_argument_order_first(), spec_d14_equal_names_keep_argument_order_second()])).stdout == seq![
        header(n_d1()), n_a(), seq![], header(n_d1()), n_b(),
    ]) by (compute_only);
}

spec fn spec_d17_unreadable_u() -> OperandS { op(n_d2(), OutcomeS::Unreadable(m_enoent())) }
spec fn spec_d17_unreadable_r() -> RequestS { req(false, false, seq![d1(), spec_d17_unreadable_u()]) }

proof fn spec_d17_unreadable() {
    // unreadable directory: error line, no stdout group, exit 2
    assert(ls(spec_d17_unreadable_r()) == ResponseS {
        stdout: seq![header(n_d1()), n_bang_x(), n_a(), n_b()],
        stderr: seq![msg_cannot_open() + n_d2() + colon_space() + m_enoent()],
        exit: 2,
    }) by (compute_only);
}

// ---- Properties --------------------------------------------------------------

/// D4: `lex_lt` is a strict total order.
proof fn lemma_lex_irreflexive(a: Seq<u8>)
    ensures
        !lex_lt(a, a),
    decreases a.len(),
{
    if a.len() > 0 {
        lemma_lex_irreflexive(a.subrange(1, a.len() as int));
    }
}

proof fn lemma_lex_transitive(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>)
    requires
        lex_lt(a, b),
        lex_lt(b, c),
    ensures
        lex_lt(a, c),
    decreases a.len(),
{
    if a.len() > 0 && a[0] == b[0] && b[0] == c[0] {
        lemma_lex_transitive(
            a.subrange(1, a.len() as int),
            b.subrange(1, b.len() as int),
            c.subrange(1, c.len() as int),
        );
    }
}

proof fn lemma_lex_total(a: Seq<u8>, b: Seq<u8>)
    requires
        a != b,
    ensures
        lex_lt(a, b) || lex_lt(b, a),
    decreases a.len(),
{
    if a.len() > 0 && b.len() > 0 && a[0] == b[0] {
        let (ta, tb) = (a.subrange(1, a.len() as int), b.subrange(1, b.len() as int));
        if ta == tb {
            assert(a =~= seq![a[0]] + ta);
            assert(b =~= seq![b[0]] + tb);
        }
        lemma_lex_total(ta, tb);
    } else if a.len() == 0 && b.len() == 0 {
        assert(a =~= b);
    }
}

pub open spec fn strictly_sorted(s: Seq<Seq<u8>>, reverse: bool) -> bool {
    forall|i: int, j: int| 0 <= i < j < s.len() ==> before(#[trigger] s[i], #[trigger] s[j], reverse)
}

proof fn lemma_before_order(a: Seq<u8>, b: Seq<u8>, c: Seq<u8>, reverse: bool)
    ensures
        !before(a, a, reverse),
        before(a, b, reverse) && before(b, c, reverse) ==> before(a, c, reverse),
        a != b ==> before(a, b, reverse) || before(b, a, reverse),
{
    lemma_lex_irreflexive(a);
    if before(a, b, reverse) && before(b, c, reverse) {
        if reverse {
            lemma_lex_transitive(c, b, a);
        } else {
            lemma_lex_transitive(a, b, c);
        }
    }
    if a != b {
        lemma_lex_total(a, b);
    }
}

proof fn lemma_contains_add(a: Seq<Seq<u8>>, b: Seq<Seq<u8>>)
    ensures
        forall|n: Seq<u8>| #![trigger (a + b).contains(n)] (a + b).contains(n) <==> (a.contains(n) || b.contains(n)),
{
    assert forall|n: Seq<u8>| #![trigger (a + b).contains(n)] (a + b).contains(n) <==> (a.contains(n) || b.contains(n)) by {
        if (a + b).contains(n) {
            let k = choose|k: int| 0 <= k < (a + b).len() && (a + b)[k] == n;
            if k < a.len() {
                assert(a[k] == n);
            } else {
                assert(b[k - a.len()] == n);
            }
        }
        if a.contains(n) {
            let k = choose|k: int| 0 <= k < a.len() && a[k] == n;
            assert((a + b)[k] == n);
        }
        if b.contains(n) {
            let k = choose|k: int| 0 <= k < b.len() && b[k] == n;
            assert((a + b)[k + a.len()] == n);
        }
    }
}

proof fn lemma_contains_split(s: Seq<Seq<u8>>, i: int)
    requires
        0 <= i <= s.len(),
    ensures
        s == s.subrange(0, i) + s.subrange(i, s.len() as int),
        forall|n: Seq<u8>| #![trigger s.contains(n)]
            s.contains(n) <==> (s.subrange(0, i).contains(n) || s.subrange(i, s.len() as int).contains(n)),
{
    assert(s =~= s.subrange(0, i) + s.subrange(i, s.len() as int));
    lemma_contains_add(s.subrange(0, i), s.subrange(i, s.len() as int));
}

proof fn lemma_contains_single(x: Seq<u8>)
    ensures
        forall|n: Seq<u8>| #![trigger seq![x].contains(n)] seq![x].contains(n) <==> n == x,
{
    assert forall|n: Seq<u8>| seq![x].contains(n) <==> n == x by {
        if n == x {
            assert(seq![x][0] == n);
        }
    }
}

proof fn lemma_sorted_tail(s: Seq<Seq<u8>>, reverse: bool)
    requires
        strictly_sorted(s, reverse),
        s.len() > 0,
    ensures
        strictly_sorted(s.subrange(1, s.len() as int), reverse),
        forall|j: int| 1 <= j < s.len() ==> before(s[0], #[trigger] s[j], reverse),
{
    let t = s.subrange(1, s.len() as int);
    assert forall|i: int, j: int| 0 <= i < j < t.len() implies before(t[i], t[j], reverse) by {
        assert(t[i] == s[i + 1] && t[j] == s[j + 1]);
    }
    assert forall|j: int| 1 <= j < s.len() implies before(s[0], #[trigger] s[j], reverse) by {
        assert(before(s[0], s[j], reverse));
    }
}

proof fn lemma_insert_unique(x: Seq<u8>, s: Seq<Seq<u8>>, reverse: bool)
    requires
        strictly_sorted(s, reverse),
    ensures
        strictly_sorted(insert_unique(x, s, reverse), reverse),
        forall|n: Seq<u8>| #![trigger insert_unique(x, s, reverse).contains(n)]
            insert_unique(x, s, reverse).contains(n) <==> (n == x || s.contains(n)),
    decreases s.len(),
{
    let r = insert_unique(x, s, reverse);
    lemma_contains_single(x);
    if s.len() == 0 {
        assert(r == seq![x]);
    } else if x == s[0] {
        assert(s.contains(s[0]));
    } else {
        lemma_contains_split(s, 1);
        let t = s.subrange(1, s.len() as int);
        let h = s.subrange(0, 1);
        assert(h =~= seq![s[0]]);
        lemma_contains_single(s[0]);
        lemma_sorted_tail(s, reverse);
        if before(x, s[0], reverse) {
            assert(r == seq![x] + s);
            lemma_contains_add(seq![x], s);
            assert forall|i: int, j: int| 0 <= i < j < r.len() implies before(r[i], r[j], reverse) by {
                if i == 0 {
                    if j > 1 {
                        lemma_before_order(x, s[0], s[j - 1], reverse);
                    }
                } else {
                    assert(r[i] == s[i - 1] && r[j] == s[j - 1]);
                }
            }
        } else {
            lemma_insert_unique(x, t, reverse);
            let rt = insert_unique(x, t, reverse);
            assert(r == seq![s[0]] + rt);
            lemma_contains_add(seq![s[0]], rt);
            lemma_before_order(x, s[0], x, reverse);  // so before(s[0], x)
            assert forall|i: int, j: int| 0 <= i < j < r.len() implies before(r[i], r[j], reverse) by {
                if i == 0 {
                    let y = rt[j - 1];
                    assert(r[j] == y);
                    assert(rt.contains(y));
                    if y != x {
                        assert(t.contains(y));
                        let k = choose|k: int| 0 <= k < t.len() && t[k] == y;
                        assert(s[k + 1] == y);
                    }
                } else {
                    assert(r[i] == rt[i - 1] && r[j] == rt[j - 1]);
                }
            }
        }
    }
}

/// P3 (sorting part): `sort_unique` yields each name of `s` once, strictly ordered.
proof fn lemma_sort_unique(s: Seq<Seq<u8>>, reverse: bool)
    ensures
        strictly_sorted(sort_unique(s, reverse), reverse),
        forall|n: Seq<u8>| #![trigger sort_unique(s, reverse).contains(n)] #![trigger s.contains(n)]
            sort_unique(s, reverse).contains(n) <==> s.contains(n),
    decreases s.len(),
{
    if s.len() > 0 {
        let p = s.subrange(0, s.len() - 1);
        let x = s[s.len() - 1];
        lemma_sort_unique(p, reverse);
        lemma_insert_unique(x, sort_unique(p, reverse), reverse);
        lemma_contains_split(s, s.len() - 1);
        assert(s.subrange(s.len() - 1, s.len() as int) =~= seq![x]);
        lemma_contains_single(x);
    } else {
        assert(sort_unique(s, reverse) =~= seq![]);
    }
}

proof fn lemma_shown_entries(es: Seq<Seq<u8>>, all: bool)
    ensures
        forall|n: Seq<u8>| #![trigger shown_entries(es, all).contains(n)] #![trigger es.contains(n)]
            shown_entries(es, all).contains(n) <==> (es.contains(n) && shown(n, all)),
    decreases es.len(),
{
    if es.len() > 0 {
        let t = es.subrange(1, es.len() as int);
        lemma_shown_entries(t, all);
        let head: Seq<Seq<u8>> = if shown(es[0], all) { seq![es[0]] } else { seq![] };
        assert(shown_entries(es, all) == head + shown_entries(t, all));
        lemma_contains_add(head, shown_entries(t, all));
        lemma_contains_single(es[0]);
        lemma_contains_split(es, 1);
        assert(es.subrange(0, 1) =~= seq![es[0]]);
        assert forall|n: Seq<u8>| !Seq::<Seq<u8>>::empty().contains(n) by {}
    } else {
        assert(shown_entries(es, all) =~= seq![]);
    }
}

/// P3: a directory listing (before escaping) is exactly the D5/D10 name set,
/// each name once, strictly increasing (strictly decreasing with `-r`).
proof fn spec_p3_faithful_listing(es: Seq<Seq<u8>>, all: bool, reverse: bool)
    ensures
        strictly_sorted(sort_unique(listed_names(es, all), reverse), reverse),
        forall|n: Seq<u8>| #![trigger sort_unique(listed_names(es, all), reverse).contains(n)]
            sort_unique(listed_names(es, all), reverse).contains(n) <==> ((es.contains(n) && shown(n, all)) || (
            all && (n == dot() || n == dotdot()))),
{
    lemma_shown_entries(es, all);
    lemma_sort_unique(listed_names(es, all), reverse);
    let l = listed_names(es, all);
    assert forall|n: Seq<u8>| l.contains(n) <==> ((es.contains(n) && shown(n, all)) || (all && (n == dot() || n
        == dotdot()))) by {
        let se = shown_entries(es, all);
        if all {
            if l.contains(n) {
                let k = choose|k: int| 0 <= k < l.len() && l[k] == n;
                if k < se.len() {
                    assert(se[k] == n);
                }
            }
            if es.contains(n) && shown(n, all) {
                let k = choose|k: int| 0 <= k < se.len() && se[k] == n;
                assert(l[k] == n);
            }
            if n == dot() {
                assert(l[se.len() as int] == n);
            }
            if n == dotdot() {
                assert(l[se.len() as int + 1] == n);
            }
        }
    }
}

/// Strictly sorted lists with the same elements are equal.
proof fn lemma_sorted_unique(a: Seq<Seq<u8>>, b: Seq<Seq<u8>>, reverse: bool)
    requires
        strictly_sorted(a, reverse),
        strictly_sorted(b, reverse),
        forall|n: Seq<u8>| a.contains(n) <==> b.contains(n),
    ensures
        a == b,
    decreases a.len(),
{
    if a.len() == 0 {
        if b.len() > 0 {
            assert(b.contains(b[0]));
        }
        assert(a =~= b);
    } else {
        assert(a.contains(a[0]));
        let k = choose|k: int| 0 <= k < b.len() && b[k] == a[0];
        assert(b.contains(b[0]));
        let m = choose|m: int| 0 <= m < a.len() && a[m] == b[0];
        lemma_before_order(a[0], b[0], a[0], reverse);
        if k > 0 {
            assert(before(b[0], b[k], reverse));
            if m > 0 {
                assert(before(a[0], a[m], reverse));
                lemma_before_order(b[0], a[0], b[0], reverse);
            } else {
                lemma_before_order(b[0], b[0], b[0], reverse);
            }
        }
        assert(a[0] == b[0]);
        let ta = a.subrange(1, a.len() as int);
        let tb = b.subrange(1, b.len() as int);
        assert forall|i: int, j: int| 0 <= i < j < ta.len() implies before(ta[i], ta[j], reverse) by {
            assert(ta[i] == a[i + 1] && ta[j] == a[j + 1]);
        }
        assert forall|i: int, j: int| 0 <= i < j < tb.len() implies before(tb[i], tb[j], reverse) by {
            assert(tb[i] == b[i + 1] && tb[j] == b[j + 1]);
        }
        assert forall|n: Seq<u8>| ta.contains(n) <==> tb.contains(n) by {
            if ta.contains(n) {
                let i = choose|i: int| 0 <= i < ta.len() && ta[i] == n;
                assert(a[i + 1] == n && before(a[0], a[i + 1], reverse));
                lemma_before_order(n, n, n, reverse);
                assert(b.contains(n));
                let j = choose|j: int| 0 <= j < b.len() && b[j] == n;
                assert(j != 0);
                assert(tb[j - 1] == n);
            }
            if tb.contains(n) {
                let i = choose|i: int| 0 <= i < tb.len() && tb[i] == n;
                assert(b[i + 1] == n && before(b[0], b[i + 1], reverse));
                lemma_before_order(n, n, n, reverse);
                assert(a.contains(n));
                let j = choose|j: int| 0 <= j < a.len() && a[j] == n;
                assert(j != 0);
                assert(ta[j - 1] == n);
            }
        }
        lemma_sorted_unique(ta, tb, reverse);
        assert(a =~= seq![a[0]] + ta);
        assert(b =~= seq![b[0]] + tb);
    }
}

pub open spec fn reversed<T>(s: Seq<T>) -> Seq<T> {
    Seq::new(s.len(), |i: int| s[s.len() - 1 - i])
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

/// P4: under `-r` a directory's entry lines are exactly reversed.
proof fn spec_p4_reverse_is_reverse(es: Seq<Seq<u8>>, all: bool)
    ensures
        escape_all(sort_unique(listed_names(es, all), true)) == reversed(
            escape_all(sort_unique(listed_names(es, all), false)),
        ),
{
    let l = listed_names(es, all);
    let up = sort_unique(l, false);
    let down = sort_unique(l, true);
    lemma_sort_unique(l, false);
    lemma_sort_unique(l, true);
    let rup = reversed(up);
    assert forall|i: int, j: int| 0 <= i < j < rup.len() implies before(rup[i], rup[j], true) by {
        assert(lex_lt(up[up.len() - 1 - j], up[up.len() - 1 - i]));
    }
    assert forall|n: Seq<u8>| rup.contains(n) <==> down.contains(n) by {
        if rup.contains(n) {
            let k = choose|k: int| 0 <= k < rup.len() && rup[k] == n;
            assert(up[up.len() - 1 - k] == n);
            assert(up.contains(n));
            assert(l.contains(n));
        }
        if down.contains(n) {
            assert(l.contains(n));
            assert(up.contains(n));
            let k = choose|k: int| 0 <= k < up.len() && up[k] == n;
            assert(rup[up.len() - 1 - k] == n);
        }
    }
    lemma_sorted_unique(down, rup, true);
    lemma_escape_all_index(up);
    lemma_escape_all_index(down);
    assert(escape_all(down) =~= reversed(escape_all(up)));
}

proof fn lemma_escape_byte_shape(b: u8)
    ensures
        escape_byte(b).len() > 0,
        escape_byte(b)[0] != 92 ==> escape_byte(b) == seq![b],
        escape_byte(b)[0] == 92 ==> escape_byte(b).len() >= 2,
        forall|i: int| 0 <= i < escape_byte(b).len() ==> 32 <= #[trigger] escape_byte(b)[i] <= 126,
{
}

proof fn lemma_escape_byte_prefix(x: u8, y: u8, r1: Seq<u8>, r2: Seq<u8>)
    requires
        escape_byte(x) + r1 == escape_byte(y) + r2,
    ensures
        x == y,
        r1 == r2,
{
    let (ex, ey) = (escape_byte(x), escape_byte(y));
    let s = ex + r1;
    lemma_escape_byte_shape(x);
    lemma_escape_byte_shape(y);
    assert(s[0] == ex[0] && s[0] == ey[0]);
    if ex[0] == 92 {
        assert(s[1] == ex[1] && s[1] == ey[1]);
        if ex[1] == 120 {
            assert(s[2] == ex[2] && s[2] == ey[2]);
            assert(s[3] == ex[3] && s[3] == ey[3]);
            assert(x == y);
        }
    }
    assert(ex == ey);
    assert(r1 =~= s.subrange(ex.len() as int, s.len() as int));
    assert(r2 =~= (ey + r2).subrange(ey.len() as int, s.len() as int));
}

/// P1: escaping is injective (distinct names never print the same line).
proof fn spec_p1_escape_injective(a: Seq<u8>, b: Seq<u8>)
    requires
        escape(a) == escape(b),
    ensures
        a == b,
    decreases a.len(),
{
    if a.len() == 0 || b.len() == 0 {
        if a.len() > 0 {
            lemma_escape_byte_shape(a[0]);
        }
        if b.len() > 0 {
            lemma_escape_byte_shape(b[0]);
        }
        assert(a =~= b);
    } else {
        let (ta, tb) = (a.subrange(1, a.len() as int), b.subrange(1, b.len() as int));
        lemma_escape_byte_prefix(a[0], b[0], escape(ta), escape(tb));
        spec_p1_escape_injective(ta, tb);
        assert(a =~= seq![a[0]] + ta);
        assert(b =~= seq![b[0]] + tb);
    }
}

/// P2: escaped names contain only printable ASCII (no newline, no control byte).
proof fn spec_p2_escape_printable(s: Seq<u8>)
    ensures
        forall|i: int| 0 <= i < escape(s).len() ==> 32 <= #[trigger] escape(s)[i] <= 126,
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.subrange(1, s.len() as int);
        spec_p2_escape_printable(t);
        lemma_escape_byte_shape(s[0]);
        let e = escape(s);
        let h = escape_byte(s[0]);
        assert forall|i: int| 0 <= i < e.len() implies 32 <= #[trigger] e[i] <= 126 by {
            if i < h.len() {
                assert(e[i] == h[i]);
            } else {
                assert(e[i] == escape(t)[i - h.len()]);
            }
        }
    }
}

/// P5: exit status 2 iff something was written to stderr.
proof fn spec_p5_errors_iff_exit_2(ops: Seq<OperandS>)
    ensures
        (ls(RequestS { all: false, reverse: false, operands: ops }).exit == 2) <==> error_lines(ops).len() > 0,
        any_failed(ops) <==> error_lines(ops).len() > 0,
    decreases ops.len(),
{
    if ops.len() > 0 {
        spec_p5_errors_iff_exit_2(ops.subrange(1, ops.len() as int));
    }
}

// P6 (determinism) holds by construction: `run` must return exactly `ls(req@)`.

} // verus!

// Runtime tests (cargo test): the intent's examples on the compiled core.
#[cfg(test)]
mod tests {
    use super::*;

    fn b(s: &str) -> Vec<u8> {
        s.as_bytes().to_vec()
    }

    fn dir(name: &str, entries: &[&[u8]]) -> Operand {
        Operand { name: b(name), outcome: Outcome::Dir(entries.iter().map(|e| e.to_vec()).collect()) }
    }

    fn file(name: &str) -> Operand {
        Operand { name: b(name), outcome: Outcome::File }
    }

    fn missing(name: &str) -> Operand {
        Operand { name: b(name), outcome: Outcome::Missing(b("No such file or directory")) }
    }

    fn d1() -> Operand {
        dir("d1", &[b"b", b"a", b".h", b"!x"])
    }

    fn out(all: bool, reverse: bool, operands: Vec<Operand>) -> (Vec<String>, Vec<String>, u8) {
        let r = run(&Request { all, reverse, operands });
        let s = |v: Vec<Vec<u8>>| v.into_iter().map(|l| String::from_utf8(l).unwrap()).collect();
        (s(r.stdout), s(r.stderr), r.exit)
    }

    #[test]
    fn e1_to_e3() {
        assert_eq!(out(false, false, vec![d1()]).0, ["!x", "a", "b"]);
        assert_eq!(out(true, false, vec![d1()]).0, ["!x", ".", "..", ".h", "a", "b"]);
        assert_eq!(out(true, true, vec![d1()]).0, ["b", "a", ".h", "..", ".", "!x"]);
    }

    #[test]
    fn e4_e5_layout() {
        assert_eq!(
            out(false, true, vec![d1(), dir("d2", &[b"z"]), file("f1")]).0,
            ["f1", "", "d2:", "z", "", "d1:", "b", "a", "!x"]
        );
        assert_eq!(
            out(false, false, vec![file("f1"), file(".hid"), dir("d2", &[b"z"]), dir("d3", &[])]).0,
            [".hid", "f1", "", "d2:", "z", "", "d3:"]
        );
    }

    #[test]
    fn e6_e7_errors() {
        let (o, e, x) = out(false, false, vec![d1(), missing("missing")]);
        assert_eq!(o, ["d1:", "!x", "a", "b"]);
        assert_eq!(e, ["vls: cannot access missing: No such file or directory"]);
        assert_eq!(x, 2);
        let (o, e, x) = out(false, false, vec![missing("missing")]);
        assert!(o.is_empty());
        assert_eq!(e.len(), 1);
        assert_eq!(x, 2);
    }

    #[test]
    fn e8_duplicates() {
        assert_eq!(out(false, false, vec![d1(), d1()]).0, ["d1:", "!x", "a", "b", "", "d1:", "!x", "a", "b"]);
    }

    #[test]
    fn e9_escaping() {
        assert_eq!(
            out(false, false, vec![dir("d", &[b"a\nb", b"a\\b", "caf\u{e9}".as_bytes()])]).0,
            ["a\\nb", "a\\\\b", "caf\\xc3\\xa9"]
        );
    }

    #[test]
    fn e10_robust() {
        assert_eq!(out(false, false, vec![dir("d", &[b"a", b"a", b".", b"", b"b"])]).0, ["a", "b"]);
    }
}
