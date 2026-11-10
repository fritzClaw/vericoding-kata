//! lib-security-property — reusable, verified injection safety for
//! line-based output (crate `security_property`).
//! Intent: intents/lib-security-property.md
//!
//! A `Codec` fixes an escape table, a record delimiter and a header marker.
//! For every Codec whose table meets C0–C4 (`codec_ok`), the library proves:
//!   - records: the delimiter count equals the record count, and the
//!     encoding is injective with a strict decoder;
//!   - grouped documents: parse(unparse(x)) = x (Hermerschmidt et al.,
//!     IEEE SPW 2015), injectivity, and a strict decoder.
//! `EscapeFamily` builds C-style tables whose conditions follow from a few
//! per-byte facts; `BackslashEscape` (vls's table) is a ready instance.
//! 0.2.0: token languages (`TokenLang`): untrusted data inside SQL, shell or
//! CSV text, with lex(unparse(ts)) = ts and verified SQL/shell/CSV instances.
//!
//! Everything OUTSIDE the `<vc-helpers>` / `<vc-code>` regions is the frozen,
//! human-approved specification (hashed in specs.lock.json).
#![forbid(unsafe_code)]

use vstd::prelude::*;

verus! {

// ===========================================================================
// Codec (D1, D3)
// ===========================================================================

/// `a` is a prefix of `b`.
pub open spec fn is_prefix(a: Seq<u8>, b: Seq<u8>) -> bool {
    a.len() <= b.len() && b.subrange(0, a.len() as int) == a
}

/// C0–C4 for an escape table `code`, delimiter `d` and header marker `m`.
pub open spec fn codec_conditions(code: spec_fn(u8) -> Seq<u8>, d: u8, m: u8) -> bool {
    // C0: delimiter and marker differ
    &&& d != m
    // C1: every code is non-empty
    &&& forall|b: u8| (#[trigger] code(b)).len() > 0
    // C2: no code contains the delimiter
    &&& forall|b: u8, i: int| 0 <= i < code(b).len() ==> (#[trigger] code(b)[i]) != d
    // C3: prefix-free: no code is a prefix of another byte's code
    &&& forall|b: u8, c: u8| b != c ==> !is_prefix(#[trigger] code(b), #[trigger] code(c))
    // C4: no code starts with the marker
    &&& forall|b: u8| (#[trigger] code(b))[0] != m
}

pub trait Codec: Sized {
    /// The escape table: the bytes byte `b` is written as.
    spec fn code(b: u8) -> Seq<u8>;

    /// The record delimiter (e.g. LF).
    spec fn delim() -> u8;

    /// The header marker (e.g. `:`).
    spec fn marker() -> u8;

    fn delim_exec() -> (r: u8)
        ensures
            r == Self::delim(),
    ;

    fn marker_exec() -> (r: u8)
        ensures
            r == Self::marker(),
    ;

    fn push_code(out: &mut Vec<u8>, b: u8)
        ensures
            final(out)@ == old(out)@ + Self::code(b),
    ;

    /// Every Codec must discharge C0–C4 (this is `codec_ok::<Self>()`).
    proof fn lemma_codec_ok()
        ensures
            codec_conditions(|b: u8| Self::code(b), Self::delim(), Self::marker()),
    ;
}

pub open spec fn codec_ok<C: Codec>() -> bool {
    codec_conditions(|b: u8| C::code(b), C::delim(), C::marker())
}

// ===========================================================================
// Encoding and records (D2)
// ===========================================================================

#[verifier::memoize]
pub open spec fn encode<C: Codec>(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![]
    } else {
        C::code(s[0]) + encode::<C>(s.subrange(1, s.len() as int))
    }
}

#[verifier::memoize]
pub open spec fn encode_all<C: Codec>(xs: Seq<Seq<u8>>) -> Seq<Seq<u8>>
    decreases xs.len(),
{
    if xs.len() == 0 {
        seq![]
    } else {
        seq![encode::<C>(xs[0])] + encode_all::<C>(xs.subrange(1, xs.len() as int))
    }
}

/// Lines written out: each followed by the delimiter.
#[verifier::memoize]
pub open spec fn unparse_lines<C: Codec>(lines: Seq<Seq<u8>>) -> Seq<u8>
    decreases lines.len(),
{
    if lines.len() == 0 {
        seq![]
    } else {
        lines[0] + seq![C::delim()] + unparse_lines::<C>(lines.subrange(1, lines.len() as int))
    }
}

/// Records: every value encoded and terminated by the delimiter.
pub open spec fn unparse_records<C: Codec>(rs: Seq<Seq<u8>>) -> Seq<u8> {
    unparse_lines::<C>(encode_all::<C>(rs))
}

/// The number of occurrences of byte `d`.
#[verifier::memoize]
pub open spec fn count_byte(s: Seq<u8>, d: u8) -> nat
    decreases s.len(),
{
    if s.len() == 0 {
        0
    } else {
        (if s[0] == d {
            1nat
        } else {
            0nat
        }) + count_byte(s.subrange(1, s.len() as int), d)
    }
}

// ===========================================================================
// Grouped documents (D2, D7)
// ===========================================================================

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

/// D7: well-formed documents.
pub open spec fn wf_document(doc: Seq<GroupS>) -> bool {
    &&& forall|i: int, j: int|
        0 <= i < doc.len() && 0 <= j < doc[i].names.len() ==> (#[trigger] doc[i].names[j]).len() > 0
    &&& forall|i: int| 0 < i < doc.len() ==> has_header(#[trigger] doc[i])
    &&& (doc.len() > 0 && !has_header(doc[0])) ==> doc[0].names.len() > 0
}

/// A group's lines: `encode(header) + marker` (if any), then the encoded names.
pub open spec fn group_lines<C: Codec>(g: GroupS) -> Seq<Seq<u8>> {
    (match g.header {
        Some(h) => seq![encode::<C>(h) + seq![C::marker()]],
        None => seq![],
    }) + encode_all::<C>(g.names)
}

#[verifier::memoize]
pub open spec fn groups_lines<C: Codec>(doc: Seq<GroupS>) -> Seq<Seq<Seq<u8>>>
    decreases doc.len(),
{
    if doc.len() == 0 {
        seq![]
    } else {
        seq![group_lines::<C>(doc[0])] + groups_lines::<C>(doc.subrange(1, doc.len() as int))
    }
}

/// Groups separated by exactly one empty line.
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

pub open spec fn unparse_document<C: Codec>(doc: Seq<GroupS>) -> Seq<u8> {
    unparse_lines::<C>(join_groups(groups_lines::<C>(doc)))
}

// ===========================================================================
// Escape family (D14)
// ===========================================================================

pub open spec fn hex_digit(d: u8) -> u8 {
    if d < 10 {
        (48 + d) as u8
    } else {
        (87 + d) as u8
    }
}

pub open spec fn is_hex_char(c: u8) -> bool {
    (48 <= c && c <= 57) || (97 <= c && c <= 102)
}

/// A C-style escape table: literal bytes as themselves, short escapes
/// `[esc, s]`, every other byte as `[esc, 'x', hex, hex]` (lowercase).
pub open spec fn family_code(esc: u8, literal: spec_fn(u8) -> bool, short: spec_fn(u8) -> Option<u8>, b: u8) -> Seq<
    u8,
> {
    if literal(b) {
        seq![b]
    } else {
        match short(b) {
            Some(s) => seq![esc, s],
            None => seq![esc, 120u8, hex_digit(b / 16), hex_digit(b % 16)],
        }
    }
}

/// F1–F3: the per-byte facts that imply C0–C4. `short_inv` witnesses that
/// short letters are distinct.
pub open spec fn family_conditions(
    esc: u8,
    literal: spec_fn(u8) -> bool,
    short: spec_fn(u8) -> Option<u8>,
    short_inv: spec_fn(u8) -> Option<u8>,
    d: u8,
    m: u8,
) -> bool {
    &&& d != m
    // F3: the escape byte, `x` and the hex digits never are the delimiter
    &&& esc != d
    &&& esc != m
    &&& d != 120
    &&& !is_hex_char(d)
    // F1: literals are never the escape byte, the delimiter or the marker
    &&& forall|b: u8| #[trigger] literal(b) ==> b != esc && b != d && b != m
    // F2: short escapes: only for non-literals, never `x` or the delimiter, distinct
    &&& forall|b: u8|
        (#[trigger] short(b)) matches Some(s) ==> !literal(b) && s != 120 && s != d && short_inv(s) == Some(b)
}

/// The table of an escape family, as a type (independent of `Codec`).
pub trait EscapeFamily: Sized {
    spec fn esc() -> u8;

    spec fn literal(b: u8) -> bool;

    spec fn short(b: u8) -> Option<u8>;

    fn esc_exec() -> (r: u8)
        ensures
            r == Self::esc(),
    ;

    fn literal_exec(b: u8) -> (r: bool)
        ensures
            r == Self::literal(b),
    ;

    fn short_exec(b: u8) -> (r: Option<u8>)
        ensures
            r == Self::short(b),
    ;
}

pub open spec fn family_table<F: EscapeFamily>(b: u8) -> Seq<u8> {
    family_code(F::esc(), |x: u8| F::literal(x), |x: u8| F::short(x), b)
}

// ===========================================================================
// Executable interface (D5)
// ===========================================================================

pub open spec fn seqs_view(v: Seq<Vec<u8>>) -> Seq<Seq<u8>> {
    Seq::new(v.len(), |i: int| v[i]@)
}

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
            names: seqs_view(self.names@),
        }
    }
}

pub open spec fn doc_view(d: Seq<Group>) -> Seq<GroupS> {
    Seq::new(d.len(), |i: int| d[i]@)
}

// ===========================================================================
// The ready-made codec: vls's table (D14)
// ===========================================================================

/// `\` -> `\\`, LF -> `\n`, TAB -> `\t`, `:` -> `\:`, other printable ASCII
/// as itself, everything else `\xHH`. Delimiter LF, header marker `:`.
pub struct BackslashEscape;

impl EscapeFamily for BackslashEscape {
    open spec fn esc() -> u8 {
        92
    }

    open spec fn literal(b: u8) -> bool {
        32 <= b && b <= 126 && b != 92 && b != 58
    }

    open spec fn short(b: u8) -> Option<u8> {
        if b == 92 {
            Some(92u8)
        } else if b == 10 {
            Some(110u8)
        } else if b == 9 {
            Some(116u8)
        } else if b == 58 {
            Some(58u8)
        } else {
            None
        }
    }

    fn esc_exec() -> (r: u8) {
        // <vc-code>
        92u8
        // </vc-code>
    }

    fn literal_exec(b: u8) -> (r: bool) {
        // <vc-code>
        32 <= b && b <= 126 && b != 92 && b != 58
        // </vc-code>
    }

    fn short_exec(b: u8) -> (r: Option<u8>) {
        // <vc-code>
        if b == 92 {
            Some(92u8)
        } else if b == 10 {
            Some(110u8)
        } else if b == 9 {
            Some(116u8)
        } else if b == 58 {
            Some(58u8)
        } else {
            None
        }
        // </vc-code>
    }
}

/// The inverse of `BackslashEscape`'s short escapes (F2 witness).
pub open spec fn backslash_short_inv(s: u8) -> Option<u8> {
    if s == 92 {
        Some(92u8)
    } else if s == 110 {
        Some(10u8)
    } else if s == 116 {
        Some(9u8)
    } else if s == 58 {
        Some(58u8)
    } else {
        None
    }
}

impl Codec for BackslashEscape {
    open spec fn code(b: u8) -> Seq<u8> {
        family_table::<BackslashEscape>(b)
    }

    open spec fn delim() -> u8 {
        10
    }

    open spec fn marker() -> u8 {
        58
    }

    fn delim_exec() -> (r: u8) {
        // <vc-code>
        10u8
        // </vc-code>
    }

    fn marker_exec() -> (r: u8) {
        // <vc-code>
        58u8
        // </vc-code>
    }

    fn push_code(out: &mut Vec<u8>, b: u8) {
        // <vc-code>
        family_push_code::<BackslashEscape>(out, b);
        // </vc-code>
    }

    proof fn lemma_codec_ok() {
        // <vc-code>
        let esc = BackslashEscape::esc();
        let literal = |x: u8| BackslashEscape::literal(x);
        let short = |x: u8| BackslashEscape::short(x);
        let short_inv = |s: u8| backslash_short_inv(s);
        assert(family_conditions(esc, literal, short, short_inv, 10, 58)) by {
            assert forall|b: u8| #[trigger] literal(b) implies b != esc && b != 10 && b != 58 by {}
            assert forall|b: u8|
                ((#[trigger] short(b)) matches Some(s) ==> !literal(b) && s != 120 && s != 10 && short_inv(s) == Some(b)) by {}
        }
        lemma_family_codec_ok(|b: u8| BackslashEscape::code(b), esc, literal, short, short_inv, 10, 58);
        // </vc-code>
    }
}

// <vc-helpers>

// ===== part 1: conditions, counting, encoders ================================

/// codec_ok in direct (non-closure) form.
proof fn lemma_ok<C: Codec>()
    requires
        codec_ok::<C>(),
    ensures
        C::delim() != C::marker(),
        forall|b: u8| (#[trigger] C::code(b)).len() > 0,
        forall|b: u8, i: int| 0 <= i < C::code(b).len() ==> (#[trigger] C::code(b)[i]) != C::delim(),
        forall|b: u8, c: u8| b != c ==> !is_prefix(#[trigger] C::code(b), #[trigger] C::code(c)),
        forall|b: u8| (#[trigger] C::code(b))[0] != C::marker(),
{
    let f = |b: u8| C::code(b);
    assert forall|b: u8| (#[trigger] C::code(b)).len() > 0 by {
        assert(f(b) == C::code(b));
    }
    assert forall|b: u8, i: int| 0 <= i < C::code(b).len() implies (#[trigger] C::code(b)[i]) != C::delim() by {
        assert(f(b) == C::code(b));
        assert(f(b)[i] != C::delim());
    }
    assert forall|b: u8, c: u8| b != c implies !is_prefix(#[trigger] C::code(b), #[trigger] C::code(c)) by {
        assert(f(b) == C::code(b) && f(c) == C::code(c));
        assert(!is_prefix(f(b), f(c)));
    }
    assert forall|b: u8| (#[trigger] C::code(b))[0] != C::marker() by {
        assert(f(b) == C::code(b));
        assert(f(b)[0] != C::marker());
    }
}

proof fn lemma_count_concat(a: Seq<u8>, b: Seq<u8>, d: u8)
    ensures
        count_byte(a + b, d) == count_byte(a, d) + count_byte(b, d),
    decreases a.len(),
{
    if a.len() > 0 {
        let t = a.subrange(1, a.len() as int);
        lemma_count_concat(t, b, d);
        assert((a + b).subrange(1, (a + b).len() as int) =~= t + b);
        assert((a + b)[0] == a[0]);
    } else {
        assert(a + b =~= b);
    }
}

pub open spec fn no_byte(s: Seq<u8>, d: u8) -> bool {
    forall|i: int| 0 <= i < s.len() ==> s[i] != d
}

proof fn lemma_count_zero(s: Seq<u8>, d: u8)
    requires
        no_byte(s, d),
    ensures
        count_byte(s, d) == 0,
    decreases s.len(),
{
    if s.len() > 0 {
        let t = s.subrange(1, s.len() as int);
        assert forall|i: int| 0 <= i < t.len() implies t[i] != d by {
            assert(t[i] == s[i + 1]);
        }
        lemma_count_zero(t, d);
    }
}

proof fn lemma_encode_no_delim<C: Codec>(s: Seq<u8>)
    requires
        codec_ok::<C>(),
    ensures
        no_byte(encode::<C>(s), C::delim()),
        s.len() > 0 ==> encode::<C>(s).len() > 0,
    decreases s.len(),
{
    lemma_ok::<C>();
    if s.len() > 0 {
        let t = s.subrange(1, s.len() as int);
        lemma_encode_no_delim::<C>(t);
        let e = encode::<C>(s);
        let h = C::code(s[0]);
        assert(e == h + encode::<C>(t));
        assert forall|i: int| 0 <= i < e.len() implies e[i] != C::delim() by {
            if i < h.len() {
                assert(e[i] == h[i]);
            } else {
                assert(e[i] == encode::<C>(t)[i - h.len()]);
            }
        }
    }
}

proof fn lemma_encode_all_index<C: Codec>(xs: Seq<Seq<u8>>)
    ensures
        encode_all::<C>(xs).len() == xs.len(),
        forall|i: int| 0 <= i < xs.len() ==> #[trigger] encode_all::<C>(xs)[i] == encode::<C>(xs[i]),
    decreases xs.len(),
{
    if xs.len() > 0 {
        let t = xs.subrange(1, xs.len() as int);
        lemma_encode_all_index::<C>(t);
        assert forall|i: int| 0 <= i < xs.len() implies #[trigger] encode_all::<C>(xs)[i] == encode::<C>(xs[i]) by {
            if i > 0 {
                assert(t[i - 1] == xs[i]);
            }
        }
    }
}

proof fn lemma_count_lines<C: Codec>(lines: Seq<Seq<u8>>)
    requires
        forall|k: int| 0 <= k < lines.len() ==> no_byte(#[trigger] lines[k], C::delim()),
    ensures
        count_byte(unparse_lines::<C>(lines), C::delim()) == lines.len(),
    decreases lines.len(),
{
    if lines.len() > 0 {
        let d = C::delim();
        let t = lines.subrange(1, lines.len() as int);
        assert forall|k: int| 0 <= k < t.len() implies no_byte(#[trigger] t[k], d) by {
            assert(t[k] == lines[k + 1]);
        }
        lemma_count_lines::<C>(t);
        assert(no_byte(lines[0], d));
        lemma_count_zero(lines[0], d);
        lemma_count_concat(lines[0] + seq![d], unparse_lines::<C>(t), d);
        lemma_count_concat(lines[0], seq![d], d);
        assert(count_byte(seq![d], d) == 1) by {
            assert(seq![d].subrange(1, 1) =~= Seq::<u8>::empty());
            assert(count_byte(Seq::<u8>::empty(), d) == 0);
        }
    }
}

proof fn lemma_record_count<C: Codec>(rs: Seq<Seq<u8>>)
    requires
        codec_ok::<C>(),
    ensures
        count_byte(unparse_records::<C>(rs), C::delim()) == rs.len(),
{
    let lines = encode_all::<C>(rs);
    lemma_encode_all_index::<C>(rs);
    assert forall|k: int| 0 <= k < lines.len() implies no_byte(#[trigger] lines[k], C::delim()) by {
        lemma_encode_no_delim::<C>(rs[k]);
    }
    lemma_count_lines::<C>(lines);
}

// ---- escape family ----

proof fn lemma_hex_digit(d: u8)
    requires
        d < 16,
    ensures
        is_hex_char(hex_digit(d)),
        hex_digit(d) != 120,
{
}

proof fn lemma_hex_digit_injective(a: u8, b: u8)
    requires
        a < 16,
        b < 16,
        hex_digit(a) == hex_digit(b),
    ensures
        a == b,
{
}

proof fn lemma_div_mod_16(b: u8, c: u8)
    requires
        b / 16 == c / 16,
        b % 16 == c % 16,
    ensures
        b == c,
{
    assert(b == 16 * (b / 16) + b % 16) by (nonlinear_arith);
    assert(c == 16 * (c / 16) + c % 16) by (nonlinear_arith);
}

proof fn lemma_family_codec_ok(
    code: spec_fn(u8) -> Seq<u8>,
    esc: u8,
    literal: spec_fn(u8) -> bool,
    short: spec_fn(u8) -> Option<u8>,
    short_inv: spec_fn(u8) -> Option<u8>,
    d: u8,
    m: u8,
)
    requires
        family_conditions(esc, literal, short, short_inv, d, m),
        forall|b: u8| #[trigger] code(b) == family_code(esc, literal, short, b),
    ensures
        codec_conditions(code, d, m),
{
    assert forall|b: u8| (#[trigger] code(b)).len() > 0 by {
        assert(code(b) == family_code(esc, literal, short, b));
    }
    assert forall|b: u8, i: int| 0 <= i < code(b).len() implies (#[trigger] code(b)[i]) != d by {
        assert(code(b) == family_code(esc, literal, short, b));
        if !literal(b) && short(b) is None {
            lemma_hex_digit(b / 16);
            lemma_hex_digit(b % 16);
        }
    }
    assert forall|b: u8| (#[trigger] code(b))[0] != m by {
        assert(code(b) == family_code(esc, literal, short, b));
    }
    assert forall|b: u8, c: u8| b != c implies !is_prefix(#[trigger] code(b), #[trigger] code(c)) by {
        let x = code(b);
        let y = code(c);
        assert(x == family_code(esc, literal, short, b));
        assert(y == family_code(esc, literal, short, c));
        if is_prefix(x, y) {
            assert(y.subrange(0, x.len() as int) == x);
            assert(y[0] == x[0]);
            if literal(b) {
                if literal(c) {
                    assert(b == c);
                } else {
                    assert(y[0] == esc);
                }
            } else if let Some(s) = short(b) {
                assert(x.len() == 2 && y.len() >= 2);
                assert(y[1] == x[1]);
                assert(!literal(c));
                if let Some(s2) = short(c) {
                    assert(s == s2);
                    assert(short_inv(s) == Some(b) && short_inv(s2) == Some(c));
                } else {
                    assert(y[1] == 120u8);
                }
            } else {
                assert(x.len() == 4 && y.len() >= 4);
                assert(!literal(c) && short(c) is None);
                assert(y[2] == x[2] && y[3] == x[3]);
                lemma_hex_digit_injective(b / 16, c / 16);
                lemma_hex_digit_injective(b % 16, c % 16);
                lemma_div_mod_16(b, c);
            }
        }
    }
}

// ===== part 2: the generic parser (spec) =====================================

// ---- split into lines (byte fold) ----
pub struct SplitS {
    pub lines: Seq<Seq<u8>>,
    pub cur: Seq<u8>,
}

pub open spec fn split_init() -> SplitS {
    SplitS { lines: seq![], cur: seq![] }
}

pub open spec fn split_step(st: SplitS, b: u8, d: u8) -> SplitS {
    if b == d {
        SplitS { lines: st.lines.push(st.cur), cur: seq![] }
    } else {
        SplitS { lines: st.lines, cur: st.cur.push(b) }
    }
}

pub open spec fn split_run(st: SplitS, s: Seq<u8>, d: u8) -> SplitS
    decreases s.len(),
{
    if s.len() == 0 {
        st
    } else {
        split_step(split_run(st, s.subrange(0, s.len() - 1), d), s[s.len() - 1], d)
    }
}

pub open spec fn split_lines(s: Seq<u8>, d: u8) -> Option<Seq<Seq<u8>>> {
    let st = split_run(split_init(), s, d);
    if st.cur.len() == 0 {
        Some(st.lines)
    } else {
        None
    }
}

proof fn lemma_split_run_add(st: SplitS, a: Seq<u8>, b: Seq<u8>, d: u8)
    ensures
        split_run(st, a + b, d) == split_run(split_run(st, a, d), b, d),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        let bp = b.subrange(0, b.len() - 1);
        lemma_split_run_add(st, a, bp, d);
        assert((a + b).subrange(0, (a + b).len() - 1) =~= a + bp);
        assert((a + b)[(a + b).len() - 1] == b[b.len() - 1]);
    }
}

proof fn lemma_split_run_plain(st: SplitS, l: Seq<u8>, d: u8)
    requires
        no_byte(l, d),
    ensures
        split_run(st, l, d) == (SplitS { lines: st.lines, cur: st.cur + l }),
    decreases l.len(),
{
    if l.len() == 0 {
        assert(st.cur + l =~= st.cur);
    } else {
        let lp = l.subrange(0, l.len() - 1);
        assert(no_byte(lp, d)) by {
            assert forall|i: int| 0 <= i < lp.len() implies lp[i] != d by {
                assert(lp[i] == l[i]);
            }
        }
        lemma_split_run_plain(st, lp, d);
        assert(l[l.len() - 1] != d);
        assert((st.cur + lp).push(l[l.len() - 1]) =~= st.cur + l);
    }
}

proof fn lemma_split_unparse<C: Codec>(ls0: Seq<Seq<u8>>, lines: Seq<Seq<u8>>)
    requires
        forall|k: int| 0 <= k < lines.len() ==> no_byte(#[trigger] lines[k], C::delim()),
    ensures
        split_run(SplitS { lines: ls0, cur: seq![] }, unparse_lines::<C>(lines), C::delim()) == (SplitS {
            lines: ls0 + lines,
            cur: seq![],
        }),
    decreases lines.len(),
{
    let d = C::delim();
    let st = SplitS { lines: ls0, cur: seq![] };
    if lines.len() == 0 {
        assert(ls0 + lines =~= ls0);
    } else {
        let t = lines.subrange(1, lines.len() as int);
        assert forall|k: int| 0 <= k < t.len() implies no_byte(#[trigger] t[k], d) by {
            assert(t[k] == lines[k + 1]);
        }
        let l0 = lines[0];
        assert(no_byte(l0, d));
        lemma_split_run_add(st, l0 + seq![d], unparse_lines::<C>(t), d);
        lemma_split_run_add(st, l0, seq![d], d);
        lemma_split_run_plain(st, l0, d);
        let s1 = split_run(st, l0, d);
        assert(s1.cur =~= l0);
        assert(seq![d].subrange(0, 0) =~= Seq::<u8>::empty());
        assert(split_run(s1, Seq::<u8>::empty(), d) == s1);
        assert(split_run(s1, seq![d], d) == split_step(s1, d, d));
        lemma_split_unparse::<C>(ls0.push(l0), t);
        assert(ls0.push(l0) + t =~= ls0 + lines);
    }
}

proof fn lemma_unparse_lines_push<C: Codec>(lines: Seq<Seq<u8>>, l: Seq<u8>)
    ensures
        unparse_lines::<C>(lines.push(l)) == unparse_lines::<C>(lines) + l + seq![C::delim()],
    decreases lines.len(),
{
    if lines.len() == 0 {
        assert(lines.push(l).subrange(1, 1) =~= Seq::<Seq<u8>>::empty());
        assert(unparse_lines::<C>(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
        assert(unparse_lines::<C>(lines.push(l)) =~= unparse_lines::<C>(lines) + l + seq![C::delim()]);
    } else {
        let t = lines.subrange(1, lines.len() as int);
        lemma_unparse_lines_push::<C>(t, l);
        assert(lines.push(l).subrange(1, lines.len() as int + 1) =~= t.push(l));
        assert(unparse_lines::<C>(lines.push(l)) =~= unparse_lines::<C>(lines) + l + seq![C::delim()]);
    }
}

proof fn lemma_split_reverse<C: Codec>(s: Seq<u8>)
    ensures
        s == unparse_lines::<C>(split_run(split_init(), s, C::delim()).lines) + split_run(
            split_init(),
            s,
            C::delim(),
        ).cur,
    decreases s.len(),
{
    let d = C::delim();
    if s.len() == 0 {
        assert(unparse_lines::<C>(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
        assert(s =~= unparse_lines::<C>(Seq::<Seq<u8>>::empty()) + Seq::<u8>::empty());
    } else {
        let p = s.subrange(0, s.len() - 1);
        let b = s[s.len() - 1];
        lemma_split_reverse::<C>(p);
        let st = split_run(split_init(), p, d);
        assert(s =~= p.push(b));
        if b == d {
            lemma_unparse_lines_push::<C>(st.lines, st.cur);
            assert(s =~= unparse_lines::<C>(st.lines.push(st.cur)) + Seq::<u8>::empty());
        } else {
            assert(s =~= unparse_lines::<C>(st.lines) + st.cur.push(b));
        }
    }
}

// ---- tokens and lines ----

/// The byte whose code starts `l` (unique when codec_ok holds, by C3).
pub open spec fn token<C: Codec>(l: Seq<u8>) -> Option<(u8, nat)> {
    if exists|b: u8| #[trigger] is_prefix(C::code(b), l) {
        let b = choose|b: u8| #[trigger] is_prefix(C::code(b), l);
        Some((b, C::code(b).len()))
    } else {
        None
    }
}

proof fn lemma_prefix_unique<C: Codec>(b: u8, c: u8, l: Seq<u8>)
    requires
        codec_ok::<C>(),
        is_prefix(C::code(b), l),
        is_prefix(C::code(c), l),
    ensures
        b == c,
{
    lemma_ok::<C>();
    let (x, y) = (C::code(b), C::code(c));
    if b != c {
        if x.len() <= y.len() {
            assert(y.subrange(0, x.len() as int) =~= l.subrange(0, x.len() as int));
            assert(is_prefix(x, y));
        } else {
            assert(x.subrange(0, y.len() as int) =~= l.subrange(0, y.len() as int));
            assert(is_prefix(y, x));
        }
    }
}

proof fn lemma_token_code<C: Codec>(b: u8, t: Seq<u8>)
    requires
        codec_ok::<C>(),
    ensures
        token::<C>(C::code(b) + t) == Some((b, C::code(b).len())),
{
    let l = C::code(b) + t;
    assert(l.subrange(0, C::code(b).len() as int) =~= C::code(b));
    assert(is_prefix(C::code(b), l));
    let c = choose|c: u8| #[trigger] is_prefix(C::code(c), l);
    lemma_prefix_unique::<C>(b, c, l);
}

proof fn lemma_token_shape<C: Codec>(l: Seq<u8>)
    requires
        codec_ok::<C>(),
    ensures
        token::<C>(l) matches Some((b, n)) ==> 0 < n <= l.len() && l.subrange(0, n as int) == C::code(b),
{
    lemma_ok::<C>();
}

pub open spec fn suffix<C: Codec>(header: bool) -> Seq<u8> {
    if header {
        seq![C::marker()]
    } else {
        seq![]
    }
}

pub open spec fn dec_line<C: Codec>(l: Seq<u8>) -> Option<(Seq<u8>, bool)>
    decreases l.len(),
{
    if l.len() == 0 {
        Some((seq![], false))
    } else if l.len() == 1 && l[0] == C::marker() {
        Some((seq![], true))
    } else {
        match token::<C>(l) {
            None => None,
            Some((b, n)) => if 0 < n && n <= l.len() {
                match dec_line::<C>(l.subrange(n as int, l.len() as int)) {
                    None => None,
                    Some((v, h)) => Some((seq![b] + v, h)),
                }
            } else {
                None
            },
        }
    }
}

proof fn lemma_dec_encode<C: Codec>(v: Seq<u8>, h: bool)
    requires
        codec_ok::<C>(),
    ensures
        dec_line::<C>(encode::<C>(v) + suffix::<C>(h)) == Some((v, h)),
    decreases v.len(),
{
    lemma_ok::<C>();
    if v.len() == 0 {
        assert(encode::<C>(v) + suffix::<C>(h) =~= suffix::<C>(h));
    } else {
        let rest = v.subrange(1, v.len() as int);
        let e = C::code(v[0]);
        let l = encode::<C>(v) + suffix::<C>(h);
        assert(l =~= e + (encode::<C>(rest) + suffix::<C>(h)));
        lemma_token_code::<C>(v[0], encode::<C>(rest) + suffix::<C>(h));
        if l.len() == 1 {
            assert(l[0] == e[0]);
        }
        assert(l.subrange(e.len() as int, l.len() as int) =~= encode::<C>(rest) + suffix::<C>(h));
        lemma_dec_encode::<C>(rest, h);
        assert(seq![v[0]] + rest =~= v);
    }
}

proof fn lemma_dec_reverse<C: Codec>(l: Seq<u8>)
    requires
        codec_ok::<C>(),
    ensures
        dec_line::<C>(l) matches Some((v, h)) ==> l == encode::<C>(v) + suffix::<C>(h),
    decreases l.len(),
{
    if let Some((v, h)) = dec_line::<C>(l) {
        if l.len() == 0 {
            assert(encode::<C>(v) + suffix::<C>(h) =~= l);
        } else if l.len() == 1 && l[0] == C::marker() {
            assert(encode::<C>(v) + suffix::<C>(h) =~= l);
        } else {
            lemma_token_shape::<C>(l);
            let (b, n) = token::<C>(l).unwrap();
            let rest = l.subrange(n as int, l.len() as int);
            lemma_dec_reverse::<C>(rest);
            let (v2, h2) = dec_line::<C>(rest).unwrap();
            assert(v == seq![b] + v2 && h == h2);
            assert((seq![b] + v2).subrange(1, v.len() as int) =~= v2);
            assert(encode::<C>(v) == C::code(b) + encode::<C>(v2));
            assert(l =~= l.subrange(0, n as int) + rest);
            assert(l =~= encode::<C>(v) + suffix::<C>(h));
        }
    }
}

// ---- records ----

pub open spec fn dec_records<C: Codec>(lines: Seq<Seq<u8>>) -> Option<Seq<Seq<u8>>>
    decreases lines.len(),
{
    if lines.len() == 0 {
        Some(seq![])
    } else {
        match dec_line::<C>(lines[0]) {
            Some((v, false)) => match dec_records::<C>(lines.subrange(1, lines.len() as int)) {
                Some(vs) => Some(seq![v] + vs),
                None => None,
            },
            _ => None,
        }
    }
}

pub open spec fn parse_records<C: Codec>(s: Seq<u8>) -> Option<Seq<Seq<u8>>> {
    match split_lines(s, C::delim()) {
        Some(lines) => dec_records::<C>(lines),
        None => None,
    }
}

proof fn lemma_dec_records_encode<C: Codec>(xs: Seq<Seq<u8>>)
    requires
        codec_ok::<C>(),
    ensures
        dec_records::<C>(encode_all::<C>(xs)) == Some(xs),
    decreases xs.len(),
{
    if xs.len() == 0 {
        assert(encode_all::<C>(xs) =~= Seq::<Seq<u8>>::empty());
        assert(xs =~= Seq::<Seq<u8>>::empty());
    } else {
        let t = xs.subrange(1, xs.len() as int);
        lemma_dec_records_encode::<C>(t);
        let ea = encode_all::<C>(xs);
        assert(ea == seq![encode::<C>(xs[0])] + encode_all::<C>(t));
        assert(ea.subrange(1, ea.len() as int) =~= encode_all::<C>(t));
        lemma_dec_encode::<C>(xs[0], false);
        assert(encode::<C>(xs[0]) + suffix::<C>(false) =~= encode::<C>(xs[0]));
        assert(seq![xs[0]] + t =~= xs);
    }
}

proof fn lemma_records_round_trip<C: Codec>(xs: Seq<Seq<u8>>)
    requires
        codec_ok::<C>(),
    ensures
        parse_records::<C>(unparse_records::<C>(xs)) == Some(xs),
{
    let lines = encode_all::<C>(xs);
    lemma_encode_all_index::<C>(xs);
    assert forall|k: int| 0 <= k < lines.len() implies no_byte(#[trigger] lines[k], C::delim()) by {
        lemma_encode_no_delim::<C>(xs[k]);
    }
    lemma_split_unparse::<C>(Seq::<Seq<u8>>::empty(), lines);
    assert(Seq::<Seq<u8>>::empty() + lines =~= lines);
    assert(split_init() == (SplitS { lines: Seq::<Seq<u8>>::empty(), cur: Seq::<u8>::empty() }));
    lemma_dec_records_encode::<C>(xs);
}

proof fn lemma_dec_records_reverse<C: Codec>(lines: Seq<Seq<u8>>)
    requires
        codec_ok::<C>(),
    ensures
        dec_records::<C>(lines) matches Some(xs) ==> lines == encode_all::<C>(xs),
    decreases lines.len(),
{
    if let Some(xs) = dec_records::<C>(lines) {
        if lines.len() == 0 {
            assert(xs =~= Seq::<Seq<u8>>::empty());
            assert(encode_all::<C>(xs) =~= lines);
        } else {
            let t = lines.subrange(1, lines.len() as int);
            lemma_dec_records_reverse::<C>(t);
            lemma_dec_reverse::<C>(lines[0]);
            let (v, h) = dec_line::<C>(lines[0]).unwrap();
            let vs = dec_records::<C>(t).unwrap();
            assert(xs == seq![v] + vs);
            assert(lines[0] =~= encode::<C>(v));
            assert(xs.subrange(1, xs.len() as int) =~= vs);
            assert(encode_all::<C>(xs) =~= lines);
        }
    }
}

proof fn lemma_records_reverse<C: Codec>(s: Seq<u8>)
    requires
        codec_ok::<C>(),
    ensures
        parse_records::<C>(s) matches Some(xs) ==> unparse_records::<C>(xs) == s,
{
    if let Some(xs) = parse_records::<C>(s) {
        lemma_split_reverse::<C>(s);
        let st = split_run(split_init(), s, C::delim());
        assert(st.cur.len() == 0);
        assert(s =~= unparse_lines::<C>(st.lines));
        lemma_dec_records_reverse::<C>(st.lines);
    }
}

proof fn lemma_records_injective<C: Codec>(x: Seq<Seq<u8>>, y: Seq<Seq<u8>>)
    requires
        codec_ok::<C>(),
        unparse_records::<C>(x) == unparse_records::<C>(y),
    ensures
        x == y,
{
    lemma_records_round_trip::<C>(x);
    lemma_records_round_trip::<C>(y);
}

pub open spec fn no_delim<C: Codec>(l: Seq<u8>) -> bool {
    no_byte(l, C::delim())
}

pub open spec fn all_nonempty(s: Seq<Seq<u8>>) -> bool {
    forall|k: int| 0 <= k < s.len() ==> (#[trigger] s[k]).len() > 0
}


proof fn lemma_groups_lines_add<C: Codec>(a: Seq<GroupS>, b: Seq<GroupS>)
    requires
        codec_ok::<C>(),
    ensures
        groups_lines::<C>(a + b) == groups_lines::<C>(a) + groups_lines::<C>(b),
    decreases a.len(),
{
    if a.len() > 0 {
        let t = a.subrange(1, a.len() as int);
        lemma_groups_lines_add::<C>(t, b);
        assert((a + b).subrange(1, (a + b).len() as int) =~= t + b);
        assert((a + b)[0] == a[0]);
        assert(groups_lines::<C>(a + b) =~= groups_lines::<C>(a) + groups_lines::<C>(b));
    } else {
        assert(a + b =~= b);
        assert(groups_lines::<C>(a) =~= Seq::<Seq<Seq<u8>>>::empty());
        assert(groups_lines::<C>(a) + groups_lines::<C>(b) =~= groups_lines::<C>(b));
    }
}

// ===== part 3: documents (line fold), ported from kata 0003 =====
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

pub open spec fn pstep<C: Codec>(st: PState, line: Seq<u8>) -> PState {
    if !st.ok {
        st
    } else if line.len() == 0 {
        if st.fresh {
            pfail()
        } else {
            PState { ok: true, doc: st.doc, fresh: true }
        }
    } else {
        match dec_line::<C>(line) {
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

pub open spec fn prun<C: Codec>(st: PState, lines: Seq<Seq<u8>>) -> PState
    decreases lines.len(),
{
    if lines.len() == 0 {
        st
    } else {
        pstep::<C>(prun::<C>(st, lines.subrange(0, lines.len() - 1)), lines[lines.len() - 1])
    }
}

pub open spec fn parse_lines<C: Codec>(lines: Seq<Seq<u8>>) -> Option<Seq<GroupS>> {
    let st = prun::<C>(pinit(), lines);
    if st.ok && !(st.fresh && st.doc.len() > 0) {
        Some(st.doc)
    } else {
        None
    }
}

pub open spec fn parse_document<C: Codec>(s: Seq<u8>) -> Option<Seq<GroupS>> {
    match split_lines(s, C::delim()) {
        Some(lines) => parse_lines::<C>(lines),
        None => None,
    }
}

proof fn lemma_prun_add<C: Codec>(st: PState, a: Seq<Seq<u8>>, b: Seq<Seq<u8>>)
    requires
        codec_ok::<C>(),
    ensures
        prun::<C>(st, a + b) == prun::<C>(prun::<C>(st, a), b),
    decreases b.len(),
{
    if b.len() == 0 {
        assert(a + b =~= a);
    } else {
        let bp = b.subrange(0, b.len() - 1);
        lemma_prun_add::<C>(st, a, bp);
        assert((a + b).subrange(0, (a + b).len() - 1) =~= a + bp);
        assert((a + b)[(a + b).len() - 1] == b[b.len() - 1]);
    }
}

proof fn lemma_prun_one<C: Codec>(st: PState, l: Seq<u8>)
    requires
        codec_ok::<C>(),
    ensures
        prun::<C>(st, seq![l]) == pstep::<C>(st, l),
{
    assert(seq![l].subrange(0, 0) =~= Seq::<Seq<u8>>::empty());
    assert(prun::<C>(st, Seq::<Seq<u8>>::empty()) == st);
    assert(seq![l][0] == l);
}

proof fn lemma_encode_all_push<C: Codec>(m: Seq<Seq<u8>>, v: Seq<u8>)
    requires
        codec_ok::<C>(),
    ensures
        encode_all::<C>(m.push(v)) == encode_all::<C>(m) + seq![encode::<C>(v)],
    decreases m.len(),
{
    if m.len() == 0 {
        assert(m.push(v).subrange(1, 1) =~= Seq::<Seq<u8>>::empty());
        assert(encode_all::<C>(Seq::<Seq<u8>>::empty()) == Seq::<Seq<u8>>::empty());
        assert(encode_all::<C>(m.push(v)) =~= encode_all::<C>(m) + seq![encode::<C>(v)]);
    } else {
        let t = m.subrange(1, m.len() as int);
        lemma_encode_all_push::<C>(t, v);
        assert(m.push(v).subrange(1, m.len() as int + 1) =~= t.push(v));
        assert(encode_all::<C>(m.push(v)) =~= encode_all::<C>(m) + seq![encode::<C>(v)]);
    }
}

/// Appending escaped names to the open last group.
proof fn lemma_prun_names<C: Codec>(st: PState, m: Seq<Seq<u8>>)
    requires
        codec_ok::<C>(),
        st.ok,
        !st.fresh,
        st.doc.len() > 0,
        all_nonempty(m),
    ensures
        prun::<C>(st, encode_all::<C>(m)) == (PState {
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
        assert(encode_all::<C>(m) =~= Seq::<Seq<u8>>::empty());
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
        lemma_prun_names::<C>(st, mp);
        assert(mp.push(v) =~= m);
        lemma_encode_all_push::<C>(mp, v);
        lemma_prun_add::<C>(st, encode_all::<C>(mp), seq![encode::<C>(v)]);
        let mid = prun::<C>(st, encode_all::<C>(mp));
        lemma_prun_one::<C>(mid, encode::<C>(v));
        assert(v.len() > 0);
        lemma_encode_no_delim::<C>(v);
        lemma_dec_encode::<C>(v, false);
        assert(encode::<C>(v) + suffix::<C>(false) =~= encode::<C>(v));
        assert(mid.doc[mid.doc.len() - 1].names.push(v) =~= last.names + m);
        assert(add_name(mid.doc, v) =~= st.doc.update(
            st.doc.len() - 1,
            GroupS { header: last.header, names: last.names + m },
        ));
    }
}

/// A group with a header, started from a fresh state.
proof fn lemma_prun_header_group<C: Codec>(st: PState, g: GroupS)
    requires
        codec_ok::<C>(),
        st.ok,
        st.fresh,
        has_header(g),
        all_nonempty(g.names),
    ensures
        prun::<C>(st, group_lines::<C>(g)) == (PState { ok: true, doc: st.doc.push(g), fresh: false }),
{
    let h = g.header.unwrap();
    let hl = encode::<C>(h) + seq![C::marker()];
    assert(group_lines::<C>(g) == seq![hl] + encode_all::<C>(g.names));
    lemma_prun_add::<C>(st, seq![hl], encode_all::<C>(g.names));
    lemma_prun_one::<C>(st, hl);
    lemma_dec_encode::<C>(h, true);
    let s1 = PState { ok: true, doc: st.doc.push(GroupS { header: Some(h), names: seq![] }), fresh: false };
    assert(pstep::<C>(st, hl) == s1);
    lemma_prun_names::<C>(s1, g.names);
    assert(Seq::<Seq<u8>>::empty() + g.names =~= g.names);
    assert(s1.doc.update(s1.doc.len() - 1, GroupS { header: Some(h), names: Seq::<Seq<u8>>::empty() + g.names })
        =~= st.doc.push(g));
}

/// A headerless (hence first, non-empty) group, from the initial state.
proof fn lemma_prun_first_plain_group<C: Codec>(g: GroupS)
    requires
        codec_ok::<C>(),
        !has_header(g),
        g.names.len() > 0,
        all_nonempty(g.names),
    ensures
        prun::<C>(pinit(), group_lines::<C>(g)) == (PState { ok: true, doc: seq![g], fresh: false }),
{
    let m = g.names;
    let rest = m.subrange(1, m.len() as int);
    assert(group_lines::<C>(g) =~= encode_all::<C>(m));
    assert(encode_all::<C>(m) == seq![encode::<C>(m[0])] + encode_all::<C>(rest));
    lemma_prun_add::<C>(pinit(), seq![encode::<C>(m[0])], encode_all::<C>(rest));
    lemma_prun_one::<C>(pinit(), encode::<C>(m[0]));
    lemma_encode_no_delim::<C>(m[0]);
    lemma_dec_encode::<C>(m[0], false);
    assert(encode::<C>(m[0]) + suffix::<C>(false) =~= encode::<C>(m[0]));
    let s1 = PState { ok: true, doc: seq![GroupS { header: None, names: seq![m[0]] }], fresh: false };
    assert(pstep::<C>(pinit(), encode::<C>(m[0])) == s1);
    assert(all_nonempty(rest)) by {
        assert forall|k: int| 0 <= k < rest.len() implies (#[trigger] rest[k]).len() > 0 by {
            assert(rest[k] == m[k + 1]);
        }
    }
    lemma_prun_names::<C>(s1, rest);
    assert(seq![m[0]] + rest =~= m);
    assert(g.header == None::<Seq<u8>>);
    assert(s1.doc.update(0, GroupS { header: None, names: seq![m[0]] + rest }) =~= seq![g]);
}

proof fn lemma_groups_lines_push<C: Codec>(x: Seq<GroupS>, g: GroupS)
    requires
        codec_ok::<C>(),
    ensures
        groups_lines::<C>(x.push(g)) == groups_lines::<C>(x).push(group_lines::<C>(g)),
{
    lemma_groups_lines_add::<C>(x, seq![g]);
    assert(x.push(g) =~= x + seq![g]);
    assert(seq![g].subrange(1, 1) =~= Seq::<GroupS>::empty());
    assert(groups_lines::<C>(Seq::<GroupS>::empty()) == Seq::<Seq<Seq<u8>>>::empty());
    assert(groups_lines::<C>(seq![g]) =~= seq![group_lines::<C>(g)]);
    assert(groups_lines::<C>(x) + seq![group_lines::<C>(g)] =~= groups_lines::<C>(x).push(group_lines::<C>(g)));
}

proof fn lemma_groups_lines_len<C: Codec>(x: Seq<GroupS>)
    requires
        codec_ok::<C>(),
    ensures
        groups_lines::<C>(x).len() == x.len(),
    decreases x.len(),
{
    if x.len() > 0 {
        lemma_groups_lines_len::<C>(x.subrange(1, x.len() as int));
    }
}

proof fn lemma_wf_prefix<C: Codec>(x: Seq<GroupS>)
    requires
        codec_ok::<C>(),
        wf_document(x),
        x.len() > 0,
    ensures
        wf_document(x.subrange(0, x.len() - 1)),
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
proof fn lemma_prun_doc<C: Codec>(x: Seq<GroupS>)
    requires
        codec_ok::<C>(),
        wf_document(x),
        x.len() > 0,
    ensures
        prun::<C>(pinit(), join_groups(groups_lines::<C>(x))) == (PState { ok: true, doc: x, fresh: false }),
    decreases x.len(),
{
    lemma_wf_prefix::<C>(x);
    lemma_groups_lines_len::<C>(x);
    let k = x.len();
    let g = x[k - 1];
    let p = x.subrange(0, k - 1);
    assert(x =~= p.push(g));
    lemma_groups_lines_push::<C>(p, g);
    let gl = groups_lines::<C>(x);
    if k == 1 {
        assert(join_groups(gl) == gl[0]);
        assert(gl[0] == group_lines::<C>(g));
        if has_header(g) {
            lemma_prun_header_group::<C>(pinit(), g);
            assert(Seq::<GroupS>::empty().push(g) =~= x);
        } else {
            lemma_prun_first_plain_group::<C>(g);
            assert(seq![g] =~= x);
        }
    } else {
        lemma_prun_doc::<C>(p);
        lemma_groups_lines_len::<C>(p);
        assert(gl.subrange(0, gl.len() - 1) =~= groups_lines::<C>(p));
        assert(join_groups(gl) == join_groups(groups_lines::<C>(p)) + seq![Seq::<u8>::empty()] + group_lines::<C>(g));
        let s1 = PState { ok: true, doc: p, fresh: false };
        lemma_prun_add::<C>(pinit(), join_groups(groups_lines::<C>(p)) + seq![Seq::<u8>::empty()], group_lines::<C>(g));
        lemma_prun_add::<C>(pinit(), join_groups(groups_lines::<C>(p)), seq![Seq::<u8>::empty()]);
        lemma_prun_one::<C>(s1, Seq::<u8>::empty());
        let s2 = PState { ok: true, doc: p, fresh: true };
        assert(pstep::<C>(s1, Seq::<u8>::empty()) == s2);
        assert(has_header(x[k - 1]));
        lemma_prun_header_group::<C>(s2, g);
    }
}

proof fn lemma_group_lines_no_lf<C: Codec>(g: GroupS)
    requires
        codec_ok::<C>(),
    ensures
        forall|k: int| 0 <= k < group_lines::<C>(g).len() ==> no_delim::<C>(#[trigger] group_lines::<C>(g)[k]),
{
    lemma_encode_all_index::<C>(g.names);
    let gl = group_lines::<C>(g);
    assert forall|k: int| 0 <= k < gl.len() implies no_delim::<C>(#[trigger] gl[k]) by {
        match g.header {
            Some(h) => {
                if k == 0 {
                    lemma_encode_no_delim::<C>(h);
                    let hl = encode::<C>(h) + seq![C::marker()];
                    assert(gl[0] == hl);
                    lemma_ok::<C>();
                    assert forall|i: int| 0 <= i < hl.len() implies hl[i] != C::delim() by {
                        if i < encode::<C>(h).len() {
                            assert(hl[i] == encode::<C>(h)[i]);
                        }
                    }
                } else {
                    assert(gl[k] == encode_all::<C>(g.names)[k - 1]);
                    lemma_encode_no_delim::<C>(g.names[k - 1]);
                }
            },
            None => {
                assert(gl[k] == encode_all::<C>(g.names)[k]);
                lemma_encode_no_delim::<C>(g.names[k]);
            },
        }
    }
}

proof fn lemma_join_no_lf<C: Codec>(gs: Seq<Seq<Seq<u8>>>)
    requires
        codec_ok::<C>(),
        forall|i: int, k: int| 0 <= i < gs.len() && 0 <= k < gs[i].len() ==> no_delim::<C>(#[trigger] gs[i][k]),
    ensures
        forall|k: int| 0 <= k < join_groups(gs).len() ==> no_delim::<C>(#[trigger] join_groups(gs)[k]),
    decreases gs.len(),
{
    let j = join_groups(gs);
    if gs.len() == 1 {
        assert forall|k: int| 0 <= k < j.len() implies no_delim::<C>(#[trigger] j[k]) by {
            assert(j[k] == gs[0][k]);
        }
    } else if gs.len() > 1 {
        let p = gs.subrange(0, gs.len() - 1);
        lemma_join_no_lf::<C>(p);
        let jp = join_groups(p);
        let last = gs[gs.len() - 1];
        assert(j == jp + seq![Seq::<u8>::empty()] + last);
        assert forall|k: int| 0 <= k < j.len() implies no_delim::<C>(#[trigger] j[k]) by {
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

proof fn lemma_unparse_lines_no_lf<C: Codec>(x: Seq<GroupS>)
    requires
        codec_ok::<C>(),
    ensures
        forall|k: int|
            0 <= k < join_groups(groups_lines::<C>(x)).len() ==> no_delim::<C>(#[trigger] join_groups(groups_lines::<C>(x))[k]),
{
    let gs = groups_lines::<C>(x);
    lemma_groups_lines_len::<C>(x);
    assert forall|i: int, k: int| 0 <= i < gs.len() && 0 <= k < gs[i].len() implies no_delim::<C>(#[trigger] gs[i][k]) by {
        lemma_groups_lines_index::<C>(x, i);
        lemma_group_lines_no_lf::<C>(x[i]);
    }
    lemma_join_no_lf::<C>(gs);
}

proof fn lemma_groups_lines_index<C: Codec>(x: Seq<GroupS>, i: int)
    requires
        codec_ok::<C>(),
        0 <= i < x.len(),
    ensures
        groups_lines::<C>(x)[i] == group_lines::<C>(x[i]),
    decreases x.len(),
{
    let t = x.subrange(1, x.len() as int);
    assert(groups_lines::<C>(x) == seq![group_lines::<C>(x[0])] + groups_lines::<C>(t));
    lemma_groups_lines_len::<C>(t);
    if i > 0 {
        lemma_groups_lines_index::<C>(t, i - 1);
        assert(t[i - 1] == x[i]);
        assert(groups_lines::<C>(x)[i] == groups_lines::<C>(t)[i - 1]);
    }
}

/// The paper's round trip, at spec level: parse(unparse_document::<C>(x)) = x.
proof fn lemma_document_round_trip<C: Codec>(x: Seq<GroupS>)
    requires
        codec_ok::<C>(),
        wf_document(x),
    ensures
        parse_document::<C>(unparse_document::<C>(x)) == Some(x),
{
    let lines = join_groups(groups_lines::<C>(x));
    lemma_unparse_lines_no_lf::<C>(x);
    lemma_split_unparse::<C>(Seq::<Seq<u8>>::empty(), lines);
    assert(Seq::<Seq<u8>>::empty() + lines =~= lines);
    assert(split_init() == (SplitS { lines: Seq::<Seq<u8>>::empty(), cur: Seq::<u8>::empty() }));
    assert(split_lines(unparse_document::<C>(x), C::delim()) == Some(lines));
    if x.len() > 0 {
        lemma_prun_doc::<C>(x);
    } else {
        assert(groups_lines::<C>(x) =~= Seq::<Seq<Seq<u8>>>::empty());
        assert(lines =~= Seq::<Seq<u8>>::empty());
    }
}

// ---- reverse direction: whatever parses, unparses back (strictness) ----

proof fn lemma_join_extend<C: Codec>(gs: Seq<Seq<Seq<u8>>>, l: Seq<u8>)
    requires
        codec_ok::<C>(),
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

proof fn lemma_join_push<C: Codec>(gs: Seq<Seq<Seq<u8>>>, g: Seq<Seq<u8>>)
    requires
        codec_ok::<C>(),
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

pub open spec fn prun_inv<C: Codec>(lines: Seq<Seq<u8>>, st: PState) -> bool {
    &&& wf_document(st.doc)
    &&& st.doc.len() == 0 ==> lines.len() == 0 && st.fresh
    &&& st.doc.len() > 0 ==> lines == join_groups(groups_lines::<C>(st.doc)) + (if st.fresh {
        seq![Seq::<u8>::empty()]
    } else {
        Seq::<Seq<u8>>::empty()
    })
}

proof fn lemma_prun_reverse<C: Codec>(lines: Seq<Seq<u8>>)
    requires
        codec_ok::<C>(),
    ensures
        prun::<C>(pinit(), lines).ok ==> prun_inv::<C>(lines, prun::<C>(pinit(), lines)),
    decreases lines.len(),
{
    let st = prun::<C>(pinit(), lines);
    if lines.len() == 0 || !st.ok {
        return;
    }
    let p = lines.subrange(0, lines.len() - 1);
    let l = lines[lines.len() - 1];
    lemma_prun_reverse::<C>(p);
    let s0 = prun::<C>(pinit(), p);
    assert(lines =~= p.push(l));
    assert(st == pstep::<C>(s0, l));
    assert(s0.ok);
    lemma_groups_lines_len::<C>(s0.doc);
    if l.len() == 0 {
        assert(!s0.fresh && s0.doc.len() > 0);
        assert(p =~= join_groups(groups_lines::<C>(s0.doc)));
        assert(l =~= Seq::<u8>::empty());
        assert(lines =~= join_groups(groups_lines::<C>(s0.doc)) + seq![Seq::<u8>::empty()]);
    } else {
        lemma_dec_reverse::<C>(l);
        let (v, h) = dec_line::<C>(l).unwrap();
        assert(l == encode::<C>(v) + suffix::<C>(h));
        if h {
            let g = GroupS { header: Some(v), names: seq![] };
            assert(st.doc == s0.doc.push(g));
            lemma_groups_lines_push::<C>(s0.doc, g);
            lemma_join_push::<C>(groups_lines::<C>(s0.doc), group_lines::<C>(g));
            assert(encode_all::<C>(Seq::<Seq<u8>>::empty()) == Seq::<Seq<u8>>::empty());
            assert(group_lines::<C>(g) =~= seq![l]);
            if s0.doc.len() == 0 {
                assert(lines =~= seq![l]);
                assert(join_groups(groups_lines::<C>(st.doc)) =~= seq![l]);
            } else {
                assert(lines =~= join_groups(groups_lines::<C>(st.doc)));
            }
            assert(wf_document(st.doc)) by {
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
                    assert(encode::<C>(v) =~= Seq::<u8>::empty());
                    assert(l =~= Seq::<u8>::empty());
                }
            }
            assert(l =~= encode::<C>(v));
            if s0.fresh {
                let g = GroupS { header: None, names: seq![v] };
                assert(s0.doc.len() == 0 && p.len() == 0);
                assert(st.doc == seq![g]);
                assert(seq![g] =~= Seq::<GroupS>::empty().push(g));
                lemma_groups_lines_push::<C>(Seq::<GroupS>::empty(), g);
                assert(groups_lines::<C>(Seq::<GroupS>::empty()) == Seq::<Seq<Seq<u8>>>::empty());
                lemma_join_push::<C>(Seq::<Seq<Seq<u8>>>::empty(), group_lines::<C>(g));
                lemma_encode_all_push::<C>(Seq::<Seq<u8>>::empty(), v);
                assert(Seq::<Seq<u8>>::empty().push(v) =~= seq![v]);
                assert(encode_all::<C>(Seq::<Seq<u8>>::empty()) == Seq::<Seq<u8>>::empty());
                assert(group_lines::<C>(g) =~= seq![l]);
                assert(lines =~= seq![l]);
                assert(wf_document(st.doc)) by {
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
                lemma_encode_all_push::<C>(last.names, v);
                assert(group_lines::<C>(last2) =~= group_lines::<C>(last).push(l));
                let gl = groups_lines::<C>(d);
                lemma_groups_lines_index::<C>(d, d.len() - 1);
                assert(groups_lines::<C>(st.doc) =~= gl.update(gl.len() - 1, gl[gl.len() - 1].push(l))) by {
                    lemma_groups_lines_len::<C>(st.doc);
                    assert forall|i: int| 0 <= i < gl.len() implies #[trigger] groups_lines::<C>(st.doc)[i] == gl.update(
                        gl.len() - 1,
                        gl[gl.len() - 1].push(l),
                    )[i] by {
                        lemma_groups_lines_index::<C>(st.doc, i);
                        lemma_groups_lines_index::<C>(d, i);
                    }
                }
                lemma_join_extend::<C>(gl, l);
                assert(lines =~= join_groups(groups_lines::<C>(st.doc)) + Seq::<Seq<u8>>::empty());
                assert(wf_document(st.doc)) by {
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

proof fn lemma_document_reverse<C: Codec>(s: Seq<u8>)
    requires
        codec_ok::<C>(),
    ensures
        parse_document::<C>(s) matches Some(d) ==> wf_document(d) && unparse_document::<C>(d) == s,
{
    if let Some(d) = parse_document::<C>(s) {
        lemma_split_reverse::<C>(s);
        let st = split_run(split_init(), s, C::delim());
        assert(st.cur.len() == 0);
        assert(s =~= unparse_lines::<C>(st.lines));
        lemma_prun_reverse::<C>(st.lines);
        let ps = prun::<C>(pinit(), st.lines);
        if ps.doc.len() == 0 {
            assert(st.lines.len() == 0);
            assert(groups_lines::<C>(d) =~= Seq::<Seq<Seq<u8>>>::empty());
            assert(join_groups(groups_lines::<C>(d)) =~= st.lines);
        } else {
            assert(st.lines =~= join_groups(groups_lines::<C>(d)));
        }
    }
}

proof fn lemma_document_injective<C: Codec>(x: Seq<GroupS>, y: Seq<GroupS>)
    requires
        codec_ok::<C>(),
        wf_document(x),
        wf_document(y),
        unparse_document::<C>(x) == unparse_document::<C>(y),
    ensures
        x == y,
{
    lemma_document_round_trip::<C>(x);
    lemma_document_round_trip::<C>(y);
}


// ===== part 4: executable decoders and document unparser ====================

proof fn lemma_codec_ok_of<C: Codec>()
    ensures
        codec_ok::<C>(),
{
    C::lemma_codec_ok();
}

fn split_exec(input: &Vec<u8>, d: u8) -> (r: (Vec<Vec<u8>>, Vec<u8>))
    ensures
        (SplitS { lines: seqs_view(r.0@), cur: r.1@ }) == split_run(split_init(), input@, d),
{
    let mut lines: Vec<Vec<u8>> = Vec::new();
    let mut cur: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    assert(input@.subrange(0, 0) =~= Seq::<u8>::empty());
    assert(seqs_view(lines@) =~= Seq::<Seq<u8>>::empty());
    assert(cur@ =~= Seq::<u8>::empty());
    while i < input.len()
        invariant
            i <= input.len(),
            (SplitS { lines: seqs_view(lines@), cur: cur@ }) == split_run(
                split_init(),
                input@.subrange(0, i as int),
                d,
            ),
        decreases input.len() - i,
    {
        let ghost pre = input@.subrange(0, i as int);
        let ghost next = input@.subrange(0, i + 1);
        assert(next.subrange(0, i as int) =~= pre);
        assert(next[i as int] == input@[i as int]);
        let ghost lv = seqs_view(lines@);
        let ghost cv = cur@;
        let b = input[i];
        if b == d {
            lines.push(cur);
            cur = Vec::new();
            assert(seqs_view(lines@) =~= lv.push(cv));
            assert(cur@ =~= Seq::<u8>::empty());
        } else {
            cur.push(b);
        }
        i += 1;
    }
    assert(input@.subrange(0, input@.len() as int) =~= input@);
    (lines, cur)
}

fn code_vec<C: Codec>(b: u8) -> (r: Vec<u8>)
    ensures
        r@ == C::code(b),
{
    let mut r: Vec<u8> = Vec::new();
    C::push_code(&mut r, b);
    assert(r@ =~= C::code(b));
    r
}

fn prefix_at(c: &Vec<u8>, l: &Vec<u8>, i: usize) -> (r: bool)
    requires
        i <= l.len(),
    ensures
        r == is_prefix(c@, l@.subrange(i as int, l@.len() as int)),
{
    let ghost rest = l@.subrange(i as int, l@.len() as int);
    if c.len() > l.len() - i {
        return false;
    }
    let mut k: usize = 0;
    while k < c.len()
        invariant
            k <= c.len(),
            c.len() <= l.len() - i,
            i <= l.len(),
            rest == l@.subrange(i as int, l@.len() as int),
            forall|j: int| 0 <= j < k ==> #[trigger] c@[j] == rest[j],
        decreases c.len() - k,
    {
        if c[k] != l[i + k] {
            assert(rest[k as int] == l@[i + k]);
            assert(rest.subrange(0, c@.len() as int)[k as int] != c@[k as int]);
            return false;
        }
        k += 1;
    }
    assert(rest.subrange(0, c@.len() as int) =~= c@);
    true
}

fn token_exec<C: Codec>(l: &Vec<u8>, i: usize) -> (r: Option<(u8, usize)>)
    requires
        i <= l.len(),
    ensures
        match (r, token::<C>(l@.subrange(i as int, l@.len() as int))) {
            (Some((b, n)), Some((b2, n2))) => b == b2 && n as nat == n2,
            (None, None) => true,
            _ => false,
        },
{
    proof {
        lemma_codec_ok_of::<C>();
    }
    let ghost rest = l@.subrange(i as int, l@.len() as int);
    let mut b: u16 = 0;
    while b < 256
        invariant
            b <= 256,
            i <= l.len(),
            rest == l@.subrange(i as int, l@.len() as int),
            codec_ok::<C>(),
            forall|x: u8| (x as u16) < b ==> !is_prefix(#[trigger] C::code(x), rest),
        decreases 256 - b,
    {
        let c = code_vec::<C>(b as u8);
        if prefix_at(&c, l, i) {
            proof {
                let ch = choose|x: u8| #[trigger] is_prefix(C::code(x), rest);
                lemma_prefix_unique::<C>(b as u8, ch, rest);
            }
            return Some((b as u8, c.len()));
        }
        b += 1;
    }
    assert(!exists|x: u8| #[trigger] is_prefix(C::code(x), rest)) by {
        assert forall|x: u8| !is_prefix(#[trigger] C::code(x), rest) by {
            assert((x as u16) < 256);
        }
    }
    None
}

pub open spec fn prepend(out: Seq<u8>, r: Option<(Seq<u8>, bool)>) -> Option<(Seq<u8>, bool)> {
    match r {
        Some((v, h)) => Some((out + v, h)),
        None => None,
    }
}

fn dec_line_exec<C: Codec>(l: &Vec<u8>) -> (r: Option<(Vec<u8>, bool)>)
    ensures
        match r {
            Some((v, h)) => dec_line::<C>(l@) == Some((v@, h)),
            None => dec_line::<C>(l@) == None::<(Seq<u8>, bool)>,
        },
{
    proof {
        lemma_codec_ok_of::<C>();
    }
    let m = C::marker_exec();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    assert(l@.subrange(0, l@.len() as int) =~= l@);
    proof {
        if let Some((v, h)) = dec_line::<C>(l@) {
            assert(out@ + v =~= v);
        }
    }
    loop
        invariant
            i <= l.len(),
            m == C::marker(),
            codec_ok::<C>(),
            dec_line::<C>(l@) == prepend(out@, dec_line::<C>(l@.subrange(i as int, l@.len() as int))),
        decreases l.len() - i,
    {
        let ghost t = l@.subrange(i as int, l@.len() as int);
        if i == l.len() {
            assert(t.len() == 0);
            assert(out@ + Seq::<u8>::empty() =~= out@);
            return Some((out, false));
        }
        assert(t[0] == l@[i as int]);
        if l.len() - i == 1 && l[i] == m {
            assert(out@ + Seq::<u8>::empty() =~= out@);
            return Some((out, true));
        }
        match token_exec::<C>(l, i) {
            None => {
                return None;
            },
            Some((b, n)) => {
                proof {
                    lemma_token_shape::<C>(t);
                    assert(t.subrange(n as int, t.len() as int) =~= l@.subrange(i + n, l@.len() as int));
                    let rest = l@.subrange(i + n, l@.len() as int);
                    if let Some((v, h)) = dec_line::<C>(rest) {
                        assert(out@ + (seq![b] + v) =~= out@.push(b) + v);
                    }
                }
                out.push(b);
                i = i + n;
            },
        }
    }
}

pub open spec fn opt_cat(o: Seq<Seq<u8>>, r: Option<Seq<Seq<u8>>>) -> Option<Seq<Seq<u8>>> {
    match r {
        Some(vs) => Some(o + vs),
        None => None,
    }
}

fn decode_records_impl<C: Codec>(input: &Vec<u8>) -> (r: Option<Vec<Vec<u8>>>)
    ensures
        match r {
            Some(rs) => parse_records::<C>(input@) == Some(seqs_view(rs@)),
            None => parse_records::<C>(input@) == None::<Seq<Seq<u8>>>,
        },
{
    let d = C::delim_exec();
    let (lines, cur) = split_exec(input, d);
    if cur.len() > 0 {
        return None;
    }
    let ghost lv = seqs_view(lines@);
    assert(split_lines(input@, C::delim()) == Some(lv));
    let mut out: Vec<Vec<u8>> = Vec::new();
    let mut i: usize = 0;
    assert(lv.subrange(0, lv.len() as int) =~= lv);
    proof {
        if let Some(vs) = dec_records::<C>(lv) {
            assert(seqs_view(out@) + vs =~= vs);
        }
    }
    while i < lines.len()
        invariant
            i <= lines.len(),
            lv == seqs_view(lines@),
            split_lines(input@, C::delim()) == Some(lv),
            dec_records::<C>(lv) == opt_cat(seqs_view(out@), dec_records::<C>(lv.subrange(i as int, lv.len() as int))),
        decreases lines.len() - i,
    {
        let ghost t = lv.subrange(i as int, lv.len() as int);
        let ghost rest = lv.subrange(i + 1, lv.len() as int);
        assert(t.subrange(1, t.len() as int) =~= rest);
        assert(t[0] == lines@[i as int]@);
        let res = dec_line_exec::<C>(&lines[i]);
        match res {
            Some((v, false)) => {
                let ghost vv = v@;
                let ghost before = seqs_view(out@);
                out.push(v);
                assert(seqs_view(out@) =~= before.push(vv));
                proof {
                    if let Some(vs) = dec_records::<C>(rest) {
                        assert(before + (seq![vv] + vs) =~= before.push(vv) + vs);
                    }
                }
            },
            _ => {
                assert(dec_records::<C>(t) == None::<Seq<Seq<u8>>>);
                return None;
            },
        }
        i += 1;
    }
    assert(lv.subrange(lv.len() as int, lv.len() as int) =~= Seq::<Seq<u8>>::empty());
    assert(seqs_view(out@) + Seq::<Seq<u8>>::empty() =~= seqs_view(out@));
    Some(out)
}

fn unparse_lines_exec<C: Codec>(lines: &Vec<Vec<u8>>) -> (r: Vec<u8>)
    ensures
        r@ == unparse_lines::<C>(seqs_view(lines@)),
{
    let ghost all = seqs_view(lines@);
    let d = C::delim_exec();
    let mut out: Vec<u8> = Vec::new();
    let mut i: usize = 0;
    assert(all.subrange(0, all.len() as int) =~= all);
    assert(out@ + unparse_lines::<C>(all) =~= unparse_lines::<C>(all));
    while i < lines.len()
        invariant
            i <= lines.len(),
            all == seqs_view(lines@),
            d == C::delim(),
            out@ + unparse_lines::<C>(all.subrange(i as int, all.len() as int)) == unparse_lines::<C>(all),
        decreases lines.len() - i,
    {
        let ghost t = all.subrange(i as int, all.len() as int);
        let ghost rest = all.subrange(i + 1, all.len() as int);
        assert(t.subrange(1, t.len() as int) =~= rest);
        assert(t[0] == lines@[i as int]@);
        let ghost before = out@;
        let line = &lines[i];
        let mut k: usize = 0;
        while k < line.len()
            invariant
                k <= line.len(),
                out@ == before + line@.subrange(0, k as int),
            decreases line.len() - k,
        {
            out.push(line[k]);
            assert(before + line@.subrange(0, k + 1) =~= (before + line@.subrange(0, k as int)).push(line@[k as int]));
            k += 1;
        }
        assert(line@.subrange(0, line@.len() as int) =~= line@);
        out.push(d);
        assert(out@ + unparse_lines::<C>(rest) =~= before + unparse_lines::<C>(t));
        i += 1;
    }
    assert(all.subrange(all.len() as int, all.len() as int) =~= Seq::<Seq<u8>>::empty());
    assert(unparse_lines::<C>(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
    assert(out@ + Seq::<u8>::empty() =~= out@);
    out
}

fn encode_line<C: Codec>(s: &Vec<u8>) -> (r: Vec<u8>)
    ensures
        r@ == encode::<C>(s@),
{
    let mut r: Vec<u8> = Vec::new();
    encode_into::<C>(&mut r, s);
    assert(r@ =~= encode::<C>(s@));
    r
}

fn group_lines_exec<C: Codec>(g: &Group) -> (r: Vec<Vec<u8>>)
    ensures
        seqs_view(r@) == group_lines::<C>(g@),
{
    let mut out: Vec<Vec<u8>> = Vec::new();
    let ghost gv = g@;
    match &g.header {
        Some(h) => {
            let mut hl = encode_line::<C>(h);
            hl.push(C::marker_exec());
            assert(hl@ =~= encode::<C>(h@) + seq![C::marker()]);
            out.push(hl);
            assert(seqs_view(out@) =~= seq![encode::<C>(h@) + seq![C::marker()]]);
        },
        None => {
            assert(seqs_view(out@) =~= Seq::<Seq<u8>>::empty());
        },
    }
    let ghost head = seqs_view(out@);
    let ghost names = seqs_view(g.names@);
    proof {
        lemma_encode_all_index::<C>(names);
    }
    let mut i: usize = 0;
    while i < g.names.len()
        invariant
            i <= g.names.len(),
            names == seqs_view(g.names@),
            encode_all::<C>(names).len() == names.len(),
            forall|k: int| 0 <= k < names.len() ==> #[trigger] encode_all::<C>(names)[k] == encode::<C>(names[k]),
            seqs_view(out@) == head + encode_all::<C>(names).subrange(0, i as int),
        decreases g.names.len() - i,
    {
        let ghost before = seqs_view(out@);
        out.push(encode_line::<C>(&g.names[i]));
        assert(encode_all::<C>(names).subrange(0, i + 1) =~= encode_all::<C>(names).subrange(0, i as int).push(
            encode::<C>(names[i as int]),
        ));
        assert(seqs_view(out@) =~= before.push(encode::<C>(names[i as int])));
        i += 1;
    }
    assert(encode_all::<C>(names).subrange(0, names.len() as int) =~= encode_all::<C>(names));
    out
}

fn unparse_document_impl<C: Codec>(doc: &Vec<Group>) -> (r: Vec<u8>)
    ensures
        r@ == unparse_document::<C>(doc_view(doc@)),
{
    proof {
        lemma_codec_ok_of::<C>();
    }
    let ghost dv = doc_view(doc@);
    let mut lines: Vec<Vec<u8>> = Vec::new();
    let mut k: usize = 0;
    assert(dv.subrange(0, 0) =~= Seq::<GroupS>::empty());
    assert(groups_lines::<C>(Seq::<GroupS>::empty()) == Seq::<Seq<Seq<u8>>>::empty());
    assert(seqs_view(lines@) =~= join_groups(Seq::<Seq<Seq<u8>>>::empty()));
    while k < doc.len()
        invariant
            k <= doc.len(),
            dv == doc_view(doc@),
            codec_ok::<C>(),
            seqs_view(lines@) == join_groups(groups_lines::<C>(dv.subrange(0, k as int))),
        decreases doc.len() - k,
    {
        let ghost done = groups_lines::<C>(dv.subrange(0, k as int));
        let g = group_lines_exec::<C>(&doc[k]);
        let ghost gv = seqs_view(g@);
        proof {
            assert(dv.subrange(0, k + 1) =~= dv.subrange(0, k as int).push(doc@[k as int]@));
            lemma_groups_lines_push::<C>(dv.subrange(0, k as int), doc@[k as int]@);
            lemma_groups_lines_len::<C>(dv.subrange(0, k as int));
            lemma_join_push::<C>(done, gv);
        }
        let ghost before = seqs_view(lines@);
        if k > 0 {
            lines.push(Vec::new());
        }
        let mut j: usize = 0;
        let ghost mid = seqs_view(lines@);
        while j < g.len()
            invariant
                j <= g.len(),
                gv == seqs_view(g@),
                seqs_view(lines@) == mid + gv.subrange(0, j as int),
            decreases g.len() - j,
        {
            let ghost b2 = seqs_view(lines@);
            let mut line: Vec<u8> = Vec::new();
            let src = &g[j];
            let mut q: usize = 0;
            while q < src.len()
                invariant
                    q <= src.len(),
                    line@ == src@.subrange(0, q as int),
                decreases src.len() - q,
            {
                line.push(src[q]);
                assert(src@.subrange(0, q + 1) =~= src@.subrange(0, q as int).push(src@[q as int]));
                q += 1;
            }
            assert(src@.subrange(0, src@.len() as int) =~= src@);
            lines.push(line);
            assert(gv.subrange(0, j + 1) =~= gv.subrange(0, j as int).push(gv[j as int]));
            assert(seqs_view(lines@) =~= b2.push(gv[j as int]));
            j += 1;
        }
        assert(gv.subrange(0, gv.len() as int) =~= gv);
        if k > 0 {
            assert(mid =~= before + seq![Seq::<u8>::empty()]);
            assert(seqs_view(lines@) =~= before + seq![Seq::<u8>::empty()] + gv);
        } else {
            assert(done == Seq::<Seq<Seq<u8>>>::empty());
            assert(before =~= Seq::<Seq<u8>>::empty());
            assert(seqs_view(lines@) =~= gv);
        }
        k += 1;
    }
    assert(dv.subrange(0, dv.len() as int) =~= dv);
    unparse_lines_exec::<C>(&lines)
}

pub open spec fn pview(ok: bool, doc: Seq<Group>, fresh: bool) -> PState {
    PState { ok, doc: doc_view(doc), fresh }
}

fn decode_document_impl<C: Codec>(input: &Vec<u8>) -> (r: Option<Vec<Group>>)
    ensures
        match r {
            Some(d) => parse_document::<C>(input@) == Some(doc_view(d@)),
            None => parse_document::<C>(input@) == None::<Seq<GroupS>>,
        },
{
    let dl = C::delim_exec();
    let (lines, cur) = split_exec(input, dl);
    if cur.len() > 0 {
        return None;
    }
    let ghost lv = seqs_view(lines@);
    assert(split_lines(input@, C::delim()) == Some(lv));
    let mut ok = true;
    let mut doc: Vec<Group> = Vec::new();
    let mut fresh = true;
    let mut i: usize = 0;
    assert(lv.subrange(0, 0) =~= Seq::<Seq<u8>>::empty());
    assert(doc_view(doc@) =~= Seq::<GroupS>::empty());
    while i < lines.len()
        invariant
            i <= lines.len(),
            lv == seqs_view(lines@),
            pview(ok, doc@, fresh) == prun::<C>(pinit(), lv.subrange(0, i as int)),
            !fresh ==> doc.len() > 0,
        decreases lines.len() - i,
    {
        let ghost pre = lv.subrange(0, i as int);
        assert(lv.subrange(0, i + 1).subrange(0, i as int) =~= pre);
        assert(lv.subrange(0, i + 1)[i as int] == lines@[i as int]@);
        let ghost dv = doc_view(doc@);
        let line = &lines[i];
        if ok {
            if line.len() == 0 {
                if fresh {
                    ok = false;
                    doc = Vec::new();
                    assert(doc_view(doc@) =~= Seq::<GroupS>::empty());
                } else {
                    fresh = true;
                }
            } else {
                match dec_line_exec::<C>(line) {
                    None => {
                        ok = false;
                        doc = Vec::new();
                        fresh = true;
                        assert(doc_view(doc@) =~= Seq::<GroupS>::empty());
                    },
                    Some((v, h)) => {
                        let ghost vv = v@;
                        if h {
                            if fresh {
                                let g = Group { header: Some(v), names: Vec::new() };
                                assert(seqs_view(g.names@) =~= Seq::<Seq<u8>>::empty());
                                let ghost gv = g@;
                                doc.push(g);
                                fresh = false;
                                assert(doc_view(doc@) =~= dv.push(gv));
                            } else {
                                ok = false;
                                doc = Vec::new();
                                fresh = true;
                                assert(doc_view(doc@) =~= Seq::<GroupS>::empty());
                            }
                        } else if fresh {
                            if doc.len() == 0 {
                                let mut names: Vec<Vec<u8>> = Vec::new();
                                names.push(v);
                                assert(seqs_view(names@) =~= seq![vv]);
                                let g = Group { header: None, names };
                                let ghost gv = g@;
                                doc.push(g);
                                fresh = false;
                                assert(doc_view(doc@) =~= seq![gv]);
                            } else {
                                ok = false;
                                doc = Vec::new();
                                fresh = true;
                                assert(doc_view(doc@) =~= Seq::<GroupS>::empty());
                            }
                        } else {
                            let ghost d0 = doc@;
                            match doc.pop() {
                                Some(g) => {
                                    let ghost g0 = g@;
                                    let mut g = g;
                                    g.names.push(v);
                                    assert(seqs_view(g.names@) =~= g0.names.push(vv));
                                    doc.push(g);
                                    assert(doc@ =~= d0.update(d0.len() - 1, doc@[d0.len() - 1]));
                                    assert(doc_view(doc@) =~= add_name(dv, vv));
                                },
                                None => {},
                            }
                        }
                    },
                }
            }
        }
        i += 1;
    }
    assert(lv.subrange(0, lv.len() as int) =~= lv);
    if ok && !(fresh && doc.len() > 0) {
        Some(doc)
    } else {
        None
    }
}
// </vc-helpers>

// ===========================================================================
// Executable operations (D5): generic, verified for every Codec
// ===========================================================================

pub fn encode_into<C: Codec>(out: &mut Vec<u8>, s: &Vec<u8>)
    ensures
        final(out)@ == old(out)@ + encode::<C>(s@),
{
    // <vc-code>
    let ghost o = out@;
    let mut i: usize = 0;
    assert(s@.subrange(0, s@.len() as int) =~= s@);
    assert(o + encode::<C>(s@) =~= o + encode::<C>(s@));
    while i < s.len()
        invariant
            i <= s.len(),
            out@ + encode::<C>(s@.subrange(i as int, s@.len() as int)) == o + encode::<C>(s@),
        decreases s.len() - i,
    {
        let ghost t = s@.subrange(i as int, s@.len() as int);
        let ghost rest = s@.subrange(i + 1, s@.len() as int);
        assert(t.subrange(1, t.len() as int) =~= rest);
        assert(t[0] == s@[i as int]);
        assert(encode::<C>(t) == C::code(s@[i as int]) + encode::<C>(rest));
        let ghost before = out@;
        C::push_code(out, s[i]);
        assert(out@ + encode::<C>(rest) =~= before + encode::<C>(t));
        i += 1;
    }
    assert(s@.subrange(s@.len() as int, s@.len() as int) =~= Seq::<u8>::empty());
    assert(out@ + encode::<C>(Seq::<u8>::empty()) =~= out@);
    // </vc-code>
}

pub fn unparse_records_exec<C: Codec>(rs: &Vec<Vec<u8>>) -> (r: Vec<u8>)
    ensures
        r@ == unparse_records::<C>(seqs_view(rs@)),
{
    // <vc-code>
    let ghost all = seqs_view(rs@);
    let mut out: Vec<u8> = Vec::new();
    let d = C::delim_exec();
    let mut i: usize = 0;
    assert(all.subrange(0, all.len() as int) =~= all);
    assert(out@ + unparse_records::<C>(all) =~= unparse_records::<C>(all));
    while i < rs.len()
        invariant
            i <= rs.len(),
            all == seqs_view(rs@),
            d == C::delim(),
            out@ + unparse_lines::<C>(encode_all::<C>(all.subrange(i as int, all.len() as int))) == unparse_records::<C>(all),
        decreases rs.len() - i,
    {
        let ghost t = all.subrange(i as int, all.len() as int);
        let ghost rest = all.subrange(i + 1, all.len() as int);
        assert(t.subrange(1, t.len() as int) =~= rest);
        assert(t[0] == rs@[i as int]@);
        let ghost et = encode_all::<C>(t);
        assert(et == seq![encode::<C>(t[0])] + encode_all::<C>(rest));
        assert(et.subrange(1, et.len() as int) =~= encode_all::<C>(rest));
        assert(unparse_lines::<C>(et) == et[0] + seq![d] + unparse_lines::<C>(encode_all::<C>(rest)));
        let ghost before = out@;
        encode_into::<C>(&mut out, &rs[i]);
        out.push(d);
        assert(out@ + unparse_lines::<C>(encode_all::<C>(rest)) =~= before + unparse_lines::<C>(et));
        i += 1;
    }
    assert(all.subrange(all.len() as int, all.len() as int) =~= Seq::<Seq<u8>>::empty());
    assert(encode_all::<C>(Seq::<Seq<u8>>::empty()) == Seq::<Seq<u8>>::empty());
    assert(unparse_lines::<C>(Seq::<Seq<u8>>::empty()) == Seq::<u8>::empty());
    assert(out@ + Seq::<u8>::empty() =~= out@);
    out
    // </vc-code>
}

/// Count delimiters chunk by chunk; `None` on u64 overflow.
pub fn count_delims<C: Codec>(acc: u64, chunk: &Vec<u8>) -> (r: Option<u64>)
    ensures
        r == (if acc + count_byte(chunk@, C::delim()) <= u64::MAX {
            Some((acc + count_byte(chunk@, C::delim())) as u64)
        } else {
            None::<u64>
        }),
{
    // <vc-code>
    let d = C::delim_exec();
    let mut n: u64 = acc;
    let mut i: usize = 0;
    assert(chunk@.subrange(0, chunk@.len() as int) =~= chunk@);
    while i < chunk.len()
        invariant
            i <= chunk.len(),
            d == C::delim(),
            n + count_byte(chunk@.subrange(i as int, chunk@.len() as int), d) == acc + count_byte(chunk@, d),
        decreases chunk.len() - i,
    {
        let ghost t = chunk@.subrange(i as int, chunk@.len() as int);
        assert(t.subrange(1, t.len() as int) =~= chunk@.subrange(i + 1, chunk@.len() as int));
        assert(t[0] == chunk@[i as int]);
        if chunk[i] == d {
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

/// Strict record decoder: `Some(rs)` iff `input` is an unparse of records,
/// and then `rs` is the only such list.
pub fn decode_records<C: Codec>(input: &Vec<u8>) -> (r: Option<Vec<Vec<u8>>>)
    ensures
        match r {
            Some(rs) => {
                &&& unparse_records::<C>(seqs_view(rs@)) == input@
                &&& forall|x: Seq<Seq<u8>>| #[trigger] unparse_records::<C>(x) == input@ ==> x == seqs_view(rs@)
            },
            None => forall|x: Seq<Seq<u8>>| #[trigger] unparse_records::<C>(x) != input@,
        },
{
    // <vc-code>
    let r = decode_records_impl::<C>(input);
    proof {
        lemma_codec_ok_of::<C>();
        match &r {
            Some(rs) => {
                lemma_records_reverse::<C>(input@);
                assert forall|x: Seq<Seq<u8>>| #[trigger] unparse_records::<C>(x) == input@ implies x == seqs_view(rs@) by {
                    lemma_records_round_trip::<C>(x);
                }
            },
            None => {
                assert forall|x: Seq<Seq<u8>>| #[trigger] unparse_records::<C>(x) != input@ by {
                    lemma_records_round_trip::<C>(x);
                }
            },
        }
    }
    r
    // </vc-code>
}

pub fn unparse_document_exec<C: Codec>(doc: &Vec<Group>) -> (r: Vec<u8>)
    ensures
        r@ == unparse_document::<C>(doc_view(doc@)),
{
    // <vc-code>
    unparse_document_impl::<C>(doc)
    // </vc-code>
}

/// Strict document decoder (P1/P2): `Some(d)` iff `input` is the unparse of a
/// well-formed document, and then `d` is that (unique) document.
pub fn decode_document<C: Codec>(input: &Vec<u8>) -> (r: Option<Vec<Group>>)
    ensures
        match r {
            Some(d) => {
                &&& wf_document(doc_view(d@))
                &&& unparse_document::<C>(doc_view(d@)) == input@
                &&& forall|x: Seq<GroupS>| wf_document(x) && #[trigger] unparse_document::<C>(x) == input@ ==> x
                    == doc_view(d@)
            },
            None => forall|x: Seq<GroupS>| wf_document(x) ==> #[trigger] unparse_document::<C>(x) != input@,
        },
{
    // <vc-code>
    let r = decode_document_impl::<C>(input);
    proof {
        lemma_codec_ok_of::<C>();
        match &r {
            Some(d) => {
                lemma_document_reverse::<C>(input@);
                assert forall|x: Seq<GroupS>| wf_document(x) && #[trigger] unparse_document::<C>(x) == input@ implies x
                    == doc_view(d@) by {
                    lemma_document_round_trip::<C>(x);
                }
            },
            None => {
                assert forall|x: Seq<GroupS>| wf_document(x) implies #[trigger] unparse_document::<C>(x) != input@ by {
                    lemma_document_round_trip::<C>(x);
                }
            },
        }
    }
    r
    // </vc-code>
}

/// Ready-made exec table for any escape family.
pub fn family_push_code<F: EscapeFamily>(out: &mut Vec<u8>, b: u8)
    ensures
        final(out)@ == old(out)@ + family_table::<F>(b),
{
    // <vc-code>
    let ghost o = out@;
    if F::literal_exec(b) {
        out.push(b);
    } else {
        match F::short_exec(b) {
            Some(s) => {
                out.push(F::esc_exec());
                out.push(s);
            },
            None => {
                let hi = b / 16;
                let lo = b % 16;
                out.push(F::esc_exec());
                out.push(120u8);
                out.push(if hi < 10 { 48 + hi } else { 87 + hi });
                out.push(if lo < 10 { 48 + lo } else { 87 + lo });
            },
        }
    }
    assert(out@ =~= o + family_table::<F>(b));
    // </vc-code>
}

// ===========================================================================
// Theorems (D4, D14): statements frozen, proofs are vericode
// ===========================================================================

/// T1: the delimiter count of a record stream equals the number of records.
pub proof fn theorem_record_count<C: Codec>(rs: Seq<Seq<u8>>)
    requires
        codec_ok::<C>(),
    ensures
        count_byte(unparse_records::<C>(rs), C::delim()) == rs.len(),
{
    // <vc-code>
    lemma_record_count::<C>(rs);
    // </vc-code>
}

/// T4: counting chunk by chunk gives the count of the whole.
pub proof fn theorem_count_concat(a: Seq<u8>, b: Seq<u8>, d: u8)
    ensures
        count_byte(a + b, d) == count_byte(a, d) + count_byte(b, d),
{
    // <vc-code>
    lemma_count_concat(a, b, d);
    // </vc-code>
}

/// T2: record streams are injective (no value can forge or hide a record).
pub proof fn theorem_records_injective<C: Codec>(x: Seq<Seq<u8>>, y: Seq<Seq<u8>>)
    requires
        codec_ok::<C>(),
        unparse_records::<C>(x) == unparse_records::<C>(y),
    ensures
        x == y,
{
    // <vc-code>
    lemma_records_injective::<C>(x, y);
    // </vc-code>
}

/// T3: parse(unparse(x)) = x is well defined: different well-formed documents
/// never print the same bytes (no structure injection).
pub proof fn theorem_document_injective<C: Codec>(x: Seq<GroupS>, y: Seq<GroupS>)
    requires
        codec_ok::<C>(),
        wf_document(x),
        wf_document(y),
        unparse_document::<C>(x) == unparse_document::<C>(y),
    ensures
        x == y,
{
    // <vc-code>
    lemma_document_injective::<C>(x, y);
    // </vc-code>
}

/// P2 (D14): every escape family whose per-byte facts hold is a valid codec.
pub proof fn theorem_family_codec_ok(
    code: spec_fn(u8) -> Seq<u8>,
    esc: u8,
    literal: spec_fn(u8) -> bool,
    short: spec_fn(u8) -> Option<u8>,
    short_inv: spec_fn(u8) -> Option<u8>,
    d: u8,
    m: u8,
)
    requires
        family_conditions(esc, literal, short, short_inv, d, m),
        forall|b: u8| #[trigger] code(b) == family_code(esc, literal, short, b),
    ensures
        codec_conditions(code, d, m),
{
    // <vc-code>
    lemma_family_codec_ok(code, esc, literal, short, short_inv, d, m);
    // </vc-code>
}

// ===========================================================================
// Token languages (0.2.0, D15–D25): SQL, shell, CSV, …
// ===========================================================================

/// D15: a token of a token language (spec view).
pub enum TokenS {
    /// keyword, identifier or punctuation from the language's whitelist
    Word(Seq<u8>),
    /// one boundary byte (e.g. a space)
    Boundary(u8),
    /// a number, rendered in decimal
    Num(u64),
    /// untrusted data in context `k`
    Data(u8, Seq<u8>),
}

/// The parameters of a token language, as plain spec functions.
pub struct LangS {
    pub boundary: spec_fn(u8) -> bool,
    pub word: spec_fn(Seq<u8>) -> bool,
    pub ctx: spec_fn(u8) -> bool,
    pub open: spec_fn(u8) -> Seq<u8>,
    pub close: spec_fn(u8) -> Seq<u8>,
    pub allowed: spec_fn(u8, u8) -> bool,
    pub code: spec_fn(u8, u8) -> Seq<u8>,
}

pub open spec fn is_digit(b: u8) -> bool {
    48 <= b && b <= 57
}

/// D17: the conditions a token language must meet.
pub open spec fn token_lang_conditions(g: LangS) -> bool {
    // boundaries are never digits
    &&& forall|b: u8| #[trigger] (g.boundary)(b) ==> !is_digit(b)
    // contexts: delimiters non-empty; an opening delimiter never starts with a digit or a boundary
    &&& forall|k: u8|
        #[trigger] (g.ctx)(k) ==> (g.open)(k).len() > 0 && (g.close)(k).len() > 0 && !is_digit((g.open)(k)[0])
            && !(g.boundary)((g.open)(k)[0])
    // opening delimiters of different contexts are prefix-incomparable
    &&& forall|k: u8, j: u8|
        (#[trigger] (g.ctx)(k)) && (#[trigger] (g.ctx)(j)) && k != j ==> !is_prefix((g.open)(k), (g.open)(j))
    // codes of allowed bytes: non-empty
    &&& forall|k: u8, b: u8| (g.ctx)(k) && #[trigger] (g.allowed)(k, b) ==> ((g.code)(k, b)).len() > 0
    // codes of allowed bytes: prefix-free
    &&& forall|k: u8, b: u8, c: u8|
        (g.ctx)(k) && (#[trigger] (g.allowed)(k, b)) && (#[trigger] (g.allowed)(k, c)) && b != c ==> !is_prefix(
            (g.code)(k, b),
            (g.code)(k, c),
        )
    // data can't end its literal early: no code is prefix-comparable with close + boundary
    &&& forall|k: u8, b: u8, s: u8|
        (g.ctx)(k) && (#[trigger] (g.allowed)(k, b)) && (#[trigger] (g.boundary)(s)) ==> !is_prefix(
            (g.code)(k, b),
            (g.close)(k) + seq![s],
        ) && !is_prefix((g.close)(k) + seq![s], (g.code)(k, b))
    // ... nor be a prefix of the bare closing delimiter (end of text)
    &&& forall|k: u8, b: u8| (g.ctx)(k) && #[trigger] (g.allowed)(k, b) ==> !is_prefix((g.code)(k, b), (g.close)(k))
    // words: non-empty, no boundary bytes, not starting with a digit or an opening delimiter
    &&& forall|w: Seq<u8>|
        #[trigger] (g.word)(w) ==> w.len() > 0 && !is_digit(w[0]) && (forall|i: int|
            0 <= i < w.len() ==> !(g.boundary)(#[trigger] w[i])) && (forall|k: u8|
            #[trigger] (g.ctx)(k) ==> !is_prefix((g.open)(k), w))
}

pub trait TokenLang: Sized {
    spec fn is_boundary(b: u8) -> bool;

    spec fn is_word(w: Seq<u8>) -> bool;

    spec fn has_context(k: u8) -> bool;

    spec fn open(k: u8) -> Seq<u8>;

    spec fn close(k: u8) -> Seq<u8>;

    spec fn allowed(k: u8, b: u8) -> bool;

    spec fn code(k: u8, b: u8) -> Seq<u8>;

    fn is_boundary_exec(b: u8) -> (r: bool)
        ensures
            r == Self::is_boundary(b),
    ;

    fn is_word_exec(w: &Vec<u8>) -> (r: bool)
        ensures
            r == Self::is_word(w@),
    ;

    fn has_context_exec(k: u8) -> (r: bool)
        ensures
            r == Self::has_context(k),
    ;

    fn open_exec(k: u8) -> (r: Vec<u8>)
        ensures
            r@ == Self::open(k),
    ;

    fn close_exec(k: u8) -> (r: Vec<u8>)
        ensures
            r@ == Self::close(k),
    ;

    fn allowed_exec(k: u8, b: u8) -> (r: bool)
        ensures
            r == Self::allowed(k, b),
    ;

    fn push_code(k: u8, out: &mut Vec<u8>, b: u8)
        ensures
            final(out)@ == old(out)@ + Self::code(k, b),
    ;

    /// Discharge D17 (this is `lang_ok::<Self>()`).
    proof fn lemma_lang_ok()
        ensures
            token_lang_conditions(
                LangS {
                    boundary: |b: u8| Self::is_boundary(b),
                    word: |w: Seq<u8>| Self::is_word(w),
                    ctx: |k: u8| Self::has_context(k),
                    open: |k: u8| Self::open(k),
                    close: |k: u8| Self::close(k),
                    allowed: |k: u8, b: u8| Self::allowed(k, b),
                    code: |k: u8, b: u8| Self::code(k, b),
                },
            ),
    ;
}

pub open spec fn lang_of<L: TokenLang>() -> LangS {
    LangS {
        boundary: |b: u8| L::is_boundary(b),
        word: |w: Seq<u8>| L::is_word(w),
        ctx: |k: u8| L::has_context(k),
        open: |k: u8| L::open(k),
        close: |k: u8| L::close(k),
        allowed: |k: u8, b: u8| L::allowed(k, b),
        code: |k: u8, b: u8| L::code(k, b),
    }
}

pub open spec fn lang_ok<L: TokenLang>() -> bool {
    token_lang_conditions(lang_of::<L>())
}

/// Decimal digits of `n` (no leading zeros; `0` is "0").
pub open spec fn decimal(n: u64) -> Seq<u8>
    decreases n,
{
    if n < 10 {
        seq![(48 + n) as u8]
    } else {
        decimal(n / 10) + seq![(48 + n % 10) as u8]
    }
}

/// Encode the data `v` of context `k` byte by byte.
pub open spec fn encode_ctx(g: LangS, k: u8, v: Seq<u8>) -> Seq<u8>
    decreases v.len(),
{
    if v.len() == 0 {
        seq![]
    } else {
        (g.code)(k, v[0]) + encode_ctx(g, k, v.subrange(1, v.len() as int))
    }
}

pub open spec fn render(g: LangS, t: TokenS) -> Seq<u8> {
    match t {
        TokenS::Word(w) => w,
        TokenS::Boundary(b) => seq![b],
        TokenS::Num(n) => decimal(n),
        TokenS::Data(k, v) => (g.open)(k) + encode_ctx(g, k, v) + (g.close)(k),
    }
}

/// The unparser of a token language: render every token, concatenate.
pub open spec fn unparse_tokens(g: LangS, ts: Seq<TokenS>) -> Seq<u8>
    decreases ts.len(),
{
    if ts.len() == 0 {
        seq![]
    } else {
        render(g, ts[0]) + unparse_tokens(g, ts.subrange(1, ts.len() as int))
    }
}

pub open spec fn in_alphabet(g: LangS, k: u8, v: Seq<u8>) -> bool {
    forall|i: int| 0 <= i < v.len() ==> (g.allowed)(k, #[trigger] v[i])
}

pub open spec fn is_boundary_token(t: TokenS) -> bool {
    match t {
        TokenS::Boundary(_) => true,
        _ => false,
    }
}

pub open spec fn token_ok(g: LangS, t: TokenS) -> bool {
    match t {
        TokenS::Word(w) => (g.word)(w),
        TokenS::Boundary(b) => (g.boundary)(b),
        TokenS::Num(_) => true,
        TokenS::Data(k, v) => (g.ctx)(k) && in_alphabet(g, k, v),
    }
}

/// D15: valid tokens, and never two non-boundary tokens side by side.
pub open spec fn wf_tokens(g: LangS, ts: Seq<TokenS>) -> bool {
    &&& forall|i: int| 0 <= i < ts.len() ==> token_ok(g, #[trigger] ts[i])
    &&& forall|i: int|
        0 <= i < ts.len() - 1 ==> is_boundary_token(#[trigger] ts[i]) || is_boundary_token(ts[i + 1])
}

/// D19: the structure of a token sequence (payloads of data and numbers erased).
pub open spec fn template_token(t: TokenS) -> TokenS {
    match t {
        TokenS::Num(_) => TokenS::Num(0),
        TokenS::Data(k, _) => TokenS::Data(k, seq![]),
        _ => t,
    }
}

pub open spec fn template(ts: Seq<TokenS>) -> Seq<TokenS> {
    Seq::new(ts.len(), |i: int| template_token(ts[i]))
}

// ---- executable tokens ----

pub enum Token {
    Word(Vec<u8>),
    Boundary(u8),
    Num(u64),
    Data(u8, Vec<u8>),
}

impl View for Token {
    type V = TokenS;

    open spec fn view(&self) -> TokenS {
        match self {
            Token::Word(w) => TokenS::Word(w@),
            Token::Boundary(b) => TokenS::Boundary(*b),
            Token::Num(n) => TokenS::Num(*n),
            Token::Data(k, v) => TokenS::Data(*k, v@),
        }
    }
}

pub open spec fn tokens_view(ts: Seq<Token>) -> Seq<TokenS> {
    Seq::new(ts.len(), |i: int| ts[i]@)
}

// ---- D20: the LIKE pattern language (inner language of a SQL string) ----

/// Escape `%`, `_` and `\` with `\` (SQL `LIKE … ESCAPE '\'`).
pub open spec fn like_escape(s: Seq<u8>) -> Seq<u8>
    decreases s.len(),
{
    if s.len() == 0 {
        seq![]
    } else {
        (if s[0] == 37 || s[0] == 95 || s[0] == 92 {
            seq![92u8, s[0]]
        } else {
            seq![s[0]]
        }) + like_escape(s.subrange(1, s.len() as int))
    }
}

/// A substring pattern: `%` + escaped text + `%`.
pub open spec fn like_substring(s: Seq<u8>) -> Seq<u8> {
    seq![37u8] + like_escape(s) + seq![37u8]
}

// ---- D21: shipped instances ----

/// SQL (SQLite subset). Contexts: 0 = string literal `'…'` (`'` -> `''`),
/// 1 = quoted identifier `"…"` (`"` -> `""`); NUL is outside both alphabets.
/// Boundary: space. Words: identifiers/keywords `[A-Za-z_][A-Za-z0-9_]*` and
/// the punctuation `( ) , = * ; . < > + -` and `||`.
pub struct SqlLang;

pub open spec fn is_alpha_(b: u8) -> bool {
    (65 <= b && b <= 90) || (97 <= b && b <= 122) || b == 95
}

pub open spec fn sql_punct(w: Seq<u8>) -> bool {
    (w.len() == 1 && (w[0] == 40 || w[0] == 41 || w[0] == 44 || w[0] == 61 || w[0] == 42 || w[0] == 59
        || w[0] == 46 || w[0] == 60 || w[0] == 62 || w[0] == 43 || w[0] == 45)) || w == seq![124u8, 124u8]
}

pub open spec fn sql_ident(w: Seq<u8>) -> bool {
    w.len() > 0 && is_alpha_(w[0]) && forall|i: int| 1 <= i < w.len() ==> is_alpha_(#[trigger] w[i]) || is_digit(w[i])
}

/// POSIX shell words. Context 0 = single-quoted `'…'` (`'` -> `'\''`), NUL
/// excluded. Boundary: space. Words: `[A-Za-z_./=:+-][A-Za-z0-9_./=:+-]*`.
pub struct ShellLang;

pub open spec fn shell_word_byte(b: u8) -> bool {
    is_alpha_(b) || is_digit(b) || b == 46 || b == 47 || b == 61 || b == 58 || b == 43 || b == 45
}

/// CSV (RFC 4180 quoting). Context 0 = quoted field `"…"` (`"` -> `""`),
/// every byte allowed. Boundaries: `,` and LF. No bare words.
pub struct CsvLang;

impl TokenLang for SqlLang {
    open spec fn is_boundary(b: u8) -> bool {
        b == 32
    }

    open spec fn is_word(w: Seq<u8>) -> bool {
        sql_ident(w) || sql_punct(w)
    }

    open spec fn has_context(k: u8) -> bool {
        k == 0 || k == 1
    }

    open spec fn open(k: u8) -> Seq<u8> {
        if k == 0 {
            seq![39u8]
        } else {
            seq![34u8]
        }
    }

    open spec fn close(k: u8) -> Seq<u8> {
        if k == 0 {
            seq![39u8]
        } else {
            seq![34u8]
        }
    }

    open spec fn allowed(k: u8, b: u8) -> bool {
        b != 0
    }

    open spec fn code(k: u8, b: u8) -> Seq<u8> {
        if k == 0 && b == 39 {
            seq![39u8, 39u8]
        } else if k == 1 && b == 34 {
            seq![34u8, 34u8]
        } else {
            seq![b]
        }
    }

    fn is_boundary_exec(b: u8) -> (r: bool) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn is_word_exec(w: &Vec<u8>) -> (r: bool) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn has_context_exec(k: u8) -> (r: bool) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn open_exec(k: u8) -> (r: Vec<u8>) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn close_exec(k: u8) -> (r: Vec<u8>) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn allowed_exec(k: u8, b: u8) -> (r: bool) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn push_code(k: u8, out: &mut Vec<u8>, b: u8) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    proof fn lemma_lang_ok() {
        // <vc-code>
        assume(false);
        // </vc-code>
    }
}

impl TokenLang for ShellLang {
    open spec fn is_boundary(b: u8) -> bool {
        b == 32
    }

    open spec fn is_word(w: Seq<u8>) -> bool {
        w.len() > 0 && !is_digit(w[0]) && forall|i: int| 0 <= i < w.len() ==> shell_word_byte(#[trigger] w[i])
    }

    open spec fn has_context(k: u8) -> bool {
        k == 0
    }

    open spec fn open(k: u8) -> Seq<u8> {
        seq![39u8]
    }

    open spec fn close(k: u8) -> Seq<u8> {
        seq![39u8]
    }

    open spec fn allowed(k: u8, b: u8) -> bool {
        b != 0
    }

    open spec fn code(k: u8, b: u8) -> Seq<u8> {
        if b == 39 {
            seq![39u8, 92u8, 39u8, 39u8]
        } else {
            seq![b]
        }
    }

    fn is_boundary_exec(b: u8) -> (r: bool) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn is_word_exec(w: &Vec<u8>) -> (r: bool) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn has_context_exec(k: u8) -> (r: bool) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn open_exec(k: u8) -> (r: Vec<u8>) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn close_exec(k: u8) -> (r: Vec<u8>) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn allowed_exec(k: u8, b: u8) -> (r: bool) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn push_code(k: u8, out: &mut Vec<u8>, b: u8) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    proof fn lemma_lang_ok() {
        // <vc-code>
        assume(false);
        // </vc-code>
    }
}

impl TokenLang for CsvLang {
    open spec fn is_boundary(b: u8) -> bool {
        b == 44 || b == 10
    }

    open spec fn is_word(w: Seq<u8>) -> bool {
        false
    }

    open spec fn has_context(k: u8) -> bool {
        k == 0
    }

    open spec fn open(k: u8) -> Seq<u8> {
        seq![34u8]
    }

    open spec fn close(k: u8) -> Seq<u8> {
        seq![34u8]
    }

    open spec fn allowed(k: u8, b: u8) -> bool {
        true
    }

    open spec fn code(k: u8, b: u8) -> Seq<u8> {
        if b == 34 {
            seq![34u8, 34u8]
        } else {
            seq![b]
        }
    }

    fn is_boundary_exec(b: u8) -> (r: bool) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn is_word_exec(w: &Vec<u8>) -> (r: bool) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn has_context_exec(k: u8) -> (r: bool) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn open_exec(k: u8) -> (r: Vec<u8>) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn close_exec(k: u8) -> (r: Vec<u8>) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn allowed_exec(k: u8, b: u8) -> (r: bool) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn push_code(k: u8, out: &mut Vec<u8>, b: u8) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    proof fn lemma_lang_ok() {
        // <vc-code>
        assume(false);
        // </vc-code>
    }
}

// ---- D22: generic executable operations ----

/// `true` iff every byte of `v` is in context `k`'s alphabet.
pub fn in_alphabet_exec<L: TokenLang>(k: u8, v: &Vec<u8>) -> (r: bool)
    ensures
        r == in_alphabet(lang_of::<L>(), k, v@),
{
    // <vc-code>
    assume(false);
    unreached()
    // </vc-code>
}

pub fn unparse_tokens_exec<L: TokenLang>(ts: &Vec<Token>) -> (r: Vec<u8>)
    requires
        wf_tokens(lang_of::<L>(), tokens_view(ts@)),
    ensures
        r@ == unparse_tokens(lang_of::<L>(), tokens_view(ts@)),
{
    // <vc-code>
    assume(false);
    unreached()
    // </vc-code>
}

/// Strict lexer: `Some(ts)` iff `text` is the unparse of a well-formed token
/// sequence, and then `ts` is the only one (D18).
pub fn lex_tokens<L: TokenLang>(text: &Vec<u8>) -> (r: Option<Vec<Token>>)
    ensures
        match r {
            Some(ts) => {
                &&& wf_tokens(lang_of::<L>(), tokens_view(ts@))
                &&& unparse_tokens(lang_of::<L>(), tokens_view(ts@)) == text@
                &&& forall|x: Seq<TokenS>|
                    wf_tokens(lang_of::<L>(), x) && #[trigger] unparse_tokens(lang_of::<L>(), x) == text@ ==> x
                        == tokens_view(ts@)
            },
            None => forall|x: Seq<TokenS>|
                wf_tokens(lang_of::<L>(), x) ==> #[trigger] unparse_tokens(lang_of::<L>(), x) != text@,
        },
{
    // <vc-code>
    assume(false);
    unreached()
    // </vc-code>
}

pub fn like_substring_exec(s: &Vec<u8>) -> (r: Vec<u8>)
    ensures
        r@ == like_substring(s@),
{
    // <vc-code>
    assume(false);
    unreached()
    // </vc-code>
}

// ---- D18–D20: theorems ----

/// D18: the token unparser is injective: no data can change the token
/// sequence (lex(unparse(ts)) = ts).
pub proof fn theorem_tokens_injective(g: LangS, x: Seq<TokenS>, y: Seq<TokenS>)
    requires
        token_lang_conditions(g),
        wf_tokens(g, x),
        wf_tokens(g, y),
        unparse_tokens(g, x) == unparse_tokens(g, y),
    ensures
        x == y,
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

/// D19: the text an app emits determines its template: if two inputs
/// produce texts with different templates, the texts differ.
pub proof fn theorem_structure_independent(g: LangS, x: Seq<TokenS>, y: Seq<TokenS>)
    requires
        token_lang_conditions(g),
        wf_tokens(g, x),
        wf_tokens(g, y),
        template(x) != template(y),
    ensures
        unparse_tokens(g, x) != unparse_tokens(g, y),
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

/// D20: the LIKE substring pattern is injective and keeps NUL-free text NUL-free.
pub proof fn theorem_like_substring(a: Seq<u8>, b: Seq<u8>)
    ensures
        like_substring(a) == like_substring(b) ==> a == b,
        (forall|i: int| 0 <= i < a.len() ==> a[i] != 0) ==> (forall|i: int|
            0 <= i < like_substring(a).len() ==> #[trigger] like_substring(a)[i] != 0),
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

/// D20: composition. If the data of position `i` is `inner(a)` resp.
/// `inner(b)` for an injective `inner`, equal texts mean equal inputs.
pub proof fn theorem_composed_injective(
    g: LangS,
    x: Seq<TokenS>,
    y: Seq<TokenS>,
    i: int,
    k: u8,
    inner: spec_fn(Seq<u8>) -> Seq<u8>,
    a: Seq<u8>,
    b: Seq<u8>,
)
    requires
        token_lang_conditions(g),
        wf_tokens(g, x),
        wf_tokens(g, y),
        0 <= i < x.len(),
        x[i] == TokenS::Data(k, inner(a)),
        i < y.len(),
        y[i] == TokenS::Data(k, inner(b)),
        forall|p: Seq<u8>, q: Seq<u8>| #[trigger] inner(p) == #[trigger] inner(q) ==> p == q,
        unparse_tokens(g, x) == unparse_tokens(g, y),
    ensures
        a == b,
{
    // <vc-code>
    assume(false);
    // </vc-code>
}

// ===========================================================================
// Spec tests: the intent's examples. Checked by Verus; they never run.
// ===========================================================================

spec fn bs() -> Seq<u8> { seq![92u8] }

proof fn spec_e1_records() {
    let rs = seq![seq![97u8, 10, 98], seq![99u8]];  // a<LF>b, c
    // a\nb<LF>c<LF>
    assert(unparse_records::<BackslashEscape>(seq![seq![97u8, 10, 98], seq![99u8]])
        =~= seq![97u8, 92, 110, 98, 10, 99, 10]) by (compute);
    assert(count_byte(seq![97u8, 92, 110, 98, 10, 99, 10], 10) == 2) by (compute);  // reject 3
}

proof fn spec_e2_document() {
    // [{-, [a]}, {x:, [b:]}]  ->  a | | x\:: | b\:
    assert(unparse_document::<BackslashEscape>(seq![
        GroupS { header: None, names: seq![seq![97u8]] },
        GroupS { header: Some(seq![120u8, 58]), names: seq![seq![98u8, 58]] },
    ]) =~= seq![97u8, 10, 10, 120, 92, 58, 58, 10, 98, 92, 58, 10]) by (compute);
    // the forged reading (header `x`, name `:`) prints differently
    assert(unparse_document::<BackslashEscape>(seq![
        GroupS { header: None, names: seq![seq![97u8]] },
        GroupS { header: Some(seq![120u8]), names: seq![seq![58u8]] },
    ]) != seq![97u8, 10, 10, 120, 92, 58, 58, 10, 98, 92, 58, 10]) by (compute);
}

/// E3: the identity table is rejected (byte LF breaks C2; `:` breaks C4).
proof fn spec_e3_identity_rejected() {
    let id = |b: u8| seq![b];
    assert(!codec_conditions(id, 10, 58)) by {
        assert(id(10u8)[0] == 10u8);
    }
}

/// E4: vls's pre-fix table (`:` as itself) is rejected by C4.
proof fn spec_e4_prefix_table_rejected() {
    let pre = |b: u8| if b == 58 { seq![58u8] } else { BackslashEscape::code(b) };
    assert(!codec_conditions(pre, 10, 58)) by {
        assert(pre(58u8)[0] == 58u8);
    }
}


// ---- token languages (E6–E11) ----

spec fn sq(v: Seq<u8>) -> Seq<TokenS> { seq![TokenS::Data(0, v)] }

/// E6: `it's` as a SQL string literal.
proof fn spec_e6_sql_quote() {
    assert(unparse_tokens(lang_of::<SqlLang>(), sq(seq![105u8, 116, 39, 115]))
        =~= seq![39u8, 105, 116, 39, 39, 115, 39]) by (compute);  // 'it''s'
}

/// E7: a classic payload stays one string token.
spec fn payload() -> Seq<u8> { seq![39u8, 41, 59, 32, 68, 82, 79, 80, 32, 84, 65, 66, 76, 69, 59, 45, 45] }  // '); DROP TABLE;--

proof fn spec_e7_payload_is_one_token(x: Seq<TokenS>) {
    assert(unparse_tokens(lang_of::<SqlLang>(), sq(payload())) =~= seq![39u8, 39, 39, 41, 59, 32, 68, 82, 79, 80,
        32, 84, 65, 66, 76, 69, 59, 45, 45, 39]) by (compute);
    SqlLang::lemma_lang_ok();
    let g = lang_of::<SqlLang>();
    if wf_tokens(g, x) && unparse_tokens(g, x) == unparse_tokens(g, sq(payload())) {
        assert(wf_tokens(g, sq(payload()))) by {
            assert(sq(payload())[0] == TokenS::Data(0, payload()));
        }
        theorem_tokens_injective(g, x, sq(payload()));
        assert(x.len() == 1);  // reject: several tokens / statements
    }
}

/// E8: a string context that doesn't double `'` violates the conditions.
proof fn spec_e8_undoubled_quote_rejected() {
    let base = lang_of::<SqlLang>();
    let g = LangS { code: |k: u8, b: u8| seq![b], ..base };
    assert(!token_lang_conditions(g)) by {
        if token_lang_conditions(g) {
            assert((g.ctx)(0u8) && (g.allowed)(0u8, 39u8) && (g.boundary)(32u8));
            assert(!is_prefix((g.code)(0u8, 39u8), (g.close)(0u8) + seq![32u8]));
            assert(((g.close)(0u8) + seq![32u8]).subrange(0, 1) =~= seq![39u8]);
        }
    }
}

/// E9: `it's` as a shell word.
proof fn spec_e9_shell_quote() {
    assert(unparse_tokens(lang_of::<ShellLang>(), sq(seq![105u8, 116, 39, 115]))
        =~= seq![39u8, 105, 116, 39, 92, 39, 39, 115, 39]) by (compute);  // 'it'\''s'
}

/// E10: a CSV row.
proof fn spec_e10_csv_row() {
    assert(unparse_tokens(lang_of::<CsvLang>(), seq![TokenS::Data(0, seq![97u8, 44, 98]), TokenS::Boundary(44),
        TokenS::Data(0, seq![120u8, 34, 121]), TokenS::Boundary(10)])
        =~= seq![34u8, 97, 44, 98, 34, 44, 34, 120, 34, 34, 121, 34, 10]) by (compute);  // "a,b","x""y"<LF>
}

/// E11: LIKE substring pattern for `50%_off`.
proof fn spec_e11_like() {
    assert(like_substring(seq![53u8, 48, 37, 95, 111, 102, 102])
        == seq![37u8, 53, 48, 92, 37, 92, 95, 111, 102, 102, 37]) by (compute_only);  // %50\%\_off%
    assert(like_substring(seq![53u8, 48, 37, 95, 111, 102, 102])
        != seq![37u8, 53, 48, 37, 95, 111, 102, 102, 37]) by (compute_only);  // reject wildcard injection
}

} // verus!

// Runtime tests (cargo test) for the executable operations.
#[cfg(test)]
mod tests {
    use super::*;

    type B = BackslashEscape;

    fn v(s: &[u8]) -> Vec<u8> {
        s.to_vec()
    }

    #[test]
    fn records_round_trip_and_count() {
        let rs = vec![v(b"a\nb"), v(b"c:"), v(b""), v(b"caf\xc3\xa9")];
        let bytes = unparse_records_exec::<B>(&rs);
        assert_eq!(bytes, v(b"a\\nb\nc\\:\n\ncaf\\xc3\\xa9\n"));
        assert_eq!(count_delims::<B>(0, &bytes), Some(4));
        assert_eq!(decode_records::<B>(&bytes), Some(rs));
        assert_eq!(count_delims::<B>(u64::MAX, &v(b"\n")), None);
    }

    #[test]
    fn e5_strict_records() {
        for bad in [&b"\\q\n"[..], b"\\x41\n", b"a", b"\\xC3\n", b"\x01\n"] {
            assert_eq!(decode_records::<B>(&v(bad)), None, "accepted {:?}", String::from_utf8_lossy(bad));
        }
    }

    // ---- token languages ----

    fn d(v: &[u8]) -> Token { Token::Data(0, v.to_vec()) }
    fn w(v: &[u8]) -> Token { Token::Word(v.to_vec()) }
    fn sp() -> Token { Token::Boundary(b' ') }

    #[test]
    fn sql_tokens_round_trip() {
        let payload = b"'); DROP TABLE notes;--";
        let q = vec![w(b"SELECT"), sp(), w(b"id"), sp(), w(b"FROM"), sp(), w(b"notes"), sp(), w(b"WHERE"), sp(),
            w(b"title"), sp(), w(b"="), sp(), d(payload), sp(), w(b"AND"), sp(), w(b"id"), sp(), w(b"="), sp(), Token::Num(42)];
        let text = unparse_tokens_exec::<SqlLang>(&q);
        assert_eq!(text, b"SELECT id FROM notes WHERE title = '''); DROP TABLE notes;--' AND id = 42".to_vec());
        let back = lex_tokens::<SqlLang>(&text).expect("lexes");
        assert_eq!(back.len(), q.len());
        assert!(matches!(&back[14], Token::Data(0, v) if v == payload));
        assert!(!in_alphabet_exec::<SqlLang>(0, &b"a\0b".to_vec()));
    }

    #[test]
    fn e12_strict_lexing() {
        for bad in [&b"'abc"[..], b"'a'b", b"SELECT  id", b"007", b"x'a'", b"'a''"] {
            assert!(lex_tokens::<SqlLang>(&bad.to_vec()).is_none(), "accepted {:?}", String::from_utf8_lossy(bad));
        }
    }

    #[test]
    fn shell_and_csv() {
        let cmd = vec![w(b"echo"), sp(), d(b"it's $HOME; rm -rf /")];
        let text = unparse_tokens_exec::<ShellLang>(&cmd);
        assert_eq!(text, b"echo 'it'\\''s $HOME; rm -rf /'".to_vec());
        assert_eq!(lex_tokens::<ShellLang>(&text).map(|t| t.len()), Some(3));
        let row = vec![d(b"a,b"), Token::Boundary(b','), d(b"x\"y\nz"), Token::Boundary(b'\n')];
        let text = unparse_tokens_exec::<CsvLang>(&row);
        assert_eq!(text, b"\"a,b\",\"x\"\"y\nz\"\n".to_vec());
        assert_eq!(lex_tokens::<CsvLang>(&text).map(|t| t.len()), Some(4));
    }

    #[test]
    fn like_pattern() {
        assert_eq!(like_substring_exec(&b"50%_off\\".to_vec()), b"%50\\%\\_off\\\\%".to_vec());
    }

    #[test]
    fn documents_round_trip_and_strict() {
        let doc = vec![
            Group { header: None, names: vec![v(b"a")] },
            Group { header: Some(v(b"x:")), names: vec![v(b"b:")] },
        ];
        let bytes = unparse_document_exec::<B>(&doc);
        assert_eq!(bytes, v(b"a\n\nx\\::\nb\\:\n"));
        let back = decode_document::<B>(&bytes).expect("round trip");
        assert_eq!(back.len(), 2);
        assert_eq!(back[1].header, Some(v(b"x:")));
        assert_eq!(back[1].names, vec![v(b"b:")]);
        for bad in [&b"\n"[..], b"a\n\nb\n", b"a:b\n", b"\\q\n"] {
            assert!(decode_document::<B>(&v(bad)).is_none(), "accepted {:?}", String::from_utf8_lossy(bad));
        }
    }
}
