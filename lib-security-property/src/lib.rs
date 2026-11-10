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
        assume(false);
        unreached()
        // </vc-code>
    }

    fn literal_exec(b: u8) -> (r: bool) {
        // <vc-code>
        assume(false);
        unreached()
        // </vc-code>
    }

    fn short_exec(b: u8) -> (r: Option<u8>) {
        // <vc-code>
        assume(false);
        unreached()
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

    proof fn lemma_codec_ok() {
        // <vc-code>
        assume(false);
        // </vc-code>
    }
}

// <vc-helpers>
// </vc-helpers>

// ===========================================================================
// Executable operations (D5): generic, verified for every Codec
// ===========================================================================

pub fn encode_into<C: Codec>(out: &mut Vec<u8>, s: &Vec<u8>)
    ensures
        final(out)@ == old(out)@ + encode::<C>(s@),
{
    // <vc-code>
    assume(false);
    unreached()
    // </vc-code>
}

pub fn unparse_records_exec<C: Codec>(rs: &Vec<Vec<u8>>) -> (r: Vec<u8>)
    ensures
        r@ == unparse_records::<C>(seqs_view(rs@)),
{
    // <vc-code>
    assume(false);
    unreached()
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
    assume(false);
    unreached()
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
    assume(false);
    unreached()
    // </vc-code>
}

pub fn unparse_document_exec<C: Codec>(doc: &Vec<Group>) -> (r: Vec<u8>)
    ensures
        r@ == unparse_document::<C>(doc_view(doc@)),
{
    // <vc-code>
    assume(false);
    unreached()
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
    assume(false);
    unreached()
    // </vc-code>
}

/// Ready-made exec table for any escape family.
pub fn family_push_code<F: EscapeFamily>(out: &mut Vec<u8>, b: u8)
    ensures
        final(out)@ == old(out)@ + family_table::<F>(b),
{
    // <vc-code>
    assume(false);
    unreached()
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
    assume(false);
    // </vc-code>
}

/// T4: counting chunk by chunk gives the count of the whole.
pub proof fn theorem_count_concat(a: Seq<u8>, b: Seq<u8>, d: u8)
    ensures
        count_byte(a + b, d) == count_byte(a, d) + count_byte(b, d),
{
    // <vc-code>
    assume(false);
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
    assume(false);
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
    assume(false);
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
