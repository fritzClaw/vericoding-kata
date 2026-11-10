# Template: proving the codec conditions for an arbitrary table

Use this when your table is not C-style (otherwise prefer
`codec-escape-family.md`, which needs no prefix-freeness proof). You prove
C0–C4 yourself, **by SMT case analysis on the table's branches**. Never
enumerate the 256 bytes with `by (compute_only)`: Verus's interpreter times
out on that.

The code below was verified as a separate consuming crate (`--no-cheating`,
0 errors). The table is written as an `if` chain; `lemma_codec_ok`
proves:

- **C1, C2, C4** (per byte) with one `assert forall … by {}` each. SMT splits
  on the branches of the table.
- **C3** (pairwise prefix-freeness) with a helper lemma: assume `code(b)` is a
  prefix of `code(c)`, compare the bytes that must agree (first byte, escape
  letter, hex digits), and conclude `b == c`. For hex codes this needs
  `b == 16 * (b / 16) + b % 16` via `nonlinear_arith`.
- **C0** (`delim != marker`) holds by computation.

`lemma_codec_ok` must ensure `codec_conditions(|b| Self::code(b), Self::delim(),
Self::marker())`. That is exactly `codec_ok::<Self>()`, spelled out because a
trait method's contract can't mention a function generic over the same trait.

```rust
use security_property::Codec;
use vstd::prelude::*;

verus! {

/// Example: an arbitrary table written directly (no escape family).
pub struct DirectTable;

pub open spec fn hex(d: u8) -> u8 {
    if d < 10 { (48 + d) as u8 } else { (87 + d) as u8 }
}

pub open spec fn direct_code(b: u8) -> Seq<u8> {
    if b == 92 { seq![92u8, 92u8] }
    else if b == 10 { seq![92u8, 110u8] }
    else if b == 58 { seq![92u8, 58u8] }
    else if 32 <= b && b <= 126 { seq![b] }
    else { seq![92u8, 120u8, hex(b / 16), hex(b % 16)] }
}

/// C3 for this table: case analysis on the shapes of both codes.
proof fn lemma_direct_prefix_free(b: u8, c: u8)
    requires b != c,
    ensures !security_property::is_prefix(direct_code(b), direct_code(c)),
{
    let (x, y) = (direct_code(b), direct_code(c));
    if security_property::is_prefix(x, y) {
        assert(y.subrange(0, x.len() as int) == x);
        assert(y[0] == x[0]);                       // same first byte
        if x.len() >= 2 { assert(y[1] == x[1]); }   // same escape letter
        if x.len() == 4 {                           // both `\xHH`: same digits
            assert(y[2] == x[2] && y[3] == x[3]);
            assert(b / 16 == c / 16 && b % 16 == c % 16);
            assert(b == 16 * (b / 16) + b % 16) by (nonlinear_arith);
            assert(c == 16 * (c / 16) + c % 16) by (nonlinear_arith);
        }
    }
}

impl Codec for DirectTable {
    open spec fn code(b: u8) -> Seq<u8> { direct_code(b) }

    open spec fn delim() -> u8 { 10 }

    open spec fn marker() -> u8 { 58 }

    fn delim_exec() -> (r: u8) { 10 }

    fn marker_exec() -> (r: u8) { 58 }

    fn push_code(out: &mut Vec<u8>, b: u8) {
        let ghost o = out@;
        if b == 92 { out.push(92); out.push(92); }
        else if b == 10 { out.push(92); out.push(110); }
        else if b == 58 { out.push(92); out.push(58); }
        else if 32 <= b && b <= 126 { out.push(b); }
        else {
            let (hi, lo) = (b / 16, b % 16);
            out.push(92); out.push(120);
            out.push(if hi < 10 { 48 + hi } else { 87 + hi });
            out.push(if lo < 10 { 48 + lo } else { 87 + lo });
        }
        assert(out@ =~= o + direct_code(b));
    }

    proof fn lemma_codec_ok() {
        let f = |b: u8| DirectTable::code(b);
        // C1, C2, C4: per byte, by SMT (no enumeration)
        assert forall|b: u8| (#[trigger] f(b)).len() > 0 by {}
        assert forall|b: u8, i: int| 0 <= i < f(b).len() implies (#[trigger] f(b)[i]) != 10 by {}
        assert forall|b: u8| (#[trigger] f(b))[0] != 58 by {}
        // C3: pairwise, via the case-analysis lemma
        assert forall|b: u8, c: u8| b != c implies !security_property::is_prefix(#[trigger] f(b), #[trigger] f(c)) by {
            lemma_direct_prefix_free(b, c);
        }
    }
}

} // verus!
```

If one of the assertions doesn't prove, the failing case is a real
ambiguity in your table: two bytes whose codes collide or prefix each other,
a code containing the delimiter, or a code starting with the marker. Fix the
table.
