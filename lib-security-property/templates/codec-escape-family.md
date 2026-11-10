# Template: a custom C-style codec (escape family)

Use this when your format escapes data C-style: some bytes stand for
themselves, a few have two-byte escapes, everything else is `ESC x HH`.
Fill in the four placeholders, and `theorem_family_codec_ok` turns a handful of
per-byte facts into the codec conditions C0–C4. You prove no prefix-freeness
yourself.

This exact code, a NUL-delimited, `=`-marked, `%`-escaped codec, was verified
as a separate consuming crate (`cargo verus verify --fwd-verus-args-to roots
-- --no-cheating`: library 109 + consumer 8 verified, 0 errors), and its
runtime round trip passes.

## Placeholders

| Placeholder | Here | Rules (F1–F3, checked by the proof) |
|---|---|---|
| escape byte `esc` | `%` (37) | `esc != delim`, `esc != marker` |
| literal set | printable ASCII except `%`, `=` | a literal is never `esc`, `delim` or `marker` |
| short escapes | `%` → `%%`, `=` → `%=` | only for non-literals; the letter is never `x` (120) or `delim`; distinct letters (give the inverse `short_inv`) |
| delimiter / marker | NUL (0) / `=` (61) | `delim != marker`; `delim` is not `x` or a hex digit `0-9a-f` |

Everything that is neither literal nor short becomes `%xHH` (lowercase hex).

## Code

```rust
use security_property::{Codec, EscapeFamily};
use vstd::prelude::*;

verus! {

/// Example: NUL-separated records, `=` header marker, `%` escape.
/// Literals: printable ASCII except `%` and `=`. Short escapes: `%%`, `%=`.
pub struct PercentEscape;

impl EscapeFamily for PercentEscape {
    open spec fn esc() -> u8 { 37 }  // '%'

    open spec fn literal(b: u8) -> bool { 32 <= b && b <= 126 && b != 37 && b != 61 }

    open spec fn short(b: u8) -> Option<u8> {
        if b == 37 { Some(37u8) } else if b == 61 { Some(61u8) } else { None }
    }

    fn esc_exec() -> (r: u8) { 37 }

    fn literal_exec(b: u8) -> (r: bool) { 32 <= b && b <= 126 && b != 37 && b != 61 }

    fn short_exec(b: u8) -> (r: Option<u8>) {
        if b == 37 { Some(37u8) } else if b == 61 { Some(61u8) } else { None }
    }
}

pub open spec fn percent_short_inv(s: u8) -> Option<u8> {
    if s == 37 { Some(37u8) } else if s == 61 { Some(61u8) } else { None }
}

impl Codec for PercentEscape {
    open spec fn code(b: u8) -> Seq<u8> { security_property::family_table::<PercentEscape>(b) }

    open spec fn delim() -> u8 { 0 }   // NUL

    open spec fn marker() -> u8 { 61 }  // '='

    fn delim_exec() -> (r: u8) { 0 }

    fn marker_exec() -> (r: u8) { 61 }

    fn push_code(out: &mut Vec<u8>, b: u8) {
        security_property::family_push_code::<PercentEscape>(out, b);
    }

    proof fn lemma_codec_ok() {
        let esc = PercentEscape::esc();
        let literal = |x: u8| PercentEscape::literal(x);
        let short = |x: u8| PercentEscape::short(x);
        let short_inv = |s: u8| percent_short_inv(s);
        assert(security_property::family_conditions(esc, literal, short, short_inv, 0, 61)) by {
            assert forall|b: u8| #[trigger] literal(b) implies b != esc && b != 0 && b != 61 by {}
            assert forall|b: u8|
                ((#[trigger] short(b)) matches Some(s) ==> !literal(b) && s != 120 && s != 0
                    && short_inv(s) == Some(b)) by {}
        }
        security_property::theorem_family_codec_ok(
            |b: u8| PercentEscape::code(b), esc, literal, short, short_inv, 0, 61,
        );
    }
}

} // verus!
```

## Then

- `PercentEscape::lemma_codec_ok()` gives you `codec_ok::<PercentEscape>()`.
  All library theorems and exec functions now work with `::<PercentEscape>`,
  e.g. `security_property::theorem_record_count::<PercentEscape>(rs)`.
- **Spec-test your table** (see `intent-rows.md`): a value containing the
  delimiter round-trips as one record; a value ending in the marker doesn't
  forge a header.
- **If a fact doesn't prove**, your table has a real ambiguity: the proof
  failure shows which byte. Fix the table; don't weaken the conditions.
