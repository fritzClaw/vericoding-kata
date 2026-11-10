# Template: tying a tool's output to the library

The library's guarantees apply to *your* tool only if its output provably
**is** the library's unparser. There are two ways.

## A. The tool calls the library (simplest)

Build the output with `unparse_records_exec::<C>` / `unparse_document_exec::<C>`
(or `encode_into::<C>` per line plus the delimiter). Their contracts state the
equality, so the tool's spec can say:

```rust
pub fn render(items: &Vec<Vec<u8>>) -> (r: Vec<u8>)
    ensures
        r@ == security_property::unparse_records::<MyCodec>(security_property::seqs_view(items@)),
```

Then `theorem_record_count::<MyCodec>` and `theorem_records_injective::<MyCodec>`
apply directly.

## B. The tool has its own spec (as vls does): prove the link

Kata `katas/0004-vls-codec-conformance` is the worked example. The shape:

```rust
use security_property::Codec;
use vstd::prelude::*;

verus! {

pub struct MyCodec;

impl Codec for MyCodec {
    open spec fn code(b: u8) -> Seq<u8> { my_tool::escape_byte(b) }   // the tool's own table
    open spec fn delim() -> u8 { 10 }
    open spec fn marker() -> u8 { 58 }
    // exec fns + lemma_codec_ok as in the codec templates
}

/// Same encoding: induction, both sides are front-recursive over bytes.
pub proof fn theorem_same_encoding(s: Seq<u8>)
    ensures my_tool::escape(s) == security_property::encode::<MyCodec>(s),
{ /* vericode */ }

/// Same output: the tool's stdout bytes are the library's unparse of the
/// tool's AST. Prove the pieces (lines, groups, join) equal by induction.
pub proof fn theorem_output_is_library_unparse(req: my_tool::RequestS)
    ensures
        my_tool::stdout_bytes(req) == security_property::unparse_document::<MyCodec>(my_ast(req)),
{ /* vericode */ }

/// Regression: the table without the marker rule is rejected.
proof fn spec_marker_rule_needed() {
    let pre = |b: u8| if b == 58 { seq![58u8] } else { my_tool::escape_byte(b) };
    assert(!security_property::codec_conditions(pre, 10, 58)) by {
        assert(pre(58u8)[0] == 58u8);
    }
}

} // verus!
```

## Pitfalls (all hit for real while building katas 0003/0004)

- **Ghost items from other crates are erased in normal builds.** Don't `use`
  spec functions of another crate (plain `cargo build` fails). Refer to them by
  full path (`my_tool::escape(s)`), or guard the `use` with `#[cfg(verus_only)]`.
- **`compute_only` can't see through generic trait calls.** Inside
  `encode::<C>` the interpreter leaves `C::code(b)` unresolved. Use
  `by (compute)` (SMT finishes) and `=~=` for sequence equality in spec tests.
- **Trait cycles:** a trait method's `ensures` can't mention a function generic
  over that same trait. That's why the conditions are written out in
  `lemma_codec_ok`, and why `EscapeFamily` is not a subtrait of `Codec`.
- **`--no-cheating` must target your crates only:**
  `cargo verus verify --fwd-verus-args-to roots -- --no-cheating`. `vstd`
  itself legitimately contains assumptions.
- **Cargo caches verification:** changing only Verus flags doesn't re-run
  Verus. Use a separate `--target-dir` for strict runs.
