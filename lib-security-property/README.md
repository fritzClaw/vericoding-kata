# lib-security-property

**Verified injection safety for line-based output.** A small Verus library
(Rust crate `security_property`) that makes two security properties reusable:

1. **Record safety:** a data value can never add or remove a record
   delimiter. Counting delimiters counts records exactly, so `mytool | wc -l`
   can't be fooled by a file name containing a newline.
2. **Structure safety (no injection):** a data value can never forge document
   structure (a `NAME:` header, a group separator). The unparser is *correct*
   in the sense of Hermerschmidt, Kugelmann and Rumpe, *Towards More Security
   in Data Exchange: Defining Unparsers with Context-Sensitive Encoders for
   Context-Free Grammars* (IEEE SPW 2015): **parse(unparse(x)) = x for every
   AST x**.

Both hold for **any** escape table meeting five conditions. Pick the ready-made
table, or describe your own in a few lines, and you get the theorems and
verified encoders and decoders without writing those proofs yourself.

The library was extracted from the `vls`/`vwc` katas of
[vericoding-kata](../README.md): proving the round trip for `vls` exposed a
real header-injection bug (see [`katas/0002-ls/vls-injection.md`](../katas/0002-ls/vls-injection.md)),
and kata `0004-vls-codec-conformance` proves that `vls`'s output *is* this
library's unparser.

---

## The model

A **codec** fixes three things (`trait Codec`):

| Item | Meaning | vls / `BackslashEscape` |
|---|---|---|
| `code(b)` | the bytes a data byte `b` is written as | `\` → `\\`, LF → `\n`, TAB → `\t`, `:` → `\:`, printable ASCII as itself, else `\xHH` |
| `delim()` | record / line delimiter | LF |
| `marker()` | header marker at the end of a header line | `:` |

Two document shapes are covered:

- **Records:** `encode(r1) DELIM encode(r2) DELIM …` (`unparse_records`).
- **Grouped documents** (`unparse_document`): groups separated by an empty
  line. Each group has an optional header line `encode(name) MARKER`, then one
  line per name. An AST is a `Seq<GroupS>` with `GroupS { header:
  Option<bytes>, names: Seq<bytes> }`. It is **well formed** (`wf_document`)
  if all names are non-empty, only the first group may lack a header, and a
  headerless group isn't empty.

### The five conditions (`codec_conditions` / `codec_ok`)

| | Condition | What it rules out |
|---|---|---|
| C0 | `delim != marker` | a header marker that is also a line end |
| C1 | every `code(b)` is non-empty | data that disappears (and empty lines that look like separators) |
| C2 | no `code(b)` contains `delim` | **data that splits a record** (the `ls \| wc -l` bug) |
| C3 | no `code(b)` is a prefix of another byte's code | ambiguous decoding (two inputs, same bytes) |
| C4 | no `code(b)` starts with `marker` | **data that forges a header** (vls bug B1) |

## What is proved

Every theorem holds for every `C: Codec` (the codec's own `lemma_codec_ok`
provides `codec_ok::<C>()`):

| Theorem | Statement |
|---|---|
| `theorem_record_count` (T1) | `count_byte(unparse_records::<C>(rs), C::delim()) == rs.len()` |
| `theorem_records_injective` (T2) | `unparse_records::<C>(x) == unparse_records::<C>(y) ⇒ x == y` |
| `theorem_document_injective` (T3) | for well-formed `x`, `y`: `unparse_document::<C>(x) == unparse_document::<C>(y) ⇒ x == y` |
| `theorem_count_concat` (T4) | `count_byte(a + b, d) == count_byte(a, d) + count_byte(b, d)` (count in chunks) |
| `theorem_family_codec_ok` | the escape-family facts F1–F3 imply C0–C4 |

And verified executable code, generic over `C: Codec`:

| Function | Contract |
|---|---|
| `encode_into::<C>(out, s)` | appends `encode::<C>(s)` |
| `unparse_records_exec::<C>(rs)` | returns `unparse_records::<C>(rs)` |
| `count_delims::<C>(acc, chunk)` | `Some(acc + #delims)`, or `None` on u64 overflow (never a wrong number) |
| `decode_records::<C>(bytes)` | **strict**: `Some(rs)` iff `bytes` is the unparse of records, and then `rs` is the unique such list |
| `unparse_document_exec::<C>(doc)` | returns `unparse_document::<C>(doc)` |
| `decode_document::<C>(bytes)` | **strict**: `Some(d)` iff `bytes` is the unparse of a well-formed document, and then `d` is the unique such document. This is parse(unparse(x)) = x, and non-canonical input (`\q`, `\x41`, a missing final delimiter, …) is rejected |
| `family_push_code::<F>(out, b)` | appends `family_table::<F>(b)` |

**What you still trust:** Verus, `vstd` and Z3; your program's code that
actually writes the bytes (e.g. a shell that prints each line plus the
delimiter); and that your program *uses* these functions or proves its output
equal to them (as kata 0004 does for `vls`). The decoder's speed isn't verified:
it finds each token by checking all 256 codes.

## Quick start: the ready-made codec

```rust
use security_property::{BackslashEscape as B, Group};

let bytes = security_property::unparse_records_exec::<B>(&records);   // escaped, LF-terminated
let n     = security_property::count_delims::<B>(0, &bytes);          // == records.len()
let back  = security_property::decode_records::<B>(&bytes);           // == Some(records)

let doc = vec![Group { header: Some(b"dir".to_vec()), names: vec![b"a:b".to_vec()] }];
let out = security_property::unparse_document_exec::<B>(&doc);       // dir:⏎a\:b⏎
```

## Your own table

**C-style tables:** describe the table with `EscapeFamily`:
- an escape byte;
- the literal bytes (written as themselves);
- optional two-byte short escapes `[esc, s]`;
- everything else as `[esc, 'x', hex, hex]`.

You then prove a few per-byte facts (F1–F3) by SMT, and `theorem_family_codec_ok`
does the rest. See [`templates/codec-escape-family.md`](templates/codec-escape-family.md).
That template was verified as a separate consuming crate: a NUL-delimited,
`=`-marked, `%`-escaped codec.

**Arbitrary tables:** prove C0–C4 directly by case analysis on your table; see
[`templates/codec-arbitrary-table.md`](templates/codec-arbitrary-table.md).

> Don't try to discharge the conditions with `by (compute_only)` over all 256
> bytes: Verus's interpreter times out or takes over 10 minutes even for linear
> checks. SMT proves them in seconds.

## Using it in your next Vericoding project

Both ways need the **same Verus toolchain**: `vstd = "=0.0.0-2026-10-18-0147"`
and Verus `0.2026.10.18.7d82994` (see `verus-toolchain.env` in this repo). A
different `vstd` won't link.

**Vendor it (default).** Copy the folder, plus the toolchain pin:

```sh
cp -r lib-security-property  <new-repo>/lib-security-property
cp verus-toolchain.env rust-toolchain.toml  <new-repo>/      # if not already pinned
```

```toml
# <new-repo>/Cargo.toml (workspace)
[workspace]
members = ["...", "lib-security-property"]
[workspace.dependencies]
vstd = "=0.0.0-2026-10-18-0147"

# the crate that uses it
[dependencies]
security_property = { path = "../lib-security-property" }
```

**Or as a git dependency:**

```toml
[dependencies]
security_property = { git = "https://github.com/fritzClaw/vericoding-kata", rev = "<commit>" }
```

(Pin a commit, or a tag such as `lib-security-property-v0.1.0` once one has been pushed.)

**Verify:** with `cargo verus verify --fwd-verus-args-to roots -- --no-cheating`.
Without `--fwd-verus-args-to roots`, `--no-cheating` also applies to `vstd`,
which legitimately contains assumptions, and the build fails.

**For agents:** copy [`skill/SKILL.md`](skill/SKILL.md) to
`<new-repo>/.claude/skills/security-property/SKILL.md`. It tells agents when
to apply the property and how, stage by stage.

## Files

```
lib-security-property/
├── Cargo.toml
├── src/lib.rs            spec (frozen, locked) + proofs and exec code (<vc-*> regions)
├── README.md             this guide
├── skill/SKILL.md        agent skill (copy into .claude/skills/security-property/)
└── templates/
    ├── intent-rows.md            Decisions / Examples / Properties rows for an intent
    ├── codec-escape-family.md    a custom C-style codec (verified example)
    ├── codec-arbitrary-table.md  proving C0–C4 for any table
    └── spec-link-theorems.md     tying a tool's output to the library (as kata 0004)
```

The `intents/lib-security-property.md` intent in this repo records every design decision.
