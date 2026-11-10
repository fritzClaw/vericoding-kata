---
id: lib-security-property
status: specced
owner: fritzClaw
---

# lib-security-property — reusable, verified injection-safety for line-based output

## Intent

Make the two security properties found in katas 0002/0003 reusable in the
next Vericoding project, without redoing the proofs:

1. **Record safety:** a data value can never add or remove a record
   delimiter. That's why `vls DIR | vwc -l` counts exactly, even for a file
   name containing a newline.
2. **Structure safety (no injection):** a data value can never forge
   document structure such as a `NAME:` header or a group separator. The
   unparser is correct in the sense of Hermerschmidt, Kugelmann and Rumpe
   (IEEE SPW 2015): "for every AST x holds parse(unparse(x)) = x".

Both properties hold for **any** byte-escape table meeting a few checkable
conditions, so a new tool picks or writes a table, discharges the conditions
(for C-style escaping just a few simple per-byte facts, proved by SMT), and
gets verified encoders, decoders and theorems for free.

## Interface

- Folder `lib-security-property/`, Rust crate `security_property`, version 0.1.0.
- `trait Codec`: the parameters of a format.
  - `spec fn code(b: u8) -> Seq<u8>`: the escape table.
  - `spec fn delim() -> u8`: the record delimiter, e.g. LF.
  - `spec fn marker() -> u8`: the header marker, e.g. `:`.
  - Exec counterparts: `push_code`, `delim_exec`, `marker_exec`.
  - `proof fn lemma_codec_ok()`: discharges the conditions.
- Generic spec, theorems and verified exec code over `C: Codec`.

## Decisions

| #   | Question | Decision | Spec clause |
|-----|----------|----------|-------------|
| D1  | How general? | Parametric over a `Codec`: escape table, delimiter byte and marker byte are all parameters. | `trait Codec` |
| D2  | Which shapes? | **Records**: each value encoded and terminated by `delim`. **Grouped documents** (vls's shape): groups separated by an empty line, each with an optional header `encode(name) + marker` and encoded names. | `unparse_records`, `unparse_document` |
| D3  | Conditions on a Codec? | C0 `delim != marker`. C1 every code is non-empty. C2 no code contains `delim`. C3 prefix-free: no code is a prefix of another byte's code (implies injective). C4 no code starts with `marker`. | `codec_ok` |
| D4  | Theorems? | T1 exact record count: `count(delim, unparse_records(R)) == R.len()`. T2 records round trip and strictness. T3 document round trip `parse(unparse(x)) == Some(x)` for every well-formed x, injectivity, and strictness (`parse(s) == Some(d)` ⇒ `d` well formed and `unparse(d) == s`). T4 chunking doesn't change counts. | `theorem_*` |
| D5  | Executable code? | Verified generic exec: `encode`, `unparse_records`, `count_delims` (checked u64, chunked), `decode_records` (strict), `unparse_document`, `decode_document` (strict). | contracts |
| D6  | How are the conditions discharged? | **By SMT**, never by enumerating bytes. *(Revised in grilling: a `compute_only` check over 256 bytes took over 10 minutes or timed out in Verus's interpreter, even for linear checks; the same conditions prove by SMT in seconds.)* Arbitrary tables: prove C0–C4 by case analysis, with a template in `templates/`. C-style tables: use the escape family (D14). | `codec_ok` |
| D7  | Well-formed document? | All names non-empty; only the first group may lack a header; a headerless group is non-empty (as in kata 0003, D8). | `wf_document` |
| D8  | Link to vls? | Kata 0004 (`0004-vls-codec-conformance`) proves vls's table is a valid Codec and that vls's output *is* this library's unparser. Locked katas 0002/0003 are untouched. | — (kata 0004) |
| D9  | Distribution? | Documented both ways: vendor (copy the folder, path dependency; default) or git dependency on this repo. Consumers must use the same Verus/vstd pin. | — (README) |
| D10 | Pipeline? | Top-level `lib-*/` crates are handled like katas: intent, spec lock, escape-hatch scan, `<vc-*>` regions, Verus `--no-cheating`, cargo test. Workspace members `["katas/*", "lib-*"]`. | — (pipeline) |
| D11 | Artifacts? | Verified crate; agent skill `skill/SKILL.md` (shipped only, not activated in this repo); human guide `README.md`; spec templates `templates/`. | — |
| D12 | Decoder strategy? | The generic tokenizer finds the unique code that prefixes the input by checking all 256 codes. Simple to prove; performance isn't verified. | — |
| D14 | Escape-family builder? | `trait EscapeFamily`: an escape byte `esc`, a literal set (`literal(b)`: b encodes as itself), short escapes (`short(b) == Some(s)`: b encodes as `[esc, s]`), and `[esc, 'x', hex(b/16), hex(b%16)]` (lowercase) for every other byte. Per-byte facts F1–F3: a literal is never `esc`, `delim` or `marker`; short letters are distinct (shown with `short_inv`), never `x` and never `delim`; `esc`, `x` and the hex digits are never `delim`; `delim != marker`; `esc != marker`. The library proves once that F1–F3 ⇒ C0–C4 for `family_code`, and provides a generic verified exec `family_push_code`. The library ships `BackslashEscape` (vls's table: `\ \n \t \:`, printable ASCII literal, `\xHH`, LF and `:`) as a ready instance. | `family_ok`, `lemma_family_codec_ok` |

## Examples

| #  | Codec / input | Expected | Plausible wrong answer the spec must reject |
|----|---------------|----------|---------------------------------------------|
| E1 | vls's table, records `["a⏎b", "c"]` | bytes `a\nb⏎c⏎`, count 2 | count 3 |
| E2 | vls's table, document `[{-, [a]}, {x:, [b:]}]` | `a⏎⏎x\::⏎b\:⏎`, which decodes back | header `x` + name `:` |
| E3 | identity table (every byte encodes as itself), LF, `:` | violates the conditions: byte LF breaks C2, byte `:` breaks C4 (proved, with witness) | accepted |
| E4 | vls's *pre-fix* table (`:` literal) | violates C4, and F1 as a family (literal `:` == marker): bug B1 of `katas/0002-ls/vls-injection.md` caught by the conditions (proved) | accepted |
| E5 | strict decoding with vls's table: `\q⏎`, `\x41⏎`, `a` (no final delimiter) | `None` | accepted |

## Properties

- P1 Every `Codec` with `codec_ok` gets T1–T4 without further proof.
- P2 The family is sound: F1–F3 ⇒ C0–C4 for every `EscapeFamily`.
- P3 The conditions are not vacuous: vls's table satisfies them (kata 0004).

## Not verified

- Decoder performance (D12).
- How a project's own shell writes the bytes (as with vls: trusted shell, reviewed).

## Open questions

None.
