---
id: 0004-vls-codec-conformance
status: grilled
owner: fritzClaw
---

# 0004 — vls conforms to lib-security-property

## Intent

Show, by proof, that `lib-security-property` covers the real case: vls's
escape table is a valid `Codec`, and vls's output *is* the library's unparser
for that Codec. The library's guarantees (exact record count, no header or
separator injection, strict decoding) therefore apply to `vls` and to
`vls DIR | vwc -l` without trusting any re-implementation. Locked katas 0002
and 0003 stay unchanged.

## Interface

- Crate `vls_conformance` (`katas/0004-vls-codec-conformance`), library only.
- Depends on `ls` (kata 0002), `count_files` (kata 0003) and `security_property`.
- `struct VlsCodec; impl Codec for VlsCodec`: code = `ls::escape_byte`, delim = LF, marker = `:`.

## Decisions

| #  | Question | Decision | Spec clause |
|----|----------|----------|-------------|
| D1 | Is vls's table a valid Codec? | Yes, discharged with the library's 256-byte checker by `compute_only`. | `VlsCodec::lemma_codec_ok` |
| D2 | Same encoding? | `ls::escape(s) == security_property::encode::<VlsCodec>(s)` for every `s`. | `theorem_same_encoding` |
| D3 | Same document? | Kata 0003's `unparse(x)` equals the library's `unparse_document::<VlsCodec>` of the same AST; with kata 0003's `theorem_vls_unparses`, vls's stdout bytes are the library's unparse of `ast_of(req)`. | `theorem_same_document`, `theorem_vls_output_is_library_unparse` |
| D4 | Same count? | Kata 0003's `count_newlines` equals the library's delimiter count for LF. | `theorem_same_count` |
| D5 | Regression? | The pre-fix vls table (no `:` rule) fails the checker (C4), so bug B1 is caught mechanically. | spec test |

## Examples

| #  | Check | Expected | Wrong answer to reject |
|----|-------|----------|------------------------|
| E1 | `table_ok` for vls's table | true | false |
| E2 | `table_ok` for the pre-fix table | false | true |
| E3 | encode `a:b` both ways | `a\:b` | `a:b` |

## Not verified

Nothing beyond what katas 0002/0003 and the library already list.

## Open questions

None.
