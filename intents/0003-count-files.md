---
id: 0003-count-files
status: grilled
owner: fritzClaw
---

# 0003 — Counting files with `vls DIR | vwc -l`

## Intent

Count the files in a directory with the pipeline `vls DIR | vwc -l`, where
`vls` is kata 0002 exactly as built (after the D12 `:` fix, PR A) and `vwc` is
a new, verified Rust replacement for the part of `wc` the pipeline needs. The
count must be exact even for hostile names (a classic `ls | wc -l` bug: a name
containing a newline is counted twice).

The deeper goal is the correctness criterion of Hermerschmidt, Kugelmann and
Rumpe, *Towards More Security in Data Exchange: Defining Unparsers with
Context-Sensitive Encoders for Context-Free Grammars* (IEEE SPW 2015): vls is
an **unparser** for a small line-based document language. It must be a
**correct (un)parse round trip**, "if for every AST x holds
parse(unparse(x)) = x", so that file names (data tokens) can never inject
document structure (control tokens: newline, blank line, `NAME:` header).

## Architecture

```
vls DIR ──bytes──▶ vwc -l ──▶ count
   │
   └─ document language:  doc   ::= group (LF group)*  |  ε
                          group ::= [header LF] (name LF)*
                          header::= escape(name) ':'
                          name  ::= escape(bytes)      (D12 of kata 0002)
```

- **AST** (the "parse tree x"): a list of groups `{header: Option<bytes>,
  names: [bytes]}`.
- **unparse**: AST → bytes, as vls prints it (lines, each + LF; one empty line
  between groups; header `escape(name):`; names escaped).
- **ast_of(req)**: the AST vls builds for a request (kata 0002's `ls` spec).
- **decode**: a verified executable parser, bytes → `Option<AST>`.

## Interface

- Binary `vwc` (crate `count_files`, `katas/0003-count-files`).
- Library: `decode(&Vec<u8>) -> Option<Vec<Group>>` and the vwc counting core.
- Depends on crate `ls` (kata 0002) for its specification.

## Decisions

| #   | Question | Decision | Spec clause |
|-----|----------|----------|-------------|
| D1  | What is a "file"? | Every entry `vls DIR` lists: names not starting with `.`, of any type (files, directories, symlinks). Uses vls unchanged. | `theorem_count_files` |
| D2  | Bash script? | No script. The pipeline is `vls DIR \| vwc -l`; `vwc` is vericoded Rust. | — |
| D3  | What does `vwc` count? | Newline bytes (0x0A), like POSIX `wc -l`; a final unterminated line is not counted. | `count_newlines` |
| D4  | `vwc` interface? | Only `vwc -l`, reading stdin. Prints the count in decimal + LF, no padding (GNU style). Any other arguments: usage on stderr, exit 2. | — (shell) |
| D5  | Overflow / read errors? | Counter is u64 with checked addition. Overflow or a read error: message on stderr, nothing on stdout, exit 2. Never a wrong number. | `count_chunk` |
| D6  | Bad input to the pipeline? | Pass through: `vls missing \| vwc -l` prints 0 (vls reports the error on stderr); `vls FILE \| vwc -l` prints 1. | — |
| D7  | Which round trip? | Paper's property for the **document AST** of every vls output, all operand shapes (made possible by kata 0002's D12 `:` fix). | `decode` ensures |
| D8  | AST shape? | Groups `{header: Option<name>, names}`. Only the first group may lack a header, and a headerless group is never empty. All names non-empty. File-vs-directory is not part of the AST (the document doesn't encode it). | `wf` |
| D9  | Link to vls? | Proved: vls's stdout bytes are exactly `unparse(ast_of(req))`, and `ast_of(req)` is well formed whenever file operands have non-empty names (the OS never yields an empty path). | `theorem_vls_unparses`, `theorem_vls_ast_wf` |
| D10 | Decoder contract? | Round trip **and strict**: for every well-formed x, `decode(unparse(x)) == Some(x)`; and `decode(s) == Some(x)` implies x well formed and `unparse(x) == s`. So it's a bijection between valid documents and ASTs; non-canonical input (`\q`, `\x41`, missing final LF, ...) is rejected. | `decode` ensures |
| D11 | Counting theorem? | For one directory operand, the number of LF bytes in vls's stdout equals the number of distinct listed names, so `vls DIR \| vwc -l` is exact. | `theorem_count_files` |
| D12 | Chunked reading? | `vwc` counts chunk by chunk; proved that chunking doesn't change the count. | `theorem_count_concat` |
| D13 | Decimal printing? | Rust `std` formatting in the trusted shell. | — (shell) |

## Examples

`d1` holds `b`, `a`, `.h`, `!x` (as in kata 0002).

| #   | Input | Expected | Plausible wrong answer the spec must reject |
|-----|-------|----------|---------------------------------------------|
| E1  | `vls d1 \| vwc -l` | `3` | `4` (counting `.h`) |
| E2  | dir with `a⏎b` and `c` | `2` | `3` (what `ls \| wc -l` says) |
| E3  | `vls -a d1 \| vwc -l` | `6` (with `.` and `..`) | `4` |
| E4  | empty dir | `0` | `1` |
| E5  | `vls missing \| vwc -l` | `0` (vls: stderr + exit 2) | — |
| E6  | AST `[{-, [a]}, {x:, [b:]}]` | unparses to `a⏎⏎x\::⏎b\:⏎` and decodes back | header `x` + name `:` |
| E7  | decode `a` (no LF), `\q⏎`, `\x41⏎`, `⏎` | `None` each | accepting any of them |
| E8  | `vwc -l` on `a⏎b` | `1` | `2` |
| E9  | `vwc -l` with an unknown flag | usage, exit 2 | counting anyway |

## Properties

- P1 **Round trip** (paper): `decode(unparse(x)) == Some(x)` for every
  well-formed AST x (D10).
- P2 **Strictness**: `decode` accepts exactly the canonical documents (D10).
- P3 **vls is this unparser**: `stdout(ls(req)) == unparse(ast_of(req))` (D9).
- P4 **vls only builds well-formed ASTs** (D9).
- P5 **Exact count** (D11), **chunking-invariant** (D12).

## Not verified

- The trusted `vwc` shell: argv check, reading stdin in chunks, decimal
  printing, exit codes (D4, D5, D13). Covered by review and runtime tests
  running `vls … | vwc -l` on temp dirs, including a name with a newline.
- vls's shell (kata 0002) writing each stdout line + LF: trusted there.

## Open questions

None.
