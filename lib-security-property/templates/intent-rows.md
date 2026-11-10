# Template: intent rows for a tool that writes untrusted data as lines

Paste these into the new kata's `intents/NNNN-*.md` during the grill-me
interview and replace the placeholders. Every row must end up as a spec clause
or a spec test.

## Questions to grill

1. Which parts of the output are **data** (names, user input, file contents)
   and which are **structure** (record delimiter, header marker, separators)?
2. Which **codec**: the ready-made `BackslashEscape` (LF records, `:`
   headers; escapes `\\`, `\n`, `\t`, `\:`, `\xHH`), a custom escape family, or an arbitrary
   table?
3. **Records** only, or **grouped documents** (headers + groups separated by an
   empty line)?
4. Must output be **decodable** (strict decoder) or only countable?
5. What may be **empty** (a record, a header name)? A grouped document forbids
   empty names (they would look like separators).

## Decisions

| #  | Question | Decision | Spec clause |
|----|----------|----------|-------------|
| Dx | How is data escaped? | Codec `<Codec>`: `<table summary>`; delimiter `<LF>`, marker `<:>`. | `impl Codec for …` (`lemma_codec_ok`) |
| Dx | Can data split a record? | No: delimiter count == record count. | `theorem_record_count` |
| Dx | Can data forge structure? | No: the output is `unparse_records`/`unparse_document` of the tool's AST, and that unparser is injective (parse(unparse(x)) = x). | link theorem + `theorem_*_injective` |
| Dx | How is the output decoded? | `decode_records`/`decode_document`, strict (only canonical bytes accepted). | library contract |
| Dx | Trusted? | The shell writes each line followed by the delimiter. | — (shell, reviewed) |

## Examples (each needs an accept *and* a reject case)

| #  | Input | Expected | Plausible wrong answer the spec must reject |
|----|-------|----------|---------------------------------------------|
| Ex | data containing the delimiter, e.g. `a⏎b` | one record `a\nb⏎` (count 1) | two records (count 2) |
| Ex | data ending with the marker, e.g. file `x:` | `x\:` | `x:`: a forged header |
| Ex | data containing the escape byte, e.g. `a\b` | `a\\b` | `a\b` (would collide with an escape) |
| Ex | non-canonical input to the decoder: `\q`, `\x41`, no final delimiter | rejected (`None`) | accepted |
| Ex | your table without the marker rule | fails `codec_conditions` (C4) | accepted |

## Properties

- Exact count: `count_byte(output, delim) == number of records`.
- Round trip: `decode(output) == Some(ast)`; injective unparser.
- The tool's output equals the library's unparser (link theorem, see
  `spec-link-theorems.md`).

## Not verified

- The shell that writes bytes (review it).
- Decoder speed (it checks the 256 codes per token).
