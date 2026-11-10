---
name: security-property
description: Apply the verified injection-safety library lib-security-property (Rust crate `security_property`) in a Vericoding project. Use whenever a kata's tool writes or parses line-based text that contains untrusted data (file names, user input, records, `NAME:` headers), its output is counted or piped (`| wc -l`, `| grep`), or the user asks for "no injection", "newline-safe output", "round trip", or "parse(unparse(x)) = x".
---

# security-property: verified record and structure safety

`lib-security-property/` proves, for any escape table meeting conditions
C0–C4:

- **record safety**: data can't add or remove a delimiter, so counts are exact;
- **structure safety**: data can't forge headers or separators. The unparser is
  injective: parse(unparse(x)) = x (Hermerschmidt et al., IEEE SPW 2015).

It also gives verified encoders, counters and **strict** decoders. Read
`lib-security-property/README.md` once; the templates are in
`lib-security-property/templates/`.

## When to use it

Use it in the **spec stage** of any kata whose output mixes untrusted data with
structure. Warning signs: printing names one per line, `NAME:` headers, an
empty line between sections, output fed to `wc -l`/`grep`/another parser.

**Not covered:** formats outside "records" and "grouped documents" (nested
structures, quoting with balanced delimiters, multi-byte markers). For those,
stop and grill the human; don't stretch the library.

## By pipeline stage

### Intent (grill-me)

Paste and fill `templates/intent-rows.md`. Decide:
- data vs structure tokens;
- the codec (`BackslashEscape`, a custom escape family, or an arbitrary table);
- records or grouped documents;
- whether decoding is needed.

Every example needs a reject case: a delimiter in the data, a marker at the end
of the data, the escape byte in the data, non-canonical decoder input, and
the table without its marker rule.

### Spec (human approves, then locked)

1. **Codec:** use `security_property::BackslashEscape`, or write one from
   `templates/codec-escape-family.md` (preferred) or
   `templates/codec-arbitrary-table.md`. The table, delimiter and marker are
   frozen spec. `lemma_codec_ok` and the exec bodies are `<vc-code>`.
2. **Link the tool to the library** (`templates/spec-link-theorems.md`):
   either the tool's contract says its output *equals*
   `unparse_records::<C>`/`unparse_document::<C>` of its data, or state link
   theorems as in kata `0004-vls-codec-conformance`.
3. **Spec tests:** accept and reject examples. Use `by (compute)` with `=~=`
   when generic trait calls are involved; `compute_only` can't resolve
   `C::code` inside generic functions.

### Vericode

- **Escape family:** in `lemma_codec_ok`, assert `family_conditions(...)` with
  two `assert forall … by {}` (literals; short escapes written as
  `(short(b) matches Some(s) ==> …)`), then call `theorem_family_codec_ok`.
- **Link theorems:** induction; both sides are front-recursive over
  bytes/lines/groups.
- **Theorems you get for free:** `theorem_record_count`,
  `theorem_records_injective`, `theorem_document_injective`,
  `theorem_count_concat`.
- **Decoders and counters:** call `decode_records`/`decode_document`/
  `count_delims` and use their contracts; never re-implement them.

## Hard rules

- **Never weaken the conditions** (C0–C4, F1–F3) or the library's spec to
  make a proof pass. A failing condition is a real ambiguity in the table:
  report the byte and fix the table.
- **Never discharge the conditions by enumerating 256 bytes** with
  `compute_only`: it times out. Use SMT case analysis.
- **Same Verus/vstd pin as the library**
  (`vstd = "=0.0.0-2026-10-18-0147"`, Verus `0.2026.10.18.7d82994`).
- **Verify with `--fwd-verus-args-to roots -- --no-cheating`.**
- **Don't `use` another crate's ghost items:** use full paths, or
  `#[cfg(verus_only)]` on the `use`.
- **The shell that writes the bytes stays trusted:** keep it to "write each
  line plus the delimiter" and flag it for review.
