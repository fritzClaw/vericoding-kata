---
id: NNNN-short-name          # matches the kata directory katas/NNNN-short-name
status: draft                # draft -> grilled -> specced
owner: your-github-handle
---

# NNNN — Title

<!--
This file is the human contract. It is the output of an intent-driven session
(e.g. the grill-me skill): keep interviewing until every question below has an
answer and every branch of the decision tree is resolved. The Verus spec is
derived from THIS file, and specs.lock pins this file's hash, so changing it
after the spec is approved forces a re-review of the spec.
-->

## Intent

One paragraph, in plain language: what the caller wants and why.

## Interface

- Function name, inputs, output (Rust types).
- Ownership / borrowing (`&[T]`, `&mut Vec<T>`, returns owned value, ...).

## Decisions

Every resolved question from the grilling session gets one row. Each row must
map to something in the spec (a `requires`, an `ensures`, or a spec test), or
be explicitly listed under "Not verified".

| #  | Question | Decision | Spec clause |
|----|----------|----------|-------------|
| D1 | What happens on empty input? | ... | `requires ...` |

## Examples

Concrete input/output pairs. These become spec tests (`proof fn` asserts that
the spec ACCEPTS the right answer and REJECTS plausible wrong answers).

| #  | Input | Expected | Plausible wrong answer the spec must reject |
|----|-------|----------|---------------------------------------------|
| E1 | ...   | ...      | ...                                         |

## Properties

Higher-level facts the spec must imply (e.g. "the answer is unique",
"output is a permutation of input"). These become spec lemmas.

## Not verified

Things the intent cares about that Verus does not prove here (performance,
allocation, I/O, ...). State how they are covered instead (review, tests,
benchmarks) — or accept them as out of scope.

## Open questions

Must be empty before the spec stage starts.
