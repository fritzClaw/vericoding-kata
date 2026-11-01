---
id: 0001-first-max
status: specced
owner: fritzClaw
---

# 0001 — Index of the first maximum

> Seed kata. It exists to exercise the pipeline end to end (intent → spec →
> verified code → CI gate). Replace or keep it as you like.

## Intent

Given a list of integers, tell me *where* the largest value is. If the
largest value occurs more than once, I want the earliest position, so the
answer is deterministic.

## Interface

- `pub fn first_max(v: &[i64]) -> usize`
- Borrows the input, does not modify it, returns an index into `v`.

## Decisions

| #  | Question | Decision | Spec clause |
|----|----------|----------|-------------|
| D1 | What happens on empty input? | Caller's obligation: the input must be non-empty. No `Option`. | `requires v.len() > 0` |
| D2 | Several equal maxima? | Return the **first** (lowest index). | `is_first_max`: every earlier element is strictly smaller |
| D3 | Is the result always a valid index? | Yes. | `is_first_max`: `0 <= i < s.len()` |
| D4 | Element type? | `i64`, compared with the usual `<=`. | signature |
| D5 | May the function modify the input? | No. | `&[i64]` (shared borrow) |
| D6 | Must it terminate? | Yes, on every valid input. | Verus total correctness (no `exec_allows_no_decreases_clause`) |

## Examples

| #  | Input          | Expected | Plausible wrong answer the spec must reject |
|----|----------------|----------|---------------------------------------------|
| E1 | `[3, 7, 2]`    | `1`      | `0` (not the max)                           |
| E2 | `[5, 1, 5]`    | `0`      | `2` (a max, but not the first one)          |
| E3 | `[42]`         | `0`      | —                                           |
| E4 | `[-4, -1, -9]` | `1`      | `2` (the minimum)                           |

## Properties

- P1 **Uniqueness**: for any non-empty input there is at most one index that
  satisfies the spec. (Guards against an under-constrained spec.)
- P2 **Existence**: for any non-empty input at least one index satisfies the
  spec. (Guards against an unsatisfiable spec.) — implied by a verified
  implementation existing.

## Not verified

- Runs in O(n) with no allocation: by review.

## Open questions

None.
