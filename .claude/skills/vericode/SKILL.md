---
name: vericode
description: Stage 3 of the vericoding pipeline. Implement and prove a kata whose Verus spec is locked, editing only the <vc-helpers>/<vc-code> regions, until scripts/verify.sh passes with --no-cheating. Use when the user says "vericode NNNN", "implement kata NNNN", "prove ...", or a kata shows ⏳ pending.
---

# Vericode

Write Rust code **and its proof** so that Verus accepts it against a spec a
human already approved. You may edit only:

```
// <vc-helpers> ... // </vc-helpers>   lemmas, spec/proof/exec helper fns
// <vc-code>    ... // </vc-code>      the body of a spec'd function
```

and, for katas with a binary, the trusted shell:

```
// <vc-shell>   ... // </vc-shell>     src/main.rs only: argv, syscalls, printing
```

The shell is **not verified**. Keep it a thin adapter: build the core's input
from the OS, call the verified core, write its output. No logic that the
intent assigns to the core. Call it out in the PR description for review.

Everything else in `katas/NNNN-*/` — and all of `intents/`, `specs.lock.json`,
`tools/`, `scripts/`, CI — is off limits. `tools/vc.py check` hashes it.

## Loop

1. `tools/vc.py status` → pick a `pending` kata. Read its intent and spec.
2. Replace the stub in `<vc-code>` with an implementation. Write the loop
   invariants and `decreases` clauses at the same time as the loop.
3. Iterate fast:
   `cargo verus focus -p <crate> -- --expand-errors`
   (does not re-verify vstd; use `--rlimit 30` if a query times out).
4. When it verifies, run the real gate:
   `scripts/verify.sh NNNN-name` → must print `✅ ... verified (--no-cheating), tests pass`.
5. Commit as `vericode(NNNN): <what>`. The diff must touch only `<vc-*>`
   regions (and `Cargo.lock` if needed).

## When the proof will not go through

- Do **not** weaken, strengthen, or reinterpret the spec — you cannot anyway
  without failing `vc check`, and you must not try.
- Forbidden (rejected by `vc check` and/or `--no-cheating`): `assume`,
  `admit`, `#[verifier::external*]`, `assume_specification`, `axiom`,
  `exec_allows_no_decreases_clause`, `assume_termination`, `unsafe`,
  `cfg(...)`, `mod`, `include!`, a second `verus!` block.
- If you believe the spec is **wrong or unprovable** (e.g. it contradicts the
  intent, or is unsatisfiable for some valid input), stop and report: quote
  the clause, give a concrete counterexample, and point to the intent row.
  That goes back to the human (spec stage), not around the gate.

## Verus proof toolbox

- Loops: invariant must hold on entry, be preserved, and with the negated
  guard imply the postcondition. Restate facts about unchanged inputs (e.g.
  `v.len() == n`) — or keep the default loop isolation and repeat them.
- Termination: `decreases <expr>` on every loop and recursive fn.
- Overflow: exec arithmetic on `usize`/`i64` must be proved in range; reason
  in `int` in ghost code (`x as int`).
- Quantifiers: give `#[trigger]`s when Verus warns about them; instantiate
  manually with `assert(P(k))` for the witness you need.
- Missing facts: factor into a `proof fn lemma_...` in `<vc-helpers>` with
  `requires`/`ensures`, prove it by induction (`decreases`), call it in the
  body. `assert(...) by { ... }` scopes local reasoning.
- Sequences: `v@` is the `Seq` view of a slice/Vec; `=~=` for extensional
  equality; `s.subrange(a, b)`, `s.push(x)`, `s.len()`.
- Nonlinear arithmetic: `assert(...) by (nonlinear_arith)`; bit tricks:
  `by (bit_vector)`.
- Docs: https://verus-lang.github.io/verus/guide/ — vstd API:
  https://verus-lang.github.io/verus/verusdoc/vstd/
