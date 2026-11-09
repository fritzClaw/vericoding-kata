---
name: spec-from-intent
description: Stage 2 of the vericoding pipeline. Turn a grilled intent document (intents/NNNN-*.md, produced with the grill-me skill) into a frozen Verus specification with spec tests, get it approved by the human, and lock it. Use when the user says "spec kata NNNN", "write the spec for ...", or an intent's status is `grilled`.
---

# Spec from intent

You translate a human intent into the **trusted** part of a kata: the Verus
spec. Everything you write here is what later code is proved against. If it is
wrong, every proof is worthless. So you optimise for *faithfulness to the
intent*, not for ease of proof.

## Preconditions

- `intents/NNNN-name.md` exists, its "Open questions" section is empty, and
  every Decision has an answer. If not: stop, and suggest running **grill-me**
  on the open points first. Do not resolve ambiguities yourself.
- If the kata does not exist yet: `tools/vc.py new NNNN-name`.

## Steps

1. **Read** the intent and `CLAUDE.md`. Look at `katas/0001-first-max` as the
   reference shape.
2. **Write the spec** in `katas/NNNN-name/src/lib.rs`, outside the `<vc-*>`
   regions:
   - `pub open spec fn` predicates that model the intent mathematically
     (over `Seq`, `int`, `Set`, `Map` — not over exec types). Name them after
     the domain concept, comment each conjunct with the Decision id (`// D2`).
   - Each exec fn signature with `requires` / `ensures` referencing those
     predicates. Body = the canonical stub, exactly:
     ```rust
     {
         // <vc-code>
         assume(false);
         unreached()
         // </vc-code>
     }
     ```
   - One empty `// <vc-helpers>` / `// </vc-helpers>` region for the prover.
   - Theorems the intent asks for are frozen `proof fn` statements
     (`requires`/`ensures`); their proof is vericode work, so the body is
     `// <vc-code>` `assume(false);` `// </vc-code>`.
3. **Write spec tests** (frozen, `proof fn`, they never run):
   - Every Example: assert the spec **accepts** the expected answer and
     **rejects** the listed plausible wrong answer. A spec that cannot reject
     a wrong answer is too weak.
   - Every Property: a lemma (`proof fn ... requires ... ensures ...`).
     Always consider *uniqueness/determinism* (is the output pinned down?) and
     *satisfiability* (`requires` not accidentally `false`, e.g. assert a
     concrete input satisfies the precondition).
   - Mirror the Examples as runtime `#[cfg(test)]` tests outside `verus!`.
4. **Check**: `scripts/verify.sh NNNN-name`. The kata must show
   `⏳ spec verified, implementation pending`. `vc check` will say the spec is
   not locked yet — that is expected until step 6.
5. **Present for approval** — this is a hard stop. Show the human:
   - the spec (predicates + contracts),
   - a table mapping every Decision / Example / Property → spec clause or
     spec test, and anything moved to "Not verified",
   - anything you found ambiguous while formalising (if there is anything,
     the intent goes back to grill-me; do not guess).
   Wait for explicit approval.
6. **Lock** after approval only: `tools/vc.py lock NNNN-name`, set the
   intent's `status: specced`, then re-lock (the intent hash is pinned too),
   run `scripts/verify.sh NNNN-name`, and commit as
   `spec(NNNN): <title>` containing intent + spec + `specs.lock.json`.

## Rules

- Never write an implementation or proof of the exec fn here; that is stage 3.
- No escape hatches in the spec either (`assume`, `admit`, `external_body`,
  `axiom`, ...). `tools/vc.py check` rejects them.
- Prefer `forall`/`exists` over recursive spec fns unless recursion is the
  natural model; if you use recursion, give `decreases`.
- Keep exec types honest: if the intent says `i64`, the spec must say what
  happens at overflow boundaries (usually via `requires`, or by specifying the
  result over `int`).
