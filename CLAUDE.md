# vericoding-kata — agent rules

This repo produces **formally verified Rust** with [Verus](https://github.com/verus-lang/verus).
Read `README.md` for the full pipeline. The short version:

```
intent (human, grill-me) ─▶ spec (agent drafts, HUMAN APPROVES, locked) ─▶ vericode (agent) ─▶ gate (CI)
intents/NNNN-*.md            katas/NNNN-*/src  outside <vc-*>               inside <vc-*>        scripts/verify.sh
```

## Which stage am I in?

| User asks to…                                | Stage    | Skill                     |
|----------------------------------------------|----------|---------------------------|
| explore / clarify a new kata                 | intent   | `grill-me` → write `intents/NNNN-*.md` from `intents/TEMPLATE.md` |
| write the spec for an intent                 | spec     | `spec-from-intent`        |
| implement / prove a pending kata             | vericode | `vericode`                |

Never do two stages in one step. In particular, never write the spec and the
proof together, and never lock a spec the human has not approved.

## Hard rules

1. **The spec is trusted, so it is frozen.** Outside `// <vc-helpers>` and
   `// <vc-code>` regions, kata files, `intents/`, and `specs.lock.json` change
   only in the spec stage, with human approval. Do not hand-edit
   `specs.lock.json`. Only `tools/vc.py lock` writes it, after approval.
2. **No escape hatches**: `assume`, `admit`, `#[verifier::external*]`,
   `assume_specification`, `axiom`, `exec_allows_no_decreases_clause`,
   `assume_termination`, `unsafe`, `cfg` tricks. The only allowed `assume` is
   a canonical pending stub as the whole `<vc-code>` body:
   `assume(false); unreached()` (exec fn) or `assume(false);` (proof fn).
3. **A failing proof is information, not an obstacle.** If the spec looks
   wrong or unprovable, stop and report a counterexample. Don't work around it.
4. **`// <vc-shell>` (only in `src/main.rs`) is trusted, unverified code.**
   It may only translate between the OS and the verified core: no sorting,
   filtering or formatting logic. Flag it for human review.
5. **Done means** `scripts/verify.sh` is green: `vc check` + Verus with
   `--no-cheating` + `cargo test`.

## Commands

```sh
scripts/install-verus.sh && eval "$(scripts/install-verus.sh --print-env)"  # toolchain
tools/vc.py status                         # katas and their state
tools/vc.py new 0002-binary-search         # scaffold intent + kata
cargo verus focus -p <crate> -- --expand-errors   # fast proof iteration
scripts/verify.sh [NNNN-name]              # the gate (same as CI)
```

Commit prefixes: `intent(NNNN):`, `spec(NNNN):`, `vericode(NNNN):`, `pipeline:`.
