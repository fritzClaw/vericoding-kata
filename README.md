# vericoding-kata

A workbench for **vericoding**: an AI agent writes Rust code *together with a
machine-checked proof* that the code meets a specification, and
[Verus](https://github.com/verus-lang/verus) checks the proof. The human
spends their attention on *what* should be true (intent and spec), not on
reading every line of code.

The weak link in vericoding is the spec. A proof against a wrong or weakened
spec is worthless. So this pipeline is built around one invariant:

> **The agent can never change what it is proving.** Specs are derived from a
> human-grilled intent, approved by a human, hash-locked, and every escape
> hatch that makes the verifier trust instead of check is rejected.

## The pipeline

```
 ┌────────────┐   grill-me    ┌────────────┐  spec-from-intent  ┌──────────────┐   vericode   ┌──────────────┐
 │   idea     │ ────────────▶ │  INTENT    │ ─────────────────▶ │  SPEC        │ ───────────▶ │  VERIFIED    │
 └────────────┘  (human +     │ intents/   │  (agent drafts,    │ frozen part  │  (agent,     │  <vc-*>      │
                  agent)      │ NNNN-*.md  │   HUMAN approves,  │ of katas/... │  iterates    │  regions     │
                              └────────────┘   vc.py lock)      │ + spec tests │  with Verus) │  filled in   │
                                                                └──────────────┘              └──────────────┘
                                                                        ▲                             │
                                                                        └─── spec bug? back to intent ┘
 gate on every push/PR:  scripts/verify.sh  =  vc.py check  +  Verus (--no-cheating)  +  cargo test
```

| Stage | Artifact | Who writes | Who approves | Changes require |
|---|---|---|---|---|
| 1. Intent | `intents/NNNN-name.md` (from `intents/TEMPLATE.md`) | human + agent via **grill-me** | human | code-owner review |
| 2. Spec | everything in `katas/NNNN-name/` **outside** `<vc-*>` regions: spec fns, contracts, spec tests | agent (`spec-from-intent` skill) | human, then `tools/vc.py lock` | code-owner review (lock changes) |
| 3. Vericode | `// <vc-helpers>` and `// <vc-code>` regions | agent (`vericode` skill) | **Verus**, via CI | green CI only |
| 3b. Shell (optional) | `// <vc-shell>` region in `src/main.rs`: trusted, unverified I/O glue | agent (`vericode` skill) | **human review** of the PR | review |

### 1. Intent: grill-me output, made checkable

Run your grill-me session, then capture the result with `intents/TEMPLATE.md`.
The important part is the **Decisions** table: every question the grilling
resolved gets a row, and each row must later map to a spec clause. Examples
list the right answer *and a plausible wrong answer*, and the spec must reject
the wrong one. "Open questions" must be empty before stage 2.

### 2. Spec: the trusted part

A kata is one crate, `katas/NNNN-name/`. Its `src/lib.rs` contains:

```rust
verus! {
pub open spec fn is_first_max(s: Seq<i64>, i: int) -> bool { ... }   // model of the intent

// <vc-helpers>
// </vc-helpers>                                                        // ← prover's space

pub fn first_max(v: &[i64]) -> (r: usize)
    requires v.len() > 0,                                               // D1
    ensures  is_first_max(v@, r as int),
{
    // <vc-code>
    assume(false);   // canonical "pending" stub, the only assume ever allowed
    unreached()
    // </vc-code>                                                       // ← prover's space
}

proof fn spec_examples() { ... }       // spec tests: accept E1..En, reject wrong answers
proof fn spec_first_max_is_unique(..)  // property lemmas: is the spec tight enough?
}
```

Spec tests are verified by Verus *before any implementation exists*. They are
how you check that the formal spec says what the intent says.

After the human approves, `tools/vc.py lock NNNN-name` pins the SHA-256 of
the frozen text (region contents removed), the kata `Cargo.toml`, and the
intent document into `specs.lock.json`.

### 3. Vericode: the untrusted part

The agent fills the regions until `scripts/verify.sh` is green. It may add
lemmas and helper fns in `<vc-helpers>`, but cannot touch anything else.

Programs that touch the OS (files, argv, stdout) keep all logic in a
verified pure core and put the syscalls in a `// <vc-shell>` region of
`src/main.rs`. Verus doesn't check that code, so it must stay a thin adapter
with no logic, and a human reviews it. Its surrounding skeleton is locked
like any spec.

### The gate: `scripts/verify.sh`

1. `tools/vc.py check`
   - the frozen spec, kata manifest, and intent match `specs.lock.json`
     (changed intent ⇒ spec must be re-reviewed);
   - every `.rs` file of a kata (`src/` and `tests/`) is locked; no other
     files (e.g. `build.rs`) may exist in a kata; every kata has
     `verify = true`; the workspace includes every kata;
   - no escape hatches anywhere (`assume`, `admit`, `external*`,
     `assume_specification`, `axiom`, `exec_allows_no_decreases_clause`,
     `assume_termination`, `unsafe`, …), and inside regions also no `cfg`,
     `mod`, `include!`, `extern`, or a second `verus!` block;
   - the toolchain pins agree (`verus-toolchain.env`, `Cargo.toml`,
     `rust-toolchain.toml`).
2. Verus: **implemented** katas with `--no-cheating` (separate target dir, so
   lenient cached results never leak in). **Pending** katas verify with the
   stub, so their spec tests are still checked.
3. `cargo test` on implemented katas (intent examples as runtime tests).

CI (`.github/workflows/verify.yml`) runs exactly this, and adds a
**⚠️ Spec change** banner on PRs that touch `specs.lock.json` or `intents/`.

## Quick start

```sh
scripts/install-verus.sh                    # pinned Verus release + Rust 1.99.1
eval "$(scripts/install-verus.sh --print-env)"
scripts/verify.sh                           # the gate
tools/vc.py status

# a new kata
tools/vc.py new 0002-binary-search          # scaffolds intent + crate
#   1. grill-me → fill intents/0002-binary-search.md
#   2. "spec kata 0002"     (spec-from-intent skill) → review → tools/vc.py lock 0002-binary-search
#   3. "vericode kata 0002" (vericode skill)         → scripts/verify.sh
```

## Layout

```
intents/                 human intent per kata (grill-me output) + TEMPLATE.md
katas/NNNN-name/         one verified crate per kata
specs.lock.json          hashes of approved specs + intents (written only by vc.py lock)
tools/vc.py              lock / check / status / new
scripts/verify.sh        the gate (local == CI)
scripts/install-verus.sh pinned Verus release installer
scripts/claude-session-start.sh   SessionStart hook for Claude Code cloud sessions
verus-toolchain.env      VERUS_VERSION / VSTD_VERSION / RUST_TOOLCHAIN pins
.claude/skills/          spec-from-intent, vericode
.github/                 CI, CODEOWNERS, PR template
docs/claude-code.md      enabling the Claude Code hook + permissions
```

## Repository settings you need to turn on

The pipeline is only as strong as its merge rules. On GitHub, protect `main`:

- Require the `verify / spec lock + Verus + tests` status check.
- Require pull request review, with **"Require review from Code Owners"**.
  Then any PR that touches `specs.lock.json`, `intents/`, or the gate itself
  needs your approval. Pure vericode PRs only need a green build.

## Releases (macOS Apple Silicon)

Push a tag `vX.Y.Z` on `main`. `.github/workflows/release.yml` then runs on an
Apple Silicon runner (`macos-14`):

1. the full gate (`tools/test_vc.py`, `scripts/verify.sh`) on that same machine;
2. `cargo build --release` for every binary target in the workspace;
3. ad-hoc signing, an arm64 check and a smoke test;
4. a GitHub Release with `vericoding-kata-vX.Y.Z-aarch64-apple-darwin.tar.gz`
   and `SHA256SUMS`, plus install notes.

The binaries are not notarized. A browser download is quarantined by
Gatekeeper; `xattr -d com.apple.quarantine <binary>` clears it. PRs that
touch the workflow run it as a dry run (build + artifact, no release).

## Upgrading Verus

Pick a release, then copy `verus`/`vstd` from
[its toolchain manifest](https://github.com/verus-lang/verus/tree/main/source/cargo-verus/toolchain-manifests)
into `verus-toolchain.env`. Update `vstd` in `Cargo.toml` and the channel in
`rust-toolchain.toml` (`vc check` fails until all three agree), then run
`scripts/verify.sh`.
