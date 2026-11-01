## Stage

- [ ] **Intent**: new/changed `intents/NNNN-*.md` (grill-me output)
- [ ] **Spec**: Verus spec + spec tests, `specs.lock.json` re-locked
- [ ] **Vericode**: implementation + proofs only (`<vc-*>` regions), no lock change
- [ ] **Pipeline**: tooling / CI / toolchain

## Kata(s)

<!-- e.g. 0002-binary-search -->

## Spec review (Spec stage only)

<!-- Map every Decision / Example / Property in the intent to the spec clause
     or spec test that captures it. Anything not captured goes under
     "Not verified" in the intent. -->

| Intent item | Spec clause / spec test |
|---|---|
| D1 | |

## Checklist

- [ ] `scripts/verify.sh` passes locally
- [ ] Vericode PRs: `specs.lock.json` and `intents/` are untouched
