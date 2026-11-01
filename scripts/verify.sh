#!/usr/bin/env bash
# The one gate. Humans, agents and CI all run exactly this.
#
#   scripts/verify.sh                 # all katas
#   scripts/verify.sh 0001-first-max  # selected katas
#
# 1. tools/vc.py check   spec lock intact, no escape hatches, pins consistent
# 2. Verus               implemented katas: --no-cheating
#                        pending katas: only the canonical stub may cheat
#                        (enforced by step 1); the spec tests must still verify
# 3. cargo test          runtime tests of implemented katas
set -euo pipefail

repo_root="$(cd "$(dirname "${BASH_SOURCE[0]}")/.." && pwd)"
cd "$repo_root"

if ! command -v cargo-verus >/dev/null; then
  eval "$(scripts/install-verus.sh --print-env)"
fi
command -v cargo-verus >/dev/null || { echo "verify: cargo-verus not found; run scripts/install-verus.sh" >&2; exit 1; }

python3 tools/vc.py check

selected=("$@")
summary=()
failed=0

while IFS=$'\t' read -r kata crate status; do
  if ((${#selected[@]})) && [[ ! " ${selected[*]} " == *" $kata "* ]]; then
    continue
  fi
  echo "::group::verify $kata ($status)"
  if [[ "$status" == "implemented" ]]; then
    # Separate target dir: cargo does not re-run Verus when only Verus flags
    # change, so strict and lenient results must never share a cache.
    if cargo verus verify -p "$crate" --target-dir target/verus-strict \
         --fwd-verus-args-to roots -- --no-cheating \
       && cargo test -q -p "$crate"; then
      summary+=("✅ $kata: verified (--no-cheating), tests pass")
    else
      summary+=("❌ $kata: FAILED"); failed=1
    fi
  else
    if cargo verus verify -p "$crate" --target-dir target/verus-pending; then
      summary+=("⏳ $kata: spec verified, implementation pending")
    else
      summary+=("❌ $kata: spec tests FAILED"); failed=1
    fi
  fi
  echo "::endgroup::"
done < <(python3 tools/vc.py status --json | python3 -c '
import json, sys
for r in json.load(sys.stdin):
    print(r["kata"], r["crate"], r["status"], sep="\t")
')

echo
printf '%s\n' "${summary[@]}"
exit "$failed"
