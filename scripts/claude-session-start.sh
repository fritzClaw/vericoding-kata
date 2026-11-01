#!/bin/bash
# Claude Code SessionStart hook: make Verus available in cloud sessions.
# Enable it by registering it in .claude/settings.json (see docs/claude-code.md).
set -euo pipefail

if [ "${CLAUDE_CODE_REMOTE:-}" != "true" ]; then
  exit 0
fi

cd "${CLAUDE_PROJECT_DIR:-.}"

# Idempotent: ~/.verus/<VERUS_VERSION> is keyed by the pin in
# verus-toolchain.env, so only a version bump downloads anything.
scripts/install-verus.sh

# Pre-fetch crates (vstd & friends).
cargo fetch --quiet

# Put verus / cargo-verus on PATH for the session.
if [ -n "${CLAUDE_ENV_FILE:-}" ]; then
  scripts/install-verus.sh --print-env >> "$CLAUDE_ENV_FILE"
fi
