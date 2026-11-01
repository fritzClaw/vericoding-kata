# Claude Code setup

## Skills

`.claude/skills/spec-from-intent` and `.claude/skills/vericode` load
automatically in this repo. `grill-me` is your own (user-level) skill. Use it
for stage 1 and save the result with `intents/TEMPLATE.md`.

## SessionStart hook + permissions (opt-in)

To get Verus installed automatically in Claude Code cloud sessions, and to
pre-approve the routine pipeline commands, create `.claude/settings.json`:

```json
{
  "hooks": {
    "SessionStart": [
      {
        "hooks": [
          { "type": "command", "command": "$CLAUDE_PROJECT_DIR/scripts/claude-session-start.sh" }
        ]
      }
    ]
  },
  "permissions": {
    "allow": [
      "Bash(scripts/verify.sh:*)",
      "Bash(tools/vc.py status:*)",
      "Bash(tools/vc.py check:*)",
      "Bash(tools/vc.py new:*)",
      "Bash(cargo verus verify:*)",
      "Bash(cargo verus focus:*)",
      "Bash(cargo test:*)"
    ],
    "ask": [
      "Bash(tools/vc.py lock:*)",
      "Bash(python3 tools/vc.py lock:*)"
    ],
    "deny": [
      "Edit(/specs.lock.json)",
      "Write(/specs.lock.json)"
    ]
  }
}
```

- The hook runs only when `CLAUDE_CODE_REMOTE=true`. It is synchronous and
  idempotent: the first session downloads the pinned Verus release (~1–2 min),
  later ones take about a second. It also puts `verus`/`cargo-verus` on `PATH`.
- `tools/vc.py lock` is on `ask`, so locking a spec always needs your
  click, and the lock file can't be hand-edited.
- The cloud environment needs network access to `github.com` release assets,
  `static.rust-lang.org` (rustup), and crates.io.
