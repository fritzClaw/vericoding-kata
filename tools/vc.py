#!/usr/bin/env python3
"""vc — gatekeeper for the vericoding pipeline (stdlib only).

The trust story of this repo: a human approves the *intent* and the *spec*;
an agent (or a human) writes code and proofs; Verus checks code against spec.
That only works if the spec cannot be quietly changed or bypassed. This tool
enforces that:

  * Each kata source file has editable regions:
        // <vc-helpers> ... // </vc-helpers>   lemmas, helper fns, ghost code
        // <vc-code>    ... // </vc-code>      function bodies (verified)
        // <vc-shell>   ... // </vc-shell>     TRUSTED, unverified I/O glue;
                                               only in src/main.rs, needs
                                               human review
    Everything else is the frozen spec. Its SHA-256 (with region contents
    removed), the kata Cargo.toml, and the intent document are pinned in
    specs.lock.json. Every .rs file of a kata (src/ and tests/) is locked and
    scanned; top-level *.md docs are allowed (never compiled, not locked); any
    other file (build.rs, ...) is rejected.
  * Escape hatches that make Verus trust instead of check (assume, admit,
    external_body, axioms, ...) are rejected everywhere, except the canonical
    pending stubs `assume(false); unreached()` (exec fn) and `assume(false);`
    (proof fn) as the whole body of a <vc-code> region.

Commands:
  vc.py new NNNN-name      scaffold intents/NNNN-name.md and katas/NNNN-name/
  vc.py new lib-name       scaffold a reusable library lib-name/ (same gate)
  vc.py lock KATA...       (re)pin spec + intent hashes after human approval
  vc.py check              verify lock, escape hatches, toolchain pins
  vc.py status [--json|--markdown]   list katas and their state
"""
from __future__ import annotations

import argparse
import hashlib
import json
import re
import sys
import tomllib
from dataclasses import dataclass, field
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
KATAS = ROOT / "katas"
INTENTS = ROOT / "intents"
LOCK = ROOT / "specs.lock.json"
TOOLCHAIN_ENV = ROOT / "verus-toolchain.env"

REGION_OPEN = re.compile(r"^\s*//\s*<vc-(helpers|code|shell)>\s*$")
REGION_CLOSE = re.compile(r"^\s*//\s*</vc-(helpers|code|shell)>\s*$")
KATA_NAME = re.compile(r"^(\d{4}|lib)-[a-z0-9]+(-[a-z0-9]+)*$")  # katas/NNNN-name or top-level lib-name
WORKSPACE_MEMBERS = ["katas/*", "lib-*"]
# Canonical pending stubs: exec fn body, and proof fn (theorem) body.
STUBS = ("assume(false);\nunreached()", "assume(false);")

# (pattern, reason). Applied to code with comments and string literals removed.
FORBIDDEN_EVERYWHERE = [
    (r"\bassume\s*\(", "`assume` makes Verus trust a fact instead of proving it"),
    (r"\badmit\s*\(", "`admit` makes Verus trust a goal instead of proving it"),
    (r"\bassume_specification\b", "`assume_specification` trusts an unverified contract"),
    (r"verifier\s*(::|\()\s*external", "`external*` attributes exempt code from verification"),
    (r"\bexec_allows_no_decreases_clause\b", "termination must be proved (D: total correctness)"),
    (r"\bassume_termination\b", "termination must be proved"),
    (r"\bassume_unsupported_attributes\b", "unsupported attributes must not be assumed away"),
    (r"verifier\s*(::|\()\s*assume\b", "`#[verifier::assume(..)]` trusts undeclared externals"),
    (r"\baxiom\b", "axioms are trusted; they belong in vstd, not here"),
    (r"\bproof_from_false\b", "`proof_from_false` is only sound in unreachable code; prove it instead"),
    (r"\bunsafe\b", "unsafe code is outside the verified fragment"),
    (r"\bverus_keep_ghost\b", "cfg tricks can hide code from the verifier"),
]
FORBIDDEN_IN_REGIONS = [
    (r"\bverus\s*!", "editable regions must stay inside the existing verus! block"),
    (r"\bcfg\s*\(", "conditional compilation can hide code from the verifier"),
    (r"^\s*(pub\s+)?mod\s", "new modules would escape the spec lock"),
    (r"\binclude(_str|_bytes)?\s*!", "including files would escape the spec lock"),
    (r"#\s*\[\s*path\b", "`#[path]` would escape the spec lock"),
    (r"\bextern\b", "foreign code is not verified"),
]


# --------------------------------------------------------------------------
# Parsing
# --------------------------------------------------------------------------

@dataclass
class Region:
    kind: str
    start: int  # 1-based line of the opening marker
    lines: list[str] = field(default_factory=list)

    @property
    def body(self) -> str:
        return "\n".join(l.strip() for l in self.lines if l.strip())


@dataclass
class Source:
    path: Path
    frozen: list[tuple[int, str]]  # (1-based line no, text) outside regions, incl. markers
    regions: list[Region]

    def frozen_text(self) -> str:
        return "\n".join(t for _, t in self.frozen) + "\n"


class VcError(Exception):
    pass


def parse_source(path: Path) -> Source:
    text = path.read_text(encoding="utf-8").replace("\r\n", "\n")
    frozen: list[tuple[int, str]] = []
    regions: list[Region] = []
    current: Region | None = None
    for no, line in enumerate(text.split("\n"), start=1):
        if (m := REGION_OPEN.match(line)) is not None:
            if current is not None:
                raise VcError(f"{rel(path)}:{no}: nested <vc-{m[1]}> inside <vc-{current.kind}>")
            current = Region(m[1], no)
            frozen.append((no, line.strip()))
        elif (m := REGION_CLOSE.match(line)) is not None:
            if current is None or current.kind != m[1]:
                raise VcError(f"{rel(path)}:{no}: unmatched </vc-{m[1]}>")
            regions.append(current)
            current = None
            frozen.append((no, line.strip()))
        elif current is not None:
            current.lines.append(line)
        else:
            frozen.append((no, line.rstrip()))
    if current is not None:
        raise VcError(f"{rel(path)}:{current.start}: <vc-{current.kind}> is never closed")
    return Source(path, frozen, regions)


def strip_comments_and_strings(code: str) -> str:
    """Blank out comments and string literals, preserving line structure."""
    out, i, n = [], 0, len(code)
    while i < n:
        c = code[i]
        if code.startswith("//", i):
            j = code.find("\n", i)
            i = n if j == -1 else j
        elif code.startswith("/*", i):
            depth, j = 1, i + 2
            while j < n and depth:
                if code.startswith("/*", j):
                    depth, j = depth + 1, j + 2
                elif code.startswith("*/", j):
                    depth, j = depth - 1, j + 2
                else:
                    j += 1
            out.append("\n" * code.count("\n", i, j))
            i = j
        elif c == '"':
            j = i + 1
            while j < n and code[j] != '"':
                j += 2 if code[j] == "\\" else 1
            out.append('""' + "\n" * code.count("\n", i, j))
            i = j + 1
        else:
            out.append(c)
            i += 1
    return "".join(out)


def sha256(data: str | bytes) -> str:
    if isinstance(data, str):
        data = data.encode("utf-8")
    return hashlib.sha256(data).hexdigest()


def rel(p: Path) -> str:
    return p.resolve().relative_to(ROOT).as_posix()


# --------------------------------------------------------------------------
# Katas
# --------------------------------------------------------------------------

@dataclass
class Kata:
    name: str
    dir: Path

    @property
    def intent(self) -> Path:
        return INTENTS / f"{self.name}.md"

    @property
    def manifest(self) -> Path:
        return self.dir / "Cargo.toml"

    def files(self) -> list[Path]:
        return sorted(p for p in self.dir.rglob("*")
                      if p.is_file() and "target" not in p.relative_to(self.dir).parts)

    def sources(self) -> list[Path]:
        return [p for p in self.files() if p.suffix == ".rs"]

    def crate(self) -> str:
        return tomllib.loads(self.manifest.read_text())["package"]["name"]

    def fingerprint(self) -> dict:
        files = {rel(self.manifest): sha256(self.manifest.read_bytes())}
        for src in self.sources():
            files[rel(src)] = sha256(parse_source(src).frozen_text())
        intent = {"path": rel(self.intent), "sha256": sha256(self.intent.read_bytes())} \
            if self.intent.exists() else None
        return {"intent": intent, "files": files}

    def status(self) -> str:
        for src in self.sources():
            for r in parse_source(src).regions:
                if r.kind == "code" and r.body in STUBS:
                    return "pending"
        return "implemented"


def all_katas() -> list[Kata]:
    """Katas (katas/NNNN-name) and reusable libraries (top-level lib-name).
    Libraries go through exactly the same gate as katas."""
    dirs = sorted(KATAS.iterdir()) if KATAS.exists() else []
    dirs += sorted(ROOT.glob("lib-*"))
    return [Kata(d.name, d) for d in dirs if d.is_dir() and (d / "Cargo.toml").exists()]


def find_kata(name: str) -> Kata:
    name = name.rstrip("/").split("/")[-1]
    for k in all_katas():
        if k.name == name:
            return k
    raise VcError(f"no kata named {name!r} under katas/ (or library lib-*)")


def load_lock() -> dict:
    if not LOCK.exists():
        return {"version": 1, "katas": {}}
    return json.loads(LOCK.read_text())


def save_lock(lock: dict) -> None:
    lock["katas"] = dict(sorted(lock["katas"].items()))
    LOCK.write_text(json.dumps(lock, indent=2) + "\n")


# --------------------------------------------------------------------------
# Checks
# --------------------------------------------------------------------------

def scan(src: Source) -> list[str]:
    problems: list[str] = []

    def run(lines: list[tuple[int, str]], rules, where: str):
        numbered = {}
        cleaned = strip_comments_and_strings("\n".join(t for _, t in lines)).split("\n")
        for (no, _), text in zip(lines, cleaned):
            numbered[no] = text
        for no, text in numbered.items():
            for pat, why in rules:
                if re.search(pat, text):
                    problems.append(f"{rel(src.path)}:{no}: forbidden in {where}: {why}\n    {text.strip()}")

    run(src.frozen, FORBIDDEN_EVERYWHERE, "spec")
    is_main = src.path.parent.name == "src" and src.path.name == "main.rs"
    for r in src.regions:
        if r.kind == "shell" and not is_main:
            problems.append(f"{rel(src.path)}:{r.start}: <vc-shell> is only allowed in src/main.rs")
        if r.kind == "code" and r.body in STUBS:
            continue  # canonical pending stub
        lines = [(r.start + 1 + i, l) for i, l in enumerate(r.lines)]
        run(lines, FORBIDDEN_EVERYWHERE + FORBIDDEN_IN_REGIONS, f"<vc-{r.kind}>")
    return problems


def check_kata(k: Kata, lock: dict) -> list[str]:
    problems: list[str] = []
    if not KATA_NAME.match(k.name):
        problems.append(f"{rel(k.dir)}: directory must be named NNNN-kebab-name (or lib-kebab-name)")
    if not k.intent.exists():
        problems.append(f"{rel(k.dir)}: missing intent document {rel(k.intent)}")

    manifest = tomllib.loads(k.manifest.read_text())
    if manifest.get("package", {}).get("metadata", {}).get("verus", {}).get("verify") is not True:
        problems.append(f"{rel(k.manifest)}: [package.metadata.verus] verify = true is required")

    for f in k.files():
        parts = f.relative_to(k.dir).parts
        is_lib = k.name.startswith("lib-")
        allowed = parts == ("Cargo.toml",) or (
            parts[0] in ("src", "tests") and f.suffix == ".rs") or (
            f.suffix == ".md" and (len(parts) == 1 or (is_lib and parts[0] not in ("src", "tests"))))
        # docs (*.md) are never compiled and not locked; libraries may keep them in subfolders
        if not allowed:
            problems.append(f"{rel(f)}: only Cargo.toml, src/**/*.rs, tests/**/*.rs and *.md docs may live "
                            "in a kata or library (build scripts and other files would escape the spec lock)")
    sources = k.sources()
    if not sources:
        problems.append(f"{rel(k.dir)}: no Rust sources")
    for path in sources:
        try:
            problems += scan(parse_source(path))
        except VcError as e:
            problems.append(str(e))
    if problems:
        return problems

    entry = lock["katas"].get(k.name)
    if entry is None:
        return [f"{rel(k.dir)}: spec is not locked. After the spec is approved run: tools/vc.py lock {k.name}"]
    current = k.fingerprint()
    if current["intent"] != entry.get("intent"):
        problems.append(f"{rel(k.intent)}: intent changed since the spec was locked; re-review the spec, then re-lock")
    locked_files, now_files = entry.get("files", {}), current["files"]
    for f in sorted(set(locked_files) | set(now_files)):
        if f not in now_files:
            problems.append(f"{f}: locked file was removed")
        elif f not in locked_files:
            problems.append(f"{f}: new file is not covered by the spec lock")
        elif locked_files[f] != now_files[f]:
            what = "manifest" if f.endswith("Cargo.toml") else "frozen spec (outside <vc-*> regions)"
            problems.append(f"{f}: {what} differs from specs.lock.json")
    return problems


def check_toolchain() -> list[str]:
    env = dict(
        line.split("=", 1) for line in TOOLCHAIN_ENV.read_text().splitlines()
        if line.strip() and not line.lstrip().startswith("#")
    )
    problems = []
    ws = tomllib.loads((ROOT / "Cargo.toml").read_text())
    vstd = ws.get("workspace", {}).get("dependencies", {}).get("vstd")
    if vstd != f"={env['VSTD_VERSION']}":
        problems.append(f"Cargo.toml: workspace vstd = {vstd!r}, expected '={env['VSTD_VERSION']}'")
    if ws.get("workspace", {}).get("members") != WORKSPACE_MEMBERS:
        problems.append(f"Cargo.toml: workspace members must be exactly {WORKSPACE_MEMBERS} so no kata or library escapes CI")
    chan = tomllib.loads((ROOT / "rust-toolchain.toml").read_text())["toolchain"]["channel"]
    if chan != env["RUST_TOOLCHAIN"]:
        problems.append(f"rust-toolchain.toml: channel {chan!r}, expected {env['RUST_TOOLCHAIN']!r}")
    return problems


# --------------------------------------------------------------------------
# Commands
# --------------------------------------------------------------------------

def cmd_check(_args) -> int:
    lock = load_lock()
    problems = check_toolchain()
    names = set()
    for k in all_katas():
        names.add(k.name)
        problems += check_kata(k, lock)
    for stale in sorted(set(lock["katas"]) - names):
        problems.append(f"specs.lock.json: kata {stale!r} is locked but its directory is gone")
    if problems:
        print("vc check: FAILED\n", file=sys.stderr)
        for p in problems:
            print(f"  ✗ {p}", file=sys.stderr)
        return 1
    print(f"vc check: OK ({len(names)} kata(s))")
    return 0


def cmd_lock(args) -> int:
    lock = load_lock()
    for name in args.katas:
        k = find_kata(name)
        problems = [p for p in check_kata(k, {"katas": {k.name: k.fingerprint()}})]
        if problems:
            for p in problems:
                print(f"  ✗ {p}", file=sys.stderr)
            print(f"vc lock: refusing to lock {k.name}", file=sys.stderr)
            return 1
        lock["katas"][k.name] = k.fingerprint()
        print(f"vc lock: pinned spec of {k.name}")
    save_lock(lock)
    return 0


def cmd_status(args) -> int:
    lock = load_lock()
    rows = []
    for k in all_katas():
        try:
            st = k.status()
        except VcError as e:
            st = f"broken ({e})"
        rows.append({"kata": k.name, "crate": k.crate(), "status": st,
                     "locked": k.name in lock["katas"]})
    if args.json:
        print(json.dumps(rows))
    elif args.markdown:
        print("| Kata | Crate | Spec locked | Status |\n|---|---|---|---|")
        for r in rows:
            icon = {"implemented": "✅ implemented", "pending": "⏳ pending"}.get(r["status"], r["status"])
            print(f"| `{r['kata']}` | `{r['crate']}` | {'🔒' if r['locked'] else '—'} | {icon} |")
    else:
        for r in rows:
            print(f"{r['kata']:32} {r['crate']:24} {'locked' if r['locked'] else 'UNLOCKED':9} {r['status']}")
    return 0


KATA_TOML = """[package]
name = "{crate}"
version = "0.1.0"
edition.workspace = true
publish.workspace = true

[dependencies]
vstd.workspace = true

[package.metadata.verus]
verify = true

[lints]
workspace = true
"""

KATA_LIB = """//! Kata {name}.
//! Intent: intents/{name}.md
//!
//! Everything OUTSIDE the `<vc-helpers>` / `<vc-code>` regions is the frozen,
//! human-approved specification (hashed in specs.lock.json).
#![forbid(unsafe_code)]

use vstd::prelude::*;

verus! {{

// ---------------------------------------------------------------------------
// Specification (derived from the intent's Decisions table)
// ---------------------------------------------------------------------------

// <vc-helpers>
// </vc-helpers>

// pub fn todo(...) -> (r: ...)
//     requires ...,
//     ensures ...,
// {{
//     // <vc-code>
//     assume(false);
//     unreached()
//     // </vc-code>
// }}

// ---------------------------------------------------------------------------
// Spec tests: one assert per Example (accept the right answer, reject the
// plausible wrong one) and one lemma per Property.
// ---------------------------------------------------------------------------

}} // verus!
"""


def cmd_new(args) -> int:
    name = args.name
    if not KATA_NAME.match(name):
        raise VcError("name must look like 0002-binary-search (kata) or lib-line-codec (library)")
    d = (ROOT if name.startswith("lib-") else KATAS) / name
    if d.exists():
        raise VcError(f"{rel(d)} already exists")
    crate = re.sub(r"^(\d{4}|lib)-", "", name).replace("-", "_")
    (d / "src").mkdir(parents=True)
    (d / "Cargo.toml").write_text(KATA_TOML.format(crate=crate))
    (d / "src" / "lib.rs").write_text(KATA_LIB.format(name=name))
    intent = INTENTS / f"{name}.md"
    if not intent.exists():
        tpl = (INTENTS / "TEMPLATE.md").read_text()
        intent.write_text(tpl.replace("NNNN-short-name", name).replace("NNNN — Title", name))
    print(f"vc new: created {rel(d)}/ (crate `{crate}`) and {rel(intent)}")
    return 0


def main(argv: list[str] | None = None) -> int:
    p = argparse.ArgumentParser(prog="vc.py", description=__doc__,
                                formatter_class=argparse.RawDescriptionHelpFormatter)
    sub = p.add_subparsers(dest="cmd", required=True)
    sub.add_parser("check").set_defaults(fn=cmd_check)
    lp = sub.add_parser("lock")
    lp.add_argument("katas", nargs="+")
    lp.set_defaults(fn=cmd_lock)
    sp = sub.add_parser("status")
    g = sp.add_mutually_exclusive_group()
    g.add_argument("--json", action="store_true")
    g.add_argument("--markdown", action="store_true")
    sp.set_defaults(fn=cmd_status)
    np_ = sub.add_parser("new")
    np_.add_argument("name")
    np_.set_defaults(fn=cmd_new)
    args = p.parse_args(argv)
    try:
        return args.fn(args)
    except VcError as e:
        print(f"vc: {e}", file=sys.stderr)
        return 2


if __name__ == "__main__":
    sys.exit(main())
