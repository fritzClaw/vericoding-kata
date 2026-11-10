"""Regression tests for tools/vc.py: every way to cheat the gate must fail.

Run: python3 -m unittest discover -s tools
Each test builds a throwaway repo (the real tools + toolchain pins, plus a
synthetic fixture kata, locked), applies one tampering, and asserts
`vc.py check` rejects it with the expected message. Independent of the real
katas, so they can be added, implemented or removed freely.
"""
import re
import shutil
import subprocess
import sys
import tempfile
import unittest
from pathlib import Path

ROOT = Path(__file__).resolve().parent.parent
COPY = ["tools", "intents/TEMPLATE.md", "Cargo.toml", "rust-toolchain.toml",
        "verus-toolchain.env"]
NAME = "0999-fixture"
KATA = f"katas/{NAME}"
LIB = f"{KATA}/src/lib.rs"
INTENT = f"intents/{NAME}.md"

# One pending fn (canonical stub) and one implemented fn.
FIXTURE_LIB = """\
use vstd::prelude::*;

verus! {

pub open spec fn is_id(x: u8, r: u8) -> bool { r == x }

// <vc-helpers>
// </vc-helpers>

pub fn pending(x: u8) -> (r: u8)
    ensures
        is_id(x, r),
{
    // <vc-code>
    assume(false);
    unreached()
    // </vc-code>
}

pub fn implemented(x: u8) -> (r: u8)
    ensures
        is_id(x, r),
{
    // <vc-code>
    x
    // </vc-code>
}

proof fn spec_examples() {
    assert(is_id(1, 1));
}

} // verus!
"""


class VcCheckTest(unittest.TestCase):
    def setUp(self):
        self.tmp = Path(tempfile.mkdtemp())
        for name in COPY:
            src, dst = ROOT / name, self.tmp / name
            dst.parent.mkdir(parents=True, exist_ok=True)
            if src.is_dir():
                shutil.copytree(src, dst, ignore=shutil.ignore_patterns("__pycache__"))
            else:
                shutil.copy(src, dst)
        self.vc("new", NAME)
        (self.tmp / LIB).write_text(FIXTURE_LIB)
        (self.tmp / INTENT).write_text("# fixture intent\n")
        self.vc("lock", NAME)

    def tearDown(self):
        shutil.rmtree(self.tmp)

    def vc(self, *args):
        r = subprocess.run([sys.executable, "-I", "tools/vc.py", *args],
                           cwd=self.tmp, capture_output=True, text=True)
        self.assertEqual(r.returncode, 0, f"vc {' '.join(args)} failed:\n{r.stderr}")
        return r

    def check(self):
        return subprocess.run([sys.executable, "-I", "tools/vc.py", "check"],
                              cwd=self.tmp, capture_output=True, text=True)

    def edit(self, rel, pattern, repl, count=1):
        p = self.tmp / rel
        text, n = re.subn(pattern, repl, p.read_text(), count=count, flags=re.M)
        self.assertEqual(n, count, f"pattern {pattern!r} not found in {rel}")
        p.write_text(text)

    def add_helper(self, code):
        self.edit(LIB, r"^// <vc-helpers>$", "// <vc-helpers>\n" + code)

    def assertRejected(self, needle):
        r = self.check()
        self.assertEqual(r.returncode, 1, r.stdout + r.stderr)
        self.assertIn(needle, r.stderr)

    # -- baseline ---------------------------------------------------------
    def test_clean_repo_passes(self):
        r = self.check()
        self.assertEqual(r.returncode, 0, r.stderr)

    def test_benign_helper_passes(self):
        self.add_helper("// we never assume(false) here\nproof fn lemma_ok() {}")
        self.assertEqual(self.check().returncode, 0)

    # -- spec tampering ---------------------------------------------------
    def test_changed_contract(self):
        self.edit(LIB, r"ensures\n", "ensures\n        true,\n")
        self.assertRejected("frozen spec")

    def test_changed_spec_test(self):
        self.edit(LIB, r"^proof fn spec_examples\(\) \{$", "proof fn spec_examples() {}\nproof fn _x() {")
        self.assertRejected("frozen spec")

    def test_changed_intent(self):
        (self.tmp / INTENT).write_text("anything goes\n")
        self.assertRejected("intent changed")

    def test_verification_disabled(self):
        self.edit(f"{KATA}/Cargo.toml", r"verify = true", "verify = false")
        self.assertRejected("verify = true is required")

    def test_unlocked_extra_file(self):
        (self.tmp / KATA / "src/extra.rs").write_text("pub fn f() {}\n")
        self.assertRejected("not covered by the spec lock")

    def test_kata_dropped_from_workspace(self):
        self.edit("Cargo.toml", r'members = \["katas/\*", "lib-\*"\]', 'members = ["katas/*"]')
        self.assertRejected("workspace members")

    def test_vstd_pin_drift(self):
        self.edit("Cargo.toml", r'vstd = "=[^"]+"', 'vstd = "*"')
        self.assertRejected("workspace vstd")

    def test_unclosed_region(self):
        self.edit(LIB, r"^    // </vc-code>\n\}\n\nproof fn", "}\n\nproof fn")
        self.assertRejected("never closed")

    # -- escape hatches ---------------------------------------------------
    def test_admit(self):
        self.add_helper("proof fn l() ensures false { admit(); }")
        self.assertRejected("`admit`")

    def test_assume_outside_stub(self):
        self.add_helper("proof fn l() ensures false { assume(false); }")
        self.assertRejected("`assume`")

    def test_proof_stub_is_pending(self):
        self.edit(LIB, r"^proof fn spec_examples\(\) \{$",
                  "proof fn spec_examples() {}\nproof fn theorem_x() ensures true {\n    // <vc-code>\n    assume(false);\n    // </vc-code>\n}\nproof fn _y() {")
        self.vc("lock", NAME)
        self.assertEqual(self.check().returncode, 0)

    def test_assume_beside_proof_stub_rejected(self):
        self.edit(LIB, r"^proof fn spec_examples\(\) \{$",
                  "proof fn spec_examples() {}\nproof fn theorem_x() ensures true {\n    // <vc-code>\n    assume(false);\n    // </vc-code>\n}\nproof fn _y() {")
        self.vc("lock", NAME)
        self.edit(LIB, r"^    assume\(false\);\n    // </vc-code>\n\}\nproof fn _y", "    assume(false);\n    assume(true);\n    // </vc-code>\n}\nproof fn _y")
        self.assertRejected("`assume`")

    def test_modified_stub_is_no_longer_exempt(self):
        self.edit(LIB, r"^    unreached\(\)$", "    let _x = 1;\n    unreached()")
        self.assertRejected("`assume`")

    def test_external_body(self):
        self.add_helper("#[verifier::external_body]\nfn f() {}")
        self.assertRejected("`external*`")

    def test_external_old_syntax(self):
        self.add_helper("#[verifier(external)]\nfn f() {}")
        self.assertRejected("`external*`")

    def test_assume_specification(self):
        self.add_helper("pub assume_specification[ core::mem::swap ](a: &mut u8, b: &mut u8);")
        self.assertRejected("assume_specification")

    def test_axiom(self):
        self.add_helper("pub axiom fn ax() ensures false;")
        self.assertRejected("axioms")

    def test_no_decreases(self):
        self.add_helper("#[verifier::exec_allows_no_decreases_clause]\nfn f() { loop {} }")
        self.assertRejected("termination")

    def test_unsafe(self):
        self.add_helper("fn f() { unsafe { } }")
        self.assertRejected("unsafe")

    def test_cfg_in_region(self):
        self.add_helper("#[cfg(any())]\nfn f() {}")
        self.assertRejected("conditional compilation")

    def test_escape_verus_block(self):
        self.add_helper("} pub fn unverified() {} verus! {")
        self.assertRejected("verus! block")

    def test_new_module(self):
        self.add_helper("mod sneaky;")
        self.assertRejected("new modules")

    # -- files outside src/ and trusted shell -----------------------------
    def test_build_script_rejected(self):
        (self.tmp / KATA / "build.rs").write_text("fn main() {}\n")
        self.assertRejected("build scripts")

    def test_top_level_markdown_allowed(self):
        (self.tmp / KATA / "NOTES.md").write_text("# notes\n")
        r = self.check()
        self.assertEqual(r.returncode, 0, r.stderr)

    def test_markdown_in_src_rejected(self):
        (self.tmp / KATA / "src/notes.md").write_text("# notes\n")
        self.assertRejected("*.md docs")

    def test_library_goes_through_the_gate(self):
        self.vc("new", "lib-demo")
        self.assertTrue((self.tmp / "lib-demo/src/lib.rs").exists())
        self.assertRejected("lib-demo: spec is not locked")
        self.vc("lock", "lib-demo")
        (self.tmp / "lib-demo/skill").mkdir()
        (self.tmp / "lib-demo/skill/SKILL.md").write_text("# skill\n")
        r = self.check()
        self.assertEqual(r.returncode, 0, r.stderr)
        (self.tmp / "lib-demo/build.rs").write_text("fn main() {}\n")
        self.assertRejected("build scripts")

    def test_library_escape_hatch_scanned(self):
        self.vc("new", "lib-demo")
        p = self.tmp / "lib-demo/src/lib.rs"
        p.write_text(p.read_text().replace("// <vc-helpers>\n", "// <vc-helpers>\nproof fn l() ensures false { admit(); }\n"))
        r = subprocess.run([sys.executable, "-I", "tools/vc.py", "lock", "lib-demo"],
                           cwd=self.tmp, capture_output=True, text=True)
        self.assertEqual(r.returncode, 1)
        self.assertIn("`admit`", r.stderr)

    def test_kata_markdown_in_subfolder_rejected(self):
        (self.tmp / KATA / "docs").mkdir()
        (self.tmp / KATA / "docs/x.md").write_text("# x\n")
        self.assertRejected("*.md docs")

    def test_unlocked_test_file(self):
        (self.tmp / KATA / "tests").mkdir()
        (self.tmp / KATA / "tests/t.rs").write_text("#[test] fn t() {}\n")
        self.assertRejected("not covered by the spec lock")

    def test_shell_region_only_in_main(self):
        self.add_helper("// <vc-shell>\n// </vc-shell>")
        self.assertRejected("nested")
        self.edit(LIB, r"^// <vc-shell>\n// </vc-shell>\n", "")
        self.edit(LIB, r"^proof fn spec_examples", "// <vc-shell>\n// </vc-shell>\nproof fn spec_examples")
        self.assertRejected("only allowed in src/main.rs")

    def _with_shell(self):
        (self.tmp / KATA / "src/main.rs").write_text(
            "fn main() {\n    // <vc-shell>\n    // </vc-shell>\n}\n")
        self.vc("lock", NAME)

    def test_shell_region_editable(self):
        self._with_shell()
        self.edit(f"{KATA}/src/main.rs", r"^    // <vc-shell>$",
                  '    // <vc-shell>\n    let args: Vec<String> = std::env::args().collect();\n    println!("{}", args.len());')
        r = self.check()
        self.assertEqual(r.returncode, 0, r.stderr)

    def test_shell_region_scanned(self):
        self._with_shell()
        self.edit(f"{KATA}/src/main.rs", r"^    // <vc-shell>$", "    // <vc-shell>\n    unsafe { }")
        self.assertRejected("unsafe")

    def test_shell_skeleton_locked(self):
        self._with_shell()
        self.edit(f"{KATA}/src/main.rs", r"^fn main\(\) \{$", "fn main() {\n    sneaky();")
        self.assertRejected("frozen spec")

    def test_include(self):
        self.add_helper('include!("x.rs");')
        self.assertRejected("including files")


if __name__ == "__main__":
    unittest.main()
