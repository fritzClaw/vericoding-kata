//! Differential test (intent 0002, "Not verified"): validates the TRUSTED
//! shell end to end by comparing `vls` with `LC_ALL=C ls -1` on plain-ASCII
//! names, where both must agree on stdout and exit status.
//! Skipped (passes trivially) if GNU `ls` is not installed.

use std::fs;
use std::path::{Path, PathBuf};
use std::process::Command;

fn gnu_ls_available() -> bool {
    Command::new("ls")
        .arg("--version")
        .output()
        .map(|o| String::from_utf8_lossy(&o.stdout).contains("GNU coreutils"))
        .unwrap_or(false)
}

/// d1: b a .h !x Zed _u a.txt   d2: z   d3: (empty)   f1, .hid: files
fn fixture() -> PathBuf {
    let root = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("vls-diff-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    for d in ["d1", "d2", "d3"] {
        fs::create_dir_all(root.join(d)).unwrap();
    }
    for f in ["d1/b", "d1/a", "d1/.h", "d1/!x", "d1/Zed", "d1/_u", "d1/a.txt", "d2/z", "f1", ".hid"] {
        fs::write(root.join(f), b"").unwrap();
    }
    root
}

fn run(program: &str, args: &[&str], cwd: &Path) -> (Vec<u8>, Option<i32>) {
    let mut cmd = Command::new(program);
    if program == "ls" {
        cmd.arg("-1");
    }
    let out = cmd.args(args).current_dir(cwd).env("LC_ALL", "C").output().unwrap();
    (out.stdout, out.status.code())
}

#[test]
fn vls_matches_gnu_ls_on_plain_names() {
    if !gnu_ls_available() {
        eprintln!("GNU ls not found; skipping differential test");
        return;
    }
    let root = fixture();
    let vls = env!("CARGO_BIN_EXE_vls");
    let cases: &[&[&str]] = &[
        &[],
        &["-a"],
        &["-r"],
        &["-ar"],
        &["-r", "-a"],
        &["d1"],
        &["-a", "d1"],
        &["d1", "-r"],                // flags after operands (D19)
        &["d1", "d2", "f1"],
        &["-r", "d1", "d2", "f1"],
        &["f1", ".hid", "d2", "d3"],
        &["d3"],
        &["d1", "d1"],
        &["d1", "missing"],
        &["missing"],
        &["missing", "f1"],
        &["-x", "d1"],                // invalid option (D19)
        &["--", "-a"],                // `--` ends options: `-a` is a (missing) operand
        &["-"],                       // lone `-` is an operand
        &["d1/b", "d2"],              // file operand printed as typed (D13)
    ];
    let mut failures = Vec::new();
    for args in cases {
        let expected = run("ls", args, &root);
        let actual = run(vls, args, &root);
        if expected != actual {
            failures.push(format!(
                "args {:?}\n  ls : {:?} exit {:?}\n  vls: {:?} exit {:?}",
                args,
                String::from_utf8_lossy(&expected.0),
                expected.1,
                String::from_utf8_lossy(&actual.0),
                actual.1
            ));
        }
    }
    let _ = fs::remove_dir_all(&root);
    assert!(failures.is_empty(), "vls differs from GNU ls:\n{}", failures.join("\n"));
}
