//! End-to-end test of `vls DIR | vwc -l` (intent 0003, "Not verified"):
//! exercises both trusted shells. Builds `vls` from kata 0002 first.

use std::fs;
use std::io::Write;
use std::path::{Path, PathBuf};
use std::process::{Command, Stdio};

fn workspace() -> PathBuf {
    Path::new(env!("CARGO_MANIFEST_DIR")).join("../..")
}

fn vls() -> PathBuf {
    let status = Command::new(env!("CARGO"))
        .args(["build", "-q", "-p", "ls", "--bin", "vls"])
        .current_dir(workspace())
        .status()
        .unwrap();
    assert!(status.success(), "building vls failed");
    let target = std::env::var_os("CARGO_TARGET_DIR").map(PathBuf::from).unwrap_or(workspace().join("target"));
    target.join("debug").join("vls")
}

/// `vls ARGS | vwc -l` -> (stdout of vwc, exit code of vwc)
fn pipeline(vls: &Path, args: &[&str], cwd: &Path) -> (String, Option<i32>) {
    let listing = Command::new(vls).args(args).current_dir(cwd).output().unwrap();
    let mut wc = Command::new(env!("CARGO_BIN_EXE_vwc"))
        .arg("-l")
        .stdin(Stdio::piped())
        .stdout(Stdio::piped())
        .spawn()
        .unwrap();
    wc.stdin.take().unwrap().write_all(&listing.stdout).unwrap();
    let out = wc.wait_with_output().unwrap();
    (String::from_utf8(out.stdout).unwrap(), out.status.code())
}

#[test]
fn counts_files() {
    let root = Path::new(env!("CARGO_TARGET_TMPDIR")).join(format!("vwc-{}", std::process::id()));
    let _ = fs::remove_dir_all(&root);
    fs::create_dir_all(root.join("d1/sub")).unwrap();
    fs::create_dir_all(root.join("empty")).unwrap();
    for f in ["d1/b", "d1/a", "d1/.h", "d1/!x", "d1/a\nb", "d1/x:"] {
        fs::write(root.join(f), b"").unwrap();
    }
    let vls = vls();
    // E1/E2: 6 visible entries (b a !x sub, a<LF>b, x:) though one name has a newline
    assert_eq!(pipeline(&vls, &["d1"], &root), ("6\n".into(), Some(0)));
    // E3: -a adds .h . ..
    assert_eq!(pipeline(&vls, &["-a", "d1"], &root), ("9\n".into(), Some(0)));
    // E4
    assert_eq!(pipeline(&vls, &["empty"], &root), ("0\n".into(), Some(0)));
    // E5 (D6 pass-through)
    assert_eq!(pipeline(&vls, &["missing"], &root), ("0\n".into(), Some(0)));
    let _ = fs::remove_dir_all(&root);
}

#[test]
fn e9_rejects_other_arguments() {
    for args in [&[][..], &["-c"], &["-l", "file"], &["-lc"]] {
        let out = Command::new(env!("CARGO_BIN_EXE_vwc")).args(args).stdin(Stdio::null()).output().unwrap();
        assert_eq!(out.status.code(), Some(2), "args {args:?}");
        assert!(out.stdout.is_empty(), "args {args:?}");
    }
}
