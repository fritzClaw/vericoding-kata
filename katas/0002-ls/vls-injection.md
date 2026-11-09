# vls: structure-injection bugs found while proving the unparse round trip

Kata 0003 had to prove that vls is a **correct unparser** in the sense of
Hermerschmidt, Kugelmann and Rumpe, *Towards More Security in Data Exchange:
Defining Unparsers with Context-Sensitive Encoders for Context-Free Grammars*
(IEEE SPW 2015):

> "the (un)parsing process for a given language is a correct round-trip, if for
> every AST x holds parse(unparse(x)) = x."

vls's output is a small document language. File names are **data tokens**.
Newline, the empty line between groups and the `NAME:` header are **control
tokens**. A correct unparser must encode every data token so that it can never
produce a control token. Writing down the AST and trying to prove the round
trip turned up the issues below.

Every example was run on two builds:
- **old**: `vls` at `496a5a7`, before the fix;
- **new**: `vls` on `main` after PR #4.

| #  | Issue | Severity | Status |
|----|-------|----------|--------|
| B1 | `:` was not escaped, so a file name can forge a `NAME:` header. Two different directory trees produce byte-identical output: the unparser is not injective. | High: structure injection | **Fixed** in PR #4 (D12: `:` → `\:`). Absence proved in kata 0003 (`theorem_unparse_injective`, `decode`) |
| B2 | Same root cause: a forged `NAME:` line inside a listing misleads line-oriented consumers | Medium | **Fixed** by the B1 fix |
| B3 | The verified core prints an empty line for a file operand with an empty name, which looks like a group separator | Low: latent, unreachable through the shell | **Not fixed.** Excluded by the precondition of `theorem_vls_ast_wf` |
| L1 | `vls EMPTYDIR` and `vls MISSING` print the same stdout (nothing) | By design | Documented. The difference is in stderr and the exit status, outside the document |
| L2 | `vls f` (a file) and `vls d` (a directory containing only `f`) print the same stdout | By design | Documented. The document doesn't encode file vs directory |

## B1: a file name forges a directory header (fixed)

**Root cause.** Kata 0002's original D12 escaped `\`, LF, TAB and
non-printable bytes, but passed `:` through unchanged. A header line is
`escape(NAME) + ":"`, so a file *named* `a:` printed exactly like the header
of a *directory* named `a`.

**Reproduction.** Two different trees and two different commands produce the same bytes:

```sh
# tree F: a regular file named "a:" and an empty directory "b"
mkdir -p F/b && touch 'F/a:'
# tree G: two empty directories "a" and "b"
mkdir -p G/a G/b

(cd F && vls 'a:' b)
(cd G && vls a b)
```

| old: `cd F && vls 'a:' b` | old: `cd G && vls a b` |
|---|---|
| `a:`<br>(empty line)<br>`b:` | `a:`<br>(empty line)<br>`b:` |

```sh
cmp <(cd F && vls 'a:' b) <(cd G && vls a b) && echo identical
# old: identical
# new: differs: F prints "a\:"
```

The file group always comes first and directory groups are sorted by name, so
the collision needs a directory that sorts first. Here `a` < `b`.

**Why it's a bug.** A data token (the file name `a:`) produced a control token
(a header). Given the output, no parser can tell whether `a` is a file or an
empty directory: `unparse` is not injective, so `parse(unparse(x)) = x` can't
hold for every AST. Any tool that consumes vls output can be steered by
whoever controls file names in the listed directories.

**How it was found.** Stating the AST for kata 0003 (groups `{header:
Option<name>, names}`) and looking for a counterexample to injectivity before
trying to prove it.

**Fix (PR #4).** D12 now maps `:` → `\:`, so an escaped name never contains a
bare `:`, and a bare `:` at the end of a line always means "header". New
spec test E12. Kata 0003 then proves:
- `theorem_unparse_injective`: different well-formed ASTs always print different bytes;
- `theorem_vls_unparses`: vls's stdout is exactly `unparse(ast_of(req))`;
- `decode`: the strict decoder inverts it.

The fixed output:

```
a\:

b:
```

## B2: forged headers inside a listing (fixed)

Same root cause as B1, different symptom. A directory *entry* ending in `:`
printed like a header in the middle of a group.

```sh
mkdir -p C/a C/c && touch 'C/a/b:' C/a/secret
cd C && vls a c
```

| old | new |
|---|---|
| `a:`<br>`b:`<br>`secret`<br>(empty line)<br>`c:` | `a:`<br>`b\:`<br>`secret`<br>(empty line)<br>`c:` |

With the old output, any line-oriented consumer that treats lines ending in `:`
as headers (`grep ':$'`, `awk '/:$/ {dir=$0}'`, …) concludes that `a` is empty
and that a directory `b` contains `secret`. Neither is true. A strict parser
that knows headers only start groups would still read this correctly, which is
why B2 is medium and B1 high. The `\:` escape removes the misreading entirely.

## B3: an empty file-operand name prints a fake separator (latent, not fixed)

kata 0002's verified core accepts any `Request` (D10, "robust core"). A
`File` operand with an empty name is printed as an empty line, which is the
group separator token:

```rust
let ops = vec![
    ls::Operand { name: b"".to_vec(), outcome: ls::Outcome::File },
    ls::Operand { name: b"d".to_vec(), outcome: ls::Outcome::Dir(vec![b"a".to_vec()]) },
];
let r = ls::run(&ls::Request { all: false, reverse: false, operands: ops });
// r.stdout == ["", "", "d:", "a"]
//            ^^ the file "" ^^ separator
```

The document then starts with an empty line, which isn't a valid unparse of any
well-formed AST: kata 0003's `decode` rejects it.

**Not reachable through the shell.** `vls ''` asks the OS, which never treats
the empty path as a file, so the operand is `Missing`:

```
$ vls ''
vls: cannot access : No such file or directory      (exit 2)
```

**Status.** Left as is. The theorem that vls only builds well-formed ASTs
(`theorem_vls_ast_wf`) requires file operands with non-empty names, so the
gap is explicit, not hidden. Closing it means a kata 0002 spec change, for
example dropping or rejecting empty-named file operands in the core (similar
to D10 for directory entries).

## L1, L2: information the document doesn't carry (by design)

These are not injections: the AST of kata 0003 deliberately doesn't contain
this information.

```
$ vls empty            # empty directory       -> stdout: (nothing)  exit 0
$ vls missing          # nonexistent path      -> stdout: (nothing)  exit 2,
                       #   stderr: vls: cannot access missing: No such file or directory
$ vls f                # regular file f        -> stdout: f
$ vls only             # directory with only f -> stdout: f
```

- L1: stdout is identical. The exit status and stderr tell them apart.
- L2: with a single operand there's no header, so the document doesn't say
  whether `f` is a file operand or an entry of a directory. Making it explicit
  would mean always printing headers, which would break `vls DIR | vwc -l`
  counting (kata 0003).

## Not affected: counting with `vls DIR | vwc -l`

None of the issues above changes the line count of a single-directory
listing. Newlines in names were already escaped (`a⏎b` prints as `a\nb`). Kata
0003 proves (`theorem_count_files`) that the number of LF bytes equals the
number of listed names, including names with newlines, where `ls | wc -l`
over-counts.

## Correction to earlier notes

PR #4's description, kata 0002's intent row E12 and the comment in the spec
test `spec_e12_colon_cannot_forge_header` give `vls x: d` vs `vls x d` as the
collision. That pair is **not** byte-identical: `vls x d` sorts `d` before `x`.
The spec test itself is still right: it checks that the old output `x:` is
rejected for that request. Only the justification is wrong; the exact
collision is the `a:` / `b` pair in B1. The intent and spec comment are locked
text, so fixing them is a spec-stage change that needs approval.
