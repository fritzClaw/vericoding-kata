//! Kata 0001 — index of the first maximum.
//! Intent: intents/0001-first-max.md
//!
//! Everything OUTSIDE the `<vc-helpers>` / `<vc-code>` regions is the frozen,
//! human-approved specification (hashed in specs.lock). Only the regions may
//! be edited during the vericoding stage.
#![forbid(unsafe_code)]

use vstd::prelude::*;

verus! {

// ---------------------------------------------------------------------------
// Specification
// ---------------------------------------------------------------------------

/// `i` is the position of the first maximum of `s`.
pub open spec fn is_first_max(s: Seq<i64>, i: int) -> bool {
    // D3: a valid index
    &&& 0 <= i < s.len()
    // it is a maximum
    &&& forall|j: int| 0 <= j < s.len() ==> s[j] <= s[i]
    // D2: and the first one: everything before it is strictly smaller
    &&& forall|j: int| 0 <= j < i ==> s[j] < s[i]
}

// <vc-helpers>
// </vc-helpers>

pub fn first_max(v: &[i64]) -> (r: usize)
    requires
        v.len() > 0,  // D1
    ensures
        is_first_max(v@, r as int),
{
    // <vc-code>
    let mut best: usize = 0;
    let mut i: usize = 1;
    while i < v.len()
        invariant
            1 <= i <= v.len(),
            best < i,
            // v[best] is a maximum of the prefix v[..i]
            forall|j: int| 0 <= j < i ==> v[j] <= v[best as int],
            // ... and the first one
            forall|j: int| 0 <= j < best ==> v[j] < v[best as int],
        decreases v.len() - i,
    {
        // strict `>` keeps the earliest maximum (D2)
        if v[i] > v[best] {
            best = i;
        }
        i += 1;
    }
    best
    // </vc-code>
}

// ---------------------------------------------------------------------------
// Spec tests: pin the spec to the intent's examples and properties.
// These are checked by Verus; they never run.
// ---------------------------------------------------------------------------

/// P1: the spec admits at most one answer.
proof fn spec_first_max_is_unique(s: Seq<i64>, i: int, k: int)
    requires
        is_first_max(s, i),
        is_first_max(s, k),
    ensures
        i == k,
{
    if i < k {
        assert(s[i] < s[k]);  // i is before k
    } else if k < i {
        assert(s[k] < s[i]);  // k is before i
    }
}

proof fn spec_examples() {
    // E1
    let e1 = seq![3i64, 7, 2];
    assert(is_first_max(e1, 1));
    assert(!is_first_max(e1, 0)) by { assert(e1[1] > e1[0]); }
    // E2: ties go to the first occurrence
    let e2 = seq![5i64, 1, 5];
    assert(is_first_max(e2, 0));
    assert(!is_first_max(e2, 2)) by { assert(!(e2[0] < e2[2])); }
    // E3
    let e3 = seq![42i64];
    assert(is_first_max(e3, 0));
    // E4: negatives
    let e4 = seq![-4i64, -1i64, -9i64];
    assert(is_first_max(e4, 1));
    assert(!is_first_max(e4, 2)) by { assert(e4[1] > e4[2]); }
}

} // verus!

// Runtime tests (cargo test): the same examples, run on the compiled code.
#[cfg(test)]
mod tests {
    use super::first_max;

    #[test]
    fn examples() {
        assert_eq!(first_max(&[3, 7, 2]), 1);
        assert_eq!(first_max(&[5, 1, 5]), 0);
        assert_eq!(first_max(&[42]), 0);
        assert_eq!(first_max(&[-4, -1, -9]), 1);
    }
}
