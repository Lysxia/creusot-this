use creusot_std::prelude::*;
#[cfg(creusot)]
use creusot_std::logic::Mapping;

// Minimal version of `mex0` for which we can prove safety (here: no out of bounds accesses).
// The trivial `invariant(true)` enables a Creusot-specific desugaring of the for loop
// which is sufficient to expose the fact that `i` is in the range `0..n`.
#[ensures(true)]
pub fn mex0_safety(a: &[usize]) -> usize {
    let n = a.len();
    #[variant(n@ - produced.len())]
    'outer: for v in 0..n {
        #[variant(n@ - produced.len())]
        #[invariant(true)]
        for i in 0..n {
            if a[i] == v {
                continue 'outer
            }
        }
        return v
    }
    n
}

#[ensures(!a@.contains(result))]
#[ensures(forall<x> 0usize <= x && x < result ==> a@.contains(x))]
pub fn mex0(a: &[usize]) -> usize {
    let n = a.len();
    let mut _idx = snapshot! { |i: Int| i };
    #[invariant(forall<x> 0 <= x && x < produced.len() ==> 0 <= _idx[x] && _idx[x] < n@ && a@[_idx[x]]@ == x)]
    'outer: for v in 0..n {
        #[invariant(!a@[..produced.len()].contains(v))]
        for i in 0..n {
            if a[i] == v {
                _idx = snapshot! { _idx.set(v@, i@) };
                continue 'outer
            }
        }
        proof_assert! { a@ == a@[..n@] };
        proof_assert! { forall<x> 0usize <= x && x < v ==> a@[_idx[x@]] == x };
        return v
    }
    let _ = snapshot! { mex0_lemma };
    n
}

#[logic]
#[requires(forall<x> 0 <= x && x < a.len() ==> 0 <= idx[x] && idx[x] < a.len() && a[idx[x]]@ == x)]
#[requires(0 <= i && i < a.len() && a[i]@ == a.len())]
#[ensures(false)]
fn mex0_lemma(idx: Mapping<Int, Int>, a: Seq<usize>, i: Int) {
    pigeonhole(a.len() + 1, a.len(), idx.set(a.len(), i))
}

// Pigeonhole principle as a logic function.
#[logic]
#[requires(0 <= m && m < n)]
#[requires(forall<i> 0 <= i && i < n ==> 0 <= f[i] && f[i] < m)]
#[ensures(exists<i1, i2> 0 <= i1 && i1 < i2 && i2 < n && f[i1] == f[i2])]
fn pigeonhole(n: Int, m: Int, f: Mapping<Int, Int>) {
    let _ = use_pigeonhole_builtin;
}

// Depend on this to import the pigeonhole principle from Why3
// Not actually callable!
#[logic]
#[builtin("pigeon.Pigeonhole.pigeonhole")]
fn use_pigeonhole_builtin() {
}
