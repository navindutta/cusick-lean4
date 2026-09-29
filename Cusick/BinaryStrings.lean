/-!
# Binary Strings, Subsequence Ideals, and Carry Decomposition

**Status: Work in progress.**

This file will formalize:

1. **Binary strings as natural numbers** — the bijection ℕ ↔ {0,1}*
2. **Principal subsequence ideal** of a string `t`: the set of binary strings that can be
   obtained from `t` by deleting some bits — a deletion-closed language.
3. **Carry decomposition** (Cheng §3): the identity
   `s2(n + t) - s2(n) - s2(t) = -2 · carries(n, t)`
   where `carries(n,t)` is the number of carry bits when adding `n` and `t` in binary.
4. The rewriting of `#{n < N : s2(n+t) ≥ s2(n)}` as a stopped random walk on the
   principal ideal of `t`.

## References

* K. Cheng, arXiv:2606.23398, §§2–4.
-/

import Cusick.SumOfDigits

namespace Cusick

-- TODO: formalize carry count
-- def carries (n t : ℕ) : ℕ := ...

-- TODO: Kummer's theorem in binary
-- theorem kummer_binary (n t : ℕ) :
--   s2 n + s2 t = s2 (n + t) + 2 * carries n t := by ...

-- TODO: principal subsequence ideal
-- def SubseqIdeal (t : ℕ) : Finset ℕ := ...

end Cusick
