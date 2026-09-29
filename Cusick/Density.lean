/-!
# Density cₜ and the Main Theorem

**Status: Work in progress.**

This file will formalize:

1. **The density** `cₜ := lim_{N→∞} (1/N) · #{0 ≤ n < N : s₂(n+t) ≥ s₂(n)}`
   as a `Filter.Tendsto` statement in Mathlib.
2. **Existence of the limit** — follows from the stopped-walk analysis in `BinaryStrings`.
3. **The main theorem** (Cheng 2026, Theorem 1):
   `∀ t : ℕ, t ≥ 1 → (1:ℝ)/2 + 2^(-(2 * s2 t + 1) : ℤ) ≤ c t`

## References

* K. Cheng, arXiv:2606.23398, §§5–6.
-/

import Cusick.BinaryStrings
import Mathlib.Topology.Algebra.Order.LiminfLimsup

namespace Cusick

-- TODO: define the counting function
-- def favorableCount (t N : ℕ) : ℕ :=
--   (Finset.range N).card (fun n => s2 n ≤ s2 (n + t))

-- TODO: define cₜ as the Cesàro limit
-- noncomputable def c (t : ℕ) : ℝ :=
--   Filter.limsup (fun N => (favorableCount t N : ℝ) / N) Filter.atTop

-- TODO: main theorem
-- theorem cusick_main (t : ℕ) (ht : 1 ≤ t) :
--   (1:ℝ)/2 + (2:ℝ)^(-(2 * (s2 t : ℤ) + 1)) ≤ c t := by ...

end Cusick
