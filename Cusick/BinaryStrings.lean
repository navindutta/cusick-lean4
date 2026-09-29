import Mathlib.Tactic
import Mathlib.Data.Nat.Digits
import Mathlib.Data.List.Basic
import Cusick.SumOfDigits

/-!
# Binary Carry Decomposition

This file proves the carry decomposition of binary digit sums, the arithmetic
core of Cheng's 2026 proof of Cusick's conjecture (arXiv:2606.23398).

## Main results

* `s2_add_le`    — subadditivity: `s2(n+t) ≤ s2(n) + s2(t)`
* `carries`      — carry count: `s2(n) + s2(t) - s2(n+t)` (always a natural number)
* `kummer_binary`— **Kummer's identity**: `s2(n) + s2(t) = s2(n+t) + carries(n,t)`
* `s2_add_ge_iff`— **Core equivalence**: `s2(n+t) ≥ s2(n) ↔ carries(n,t) ≤ s2(t)`

## The key equivalence

From Kummer: `s2(n+t) = s2(n) + s2(t) - carries(n,t)`.
So `s2(n+t) ≥ s2(n) ↔ s2(t) ≥ carries(n,t)`.

This rewrites the "favorable" event for Cusick's conjecture into a bound
on carry count, which Cheng then analyzes as a stopped random walk.
-/

namespace Cusick

/-! ### Subadditivity -/

/-- **Subadditivity**: `s2(n+t) ≤ s2(n) + s2(t)`.

    Proved by strong induction on n with 4-way even/odd case split.
    In each case we reduce to `s2` of half-sized arguments and apply the IH.

    The 4 cases (n even/odd × t even/odd) each factor via `s2_odd`/`s2_even`. -/
theorem s2_add_le : ∀ (n t : ℕ), s2 (n + t) ≤ s2 n + s2 t := by
  intro n
  induction n using Nat.strong_induction_on with
  | h n ih =>
    intro t
    rcases Nat.eq_zero_or_pos n with rfl | hn
    · simp [s2_zero]
    rcases Nat.even_or_odd n with ⟨a, ha⟩ | ⟨a, ha⟩
    · -- n = a + a (even), a = n/2 < n
      have ha_lt : a < n  := by omega
      have ha_ne : a ≠ 0  := by omega
      rcases Nat.even_or_odd t with ⟨b, hb⟩ | ⟨b, hb⟩
      · -- t = b+b (even): n+t = 2(a+b)
        --   s2(n) = s2(a), s2(t) = s2(b) [b>0], s2(n+t) = s2(a+b)
        have key : s2 (a + b) ≤ s2 a + s2 b := ih a ha_lt b
        rw [ha, hb, show a+a+(b+b) = 2*(a+b) from by ring,
            show a+a = 2*a from by ring, show b+b = 2*b from by ring,
            s2_even _ ha_ne]
        rcases Nat.eq_zero_or_pos b with rfl | hb_pos
        · simp [s2_zero, s2_even _ ha_ne]
        · rw [s2_even _ (by omega), s2_even _ (by omega)]; exact key
      · -- t = 2b+1 (odd): n+t = 2(a+b)+1
        --   s2(n) = s2(a), s2(t) = s2(b)+1, s2(n+t) = s2(a+b)+1
        have key : s2 (a + b) ≤ s2 a + s2 b := ih a ha_lt b
        rw [ha, hb, show a+a+(2*b+1) = 2*(a+b)+1 from by ring,
            show a+a = 2*a from by ring,
            s2_even _ ha_ne, s2_odd, s2_odd]
        linarith
    · -- n = 2a+1 (odd)
      rcases Nat.even_or_odd t with ⟨b, hb⟩ | ⟨b, hb⟩
      · -- t = b+b (even): n+t = 2(a+b)+1
        --   s2(n) = s2(a)+1, s2(t) = s2(b) [b>0], s2(n+t) = s2(a+b)+1
        have key : s2 (a + b) ≤ s2 a + s2 b := ih a (by omega) b
        rw [ha, hb, show 2*a+1+(b+b) = 2*(a+b)+1 from by ring,
            show b+b = 2*b from by ring, s2_odd, s2_odd]
        rcases Nat.eq_zero_or_pos b with rfl | hb_pos
        · simp [s2_zero]   -- goal: s2 a + 1 ≤ s2 a + 1 + 0, trivial
        · rw [s2_even _ (by omega)]; linarith
      · -- both odd: n=2a+1, t=2b+1, n+t=2(a+b+1)
        --   s2(n) = s2(a)+1, s2(t) = s2(b)+1, s2(n+t) = s2(a+b+1) ≤ s2(a+b)+1
        have key : s2 (a + b) ≤ s2 a + s2 b := ih a (by omega) b
        rw [ha, hb, show 2*a+1+(2*b+1) = 2*(a+b+1) from by ring,
            s2_even _ (by omega), s2_odd, s2_odd]
        linarith [s2_succ_le (a + b)]

/-! ### Kummer's identity -/

/-- **Carry count**: `carries(n,t) = s2(n) + s2(t) - s2(n+t)`.

    This equals the total number of carry bits generated when adding n and t
    in binary (including carry propagation). Well-defined as a natural number
    by `s2_add_le`. Note: `carries(n,t)` can exceed `s2(t)` (e.g., n=7, t=1
    gives carries=3 > s2(1)=1), so the favorable condition is an inequality,
    not always satisfied. -/
def carries (n t : ℕ) : ℕ := s2 n + s2 t - s2 (n + t)

/-- **Kummer's identity**: `s2(n) + s2(t) = s2(n+t) + carries(n,t)`.

    Immediate from subadditivity and the definition of carries. -/
theorem kummer_binary (n t : ℕ) : s2 n + s2 t = s2 (n + t) + carries n t := by
  have hle := s2_add_le n t
  simp [carries]; omega

/-! ### Core equivalence for Cusick -/

/-- **Key rewrite**: `s2(n+t) ≥ s2(n) ↔ carries(n,t) ≤ s2(t)`.

    The event `{n : s2(n+t) ≥ s2(n)}` (whose density is `cₜ`) is exactly
    the event `{n : carries(n,t) ≤ s2(t)}`. Cheng shows this occurs for
    strictly more than half of all n by a stopped-walk argument. -/
theorem s2_add_ge_iff (n t : ℕ) : s2 n ≤ s2 (n + t) ↔ carries n t ≤ s2 t := by
  have hle := s2_add_le n t
  simp [carries]; omega

end Cusick
