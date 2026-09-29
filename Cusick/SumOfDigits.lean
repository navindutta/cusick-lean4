import Mathlib.Tactic
import Mathlib.Data.Nat.Digits
import Mathlib.Data.List.Basic

/-!
# Binary Sum of Digits — Foundational Lemmas

This file formalizes basic arithmetic properties of the binary digit sum function
`s₂ : ℕ → ℕ` (Hamming weight / popcount): the number of `1`-bits in the binary
representation of a natural number.

These lemmas form the arithmetic foundation for Cheng's 2026 proof of Cusick's conjecture.

## Main definition

* `Cusick.s2 n` — the binary digit sum of `n`, i.e. `(Nat.digits 2 n).sum`

## Main results

* `s2_zero`    — `s2 0 = 0`
* `s2_one`     — `s2 1 = 1`
* `s2_two`     — `s2 2 = 1`
* `s2_odd`     — `s2 (2n+1) = s2 n + 1`  (appending a 1-bit)
* `s2_even`    — `s2 (2n)   = s2 n`       (appending a 0-bit, n nonzero)
* `s2_succ_le` — `forall n, s2 (n+1) <= s2 n + 1`  (1-Lipschitz under increment)

## Status

- [x] s2 arithmetic (this file) -- 6 theorems, sorry-free, Lean4 EXIT 0
- [ ] Carry decomposition and subsequence ideals (Cusick.BinaryStrings)
- [ ] Density c_t and main theorem (Cusick.Density)

## References

* K. Cheng, "Proof of Cusick's Binary Digit Sum Conjecture," arXiv:2606.23398 (June 2026).
* T. W. Cusick, original conjecture (2011).
-/

namespace Cusick

/-- The binary digit sum (Hamming weight / popcount) of a natural number.
    Counts the number of `1`-bits in the base-2 representation of `n`.
    Uses `Nat.digits 2 n` (least-significant bit first) from Mathlib. -/
def s2 (n : ℕ) : ℕ := (Nat.digits 2 n).sum

@[simp]
theorem s2_zero : s2 0 = 0 := by
  simp [s2, Nat.digits_zero]

theorem s2_one : s2 1 = 1 := by native_decide

theorem s2_two : s2 2 = 1 := by native_decide

/-- Appending a 1-bit: the binary expansion of `2n+1` is the expansion of `n`
    with a 1 prepended (at the low end), so the digit sum increases by exactly 1. -/
theorem s2_odd (n : ℕ) : s2 (2 * n + 1) = s2 n + 1 := by
  have h1 : (2 * n + 1) % 2 = 1 := by omega
  have h2 : (2 * n + 1) / 2 = n := by omega
  simp only [s2, Nat.digits_def' (by norm_num : 1 < 2) (by omega : 0 < 2 * n + 1),
             h1, h2, List.sum_cons]
  ring

/-- Appending a 0-bit: the binary expansion of `2n` (for `n ≠ 0`) is the expansion of `n`
    with a 0 prepended, so the digit sum is unchanged. -/
theorem s2_even (n : ℕ) (hn : n ≠ 0) : s2 (2 * n) = s2 n := by
  have hpos : 0 < 2 * n   := by omega
  have h1 : (2 * n) % 2 = 0 := by omega
  have h2 : (2 * n) / 2 = n := by omega
  simp only [s2, Nat.digits_def' (by norm_num : 1 < 2) hpos, h1, h2, List.sum_cons]
  simp

/-- Incrementing `n` by 1 increases its binary digit sum by at most 1.

    This captures carry propagation: adding 1 resets all trailing 1-bits to 0
    and sets the next 0-bit to 1, which can only reduce the digit sum relative
    to the single new 1-bit added.

    Proved by strong induction with even/odd case split:
    - Even case (n = 2m): n+1 = 2m+1, s2(n+1) = s2(m)+1 = s2(n)+1.
    - Odd case  (n = 2m+1): n+1 = 2(m+1), s2(n+1) = s2(m+1).
      By strong IH at m: s2(m+1) ≤ s2(m)+1 = s2(n). -/
theorem s2_succ_le (n : ℕ) : s2 (n + 1) ≤ s2 n + 1 := by
  induction n using Nat.strong_induction_on with
  | h n ih =>
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · rw [hm]
      rcases Nat.eq_zero_or_pos m with rfl | hm0
      · norm_num [s2_zero, s2_one]
      · rw [show m + m + 1 = 2 * m + 1 from by ring, s2_odd,
            show m + m = 2 * m from by ring, s2_even m (Nat.pos_iff_ne_zero.mp hm0)]
    · rw [hm, show 2 * m + 1 + 1 = 2 * (m + 1) from by ring,
          s2_even _ (by omega), s2_odd]
      linarith [ih m (by omega)]

end Cusick
