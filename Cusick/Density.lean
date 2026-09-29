import Cusick.BinaryStrings

namespace Cusick

/-- Number of n ∈ {0,..,N-1} with s2(n) ≤ s2(n + t). -/
def favorable_count (t N : ℕ) : ℕ :=
  ((Finset.range N).filter (fun n => s2 n ≤ s2 (n + t))).card

/-- s2(2^k) = 1. -/
theorem s2_two_pow (k : ℕ) : s2 (2^k) = 1 := by
  induction k with
  | zero => exact s2_one
  | succ k ih =>
    rw [pow_succ, mul_comm, s2_even _ (pow_ne_zero k (by norm_num))]
    exact ih

/-- All n < 2^(k+1) are favorable for t = 2^k. -/
theorem s2_add_pow2_ge (k : ℕ) : ∀ n : ℕ, n < 2^(k+1) → s2 n ≤ s2 (n + 2^k) := by
  induction k with
  | zero =>
    intro n hn; interval_cases n <;> simp [s2_zero, s2_one, s2_two]
  | succ k ih =>
    intro n hn
    have hpow : 2^(k + 1 + 1) = 2 * 2^(k + 1) := by ring
    have hpow2 : 2^(k+1) = 2 * 2^k := by ring
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · -- n = m + m
      have hm_lt : m < 2^(k+1) := by
        rw [hm, hpow] at hn; omega
      rcases Nat.eq_zero_or_pos m with rfl | hm_pos
      · -- n = 0
        simp [hm, s2_zero]
      · -- m > 0: rewrite via s2_even
        have hn2 : m + m + 2^(k+1) = 2 * (m + 2^k) := by linarith [hpow2]
        rw [hm, hn2, show m + m = 2 * m from by ring,
            s2_even _ (by omega), s2_even _ (by omega)]
        exact ih m hm_lt
    · -- n = 2*m + 1: rewrite via s2_odd
      have hm_lt : m < 2^(k+1) := by
        rw [hm, hpow] at hn; omega
      have heq : 2 * m + 1 + 2^(k+1) = 2 * (m + 2^k) + 1 := by linarith [hpow2]
      rw [hm, heq, s2_odd, s2_odd]
      exact Nat.succ_le_succ (ih m hm_lt)

/-- favorable_count(2^k, 2^(k+1)) = 2^(k+1): all elements are favorable. -/
theorem favorable_pow2 (k : ℕ) : favorable_count (2^k) (2^(k+1)) = 2^(k+1) := by
  unfold favorable_count
  have hall : (Finset.range (2^(k+1))).filter (fun n => s2 n ≤ s2 (n + 2^k)) =
              Finset.range (2^(k+1)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range]
    exact ⟨And.left, fun hn => ⟨hn, s2_add_pow2_ge k n hn⟩⟩
  rw [hall, Finset.card_range]

end Cusick
