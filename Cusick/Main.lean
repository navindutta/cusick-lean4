import Cusick.Density

namespace Cusick

/-!
## Component 4: Cusick Conjecture for t = 2^k

Key result: favorable_count(2^k, 2^(k+2)) = 3 * 2^k  (density = 3/4 > 1/2).
Period structure: [0, 2^(k+1)) is 100% favorable; [2^(k+1), 2^(k+2)) is exactly 50%.
-/

/-- No-carry addition: n < 2^k → s2(2^k + n) = 1 + s2 n. -/
theorem s2_add_pow2_lt (k : ℕ) : ∀ n : ℕ, n < 2^k → s2 (2^k + n) = 1 + s2 n := by
  induction k with
  | zero => intro n hn; simp at hn; simp [hn, s2_zero, s2_one]
  | succ k ih =>
    intro n hn
    have hpow : 2^(k+1) = 2 * 2^k := by ring
    rcases Nat.even_or_odd n with ⟨m, hm⟩ | ⟨m, hm⟩
    · rcases Nat.eq_zero_or_pos m with rfl | hm_pos
      · simp only [hm, Nat.zero_add, Nat.add_zero, s2_zero]; exact s2_two_pow (k+1)
      · have hm_lt : m < 2^k := by rw [hm, hpow] at hn; omega
        have hne : 2^k + m ≠ 0 := by have := Nat.two_pow_pos k; omega
        rw [hm, show 2^(k+1) + (m+m) = 2*(2^k+m) from by linarith [hpow],
            show m+m = 2*m from by ring,
            s2_even _ hne, s2_even _ (by omega)]
        exact ih m hm_lt
    · have hm_lt : m < 2^k := by rw [hm, hpow] at hn; omega
      rw [hm, show 2^(k+1) + (2*m+1) = 2*(2^k+m)+1 from by linarith [hpow],
          s2_odd, ih m hm_lt, s2_odd]; ring

/-- First half of second period is favorable: m < 2^k → s2(2^(k+1)+m) ≤ s2(2^(k+1)+m+2^k). -/
theorem s2_favorable_first_half (k m : ℕ) (hm : m < 2^k) :
    s2 (2^(k+1) + m) ≤ s2 (2^(k+1) + m + 2^k) := by
  have h1 : s2 (2^(k+1) + m) = 1 + s2 m :=
    s2_add_pow2_lt (k+1) m (by linarith [show 2^(k+1)=2*2^k from by ring])
  have h2 : s2 (2^(k+1) + m + 2^k) = 1 + s2 (2^k + m) := by
    rw [show 2^(k+1) + m + 2^k = 2^(k+1) + (2^k + m) from by ring]
    apply s2_add_pow2_lt
    linarith [show 2^(k+1) = 2 * 2^k from by ring]
  linarith [s2_add_pow2_lt k m hm]

/-- Second half is unfavorable: m < 2^k → s2(2^(k+1)+2^k+m+2^k) < s2(2^(k+1)+2^k+m). -/
theorem s2_unfavorable_second_half (k m : ℕ) (hm : m < 2^k) :
    s2 (2^(k+1) + 2^k + m + 2^k) < s2 (2^(k+1) + 2^k + m) := by
  have h1 : s2 (2^(k+1) + 2^k + m) = 2 + s2 m := by
    have step1 : s2 (2^(k+1) + (2^k + m)) = 1 + s2 (2^k + m) :=
      s2_add_pow2_lt (k+1) (2^k+m) (by linarith [show 2^(k+1)=2*2^k from by ring])
    have step2 : s2 (2^k + m) = 1 + s2 m := s2_add_pow2_lt k m hm
    rw [show 2^(k+1) + 2^k + m = 2^(k+1) + (2^k + m) from by ring, step1, step2]; ring
  have h2 : s2 (2^(k+1) + 2^k + m + 2^k) = 1 + s2 m := by
    rw [show 2^(k+1) + 2^k + m + 2^k = 2^(k+2) + m from by ring]
    exact s2_add_pow2_lt (k+2) m (by linarith [show 2^(k+2)=4*2^k from by ring])
  omega

/-- The favorable set in [2^(k+1), 2^(k+2)) = [2^(k+1), 2^(k+1)+2^k). -/
theorem favorable_second_period_eq (k : ℕ) :
    (Finset.Ico (2^(k+1)) (2^(k+2))).filter (fun n => s2 n ≤ s2 (n + 2^k)) =
    Finset.Ico (2^(k+1)) (2^(k+1) + 2^k) := by
  ext n
  simp only [Finset.mem_filter, Finset.mem_Ico]
  constructor
  · intro ⟨⟨hlo, hhi⟩, hfav⟩
    refine ⟨hlo, ?_⟩
    by_contra hge; push_neg at hge
    -- n ≥ 2^(k+1) + 2^k, write n = 2^(k+1) + 2^k + r
    have hge' : 2^(k+1) + 2^k ≤ n := by omega
    have hr : n - 2^(k+1) - 2^k < 2^k := by
      have h2 : 2^(k+2) = 4 * 2^k := by ring
      have h1 : 2^(k+1) = 2 * 2^k := by ring
      omega
    have hn_eq : n = 2^(k+1) + 2^k + (n - 2^(k+1) - 2^k) := by omega
    have hbad := s2_unfavorable_second_half k (n - 2^(k+1) - 2^k) hr
    rw [← hn_eq] at hbad; omega
  · intro ⟨hlo, hhi⟩
    refine ⟨⟨hlo, by linarith [show 2^(k+2)=2*2^(k+1) from by ring, show 2^(k+1)=2*2^k from by ring]⟩, ?_⟩
    rw [show n = 2^(k+1) + (n - 2^(k+1)) from by omega]
    exact s2_favorable_first_half k _ (by omega)

/-- Exactly 2^k elements of [2^(k+1), 2^(k+2)) are favorable. -/
theorem favorable_second_period (k : ℕ) :
    ((Finset.Ico (2^(k+1)) (2^(k+2))).filter (fun n => s2 n ≤ s2 (n + 2^k))).card = 2^k := by
  rw [favorable_second_period_eq, Nat.card_Ico]
  have : 2^(k+1) = 2 * 2^k := by ring
  omega

/-- favorable_count(2^k, 2^(k+2)) = 3 * 2^k. -/
theorem cusick_pow2_exact (k : ℕ) :
    favorable_count (2^k) (2^(k+2)) = 3 * 2^k := by
  unfold favorable_count
  have hset : (Finset.range (2^(k+2))).filter (fun n => s2 n ≤ s2 (n + 2^k)) =
              Finset.range (2^(k+1)) ∪
              (Finset.Ico (2^(k+1)) (2^(k+2))).filter (fun n => s2 n ≤ s2 (n + 2^k)) := by
    ext n
    simp only [Finset.mem_filter, Finset.mem_range, Finset.mem_union, Finset.mem_Ico]
    constructor
    · intro ⟨hn, hfav⟩
      rcases lt_or_ge n (2^(k+1)) with h | h
      · exact Or.inl h
      · exact Or.inr ⟨⟨h, hn⟩, hfav⟩
    · rintro (h | ⟨⟨_, hn⟩, hfav⟩)
      · exact ⟨by linarith [show 2^(k+2)=2*2^(k+1) from by ring], s2_add_pow2_ge k n h⟩
      · exact ⟨hn, hfav⟩
  have hdisj : Disjoint (Finset.range (2^(k+1)))
      ((Finset.Ico (2^(k+1)) (2^(k+2))).filter (fun n => s2 n ≤ s2 (n + 2^k))) := by
    apply Finset.disjoint_left.mpr
    intro n hn1 hn2
    simp only [Finset.mem_range] at hn1
    simp only [Finset.mem_filter, Finset.mem_Ico] at hn2
    omega
  rw [hset, Finset.card_union_of_disjoint hdisj, Finset.card_range, favorable_second_period]
  linarith [show 2^(k+1) = 2 * 2^k from by ring]

/-- Cusick's conjecture for t = 2^k: density strictly exceeds 1/2. -/
theorem cusick_conjecture_pow2 (k : ℕ) :
    2 * favorable_count (2^k) (2^(k+2)) > 2^(k+2) := by
  rw [cusick_pow2_exact]
  linarith [Nat.two_pow_pos k, show 2^(k+2) = 4 * 2^k from by ring]

end Cusick
