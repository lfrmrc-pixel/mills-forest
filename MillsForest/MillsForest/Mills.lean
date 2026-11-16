import Mathlib

/-!
# Mills' construction for a general exponent sequence

If `p (k+1) ∈ [p k ^ (C(k+1)/C k), (p k + 1) ^ (C(k+1)/C k) - 1)` for every `k`, then there
is a real `A` with `⌊A ^ C k⌋ = p k` for every `k`.
-/

namespace MillsForest

/-- Lower endpoint `p_k^{1/C_k}`. -/
noncomputable def lo (C : ℕ → ℝ) (p : ℕ → ℕ) (k : ℕ) : ℝ := (p k : ℝ) ^ (1 / C k)

/-- Upper endpoint `(p_k+1)^{1/C_k}`. -/
noncomputable def hi (C : ℕ → ℝ) (p : ℕ → ℕ) (k : ℕ) : ℝ := ((p k : ℝ) + 1) ^ (1 / C k)

theorem mills_of_chain (C : ℕ → ℝ) (hC : ∀ k, 0 < C k) (p : ℕ → ℕ)
    (hlow : ∀ k, (p k : ℝ) ^ (C (k + 1) / C k) ≤ p (k + 1))
    (hup : ∀ k, (p (k + 1) : ℝ) + 1 < ((p k : ℝ) + 1) ^ (C (k + 1) / C k)) :
    ∃ A : ℝ, ∀ k, ⌊A ^ C k⌋₊ = p k := by
  have key : ∀ k (x : ℝ), 0 ≤ x →
      (x ^ (C (k + 1) / C k)) ^ (1 / C (k + 1)) = x ^ (1 / C k) := by
    intro k x hx
    rw [← Real.rpow_mul hx]
    congr 1
    have h1 := (hC k).ne'
    have h2 := (hC (k + 1)).ne'
    field_simp
  have ha : ∀ k, lo C p k ≤ lo C p (k + 1) := by
    intro k
    have hpos : 0 < 1 / C (k + 1) := by have := hC (k + 1); positivity
    have h1 : ((p k : ℝ) ^ (C (k + 1) / C k)) ^ (1 / C (k + 1)) ≤
        (p (k + 1) : ℝ) ^ (1 / C (k + 1)) :=
      Real.rpow_le_rpow (Real.rpow_nonneg (Nat.cast_nonneg _) _) (hlow k) hpos.le
    rw [key k _ (Nat.cast_nonneg _)] at h1
    exact h1
  have hb : ∀ k, hi C p (k + 1) < hi C p k := by
    intro k
    have hpos : 0 < 1 / C (k + 1) := by have := hC (k + 1); positivity
    have h1 : ((p (k + 1) : ℝ) + 1) ^ (1 / C (k + 1)) <
        (((p k : ℝ) + 1) ^ (C (k + 1) / C k)) ^ (1 / C (k + 1)) :=
      Real.rpow_lt_rpow (by positivity) (hup k) hpos
    rw [key k _ (by positivity)] at h1
    exact h1
  have hab : ∀ k, lo C p k < hi C p k := by
    intro k
    have hpos : 0 < 1 / C k := by have := hC k; positivity
    exact Real.rpow_lt_rpow (Nat.cast_nonneg _) (by linarith) hpos
  have amono : Monotone (lo C p) := monotone_nat_of_le_succ ha
  have banti : StrictAnti (hi C p) := strictAnti_nat_of_succ_lt hb
  have hbound : ∀ i j, lo C p i ≤ hi C p j := by
    intro i j
    calc lo C p i ≤ lo C p (max i j) := amono (le_max_left _ _)
      _ ≤ hi C p (max i j) := (hab _).le
      _ ≤ hi C p j := banti.antitone (le_max_right _ _)
  have bdd : BddAbove (Set.range (lo C p)) := ⟨hi C p 0, by
    rintro _ ⟨i, rfl⟩
    exact hbound i 0⟩
  refine ⟨⨆ k, lo C p k, fun k => ?_⟩
  have hA1 : lo C p k ≤ ⨆ k, lo C p k := le_ciSup bdd k
  have hA2 : (⨆ k, lo C p k) < hi C p k :=
    lt_of_le_of_lt (ciSup_le fun i => hbound i (k + 1)) (hb k)
  have hA0 : 0 ≤ lo C p k := Real.rpow_nonneg (Nat.cast_nonneg _) _
  have hCk := hC k
  have e1 : lo C p k ^ C k = p k := by
    unfold lo
    rw [← Real.rpow_mul (Nat.cast_nonneg _), one_div, inv_mul_cancel₀ hCk.ne', Real.rpow_one]
  have e2 : hi C p k ^ C k = (p k : ℝ) + 1 := by
    unfold hi
    rw [← Real.rpow_mul (by positivity), one_div, inv_mul_cancel₀ hCk.ne', Real.rpow_one]
  have l1 : (p k : ℝ) ≤ (⨆ k, lo C p k) ^ C k := by
    rw [← e1]; exact Real.rpow_le_rpow hA0 hA1 hCk.le
  have l2 : (⨆ k, lo C p k) ^ C k < (p k : ℝ) + 1 := by
    rw [← e2]; exact Real.rpow_lt_rpow (hA0.trans hA1) hA2 hCk
  rw [Nat.floor_eq_iff (Real.rpow_nonneg (hA0.trans hA1) _)]
  exact ⟨l1, l2⟩

end MillsForest
