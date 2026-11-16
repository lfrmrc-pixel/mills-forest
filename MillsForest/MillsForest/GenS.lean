import MillsForest.Gen

/-!
# The forest for an arbitrary set `S ⊆ ℕ`

Two statements, both for a decidable predicate `S` with `S q → 2 ≤ q`:

* `exists_S_representing_count` (general exponent sequence `C`, roots = elements of `S` in
  `[Y, 2Y]`, lower bound `L 0` for their number given as a hypothesis): the analogue of
  `exists_prime_representing_count`, with `Nat.Prime` replaced by `S`.
* `mills_constS` (ratio `c > 1`, `C k = c^k`): if the integers `n` whose child interval
  `[⌈n^c⌉, ⌈(n+1)^c⌉ - 2]` contains fewer than `ν ℓ(n) / log((n+1)^c)` elements of `S`
  (for some fixed `ν > 0`) have a power-saving count, then there is `B` with
  `⌊B^{c^k}⌋ ∈ S` for every `k`. No lower bound for `S ∩ [Y, 2Y]` is needed: the proof goes
  through `mills_constG`, whose roots are all the integers of `[Y, 2Y]`, and uses `B = A^c`.

The arbitrary `ν > 0` is reduced to the fixed threshold of `badcG S 2 c`
(`ℓ/(5 log²)`): for `n` large, `ℓ/(5 log²) ≤ ν ℓ/log`, so every `badcG S 2 c`-integer
beyond an explicit `n₀` is `ν`-bad, and the finitely many others are absorbed in `K`.
-/

open Finset Real Filter

namespace MillsForest

section GenS

variable (S : ℕ → Prop) [DecidablePred S] (hS2 : ∀ q, S q → 2 ≤ q)

/-- The `S`-forest: roots the elements of `S` in `[Y, 2Y]`, children `kidsG S C`. -/
noncomputable def sForest (C : ℕ → ℝ) (Y : ℕ) : WForest :=
  ⟨(Finset.Icc Y (2 * Y)).filter S, kidsG S C⟩

include hS2

lemma level_rangeS (C : ℕ → ℝ) (hC : ∀ k, 0 < C k) (hC0 : C 0 = 1) (Y : ℕ) :
    ∀ k, ∀ p ∈ (sForest S C Y).level k,
      ((Y : ℝ) ^ C k ≤ p ∧ (p : ℝ) + 1 ≤ ((2 * Y + 1 : ℕ) : ℝ) ^ C k) := by
  intro k
  induction k with
  | zero =>
    intro p hp
    simp only [WForest.level, sForest, Finset.mem_filter, Finset.mem_Icc] at hp
    rw [hC0, Real.rpow_one, Real.rpow_one]
    obtain ⟨⟨h1, h2⟩, -⟩ := hp
    constructor
    · exact_mod_cast h1
    · push_cast; have : (p : ℝ) ≤ 2 * Y := by exact_mod_cast h2
      linarith
  | succ k ih =>
    intro q hq
    simp only [WForest.level, Finset.mem_biUnion] at hq
    obtain ⟨p, hp, hqp⟩ := hq
    obtain ⟨hp1, hp2⟩ := ih p hp
    obtain ⟨-, hq1, hq2⟩ := mem_kidsG S hS2 C hC hqp
    have hr := (ratio_pos C hC k).le
    have hrat : C k * ratio C k = C (k + 1) := by
      unfold ratio; field_simp [(hC k).ne']
    constructor
    · calc (Y : ℝ) ^ C (k + 1) = ((Y : ℝ) ^ C k) ^ ratio C k := by
            rw [← Real.rpow_mul (Nat.cast_nonneg _), hrat]
        _ ≤ (p : ℝ) ^ ratio C k := Real.rpow_le_rpow (by positivity) hp1 hr
        _ ≤ q := hq1
    · calc (q : ℝ) + 1 ≤ ((p : ℝ) + 1) ^ ratio C k := hq2.le
        _ ≤ ((((2 * Y + 1 : ℕ) : ℝ)) ^ C k) ^ ratio C k :=
            Real.rpow_le_rpow (by positivity) hp2 hr
        _ = (((2 * Y + 1 : ℕ) : ℝ)) ^ C (k + 1) := by
            rw [← Real.rpow_mul (Nat.cast_nonneg _), hrat]

lemma level_sub_RkS (C : ℕ → ℝ) (hC : ∀ k, 0 < C k) (hC0 : C 0 = 1) (Y k : ℕ) :
    (sForest S C Y).level k ⊆ Rk C Y k := by
  intro p hp
  obtain ⟨h1, h2⟩ := level_rangeS S hS2 C hC hC0 Y k p hp
  unfold Rk
  rw [Finset.mem_Icc]
  exact ⟨Nat.ceil_le.mpr h1, Nat.le_floor (by linarith)⟩

/-- **Tappa 1: generic forest theorem, count form.** `S` replaces the primes. The roots are
the elements of `S` in `[Y, 2Y]`, whose number is at least `L 0`; the children of `n` at level
`k` are the elements of `S` in `[⌈n^{r_k}⌉, ⌈(n+1)^{r_k}⌉ - 2]`. If the integers of the explicit
range `R_k` with fewer than `ν_k ℓ_k(n)` children have total weight `≤ β k`, and `ν, β, L`
satisfy the recursion, then some `A` has `⌊A^{C_k}⌋ ∈ S` for every `k`. -/
theorem exists_S_representing_count (C : ℕ → ℝ) (hC : ∀ k, 0 < C k)
    (hC1 : ∀ k, 1 ≤ C k) (hCm : ∀ k, C k ≤ C (k + 1)) (hC0 : C 0 = 1)
    (Y : ℕ) (hY : 1 ≤ Y) (ν β L : ℕ → ℝ) (hν : ∀ k, 0 ≤ ν k)
    (hL0 : L 0 ≤ (((Finset.Icc Y (2 * Y)).filter S).card : ℝ))
    (hLpos : ∀ k, 0 < L k) (hβ : ∀ k, β k ≤ L k / 2)
    (hLsucc : ∀ k, L (k + 1) ≤ (ν k * (1 / 3 : ℝ) ^ ratio C k) * (L k / 2))
    (hbadC : ∀ k, ∑ n ∈ (Rk C Y k).filter (fun n : ℕ =>
        decide (ν k * (((n : ℝ) + 1) ^ ratio C k - (n : ℝ) ^ ratio C k) ≤
          ((kidsG S C k n).card : ℝ)) = false), wt C k n ≤ β k) :
    ∃ A : ℝ, ∀ k, S ⌊A ^ C k⌋₊ := by
  set F := sForest S C Y with hF
  let f : ℕ → ℝ := fun k => ν k * (1 / 3 : ℝ) ^ ratio C k
  let good : ℕ → ℕ → Bool := fun k n =>
    decide (f k * wt C k n ≤ ∑ q ∈ kidsG S C k n, wt C (k + 1) q)
  have hw : ∀ k n, 0 ≤ wt C k n := wt_nonneg C hC
  have hf : ∀ k, 0 ≤ f k := fun k => by have := hν k; positivity
  have hdisj : ∀ k, Set.PairwiseDisjoint (↑(F.level k) : Set ℕ) (F.children k) :=
    fun k => kids_disjointG S hS2 C hC k _
  have hgood : ∀ k, ∀ p ∈ F.level k, good k p = true →
      f k * wt C k p ≤ ∑ q ∈ F.children k p, wt C (k + 1) q :=
    fun k p _ h => of_decide_eq_true h
  have hbad : ∀ k, ∑ p ∈ (F.level k).filter (fun p => good k p = false), wt C k p ≤ β k := by
    intro k
    refine le_trans ?_ (hbadC k)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [Finset.mem_filter] at hn ⊢
      have hnR := level_sub_RkS S hS2 C hC hC0 Y k hn.1
      refine ⟨hnR, ?_⟩
      have hn1 : 1 ≤ n := by
        have hmem := hnR
        unfold Rk at hmem
        rw [Finset.mem_Icc] at hmem
        have hpos : 0 < (Y : ℝ) ^ C k := Real.rpow_pos_of_pos (by exact_mod_cast hY) _
        have := Nat.ceil_pos.mpr hpos
        omega
      have hnot : ¬ (f k * wt C k n ≤ ∑ q ∈ kidsG S C k n, wt C (k + 1) q) :=
        decide_eq_false_iff_not.mp hn.2
      apply decide_eq_false_iff_not.mpr
      intro hcon
      exact hnot (kids_shareG S hS2 C hC hC1 hCm k n hn1 (ν k) (hν k) hcon)
    · intro n _ _; exact hw k n
  have hmass0 : F.mass (wt C) 0 = (((Finset.Icc Y (2 * Y)).filter S).card : ℝ) := by
    unfold WForest.mass
    have : ∀ n, wt C 0 n = 1 := by
      intro n; unfold wt; rw [hC0]; simp
    simp only [this, Finset.sum_const, nsmul_eq_mul, mul_one]
    rfl
  have hne := F.levels_nonempty (wt C) good f β L hw hf hdisj hgood hbad
    (by rw [hmass0]; exact hL0) hLpos hβ hLsucc
  obtain ⟨p, hp0, hpath⟩ := F.exists_path hne
  have hchain := fun k => mem_kidsG S hS2 C hC (hpath k)
  obtain ⟨A, hA⟩ := mills_of_chain C hC p (fun k => (hchain k).2.1) (fun k => (hchain k).2.2)
  refine ⟨A, fun k => ?_⟩
  rw [hA k]
  cases k with
  | zero =>
    have : p 0 ∈ (Finset.Icc Y (2 * Y)).filter S := hp0
    exact (Finset.mem_filter.mp this).2
  | succ k => exact (hchain k).1

omit hS2

/-! ### Constant ratio `c`, arbitrary threshold `ν > 0` -/

/-- The elements of `S` in the child interval `[⌈n^c⌉, ⌈(n+1)^c⌉ - 2]`. -/
noncomputable def childS (c : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc ⌈(n : ℝ) ^ c⌉₊ (⌈((n : ℝ) + 1) ^ c⌉₊ - 2)).filter S

/-- `n` is `ν`-bad for `S`: its child interval contains fewer than
`ν ℓ(n) / log((n+1)^c)` elements of `S`, with `ℓ(n) = (n+1)^c - n^c`. -/
def badNu (ν c : ℝ) (n : ℕ) : Prop :=
  ((childS S c n).card : ℝ) <
    ν * (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / Real.log (((n : ℝ) + 1) ^ c)

noncomputable instance badNu_dec (ν c : ℝ) : DecidablePred (badNu S ν c) := fun n => by
  unfold badNu; infer_instance

lemma childS_eq {c : ℝ} (hc : 1 < c) (n : ℕ) : childS S c n = kidsG S (powSeq c) 0 n := by
  unfold childS kidsG; rw [ratio_powSeq hc 0]

/-- Threshold beyond which the `badcG S 2 c` integers are `ν`-bad. -/
noncomputable def nuStart (ν : ℝ) : ℕ := ⌈Real.exp (1 / (5 * ν))⌉₊

lemma badNu_of_badcG {c ν : ℝ} (hc : 1 < c) (hν : 0 < ν) {n : ℕ} (hn : nuStart ν ≤ n)
    (hb : badcG S 2 c n) : badNu S ν c n := by
  have hn0 : 1 ≤ n := le_trans (Nat.one_le_iff_ne_zero.mpr (by
      unfold nuStart; exact (Nat.ceil_pos.mpr (Real.exp_pos _)).ne')) hn
  have hnr : (1 : ℝ) ≤ n := by exact_mod_cast hn0
  have hexp : Real.exp (1 / (5 * ν)) ≤ n := by
    have := Nat.ceil_le.mp hn; exact this
  have hlog1 : 1 / (5 * ν) ≤ Real.log ((n : ℝ) + 1) := by
    rw [Real.le_log_iff_exp_le (by linarith)]; linarith
  set Lg := Real.log (((n : ℝ) + 1) ^ c) with hLg
  have hLgeq : Lg = c * Real.log ((n : ℝ) + 1) := Real.log_rpow (by linarith) c
  have hlogn0 : 0 < Real.log ((n : ℝ) + 1) := Real.log_pos (by linarith)
  have hLpos : 0 < Lg := by rw [hLgeq]; exact mul_pos (by linarith) hlogn0
  have h5 : 1 ≤ 5 * ν * Lg := by
    rw [hLgeq]
    have h1 : 1 ≤ 5 * ν * Real.log ((n : ℝ) + 1) := by
      rw [div_le_iff₀ (by positivity)] at hlog1; linarith
    have h2 : Real.log ((n : ℝ) + 1) ≤ c * Real.log ((n : ℝ) + 1) := by nlinarith
    nlinarith
  set ℓ := ((n : ℝ) + 1) ^ c - (n : ℝ) ^ c with hℓ
  have hℓ0 : 0 ≤ ℓ := by
    have := Real.rpow_le_rpow (by linarith) (by linarith : (n : ℝ) ≤ n + 1)
      (by linarith : (0 : ℝ) ≤ c)
    linarith
  have hcmp : ℓ / (5 * Lg ^ 2) ≤ ν * ℓ / Lg := by
    rw [div_le_div_iff₀ (by positivity) hLpos]
    have : ℓ * Lg * 1 ≤ ℓ * Lg * (5 * ν * Lg) :=
      mul_le_mul_of_nonneg_left h5 (by positivity)
    nlinarith
  unfold badNu
  rw [childS_eq S hc n]
  exact lt_of_lt_of_le hb hcmp

include hS2

/-- **Tappa 2: Mills constants with values in `S`, ratio `c > 1`, threshold `ν > 0`.**
If `#{n ≤ N : n is ν-bad for S} ≤ K N^{1-δ}` for every `N ≥ 1`, then some `B` has
`⌊B^{c^k}⌋ ∈ S` for every `k`. No lower bound for `#(S ∩ [Y, 2Y])` is required. -/
theorem mills_constS {c : ℝ} (hc : 1 < c) (ν : ℝ) (hν : 0 < ν) (δ K : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hK : 0 ≤ K)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badNu S ν c n)).card : ℝ) ≤
        K * (N : ℝ) ^ (1 - δ)) :
    ∃ B : ℝ, ∀ k, S ⌊B ^ c ^ k⌋₊ := by
  set n0 := nuStart ν with hn0
  refine mills_constG S hS2 2 (by norm_num) hc δ (K + n0) hδ hδ1 (by positivity) ?_
  intro N hN
  have hsub : (Finset.range (N + 1)).filter (fun n => badcG S 2 c n) ⊆
      (Finset.range (N + 1)).filter (fun n => badNu S ν c n) ∪ Finset.range n0 := by
    intro n hn
    rw [Finset.mem_filter] at hn
    rw [Finset.mem_union, Finset.mem_filter]
    by_cases h : n < n0
    · exact Or.inr (Finset.mem_range.mpr h)
    · exact Or.inl ⟨hn.1, badNu_of_badcG S hc hν (by omega) hn.2⟩
  have hcard := le_trans (Finset.card_le_card hsub) (Finset.card_union_le _ _)
  rw [Finset.card_range] at hcard
  have hcardR : (((Finset.range (N + 1)).filter (fun n => badcG S 2 c n)).card : ℝ) ≤
      (((Finset.range (N + 1)).filter (fun n => badNu S ν c n)).card : ℝ) + n0 := by
    exact_mod_cast hcard
  have hN1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - δ) :=
    Real.one_le_rpow (by exact_mod_cast hN) (by linarith)
  have hn0r : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
  calc _ ≤ K * (N : ℝ) ^ (1 - δ) + n0 := by linarith [hexc N hN]
    _ ≤ (K + n0) * (N : ℝ) ^ (1 - δ) := by nlinarith

end GenS

end MillsForest
