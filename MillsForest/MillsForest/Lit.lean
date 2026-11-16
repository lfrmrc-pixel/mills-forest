import MillsForest.Psi

/-!
# Transfers (a) and (c): from the literature's exceptional-set measure to `PsiExcHyp`

The hypothesis is stated **as in Gafni–Tao (Definition 1.1) / Bazzanella–Perelli**, with
real `t`, Lebesgue measure, window `y = t^θ` and Chebyshev's `ψ`:

  `E_δ(X, θ) = {t ∈ [X, 2X] : |ψ(t + t^θ) - ψ(t) - t^θ| ≥ δ t^θ}`,
  `LitExcHyp θ ξ K X0 :  vol(E_{1/8}(X, θ)) ≤ K X^ξ   for all X ≥ X0`.

`μ(θ) < 1` gives this for every `ξ ∈ (μ(θ), 1)` and every fixed `δ > 0`, hence for
`δ = 1/8`.

Proved here:
* (c) pointwise: if the integer `x` is `ψ`-exceptional for the window `⌊x^θ⌋`, then every
  real `t ∈ [x-1, x)` lies in `E_{1/8}` (the floor and the shift by one are absorbed);
* (a) measure: the unit intervals `[x-1, x)` are disjoint, so the number of exceptional
  integers up to `Z` is at most `vol(E ∩ [1, Z])`, which is bounded by summing the dyadic
  blocks `[2^j, 2^{j+1}]` as a geometric series.

Result: `LitExcHyp ⇒ PsiExcHyp ⇒ … ⇒ ∃ B, ⌊B^{φ^k}⌋` prime (`mills_goldenRatio_of_litExc`).
-/

open Finset Real Filter ArithmeticFunction MeasureTheory

namespace MillsForest

/-- The literature's exceptional set (for all real `t`), with deviation `δ`. -/
def litExcSet (θ δ : ℝ) : Set ℝ :=
  {t | δ * t ^ θ ≤ |Chebyshev.psi (t + t ^ θ) - Chebyshev.psi t - t ^ θ|}

/-- The literature's hypothesis: `vol(E_{1/8}(X, θ)) ≤ K X^ξ` for `X ≥ X0`. -/
def LitExcHyp (θ ξ K X0 : ℝ) : Prop :=
  ∀ X : ℝ, X0 ≤ X → volume (litExcSet θ (1 / 8) ∩ Set.Icc X (2 * X)) ≤ ENNReal.ofReal (K * X ^ ξ)

lemma psi_nat_mono {a b : ℕ} (h : a ≤ b) :
    Chebyshev.psi (a : ℝ) ≤ Chebyshev.psi (b : ℝ) :=
  Chebyshev.psi_mono (by exact_mod_cast h)

/-- **(c), pointwise.** -/
lemma lit_of_psiExc {θ : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) {x : ℕ} (hx2 : 2 ≤ x)
    (hbig : 10 + 8 * Real.log (2 * (x : ℝ)) ≤ (x : ℝ) ^ θ)
    (hpe : psiExc θ x) {t : ℝ} (ht : t ∈ Set.Ico ((x : ℝ) - 1) x) :
    t ∈ litExcSet θ (1 / 8) := by
  obtain ⟨ht1, ht2⟩ := ht
  set H := Hθ θ x with hHdef
  have hxr : (2 : ℝ) ≤ x := by exact_mod_cast hx2
  have hxpos : (0 : ℝ) < x := by linarith
  have htpos : (1 : ℝ) ≤ t := by linarith
  have hHle : (H : ℝ) ≤ (x : ℝ) ^ θ := Nat.floor_le (by positivity)
  have hHgt : (x : ℝ) ^ θ - 1 < H := Nat.sub_one_lt_floor _
  have hxθle : (x : ℝ) ^ θ ≤ x := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ x) hθ1
    rwa [Real.rpow_one] at this
  set y := t ^ θ with hy
  have hy_le : y ≤ (x : ℝ) ^ θ := Real.rpow_le_rpow (by linarith) ht2.le hθ0.le
  -- y ≥ (x-1)^θ ≥ x^θ - 1
  have hy_ge : (x : ℝ) ^ θ - 1 ≤ y := by
    have hz : (1 : ℝ) ≤ (x : ℝ) - 1 := by linarith
    have hd := diff_le (by linarith : (0 : ℝ) < (x : ℝ) - 1) hθ0.le hθ1
    have hz1 : ((x : ℝ) - 1) ^ (θ - 1) ≤ 1 := Real.rpow_le_one_of_one_le_of_nonpos hz (by linarith)
    have e : (x : ℝ) - 1 + 1 = x := by ring
    rw [e] at hd
    have hmono : ((x : ℝ) - 1) ^ θ ≤ y := Real.rpow_le_rpow (by linarith) ht1 hθ0.le
    nlinarith
  -- ψ(t) = ψ(x - 1)
  have hfl : ⌊t⌋₊ = x - 1 := by
    rw [Nat.floor_eq_iff (by linarith)]
    have : ((x - 1 : ℕ) : ℝ) = (x : ℝ) - 1 := by
      rw [Nat.cast_sub (by omega)]; push_cast; ring
    rw [this]; constructor <;> linarith
  have hpsit : Chebyshev.psi t = Chebyshev.psi ((x - 1 : ℕ) : ℝ) := by
    rw [Chebyshev.psi_eq_psi_coe_floor, hfl]
  -- ψ(t + y) ≤ ψ(x + H)
  have hpsity : Chebyshev.psi (t + y) ≤ Chebyshev.psi ((x + H : ℕ) : ℝ) := by
    rw [Chebyshev.psi_eq_psi_coe_floor]
    apply psi_nat_mono
    have h1 : (⌊t + y⌋₊ : ℝ) ≤ t + y := Nat.floor_le (by positivity)
    have h2 : t + y < (x : ℝ) + H + 1 := by linarith
    have h3 : (⌊t + y⌋₊ : ℝ) < ((x + H + 1 : ℕ) : ℝ) := by push_cast; linarith
    have := (Nat.cast_lt (α := ℝ)).mp h3
    omega
  -- ψ(x + H) - ψ(x - 1) = lamSum x H + Λ(x + H)
  have hsum : Chebyshev.psi ((x + H : ℕ) : ℝ) - Chebyshev.psi ((x - 1 : ℕ) : ℝ) =
      lamSum x H + vonMangoldt (x + H) := by
    have e := lamSum_eq_psi (by omega : 1 ≤ x) (H + 1)
    rw [show x + (H + 1) - 1 = x + H by omega] at e
    rw [← e]
    unfold lamSum
    rw [show x + (H + 1) = (x + H) + 1 by ring, Finset.sum_Ico_succ_top (by omega)]
  have hΛ : (vonMangoldt (x + H) : ℝ) ≤ Real.log (2 * (x : ℝ)) := by
    have hle : ((x + H : ℕ) : ℝ) ≤ 2 * (x : ℝ) := by push_cast; linarith
    have hpos : (0 : ℝ) < ((x + H : ℕ) : ℝ) := by push_cast; positivity
    exact le_trans vonMangoldt_le_log (Real.log_le_log hpos hle)
  have hpe' : lamSum x H < (3 / 4) * (H : ℝ) := hpe
  -- deviation
  have hdev : Chebyshev.psi (t + y) - Chebyshev.psi t - y ≤ -(1 / 8) * y := by
    have hA : Chebyshev.psi (t + y) - Chebyshev.psi t < (3 / 4) * (H : ℝ) + Real.log (2 * (x : ℝ)) := by
      rw [hpsit]; linarith
    nlinarith
  have hy0 : 0 ≤ y := by positivity
  show (1 / 8) * y ≤ |Chebyshev.psi (t + y) - Chebyshev.psi t - y|
  rw [abs_of_nonpos (by linarith)]
  linarith

/-- The side condition of `lit_of_psiExc` holds for all large `x`. -/
lemma lit_side_eventually {θ : ℝ} (hθ0 : 0 < θ) :
    ∃ x1 : ℕ, ∀ x : ℕ, x1 ≤ x → 2 ≤ x ∧ 10 + 8 * Real.log (2 * (x : ℝ)) ≤ (x : ℝ) ^ θ := by
  have hlo := (isLittleO_log_rpow_atTop hθ0).def (by norm_num : (0 : ℝ) < 1 / 32)
  have hev1 : ∀ᶠ y : ℝ in atTop, Real.log y ≤ 1 / 32 * y ^ θ := by
    filter_upwards [hlo, eventually_gt_atTop (1 : ℝ)] with y hy hy1
    rwa [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hy1.le),
      abs_of_nonneg (by positivity)] at hy
  have hev2 : ∀ᶠ y : ℝ in atTop, 40 ≤ y ^ θ :=
    (tendsto_rpow_atTop hθ0).eventually (eventually_ge_atTop _)
  have hev := hev1.and (hev2.and (eventually_ge_atTop (2 : ℝ)))
  obtain ⟨x1, hx1⟩ := Filter.eventually_atTop.mp (tendsto_natCast_atTop_atTop.eventually hev)
  refine ⟨x1, fun x hx => ?_⟩
  obtain ⟨h1, h2, h3⟩ := hx1 x hx
  refine ⟨by exact_mod_cast h3, ?_⟩
  have hxpos : (0 : ℝ) < x := by linarith
  have hl2 : Real.log (2 * (x : ℝ)) = Real.log 2 + Real.log x := Real.log_mul (by norm_num) hxpos.ne'
  have hlog2 : Real.log 2 < 1 := by
    have := Real.log_two_lt_d9; linarith
  rw [hl2]
  linarith

/-- **(a) + (c)**: the literature's measure hypothesis implies `PsiExcHyp`. -/
theorem psiExc_of_litExc {θ ξ K X0 : ℝ} (hθ0 : 0 < θ) (hθ1 : θ ≤ 1) (hξ0 : 0 < ξ)
    (hK : 0 ≤ K) (hX0 : 0 ≤ X0) (h : LitExcHyp θ ξ K X0) :
    ∃ K1 : ℝ, 0 ≤ K1 ∧ PsiExcHyp θ ξ K1 := by
  obtain ⟨x1, hx1⟩ := lit_side_eventually hθ0
  set E := litExcSet θ (1 / 8) with hE
  set r := (2 : ℝ) ^ ξ with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) hξ0
  set C := (K + X0) * r / (r - 1) with hC
  have hC0 : 0 ≤ C := by
    have : 0 < r - 1 := by linarith
    positivity
  refine ⟨x1 + C, by positivity, fun Z hZ => ?_⟩
  have hZr : (1 : ℝ) ≤ Z := by exact_mod_cast hZ
  have hZξ : (1 : ℝ) ≤ (Z : ℝ) ^ ξ := Real.one_le_rpow hZr hξ0.le
  set S := (Finset.Icc 1 Z).filter (psiExc θ) with hS
  set S' := S.filter (fun x => x1 ≤ x) with hS'
  -- card S ≤ x1 + card S'
  have hsplit : S.card ≤ x1 + S'.card := by
    have : S ⊆ Finset.range x1 ∪ S' := by
      intro x hx
      rw [Finset.mem_union, Finset.mem_range, hS', Finset.mem_filter]
      by_cases hlt : x < x1
      · exact Or.inl hlt
      · exact Or.inr ⟨hx, by omega⟩
    have h2 := le_trans (Finset.card_le_card this) (Finset.card_union_le _ _)
    rwa [Finset.card_range] at h2
  -- the unit intervals of S' lie in E ∩ [1, Z]
  have hcover : (⋃ x ∈ S', Set.Ico ((x : ℝ) - 1) x) ⊆ E ∩ Set.Icc 1 Z := by
    intro t ht
    simp only [Set.mem_iUnion] at ht
    obtain ⟨x, hx, htx⟩ := ht
    rw [hS', hS, Finset.mem_filter, Finset.mem_filter, Finset.mem_Icc] at hx
    obtain ⟨⟨⟨hx1', hxZ⟩, hpe⟩, hx1x⟩ := hx
    obtain ⟨h2, hbig⟩ := hx1 x hx1x
    refine ⟨lit_of_psiExc hθ0 hθ1 h2 hbig hpe htx, ?_, ?_⟩
    · have : (2 : ℝ) ≤ x := by exact_mod_cast h2
      linarith [htx.1]
    · have : (x : ℝ) ≤ Z := by exact_mod_cast hxZ
      linarith [htx.2]
  have hdisj : Set.PairwiseDisjoint (↑S') (fun x : ℕ => Set.Ico ((x : ℝ) - 1) x) := by
    intro a _ b _ hab
    rw [Function.onFun, Set.disjoint_left]
    intro t hta htb
    obtain ⟨ha1, ha2⟩ := hta
    obtain ⟨hb1, hb2⟩ := htb
    rcases lt_or_gt_of_ne hab with hlt | hgt
    · have : (a : ℝ) + 1 ≤ b := by exact_mod_cast hlt
      linarith
    · have : (b : ℝ) + 1 ≤ a := by exact_mod_cast hgt
      linarith
  have hvolS' : volume (⋃ x ∈ S', Set.Ico ((x : ℝ) - 1) x) = (S'.card : ENNReal) := by
    rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_Ico)]
    simp only [Real.volume_Ico, sub_sub_cancel, ENNReal.ofReal_one, Finset.sum_const,
      nsmul_eq_mul, mul_one]
  -- dyadic cover of [1, Z]
  set J := Nat.log 2 Z with hJ
  have hdy : E ∩ Set.Icc 1 (Z : ℝ) ⊆
      ⋃ j ∈ Finset.range (J + 1), E ∩ Set.Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j) := by
    intro t ht
    obtain ⟨htE, ht1, htZ⟩ := ht
    simp only [Set.mem_iUnion, Finset.mem_range]
    set n := ⌊t⌋₊ with hn
    have hn1 : 1 ≤ n := Nat.le_floor (by exact_mod_cast ht1)
    have hnZ : n ≤ Z := Nat.floor_le_of_le htZ
    refine ⟨Nat.log 2 n, Nat.lt_succ_of_le (Nat.log_mono_right hnZ), htE, ?_, ?_⟩
    · have h1 : 2 ^ Nat.log 2 n ≤ n := Nat.pow_log_le_self 2 (by omega)
      have h2 : ((2 ^ Nat.log 2 n : ℕ) : ℝ) ≤ n := by exact_mod_cast h1
      have h3 : (n : ℝ) ≤ t := Nat.floor_le (by linarith)
      push_cast at h2
      linarith
    · have h1 : n < 2 ^ (Nat.log 2 n + 1) := Nat.lt_pow_succ_log_self (by norm_num) n
      have h2 : n + 1 ≤ 2 ^ (Nat.log 2 n + 1) := h1
      have h3 : ((n + 1 : ℕ) : ℝ) ≤ ((2 ^ (Nat.log 2 n + 1) : ℕ) : ℝ) := by exact_mod_cast h2
      have h4 : t < (n : ℝ) + 1 := Nat.lt_floor_add_one t
      push_cast at h3
      rw [pow_succ] at h3
      linarith
  -- each block: vol ≤ (K + X0) (2^j)^ξ
  have hblock : ∀ j : ℕ, volume (E ∩ Set.Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j)) ≤
      ENNReal.ofReal ((K + X0) * r ^ j) := by
    intro j
    have hpow : ((2 : ℝ) ^ j) ^ ξ = r ^ j := by
      rw [hr, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
        ← Real.rpow_mul (by norm_num), mul_comm]
    have hXj1 : (1 : ℝ) ≤ (2 : ℝ) ^ j := one_le_pow₀ (by norm_num)
    have hrj : (1 : ℝ) ≤ r ^ j := one_le_pow₀ hr1.le
    by_cases hX : X0 ≤ (2 : ℝ) ^ j
    · calc volume (E ∩ Set.Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j))
          ≤ ENNReal.ofReal (K * ((2 : ℝ) ^ j) ^ ξ) := h _ hX
        _ ≤ ENNReal.ofReal ((K + X0) * r ^ j) := by
            apply ENNReal.ofReal_le_ofReal
            rw [hpow]
            nlinarith
    · push_neg at hX
      calc volume (E ∩ Set.Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j))
          ≤ volume (Set.Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j)) := measure_mono Set.inter_subset_right
        _ = ENNReal.ofReal ((2 : ℝ) ^ j) := by rw [Real.volume_Icc]; congr 1; ring
        _ ≤ ENNReal.ofReal ((K + X0) * r ^ j) := by
            apply ENNReal.ofReal_le_ofReal
            nlinarith
  -- geometric sum
  have hgeom : ∑ j ∈ Finset.range (J + 1), (K + X0) * r ^ j ≤ C * (Z : ℝ) ^ ξ := by
    rw [← Finset.mul_sum, geom_sum_eq hr1.ne' (J + 1)]
    have hrJ : r ^ J ≤ (Z : ℝ) ^ ξ := by
      have h1 : 2 ^ J ≤ Z := Nat.pow_log_le_self 2 (by omega)
      have h2 : ((2 : ℝ) ^ J) ≤ Z := by exact_mod_cast h1
      have e : r ^ J = ((2 : ℝ) ^ J) ^ ξ := by
        rw [hr, ← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
          ← Real.rpow_mul (by norm_num), mul_comm]
      rw [e]
      exact Real.rpow_le_rpow (by positivity) h2 hξ0.le
    have hr0 : 0 < r - 1 := by linarith
    have key : (r ^ (J + 1) - 1) / (r - 1) ≤ r * (Z : ℝ) ^ ξ / (r - 1) := by
      apply div_le_div_of_nonneg_right _ hr0.le
      rw [pow_succ]
      have : 0 ≤ r ^ J := by positivity
      nlinarith
    calc (K + X0) * ((r ^ (J + 1) - 1) / (r - 1))
        ≤ (K + X0) * (r * (Z : ℝ) ^ ξ / (r - 1)) := mul_le_mul_of_nonneg_left key (by positivity)
      _ = C * (Z : ℝ) ^ ξ := by rw [hC]; ring
  -- assemble in ENNReal
  have hmain : (S'.card : ENNReal) ≤ ENNReal.ofReal (C * (Z : ℝ) ^ ξ) := by
    calc (S'.card : ENNReal) = volume (⋃ x ∈ S', Set.Ico ((x : ℝ) - 1) x) := hvolS'.symm
      _ ≤ volume (E ∩ Set.Icc 1 (Z : ℝ)) := measure_mono hcover
      _ ≤ volume (⋃ j ∈ Finset.range (J + 1),
            E ∩ Set.Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j)) := measure_mono hdy
      _ ≤ ∑ j ∈ Finset.range (J + 1),
            volume (E ∩ Set.Icc ((2 : ℝ) ^ j) (2 * (2 : ℝ) ^ j)) := measure_biUnion_finset_le _ _
      _ ≤ ∑ j ∈ Finset.range (J + 1), ENNReal.ofReal ((K + X0) * r ^ j) :=
          Finset.sum_le_sum (fun j _ => hblock j)
      _ = ENNReal.ofReal (∑ j ∈ Finset.range (J + 1), (K + X0) * r ^ j) := by
          rw [ENNReal.ofReal_sum_of_nonneg]
          intro j _; positivity
      _ ≤ ENNReal.ofReal (C * (Z : ℝ) ^ ξ) := ENNReal.ofReal_le_ofReal hgeom
  have hS'R : (S'.card : ℝ) ≤ C * (Z : ℝ) ^ ξ := by
    rw [← ENNReal.ofReal_natCast] at hmain
    exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmain
  have hSR : (S.card : ℝ) ≤ x1 + S'.card := by exact_mod_cast hsplit
  have hx1r : (0 : ℝ) ≤ x1 := Nat.cast_nonneg _
  show (S.card : ℝ) ≤ (x1 + C) * (Z : ℝ) ^ ξ
  nlinarith

open Real in
/-- **Golden ratio from the literature's hypothesis.** If, for some `θ` with
`φ θ < φ - 1` (that is `θ < 1/φ²`), the exceptional set `E_{1/8}(X, θ)` has measure
`≤ K X^ξ` with `0 < ξ < 1` for all large `X`, then there is `B` with `⌊B^{φ^k}⌋` prime
for every `k`. For `1/3 < θ < 1/φ²` this follows from `μ(θ) < 1` (Ingham–Huxley via
Gafni–Tao, or Bazzanella–Perelli). -/
theorem mills_goldenRatio_of_litExc (θ ξ K X0 : ℝ) (hθ0 : 0 < θ)
    (hθ : goldenRatio * θ < goldenRatio - 1) (hξ0 : 0 < ξ) (hξ1 : ξ < 1) (hK : 0 ≤ K)
    (hX0 : 0 ≤ X0) (h : LitExcHyp θ ξ K X0) :
    ∃ B : ℝ, ∀ k, (⌊B ^ goldenRatio ^ k⌋₊).Prime := by
  have hφ1 := one_lt_goldenRatio
  have hθ1 : θ ≤ 1 := by nlinarith [goldenRatio_lt_two]
  obtain ⟨K1, hK1, hP⟩ := psiExc_of_litExc hθ0 hθ1 hξ0 hK hX0 h
  exact mills_goldenRatio_of_psiExc θ ξ K1 hθ0 hθ hξ0.le hξ1 hK1 hP

/-- **Any ratio `c > 1` from the literature's hypothesis**, provided `c θ < c - 1`,
`c θ < 1` and `θ ≤ 1/2`. With Ingham–Huxley this covers every `c > 3/2`
(take `1/3 < θ < 1 - 1/c`). -/
theorem mills_const_of_litExc {c θ ξ K X0 : ℝ} (hc : 1 < c) (hθ0 : 0 < θ)
    (hθ1 : c * θ < c - 1) (hθ2 : c * θ < 1) (hθh : θ ≤ 1 / 2) (hξ0 : 0 < ξ) (hξ1 : ξ < 1)
    (hK : 0 ≤ K) (hX0 : 0 ≤ X0) (h : LitExcHyp θ ξ K X0) :
    ∃ B : ℝ, ∀ k, (⌊B ^ c ^ k⌋₊).Prime := by
  obtain ⟨K1, hK1, hP⟩ := psiExc_of_litExc hθ0 (by linarith) hξ0 hK hX0 h
  obtain ⟨K2, hK2, hD⟩ := discreteExc_of_psiExc hθ0 hθh hξ0.le hK1 hP
  obtain ⟨δ, K', hδ0, hδ1, hK', hexc⟩ := hexc_of_discreteExc hc hθ0 hθ1 hθ2 hξ0.le hξ1 hK2 hD
  exact mills_const hc δ K' hδ0 hδ1 hK' hexc

end MillsForest
