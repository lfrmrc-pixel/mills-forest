import MillsForest.GenS

/-!
# The threshold of the method: a `(log log)²` saving suffices

`mills_constS` asks for a power saving `#{n ≤ N : n ν-bad} ≤ K N^{1-δ}`. Here the hypothesis is
weakened to a quasi-polylogarithmic saving on dyadic windows:

  `#{n ∈ [N, 2N] : n ν-bad} ≤ K · N · exp(-C (log log N)²)`   for `N ≥ N₀`,

with `C > 1/(2 log c)` (`mills_constS_loglog`). The cumulative form
`#{n ≤ N : n ν-bad} ≤ K · N · exp(-C (log log N)²)` implies the window form with `2K`
(`mills_constS_loglog_cum`).

Differences from the power-saving chain (`Gen.lean`):
* no reduction to `badcG S 2 c` (log-power `m = 2` would give the threshold `1/log c` only):
  the forest is run with `ν_k = ν / (c^{k+1} log(2Y+2))`, whose bad integers are directly
  `badNu S ν c`;
* the bad weight on level `k` is bounded by dyadic blocks `[u 2^i, u 2^{i+1}]`,
  `u = ⌈Y^{c^k}⌉`, keeping the factor `1/c^k` of the weight; total `β_k = 3K(2Y+1) η(Y^{c^k})`;
* `β_k ≤ L_k/2` is proved by induction: the step is linear in `k` after taking logs, with
  coefficients `log c (2C log c - 1) > 0` and `2C log c - 1 > 0`.
-/

open Finset Real Filter

namespace MillsForest

/-- `η_C(x) = exp(-C (log log x)²)`. -/
noncomputable def etaLL (Cη x : ℝ) : ℝ := Real.exp (-(Cη * Real.log (Real.log x) ^ 2))

lemma etaLL_pos (Cη x : ℝ) : 0 < etaLL Cη x := Real.exp_pos _

lemma one_le_log_of_three_le {x : ℝ} (hx : 3 ≤ x) : 1 ≤ Real.log x := by
  rw [Real.le_log_iff_exp_le (by linarith)]
  have := Real.exp_one_lt_d9
  linarith

lemma etaLL_anti {Cη : ℝ} (hC : 0 ≤ Cη) {x y : ℝ} (hx : 3 ≤ x) (hxy : x ≤ y) :
    etaLL Cη y ≤ etaLL Cη x := by
  unfold etaLL
  apply Real.exp_le_exp.mpr
  have hlx : 1 ≤ Real.log x := one_le_log_of_three_le hx
  have h1 : Real.log x ≤ Real.log y := Real.log_le_log (by linarith) hxy
  have h2 : 0 ≤ Real.log (Real.log x) := Real.log_nonneg hlx
  have h3 : Real.log (Real.log x) ≤ Real.log (Real.log y) := Real.log_le_log (by linarith) h1
  have h4 : Real.log (Real.log x) ^ 2 ≤ Real.log (Real.log y) ^ 2 := pow_le_pow_left₀ h2 h3 2
  nlinarith

section Threshold

variable {c : ℝ}

/-- `ν_k = ν / (c^{k+1} log(2Y+2))`. -/
noncomputable def nuSeqT (c ν : ℝ) (Y k : ℕ) : ℝ := ν / (c ^ (k + 1) * Real.log (2 * (Y : ℝ) + 2))

/-- `L_0 = Y+1`, `L_{k+1} = ν_k 3^{-c} L_k / 2`. -/
noncomputable def LSeqT (c ν : ℝ) (Y : ℕ) : ℕ → ℝ
  | 0 => (Y : ℝ) + 1
  | k + 1 => nuSeqT c ν Y k * (1 / 3 : ℝ) ^ c * (LSeqT c ν Y k / 2)

/-- `β_k = 3 K (2Y+1) η(Y^{c^k})`. -/
noncomputable def betaT (c Cη K : ℝ) (Y k : ℕ) : ℝ :=
  3 * K * (2 * (Y : ℝ) + 1) * etaLL Cη ((Y : ℝ) ^ powSeq c k)

/-- The constant of the step inequality. -/
noncomputable def DT (c ν Cη : ℝ) : ℝ :=
  Real.log c + 2 * Real.log 2 + c * Real.log 3 - Real.log ν - Cη * Real.log c ^ 2

lemma nuSeqT_pos (hc : 1 < c) {ν : ℝ} (hν : 0 < ν) (Y k : ℕ) : 0 < nuSeqT c ν Y k := by
  unfold nuSeqT
  have := log_pos_Y Y
  have : 0 < c ^ (k + 1) := pow_pos (by linarith) _
  positivity

lemma LSeqT_pos (hc : 1 < c) {ν : ℝ} (hν : 0 < ν) (Y k : ℕ) : 0 < LSeqT c ν Y k := by
  induction k with
  | zero => show (0 : ℝ) < (Y : ℝ) + 1; positivity
  | succ k ih =>
    show 0 < nuSeqT c ν Y k * (1 / 3 : ℝ) ^ c * (LSeqT c ν Y k / 2)
    have := nuSeqT_pos hc hν Y k
    positivity

/-- The step: `η(Y^{c^{k+1}}) ≤ η(Y^{c^k}) · ν_k 3^{-c} / 2`, once `log log Y` is large. -/
lemma eta_stepT (hc : 1 < c) {ν Cη : ℝ} (hν : 0 < ν) (hCη : 1 / (2 * Real.log c) < Cη)
    {Y : ℕ} (hY3 : (3 : ℝ) ≤ Y)
    (hv : DT c ν Cη ≤ (2 * Cη * Real.log c - 1) * Real.log (Real.log Y)) (k : ℕ) :
    etaLL Cη ((Y : ℝ) ^ powSeq c (k + 1)) ≤
      etaLL Cη ((Y : ℝ) ^ powSeq c k) * (nuSeqT c ν Y k * (1 / 3 : ℝ) ^ c / 2) := by
  have hℓ0 : 0 < Real.log c := Real.log_pos hc
  have h2C : 1 < 2 * Cη * Real.log c := by
    rw [div_lt_iff₀ (by positivity)] at hCη; linarith
  have hYp : (0 : ℝ) < Y := by linarith
  have hlY : 1 ≤ Real.log Y := one_le_log_of_three_le hY3
  have hc0 : (0 : ℝ) < c := by linarith
  have hlogk : ∀ j : ℕ, Real.log (Real.log ((Y : ℝ) ^ powSeq c j)) =
      (j : ℝ) * Real.log c + Real.log (Real.log Y) := by
    intro j
    rw [Real.log_rpow hYp, powSeq, Real.log_mul (pow_ne_zero _ hc0.ne') (by linarith),
      Real.log_pow]
  have ha0 : 0 < Real.log (2 * (Y : ℝ) + 2) := log_pos_Y Y
  have hloga : Real.log (Real.log (2 * (Y : ℝ) + 2)) ≤ Real.log 2 + Real.log (Real.log Y) := by
    have h1 : Real.log (2 * (Y : ℝ) + 2) ≤ 2 * Real.log Y := by
      have e : 2 * Real.log (Y : ℝ) = Real.log ((Y : ℝ) ^ 2) := by
        rw [Real.log_pow]; push_cast; ring
      rw [e]
      exact Real.log_le_log (by positivity) (by nlinarith)
    calc Real.log (Real.log (2 * (Y : ℝ) + 2)) ≤ Real.log (2 * Real.log Y) :=
          Real.log_le_log ha0 h1
      _ = Real.log 2 + Real.log (Real.log Y) := Real.log_mul (by norm_num) (by linarith)
  have hck : 0 < c ^ (k + 1) := pow_pos hc0 _
  have hf : 0 < nuSeqT c ν Y k * (1 / 3 : ℝ) ^ c / 2 := by
    have := nuSeqT_pos hc hν Y k
    positivity
  have hlogf : Real.log (nuSeqT c ν Y k * (1 / 3 : ℝ) ^ c / 2) =
      Real.log ν - c * Real.log 3 - Real.log 2 - ((k : ℝ) + 1) * Real.log c -
        Real.log (Real.log (2 * (Y : ℝ) + 2)) := by
    unfold nuSeqT
    have h3 : (0 : ℝ) < (1 / 3 : ℝ) ^ c := by positivity
    rw [Real.log_div (by positivity) two_ne_zero, Real.log_mul (by positivity) h3.ne',
      Real.log_div hν.ne' (by positivity), Real.log_mul hck.ne' ha0.ne', Real.log_pow,
      Real.log_rpow (by norm_num), one_div, Real.log_inv]
    push_cast
    ring
  unfold etaLL
  rw [← Real.exp_log hf, ← Real.exp_add, Real.exp_le_exp, hlogf, hlogk, hlogk]
  push_cast
  have hk : 0 ≤ (k : ℝ) * Real.log c * (2 * Cη * Real.log c - 1) :=
    mul_nonneg (mul_nonneg (Nat.cast_nonneg k) hℓ0.le) (by linarith)
  unfold DT at hv
  nlinarith [hk, hv, hloga]

lemma beta_leT (hc : 1 < c) {ν Cη K : ℝ} (hν : 0 < ν) (hCη : 1 / (2 * Real.log c) < Cη)
    (hK : 0 ≤ K) {Y : ℕ} (hY3 : (3 : ℝ) ≤ Y)
    (hv : DT c ν Cη ≤ (2 * Cη * Real.log c - 1) * Real.log (Real.log Y))
    (h0 : 12 * K * etaLL Cη Y ≤ 1) :
    ∀ k, betaT c Cη K Y k ≤ LSeqT c ν Y k / 2 := by
  intro k
  induction k with
  | zero =>
    unfold betaT
    rw [powSeq_zero, Real.rpow_one]
    show 3 * K * (2 * (Y : ℝ) + 1) * etaLL Cη Y ≤ ((Y : ℝ) + 1) / 2
    have he := etaLL_pos Cη (Y : ℝ)
    have hKe : 0 ≤ K * etaLL Cη Y := mul_nonneg hK he.le
    have hY0 : (0 : ℝ) ≤ Y := by linarith
    nlinarith [mul_le_mul_of_nonneg_left h0 (by linarith : (0 : ℝ) ≤ (Y : ℝ) + 1)]
  | succ k ih =>
    have hstep := eta_stepT hc hν hCη hY3 hv k
    have hf : 0 ≤ nuSeqT c ν Y k * (1 / 3 : ℝ) ^ c / 2 := by
      have := nuSeqT_pos hc hν Y k
      positivity
    have hA : 0 ≤ 3 * K * (2 * (Y : ℝ) + 1) := by
      have : (0 : ℝ) ≤ Y := by linarith
      positivity
    show 3 * K * (2 * (Y : ℝ) + 1) * etaLL Cη ((Y : ℝ) ^ powSeq c (k + 1)) ≤
      nuSeqT c ν Y k * (1 / 3 : ℝ) ^ c * (LSeqT c ν Y k / 2) / 2
    calc 3 * K * (2 * (Y : ℝ) + 1) * etaLL Cη ((Y : ℝ) ^ powSeq c (k + 1))
        ≤ 3 * K * (2 * (Y : ℝ) + 1) *
            (etaLL Cη ((Y : ℝ) ^ powSeq c k) * (nuSeqT c ν Y k * (1 / 3 : ℝ) ^ c / 2)) :=
          mul_le_mul_of_nonneg_left hstep hA
      _ = betaT c Cη K Y k * (nuSeqT c ν Y k * (1 / 3 : ℝ) ^ c / 2) := by unfold betaT; ring
      _ ≤ (LSeqT c ν Y k / 2) * (nuSeqT c ν Y k * (1 / 3 : ℝ) ^ c / 2) :=
          mul_le_mul_of_nonneg_right ih hf
      _ = nuSeqT c ν Y k * (1 / 3 : ℝ) ^ c * (LSeqT c ν Y k / 2) / 2 := by ring

variable (S : ℕ → Prop) [DecidablePred S]

/-- An integer of `R_k` with fewer than `ν_k ℓ(n)` children is `ν`-bad. -/
lemma badNu_of_badT (hc : 1 < c) {ν : ℝ} (hν : 0 < ν) {Y : ℕ} (hY : 1 ≤ Y) (k n : ℕ)
    (hn : n ∈ Rk (powSeq c) Y k)
    (hbad : ¬ (nuSeqT c ν Y k * (((n : ℝ) + 1) ^ ratio (powSeq c) k -
        (n : ℝ) ^ ratio (powSeq c) k) ≤ ((kidsG S (powSeq c) k n).card : ℝ))) :
    badNu S ν c n := by
  have hC := powSeq_pos hc k
  have hC1 := powSeq_one_le hc k
  have hYr : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  have e : kidsG S (powSeq c) k n = childS S c n := by
    unfold kidsG childS; rw [ratio_powSeq hc k]
  rw [not_le, ratio_powSeq hc k, e] at hbad
  unfold Rk at hn
  rw [Finset.mem_Icc] at hn
  have hlo : (Y : ℝ) ^ powSeq c k ≤ n := Nat.ceil_le.mp hn.1
  have hhi : (n : ℝ) ≤ ((2 * Y + 1 : ℕ) : ℝ) ^ powSeq c k :=
    le_trans (by exact_mod_cast hn.2) (Nat.floor_le (by positivity))
  set C := powSeq c k with hCdef
  set a := Real.log (2 * (Y : ℝ) + 2) with ha
  have ha0 : 0 < a := log_pos_Y Y
  have hn1 : (1 : ℝ) ≤ n := le_trans (Real.one_le_rpow hYr hC.le) hlo
  have hℓ : 0 ≤ ((n : ℝ) + 1) ^ c - (n : ℝ) ^ c := by
    have := Real.rpow_le_rpow (by linarith) (by linarith : (n : ℝ) ≤ n + 1)
      (by linarith : (0 : ℝ) ≤ c)
    linarith
  have hn2 : (n : ℝ) + 1 ≤ (2 * (Y : ℝ) + 2) ^ C := by
    have hd := diff_ge_conv (by positivity : (0 : ℝ) < 2 * Y + 1) hC1
    have hone : 1 ≤ C * (2 * (Y : ℝ) + 1) ^ (C - 1) := by
      have : 1 ≤ (2 * (Y : ℝ) + 1) ^ (C - 1) := Real.one_le_rpow (by linarith) (by linarith)
      nlinarith
    have e2 : (2 * (Y : ℝ) + 1) + 1 = 2 * Y + 2 := by ring
    rw [e2] at hd
    have : ((2 * Y + 1 : ℕ) : ℝ) = 2 * (Y : ℝ) + 1 := by push_cast; ring
    rw [this] at hhi
    linarith
  have hlogn : Real.log (((n : ℝ) + 1) ^ c) ≤ c ^ (k + 1) * a := by
    rw [Real.log_rpow (by linarith)]
    have h1 : Real.log ((n : ℝ) + 1) ≤ C * a := by
      rw [ha, ← Real.log_rpow (by positivity)]
      exact Real.log_le_log (by linarith) hn2
    have : c ^ (k + 1) = C * c := by rw [hCdef]; exact powSeq_succ k
    rw [this]
    nlinarith
  have hlogpos : 0 < Real.log (((n : ℝ) + 1) ^ c) := by
    apply Real.log_pos
    exact Real.one_lt_rpow (by linarith) (by linarith)
  unfold badNu
  calc ((childS S c n).card : ℝ) < nuSeqT c ν Y k * (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) := hbad
    _ = ν * (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / (c ^ (k + 1) * a) := by
        unfold nuSeqT; rw [← ha]; ring
    _ ≤ ν * (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / Real.log (((n : ℝ) + 1) ^ c) :=
        div_le_div_of_nonneg_left (mul_nonneg hν.le hℓ) hlogpos hlogn

/-- **Bad weight by dyadic blocks.** -/
lemma bad_weightT (hc : 1 < c) {ν : ℝ} (hν : 0 < ν) {Cη K : ℝ} (hCη : 0 ≤ Cη) (hK : 0 ≤ K)
    {N₀ : ℕ}
    (hexc : ∀ N : ℕ, N₀ ≤ N →
      (((Finset.Icc N (2 * N)).filter (fun n => badNu S ν c n)).card : ℝ) ≤
        K * N * etaLL Cη N)
    {Y : ℕ} (hY3 : (3 : ℝ) ≤ Y) (hYN : N₀ ≤ Y) (k : ℕ) :
    ∑ n ∈ (Rk (powSeq c) Y k).filter (fun n : ℕ =>
        decide (nuSeqT c ν Y k * (((n : ℝ) + 1) ^ ratio (powSeq c) k -
          (n : ℝ) ^ ratio (powSeq c) k) ≤ ((kidsG S (powSeq c) k n).card : ℝ)) = false),
      wt (powSeq c) k n ≤ betaT c Cη K Y k := by
  classical
  have hY1 : 1 ≤ Y := by
    have : (1 : ℝ) ≤ Y := by linarith
    exact_mod_cast this
  have hYr : (1 : ℝ) ≤ Y := by linarith
  have hYp : (0 : ℝ) < Y := by linarith
  have hC := powSeq_pos hc k
  have hC1 := powSeq_one_le hc k
  set T := (Rk (powSeq c) Y k).filter (fun n : ℕ =>
        decide (nuSeqT c ν Y k * (((n : ℝ) + 1) ^ ratio (powSeq c) k -
          (n : ℝ) ^ ratio (powSeq c) k) ≤ ((kidsG S (powSeq c) k n).card : ℝ)) = false) with hT
  have hmem : ∀ n ∈ T, ⌈(Y : ℝ) ^ powSeq c k⌉₊ ≤ n ∧
      (n : ℝ) ≤ ((2 * Y + 1 : ℕ) : ℝ) ^ powSeq c k ∧ badNu S ν c n := by
    intro n hn
    rw [hT, Finset.mem_filter] at hn
    have h := hn.1
    have hb := badNu_of_badT S hc hν hY1 k n hn.1 (decide_eq_false_iff_not.mp hn.2)
    unfold Rk at h
    rw [Finset.mem_Icc] at h
    exact ⟨h.1, le_trans (by exact_mod_cast h.2) (Nat.floor_le (by positivity)), hb⟩
  set C := powSeq c k with hCdef
  set x0 := (Y : ℝ) ^ C with hx0
  have hx0Y : (Y : ℝ) ≤ x0 := by
    calc (Y : ℝ) = (Y : ℝ) ^ (1 : ℝ) := (Real.rpow_one _).symm
      _ ≤ x0 := Real.rpow_le_rpow_of_exponent_le hYr hC1
  have hx03 : 3 ≤ x0 := le_trans hY3 hx0Y
  have hx0p : 0 < x0 := by linarith
  set u := ⌈x0⌉₊ with hu
  have hux : x0 ≤ u := Nat.le_ceil _
  have hu1 : 1 ≤ u := by
    have : (1 : ℝ) ≤ u := by linarith
    exact_mod_cast this
  have huN : N₀ ≤ u := by
    have h1 : (N₀ : ℝ) ≤ Y := by exact_mod_cast hYN
    have : (N₀ : ℝ) ≤ u := by linarith
    exact_mod_cast this
  set Mb := ⌈2 * C⌉₊ with hMb
  set g : ℕ → ℕ := fun n => Nat.log 2 (n / u) with hg
  -- the dyadic block of `n`
  have hblock : ∀ n ∈ T, u * 2 ^ g n ≤ n ∧ n ≤ 2 * (u * 2 ^ g n) ∧ g n < Mb := by
    intro n hn
    obtain ⟨hun, hnX, -⟩ := hmem n hn
    have hq1 : 1 ≤ n / u := (Nat.one_le_div_iff (by omega)).mpr hun
    have hq : n / u ≠ 0 := by omega
    have h1 : 2 ^ g n ≤ n / u := Nat.pow_log_le_self 2 hq
    have h2 : n / u < 2 ^ (g n + 1) := Nat.lt_pow_succ_log_self (by norm_num) _
    have h3 : u * (n / u) ≤ n := Nat.mul_div_le n u
    have h4 : n < u * (n / u + 1) := by
      have e1 := Nat.div_add_mod n u
      have e2 := Nat.mod_lt n (by omega : u > 0)
      nlinarith
    have hlow : u * 2 ^ g n ≤ n := le_trans (Nat.mul_le_mul_left u h1) h3
    refine ⟨hlow, ?_, ?_⟩
    · have h5 : u * (n / u + 1) ≤ u * 2 ^ (g n + 1) := Nat.mul_le_mul_left u h2
      rw [pow_succ] at h5
      nlinarith
    · rw [hMb, Nat.lt_ceil]
      have hlowr : (u : ℝ) * (2 : ℝ) ^ g n ≤ n := by exact_mod_cast hlow
      have hXY : ((2 * Y + 1 : ℕ) : ℝ) ^ C ≤ (3 : ℝ) ^ C * x0 := by
        rw [hx0, ← Real.mul_rpow (by norm_num) hYp.le]
        apply Real.rpow_le_rpow (by positivity) _ hC.le
        push_cast; linarith
      have h3C : (3 : ℝ) ^ C < (4 : ℝ) ^ C := Real.rpow_lt_rpow (by norm_num) (by norm_num) hC
      have h42 : (4 : ℝ) ^ C = (2 : ℝ) ^ (2 * C) := by
        rw [Real.rpow_mul (by norm_num)]; norm_num
      have hupos : (0 : ℝ) < u := by linarith
      have h2le : (2 : ℝ) ^ g n ≤ (3 : ℝ) ^ C := by
        have : (u : ℝ) * (2 : ℝ) ^ g n ≤ (u : ℝ) * (3 : ℝ) ^ C := by
          have h3p : 0 ≤ (3 : ℝ) ^ C := by positivity
          calc (u : ℝ) * (2 : ℝ) ^ g n ≤ n := hlowr
            _ ≤ (3 : ℝ) ^ C * x0 := le_trans hnX hXY
            _ ≤ (3 : ℝ) ^ C * u := mul_le_mul_of_nonneg_left hux h3p
            _ = (u : ℝ) * (3 : ℝ) ^ C := by ring
        exact le_of_mul_le_mul_left this hupos
      have hlt : (2 : ℝ) ^ ((g n : ℕ) : ℝ) < (2 : ℝ) ^ (2 * C) := by
        rw [Real.rpow_natCast]; linarith
      exact (Real.rpow_lt_rpow_left_iff (by norm_num)).mp hlt
  have hmaps : ∀ n ∈ T, g n ∈ Finset.range Mb :=
    fun n hn => Finset.mem_range.mpr (hblock n hn).2.2
  rw [← Finset.sum_fiberwise_of_maps_to hmaps]
  set X := K * (2 * (Y : ℝ) + 1) * etaLL Cη x0 with hX
  have hX0 : 0 ≤ X := by
    have := etaLL_pos Cη x0
    have : (0 : ℝ) ≤ Y := by linarith
    positivity
  have hfib : ∀ i ∈ Finset.range Mb,
      ∑ n ∈ T with g n = i, wt (powSeq c) k n ≤ X / C := by
    intro i _
    set N := u * 2 ^ i with hN
    have hNu : u ≤ N := Nat.le_mul_of_pos_right u (by positivity)
    have hN0 : N₀ ≤ N := le_trans huN hNu
    have hNr : x0 ≤ (N : ℝ) := le_trans hux (by exact_mod_cast hNu)
    have hNp : (0 : ℝ) < N := by linarith
    have hsub : (T.filter (fun n => g n = i)) ⊆
        (Finset.Icc N (2 * N)).filter (fun n => badNu S ν c n) := by
      intro n hn
      rw [Finset.mem_filter] at hn
      obtain ⟨hnT, hgi⟩ := hn
      obtain ⟨b1, b2, -⟩ := hblock n hnT
      rw [hgi] at b1 b2
      rw [Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨b1, b2⟩, (hmem n hnT).2.2⟩
    have hcard : (((T.filter (fun n => g n = i))).card : ℝ) ≤ K * N * etaLL Cη N :=
      le_trans (by exact_mod_cast Finset.card_le_card hsub) (hexc N hN0)
    have hwt : ∀ n ∈ T.filter (fun n => g n = i),
        wt (powSeq c) k n ≤ (2 * (Y : ℝ) + 1) / (C * N) := by
      intro n hn
      have hn' := hn
      rw [Finset.mem_filter] at hn'
      obtain ⟨hnT, hgi⟩ := hn'
      obtain ⟨b1, -, -⟩ := hblock n hnT
      rw [hgi] at b1
      have hnN : (N : ℝ) ≤ n := by exact_mod_cast b1
      have hnp : (0 : ℝ) < n := by linarith
      have hhi := (hmem n hnT).2.1
      have ht0 : 0 ≤ 1 / C := by positivity
      have ht1 : 1 / C ≤ 1 := by rw [div_le_one hC]; exact hC1
      have h1 : wt (powSeq c) k n ≤ (1 / C) * (n : ℝ) ^ (1 / C - 1) := by
        unfold wt; exact diff_le hnp ht0 ht1
      have h2 : (n : ℝ) ^ (1 / C) ≤ 2 * (Y : ℝ) + 1 := by
        have := Real.rpow_le_rpow (by positivity) hhi ht0
        rw [← Real.rpow_mul (by positivity), mul_one_div_cancel hC.ne', Real.rpow_one] at this
        push_cast at this
        linarith
      rw [Real.rpow_sub_one hnp.ne'] at h1
      calc wt (powSeq c) k n ≤ (1 / C) * ((n : ℝ) ^ (1 / C) / n) := h1
        _ ≤ (1 / C) * ((2 * (Y : ℝ) + 1) / n) :=
            mul_le_mul_of_nonneg_left (div_le_div_of_nonneg_right h2 hnp.le) ht0
        _ ≤ (1 / C) * ((2 * (Y : ℝ) + 1) / N) :=
            mul_le_mul_of_nonneg_left
              (div_le_div_of_nonneg_left (by positivity) hNp hnN) ht0
        _ = (2 * (Y : ℝ) + 1) / (C * N) := by field_simp
    have heta : etaLL Cη N ≤ etaLL Cη x0 := etaLL_anti hCη hx03 hNr
    calc ∑ n ∈ T with g n = i, wt (powSeq c) k n
        ≤ ((T.filter (fun n => g n = i)).card : ℝ) * ((2 * (Y : ℝ) + 1) / (C * N)) := by
          have := Finset.sum_le_card_nsmul (T.filter (fun n => g n = i)) (wt (powSeq c) k) _ hwt
          rwa [nsmul_eq_mul] at this
      _ ≤ K * N * etaLL Cη N * ((2 * (Y : ℝ) + 1) / (C * N)) :=
          mul_le_mul_of_nonneg_right hcard (by positivity)
      _ = K * (2 * (Y : ℝ) + 1) * etaLL Cη N / C := by field_simp
      _ ≤ K * (2 * (Y : ℝ) + 1) * etaLL Cη x0 / C := by
          apply div_le_div_of_nonneg_right _ hC.le
          apply mul_le_mul_of_nonneg_left heta
          have : (0 : ℝ) ≤ Y := by linarith
          positivity
  have hMbr : (Mb : ℝ) < 2 * C + 1 := Nat.ceil_lt_add_one (by linarith)
  calc ∑ i ∈ Finset.range Mb, ∑ n ∈ T with g n = i, wt (powSeq c) k n
      ≤ (Finset.range Mb).card * (X / C) := by
        have := Finset.sum_le_card_nsmul (Finset.range Mb) _ _ hfib
        rwa [nsmul_eq_mul] at this
    _ = (Mb : ℝ) * (X / C) := by rw [Finset.card_range]
    _ ≤ 3 * X := by
        rw [mul_div_assoc', div_le_iff₀ hC]
        nlinarith
    _ = betaT c Cη K Y k := by unfold betaT; rw [hX, hx0, hCdef]; ring

variable (hS2 : ∀ q, S q → 2 ≤ q)
include hS2

/-- **Mills constants in `S` under a `(log log)²` saving.** If, for some `N₀`, the `ν`-bad
integers in each window `[N, 2N]` with `N ≥ N₀` number at most `K N exp(-C (log log N)²)`,
with `C > 1/(2 log c)`, then some `B` has `⌊B^{c^k}⌋ ∈ S` for every `k`. -/
theorem mills_constS_loglog {c : ℝ} (hc : 1 < c) (ν : ℝ) (hν : 0 < ν) (Cη K : ℝ)
    (hCη : 1 / (2 * Real.log c) < Cη) (hK : 0 ≤ K) (N₀ : ℕ)
    (hexc : ∀ N : ℕ, N₀ ≤ N →
      (((Finset.Icc N (2 * N)).filter (fun n => badNu S ν c n)).card : ℝ) ≤
        K * N * etaLL Cη N) :
    ∃ B : ℝ, ∀ k, S ⌊B ^ c ^ k⌋₊ := by
  have hℓ0 : 0 < Real.log c := Real.log_pos hc
  have hCη0 : 0 < Cη := lt_trans (by positivity) hCη
  have h2C : 0 < 2 * Cη * Real.log c - 1 := by
    rw [div_lt_iff₀ (by positivity)] at hCη; linarith
  set V := max 1 (max (DT c ν Cη / (2 * Cη * Real.log c - 1)) (Real.log (12 * K + 1) / Cη))
    with hV
  have hlim : Tendsto (fun Y : ℕ => Real.log (Real.log (Y : ℝ))) atTop atTop :=
    (Real.tendsto_log_atTop.comp Real.tendsto_log_atTop).comp tendsto_natCast_atTop_atTop
  obtain ⟨Y, hYv, hY3, hYN⟩ := ((hlim.eventually (eventually_ge_atTop V)).and
    ((eventually_ge_atTop 3).and (eventually_ge_atTop N₀))).exists
  have hYv' : V ≤ Real.log (Real.log (Y : ℝ)) := hYv
  have hY3r : (3 : ℝ) ≤ Y := by exact_mod_cast hY3
  have hY1 : 1 ≤ Y := by omega
  set v := Real.log (Real.log (Y : ℝ)) with hvdef
  have hv1 : 1 ≤ v := le_trans (le_max_left _ _) hYv'
  have hv : DT c ν Cη ≤ (2 * Cη * Real.log c - 1) * v := by
    have : DT c ν Cη / (2 * Cη * Real.log c - 1) ≤ v :=
      le_trans (le_trans (le_max_left _ _) (le_max_right _ _)) hYv'
    rw [div_le_iff₀ h2C] at this
    linarith
  have h0 : 12 * K * etaLL Cη Y ≤ 1 := by
    have hlK : Real.log (12 * K + 1) / Cη ≤ v :=
      le_trans (le_trans (le_max_right _ _) (le_max_right _ _)) hYv'
    rw [div_le_iff₀ hCη0] at hlK
    have hvv : v ≤ v ^ 2 := by nlinarith
    have hsq : Real.log (12 * K + 1) ≤ Cη * v ^ 2 := by
      have := mul_le_mul_of_nonneg_left hvv hCη0.le
      linarith
    have he : etaLL Cη Y ≤ (12 * K + 1)⁻¹ := by
      unfold etaLL
      rw [← hvdef, ← Real.exp_log (by positivity : (0 : ℝ) < 12 * K + 1), ← Real.exp_neg,
        Real.exp_le_exp]
      linarith
    have h12 : 0 ≤ 12 * K := by positivity
    calc 12 * K * etaLL Cη Y ≤ 12 * K * (12 * K + 1)⁻¹ := mul_le_mul_of_nonneg_left he h12
      _ ≤ 1 := by
        rw [← div_eq_mul_inv, div_le_one (by positivity)]; linarith
  obtain ⟨A, hA1, hA⟩ := ic_existsG S hS2 hc Y hY1 (nuSeqT c ν Y) (betaT c Cη K Y)
    (LSeqT c ν Y) (fun k => (nuSeqT_pos hc hν Y k).le) (le_refl _) (LSeqT_pos hc hν Y)
    (beta_leT hc hν hCη hK hY3r hv h0)
    (fun k => by rw [ratio_powSeq hc k]; exact le_refl _)
    (bad_weightT S hc hν hCη0.le hK hexc hY3r hYN)
  refine ⟨A ^ c, fun k => ?_⟩
  have hA0 : 0 ≤ A := by linarith
  have e : (A ^ c) ^ (c ^ k) = A ^ powSeq c (k + 1) := by
    rw [← Real.rpow_mul hA0, powSeq_succ, mul_comm]
    rfl
  rw [e]
  exact hA k

/-- **Cumulative form.** `#{n ≤ N : n ν-bad} ≤ K N exp(-C (log log N)²)` for `N ≥ N₀`, with
`C > 1/(2 log c)`, suffices as well. -/
theorem mills_constS_loglog_cum {c : ℝ} (hc : 1 < c) (ν : ℝ) (hν : 0 < ν) (Cη K : ℝ)
    (hCη : 1 / (2 * Real.log c) < Cη) (hK : 0 ≤ K) (N₀ : ℕ)
    (hexc : ∀ N : ℕ, N₀ ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badNu S ν c n)).card : ℝ) ≤
        K * N * etaLL Cη N) :
    ∃ B : ℝ, ∀ k, S ⌊B ^ c ^ k⌋₊ := by
  have hℓ0 : 0 < Real.log c := Real.log_pos hc
  have hCη0 : 0 < Cη := lt_trans (by positivity) hCη
  refine mills_constS_loglog S hS2 hc ν hν Cη (2 * K) hCη (by positivity) (max N₀ 3) ?_
  intro N hN
  have hN0 : N₀ ≤ N := le_trans (le_max_left _ _) hN
  have hN3 : 3 ≤ N := le_trans (le_max_right _ _) hN
  have hsub : (Finset.Icc N (2 * N)).filter (fun n => badNu S ν c n) ⊆
      (Finset.range (2 * N + 1)).filter (fun n => badNu S ν c n) := by
    apply Finset.filter_subset_filter
    intro x hx
    rw [Finset.mem_Icc] at hx
    rw [Finset.mem_range]
    omega
  have h1 := hexc (2 * N) (by omega)
  have hN3r : (3 : ℝ) ≤ N := by exact_mod_cast hN3
  have heta : etaLL Cη ((2 * N : ℕ) : ℝ) ≤ etaLL Cη N :=
    etaLL_anti hCη0.le hN3r (by push_cast; linarith)
  have hKN : 0 ≤ K * ((2 * N : ℕ) : ℝ) := by positivity
  calc (((Finset.Icc N (2 * N)).filter (fun n => badNu S ν c n)).card : ℝ)
      ≤ (((Finset.range (2 * N + 1)).filter (fun n => badNu S ν c n)).card : ℝ) := by
        exact_mod_cast Finset.card_le_card hsub
    _ ≤ K * ((2 * N : ℕ) : ℝ) * etaLL Cη ((2 * N : ℕ) : ℝ) := h1
    _ ≤ K * ((2 * N : ℕ) : ℝ) * etaLL Cη N := mul_le_mul_of_nonneg_left heta hKN
    _ = 2 * K * N * etaLL Cη N := by push_cast; ring

end Threshold

end MillsForest
