import MillsForest.Phi

/-!
# From a discrete exceptional-set hypothesis to `hexc`

`DiscreteExcHyp θ ξ K0` is a **discrete, prime-counting analogue** of `μ(θ) ≤ ξ < 1`:

  `#{1 ≤ x ≤ Z : π[x, x + ⌊x^θ⌋) < ⌊x^θ⌋ / (2 log x)} ≤ K0 Z^ξ`   for every `Z ≥ 1`.

The literature (`μ`, Bazzanella–Perelli, Gafni–Tao) is stated for Chebyshev's `ψ`, for real
`x`, with Lebesgue measure and window `x^θ`. The passage from there to this discrete
statement still happens **on paper**. It consists of three standard transfers:
  (a) from a real-`x` measure to integer sampling;
  (b) from `ψ` to `π`, removing prime powers;
  (c) from window `x^θ` to `⌊x^θ'⌋` with `θ' < θ`.
For `c = φ` the cited estimates cover `1/3 < θ < 1/φ²` (Ingham–Huxley via Gafni–Tao), or
`1/6 < θ < 1/φ²` (Bazzanella–Perelli).

This file proves, in Lean:
* the window lemma: a bad `n` forces many exceptional `x` in its child interval (discrete
  Markov averaging, by double counting);
* the counting step, `hexc_of_discreteExc`;
* the composite theorem `mills_goldenRatio_of_discreteExc`.
-/

open Finset Real Filter

namespace MillsForest

/-- Number of primes in `[x, x + H)`. -/
def pcount (x H : ℕ) : ℕ := ((Finset.Ico x (x + H)).filter Nat.Prime).card

/-- Window length `⌊x^θ⌋`. -/
noncomputable def Hθ (θ : ℝ) (x : ℕ) : ℕ := ⌊(x : ℝ) ^ θ⌋₊

/-- Discrete exceptional point: fewer than half of the expected primes in `[x, x + ⌊x^θ⌋)`. -/
def discExc (θ : ℝ) (x : ℕ) : Prop :=
  (pcount x (Hθ θ x) : ℝ) < (Hθ θ x : ℝ) / (2 * Real.log x)

noncomputable instance discExc_dec (θ : ℝ) : DecidablePred (discExc θ) := fun x => by
  unfold discExc; infer_instance

/-- The discrete exceptional-set hypothesis. -/
def DiscreteExcHyp (θ ξ K0 : ℝ) : Prop :=
  ∀ Z : ℕ, 1 ≤ Z → (((Finset.Icc 1 Z).filter (discExc θ)).card : ℝ) ≤ K0 * (Z : ℝ) ^ ξ

lemma pcount_mono (x : ℕ) {H H' : ℕ} (h : H ≤ H') : pcount x H ≤ pcount x H' := by
  unfold pcount
  apply Finset.card_le_card
  apply Finset.filter_subset_filter
  exact Finset.Ico_subset_Ico le_rfl (by omega)

/-- Double counting: each prime is seen by at most `H` windows of length `H`. -/
lemma sum_pcount_le (X S : Finset ℕ) (H : ℕ) (hSp : ∀ p ∈ S, p.Prime)
    (hS : ∀ x ∈ X, (Finset.Ico x (x + H)).filter Nat.Prime ⊆ S) :
    ∑ x ∈ X, pcount x H ≤ H * S.card := by
  have h1 : ∀ x ∈ X, pcount x H = (S.filter (fun p => x ≤ p ∧ p < x + H)).card := by
    intro x hx
    unfold pcount
    congr 1
    ext p
    simp only [Finset.mem_filter, Finset.mem_Ico]
    constructor
    · intro hp
      exact ⟨hS x hx (Finset.mem_filter.mpr ⟨Finset.mem_Ico.mpr hp.1, hp.2⟩), hp.1⟩
    · rintro ⟨hpS, hp⟩
      exact ⟨hp, hSp p hpS⟩
  have h2 : ∀ x ∈ X, (S.filter (fun p => x ≤ p ∧ p < x + H)).card =
      ∑ p ∈ S, if (x ≤ p ∧ p < x + H) then 1 else 0 :=
    fun x _ => Finset.card_filter _ _
  rw [Finset.sum_congr rfl h1, Finset.sum_congr rfl h2, Finset.sum_comm]
  have h3 : ∀ p ∈ S, ∑ x ∈ X, (if (x ≤ p ∧ p < x + H) then 1 else 0) ≤ H := by
    intro p _
    rw [← Finset.card_filter]
    calc (X.filter (fun x => x ≤ p ∧ p < x + H)).card
        ≤ (Finset.Ico (p + 1 - H) (p + 1)).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢
          omega
      _ ≤ H := by rw [Nat.card_Ico]; omega
  calc ∑ p ∈ S, ∑ x ∈ X, (if (x ≤ p ∧ p < x + H) then 1 else 0)
      ≤ ∑ _p ∈ S, H := Finset.sum_le_sum h3
    _ = H * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

lemma Hθ_mono {θ : ℝ} (hθ : 0 ≤ θ) {x y : ℕ} (h : x ≤ y) : Hθ θ x ≤ Hθ θ y := by
  unfold Hθ
  apply Nat.floor_le_floor
  exact Real.rpow_le_rpow (Nat.cast_nonneg _) (by exact_mod_cast h) hθ

/-- **Window lemma** (discrete Markov averaging). If `[u, w]` contains at most `T` primes,
then at least `(w + 2 - H(w) - u) - 4 T log V` of the points `x ∈ [u, w + 1 - H(w)]` are
exceptional. -/
lemma window_exc (θ : ℝ) (hθ : 0 ≤ θ) (u w : ℕ) (T V : ℝ)
    (hu : 2 ≤ u) (huw : u ≤ w) (hHlo : 1 ≤ Hθ θ u) (hHw : Hθ θ w + u ≤ w + 1)
    (hratio : Hθ θ w ≤ 2 * Hθ θ u) (hwV : (w : ℝ) ≤ V)
    (hP : ((((Finset.Icc u w).filter Nat.Prime).card : ℕ) : ℝ) ≤ T) :
    ((w + 2 - Hθ θ w - u : ℕ) : ℝ) - 4 * T * Real.log V ≤
      (((Finset.Icc u (w + 1 - Hθ θ w)).filter (discExc θ)).card : ℝ) := by
  set Hlo := Hθ θ u with hHlo_def
  set Hhi := Hθ θ w with hHhi_def
  set X := Finset.Icc u (w + 1 - Hhi) with hX_def
  set S := (Finset.Icc u w).filter Nat.Prime with hS_def
  have hHhi1 : 1 ≤ Hhi := le_trans hHlo (Hθ_mono hθ huw)
  have hu2 : (2 : ℝ) ≤ u := by exact_mod_cast hu
  have huwr : (u : ℝ) ≤ w := by exact_mod_cast huw
  have hV : 1 < V := by linarith
  have hlogV : 0 < Real.log V := Real.log_pos hV
  have hHlo' : (0 : ℝ) < Hlo := by exact_mod_cast hHlo
  -- double counting
  have hsum : ∑ x ∈ X, pcount x Hhi ≤ Hhi * S.card := by
    apply sum_pcount_le X S Hhi
    · intro p hp; exact (Finset.mem_filter.mp hp).2
    · intro x hx q hq
      rw [Finset.mem_filter, Finset.mem_Ico] at hq
      rw [hX_def, Finset.mem_Icc] at hx
      rw [hS_def, Finset.mem_filter, Finset.mem_Icc]
      exact ⟨⟨by omega, by omega⟩, hq.2⟩
  -- non-exceptional points carry many primes
  set NE := X.filter (fun x => ¬ discExc θ x) with hNE_def
  have hNE : ∀ x ∈ NE, (Hlo : ℝ) / (2 * Real.log V) ≤ (pcount x Hhi : ℝ) := by
    intro x hx
    rw [hNE_def, Finset.mem_filter, hX_def, Finset.mem_Icc] at hx
    obtain ⟨⟨hx1, hx2⟩, hne⟩ := hx
    unfold discExc at hne
    push_neg at hne
    have hx2' : x ≤ w := by omega
    have hlo : Hlo ≤ Hθ θ x := Hθ_mono hθ hx1
    have hhi : Hθ θ x ≤ Hhi := Hθ_mono hθ hx2'
    have hxr : (2 : ℝ) ≤ x := by exact_mod_cast (le_trans hu hx1)
    have hlogx : 0 < Real.log x := Real.log_pos (by linarith)
    have hxw : (x : ℝ) ≤ w := by exact_mod_cast hx2'
    have hlogxV : Real.log x ≤ Real.log V := Real.log_le_log (by linarith) (by linarith)
    calc (Hlo : ℝ) / (2 * Real.log V) ≤ (Hlo : ℝ) / (2 * Real.log x) :=
          div_le_div_of_nonneg_left (Nat.cast_nonneg _) (by positivity) (by linarith)
      _ ≤ (Hθ θ x : ℝ) / (2 * Real.log x) :=
          div_le_div_of_nonneg_right (by exact_mod_cast hlo) (by positivity)
      _ ≤ pcount x (Hθ θ x) := hne
      _ ≤ pcount x Hhi := by exact_mod_cast pcount_mono x hhi
  have hcnt : (NE.card : ℝ) * ((Hlo : ℝ) / (2 * Real.log V)) ≤ (Hhi : ℝ) * S.card := by
    have h1 := Finset.card_nsmul_le_sum NE (fun x => (pcount x Hhi : ℝ)) _ hNE
    rw [nsmul_eq_mul] at h1
    calc (NE.card : ℝ) * ((Hlo : ℝ) / (2 * Real.log V)) ≤ ∑ x ∈ NE, (pcount x Hhi : ℝ) := h1
      _ ≤ ∑ x ∈ X, (pcount x Hhi : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ (Hhi : ℝ) * S.card := by exact_mod_cast hsum
  have h2 : (Hhi : ℝ) * S.card ≤ 2 * Hlo * T := by
    have hr : (Hhi : ℝ) ≤ 2 * Hlo := by exact_mod_cast hratio
    have hS0 : (0 : ℝ) ≤ S.card := Nat.cast_nonneg _
    have hHhi0 : (0 : ℝ) ≤ Hhi := Nat.cast_nonneg _
    calc (Hhi : ℝ) * S.card ≤ (2 * Hlo) * S.card := mul_le_mul_of_nonneg_right hr hS0
      _ ≤ (2 * Hlo) * T := mul_le_mul_of_nonneg_left hP (by positivity)
  have key : (NE.card : ℝ) * ((Hlo : ℝ) / (2 * Real.log V)) ≤ 2 * Hlo * T := le_trans hcnt h2
  have hNEle : (NE.card : ℝ) ≤ 4 * T * Real.log V := by
    have e : (NE.card : ℝ) * Hlo = (NE.card * ((Hlo : ℝ) / (2 * Real.log V))) * (2 * Real.log V) := by
      field_simp
    have h3 : (NE.card : ℝ) * Hlo ≤ (2 * Hlo * T) * (2 * Real.log V) := by
      rw [e]; exact mul_le_mul_of_nonneg_right key (by positivity)
    have h4 : (NE.card : ℝ) * Hlo ≤ (4 * T * Real.log V) * Hlo := by
      calc (NE.card : ℝ) * Hlo ≤ (2 * Hlo * T) * (2 * Real.log V) := h3
        _ = (4 * T * Real.log V) * Hlo := by ring
    exact le_of_mul_le_mul_right h4 hHlo'
  have hsplit := Finset.card_filter_add_card_filter_not (s := X) (discExc θ)
  have hXc : X.card = w + 2 - Hhi - u := by
    rw [hX_def, Nat.card_Icc]; omega
  have hsplitR : ((X.filter (discExc θ)).card : ℝ) + (NE.card : ℝ) = X.card := by
    rw [hNE_def]; exact_mod_cast hsplit
  rw [hXc] at hsplitR
  linarith

/-! ### Child intervals -/

/-- `u_n = ⌈n^c⌉`. -/
noncomputable def uN (c : ℝ) (n : ℕ) : ℕ := ⌈(n : ℝ) ^ c⌉₊
/-- `w_n = ⌈(n+1)^c⌉ - 2`. -/
noncomputable def wN (c : ℝ) (n : ℕ) : ℕ := ⌈((n : ℝ) + 1) ^ c⌉₊ - 2
/-- The exceptional points in the window range of `n`. -/
noncomputable def XN (c θ : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc (uN c n) (wN c n + 1 - Hθ θ (wN c n))).filter (discExc θ)

lemma card_kids_eq {c : ℝ} (hc : 1 < c) (n : ℕ) :
    (kids (powSeq c) 0 n).card = ((Finset.Icc (uN c n) (wN c n)).filter Nat.Prime).card := by
  unfold kids uN wN; rw [ratio_powSeq hc 0]

lemma wN_le {c : ℝ} (hc : 0 < c) (n : ℕ) : (wN c n : ℝ) ≤ ((n : ℝ) + 1) ^ c - 1 := by
  have hy : 1 ≤ ((n : ℝ) + 1) ^ c :=
    Real.one_le_rpow (by have : (0 : ℝ) ≤ n := Nat.cast_nonneg n; linarith) hc.le
  have hlt := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ c)
  unfold wN
  by_cases h2 : 2 ≤ ⌈((n : ℝ) + 1) ^ c⌉₊
  · rw [Nat.cast_sub h2]; push_cast; linarith
  · have : ⌈((n : ℝ) + 1) ^ c⌉₊ - 2 = 0 := by omega
    rw [this]; push_cast; linarith

lemma le_wN {c : ℝ} (n : ℕ) : ((n : ℝ) + 1) ^ c - 2 ≤ (wN c n : ℝ) := by
  have hle := Nat.le_ceil (((n : ℝ) + 1) ^ c)
  unfold wN
  by_cases h2 : 2 ≤ ⌈((n : ℝ) + 1) ^ c⌉₊
  · rw [Nat.cast_sub h2]; push_cast; linarith
  · have h' : (⌈((n : ℝ) + 1) ^ c⌉₊ : ℝ) < 2 := by exact_mod_cast (by omega : ⌈((n : ℝ) + 1) ^ c⌉₊ < 2)
    have : ⌈((n : ℝ) + 1) ^ c⌉₊ - 2 = 0 := by omega
    rw [this]; push_cast; linarith

lemma wN_lt {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) :
    (wN c n : ℝ) + 1 < ((n : ℝ) + 1) ^ c := by
  have hn' : (2 : ℝ) ≤ (n : ℝ) + 1 := by have : (1 : ℝ) ≤ n := by exact_mod_cast hn
                                         linarith
  have hy : 1 < ((n : ℝ) + 1) ^ c := Real.one_lt_rpow (by linarith) hc
  have hlt := Nat.ceil_lt_add_one (by linarith : (0 : ℝ) ≤ ((n : ℝ) + 1) ^ c)
  unfold wN
  by_cases h2 : 2 ≤ ⌈((n : ℝ) + 1) ^ c⌉₊
  · rw [Nat.cast_sub h2]; push_cast; linarith
  · have : ⌈((n : ℝ) + 1) ^ c⌉₊ - 2 = 0 := by omega
    rw [this]; push_cast; linarith

lemma XN_disjoint {c θ : ℝ} (hc : 1 < c) {n n' : ℕ} (hn : 1 ≤ n) (h : n < n') :
    Disjoint (XN c θ n) (XN c θ n') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  unfold XN at hx hx'
  rw [Finset.mem_filter, Finset.mem_Icc] at hx hx'
  have h1 : (x : ℝ) ≤ wN c n + 1 := by exact_mod_cast (by omega : x ≤ wN c n + 1)
  have h2 := wN_lt (by linarith : (0 : ℝ) < c) hn
  have h3 : ((n : ℝ) + 1) ^ c ≤ (n' : ℝ) ^ c :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast h) (by linarith)
  have h4 : (n' : ℝ) ^ c ≤ uN c n' := Nat.le_ceil _
  have h5 : (uN c n' : ℝ) ≤ x := by exact_mod_cast hx'.1.1
  linarith

/-- Side conditions at `n` (they hold for all large `n`). -/
def Side (c θ : ℝ) (n : ℕ) : Prop :=
  2 ≤ n ∧ (Hθ θ (wN c n) : ℝ) + 1 ≤ (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / 10 ∧
    Hθ θ (wN c n) ≤ 2 * Hθ θ (uN c n)

/-- A bad `n` satisfying the side conditions has at least `ℓ(n)/10` exceptional points. -/
lemma bad_window {c θ : ℝ} (hc : 1 < c) (hθ : 0 ≤ θ) {n : ℕ} (hs : Side c θ n)
    (hbad : badc c n) :
    (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / 10 ≤ ((XN c θ n).card : ℝ) := by
  obtain ⟨hn2, hHside, hratio⟩ := hs
  set ℓ := ((n : ℝ) + 1) ^ c - (n : ℝ) ^ c with hℓ
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnc : (n : ℝ) ≤ (n : ℝ) ^ c := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ n) hc.le
    rwa [Real.rpow_one] at this
  have hu1 : (n : ℝ) ^ c ≤ uN c n := Nat.le_ceil _
  have hu2 : (uN c n : ℝ) < (n : ℝ) ^ c + 1 := Nat.ceil_lt_add_one (by positivity)
  have hu : 2 ≤ uN c n := by
    have : (2 : ℝ) ≤ uN c n := by linarith
    exact_mod_cast this
  have hw1 := le_wN (c := c) n
  have hw2 := wN_le (by linarith : (0 : ℝ) < c) n
  have hHhi0 : (0 : ℝ) ≤ Hθ θ (wN c n) := Nat.cast_nonneg _
  have hHlo : 1 ≤ Hθ θ (uN c n) := by
    unfold Hθ
    apply Nat.le_floor
    push_cast
    exact Real.one_le_rpow (by linarith) hθ
  have hHw : Hθ θ (wN c n) + uN c n ≤ wN c n + 1 := by
    have : (Hθ θ (wN c n) : ℝ) + uN c n ≤ wN c n + 1 := by linarith
    exact_mod_cast this
  set V := ((n : ℝ) + 1) ^ c with hV
  have hV1 : 1 < V := by
    have : (3 : ℝ) ≤ (n : ℝ) + 1 := by linarith
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1) hc.le
    rw [Real.rpow_one] at this
    linarith
  have hlogV : 0 < Real.log V := Real.log_pos hV1
  have hP : ((((Finset.Icc (uN c n) (wN c n)).filter Nat.Prime).card : ℕ) : ℝ) ≤
      ℓ / (5 * Real.log V) := by
    have hb := hbad
    unfold badc at hb
    rw [card_kids_eq hc n] at hb
    exact hb.le
  have huw : uN c n ≤ wN c n := by
    have : (uN c n : ℝ) ≤ wN c n := by linarith
    exact_mod_cast this
  have hwin := window_exc θ hθ (uN c n) (wN c n) (ℓ / (5 * Real.log V)) V hu huw hHlo hHw hratio
    (by linarith) hP
  have e4 : 4 * (ℓ / (5 * Real.log V)) * Real.log V = 4 / 5 * ℓ := by
    field_simp
  rw [e4] at hwin
  have hnat : wN c n + 2 - Hθ θ (wN c n) - uN c n + Hθ θ (wN c n) + uN c n = wN c n + 2 := by
    omega
  have hnatR : ((wN c n + 2 - Hθ θ (wN c n) - uN c n : ℕ) : ℝ) =
      (wN c n : ℝ) + 2 - Hθ θ (wN c n) - uN c n := by
    have := congrArg (fun m : ℕ => (m : ℝ)) hnat
    push_cast at this
    linarith
  rw [hnatR] at hwin
  unfold XN
  linarith

/-! ### Side conditions hold eventually -/

lemma side_eventually {c θ : ℝ} (hc : 1 < c) (hθ0 : 0 < θ) (hθ1 : c * θ < c - 1)
    (hθ2 : c * θ < 1) : ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0, Side c θ n := by
  set s := c * θ with hs
  have hs0 : 0 < s := by positivity
  set e := c - 1 - s with he
  have he0 : 0 < e := by linarith
  have h2s : (2 : ℝ) ^ s < 2 := by
    have := Real.rpow_lt_rpow_of_exponent_lt (by norm_num : (1 : ℝ) < 2) hθ2
    rwa [Real.rpow_one] at this
  set M1 := 2 / (2 - (2 : ℝ) ^ s) with hM1
  set M2 := 10 * ((2 : ℝ) ^ s + 1) / c with hM2
  have t1 := (tendsto_rpow_atTop hs0).comp tendsto_natCast_atTop_atTop
  have t2 := (tendsto_rpow_atTop he0).comp tendsto_natCast_atTop_atTop
  have ev := ((t1.eventually (eventually_ge_atTop (max M1 1))).and
    (t2.eventually (eventually_ge_atTop M2))).and (eventually_ge_atTop (2 : ℕ))
  obtain ⟨n0, hn0⟩ := Filter.eventually_atTop.mp ev
  refine ⟨max n0 2, le_max_right _ _, fun n hn => ?_⟩
  obtain ⟨⟨h1, h2⟩, h3⟩ := hn0 n (le_trans (le_max_left _ _) hn)
  simp only [Function.comp] at h1 h2
  have hn1 : (1 : ℝ) ≤ n := by exact_mod_cast (le_trans (by norm_num) h3)
  have hnpos : (0 : ℝ) < n := by linarith
  have hns1 : 1 ≤ (n : ℝ) ^ s := le_trans (le_max_right _ _) h1
  have hnsM : M1 ≤ (n : ℝ) ^ s := le_trans (le_max_left _ _) h1
  -- upper bound for H(w)
  have hw2 := wN_le (by linarith : (0 : ℝ) < c) n
  have hHhi : (Hθ θ (wN c n) : ℝ) ≤ (2 : ℝ) ^ s * (n : ℝ) ^ s := by
    unfold Hθ
    have hwle : (wN c n : ℝ) ≤ ((n : ℝ) + 1) ^ c := by linarith
    calc (⌊(wN c n : ℝ) ^ θ⌋₊ : ℝ) ≤ (wN c n : ℝ) ^ θ := Nat.floor_le (by positivity)
      _ ≤ (((n : ℝ) + 1) ^ c) ^ θ := Real.rpow_le_rpow (by positivity) hwle hθ0.le
      _ = ((n : ℝ) + 1) ^ s := by rw [← Real.rpow_mul (by positivity)]
      _ ≤ (2 * (n : ℝ)) ^ s := Real.rpow_le_rpow (by positivity) (by linarith) hs0.le
      _ = (2 : ℝ) ^ s * (n : ℝ) ^ s := Real.mul_rpow (by norm_num) hnpos.le
  -- lower bound for H(u)
  have hHlo : (n : ℝ) ^ s - 1 < (Hθ θ (uN c n) : ℝ) := by
    unfold Hθ
    have hu1 : (n : ℝ) ^ c ≤ uN c n := Nat.le_ceil _
    have : (n : ℝ) ^ s ≤ (uN c n : ℝ) ^ θ := by
      calc (n : ℝ) ^ s = ((n : ℝ) ^ c) ^ θ := by rw [← Real.rpow_mul hnpos.le]
        _ ≤ (uN c n : ℝ) ^ θ := Real.rpow_le_rpow (by positivity) hu1 hθ0.le
    have := Nat.sub_one_lt_floor ((uN c n : ℝ) ^ θ)
    linarith
  -- ℓ ≥ c n^{c-1} = c n^e n^s
  have hℓ : c * (n : ℝ) ^ (c - 1) ≤ ((n : ℝ) + 1) ^ c - (n : ℝ) ^ c :=
    diff_ge_conv hnpos hc.le
  have hsplit : (n : ℝ) ^ (c - 1) = (n : ℝ) ^ e * (n : ℝ) ^ s := by
    rw [← Real.rpow_add hnpos]; congr 1; rw [he]; ring
  refine ⟨le_trans (le_max_right _ _) hn, ?_, ?_⟩
  · -- H(w) + 1 ≤ ℓ/10
    have hc0 : 0 < c := by linarith
    have hM2' : M2 * (n : ℝ) ^ s ≤ (n : ℝ) ^ e * (n : ℝ) ^ s :=
      mul_le_mul_of_nonneg_right h2 (by positivity)
    have hM2e : M2 * (n : ℝ) ^ s * c = 10 * ((2 : ℝ) ^ s + 1) * (n : ℝ) ^ s := by
      rw [hM2]; field_simp
    have hA : (2 : ℝ) ^ s * (n : ℝ) ^ s + 1 ≤ ((2 : ℝ) ^ s + 1) * (n : ℝ) ^ s := by nlinarith
    have hB : 10 * (((2 : ℝ) ^ s + 1) * (n : ℝ) ^ s) ≤ c * (n : ℝ) ^ (c - 1) := by
      rw [hsplit]
      have := mul_le_mul_of_nonneg_right hM2' hc0.le
      nlinarith [hM2e]
    linarith
  · -- H(w) ≤ 2 H(u)
    have hpos : 0 < 2 - (2 : ℝ) ^ s := by linarith
    have hM1e : (2 - (2 : ℝ) ^ s) * M1 = 2 := by
      rw [hM1]; field_simp
    have : (2 : ℝ) ^ s * (n : ℝ) ^ s ≤ 2 * ((n : ℝ) ^ s - 1) := by
      have h := mul_le_mul_of_nonneg_left hnsM hpos.le
      rw [hM1e] at h
      nlinarith
    have hR : (Hθ θ (wN c n) : ℝ) < 2 * (Hθ θ (uN c n) : ℝ) + 0 := by linarith
    have : (Hθ θ (wN c n) : ℝ) ≤ 2 * (Hθ θ (uN c n) : ℝ) := by linarith
    exact_mod_cast this

lemma one_le_uN {c : ℝ} (hc : 0 < c) {n : ℕ} (hn : 1 ≤ n) : 1 ≤ uN c n := by
  have h1 : (1 : ℝ) ≤ (n : ℝ) ^ c := Real.one_le_rpow (by exact_mod_cast hn) hc.le
  have h2 : (n : ℝ) ^ c ≤ uN c n := Nat.le_ceil _
  have : (1 : ℝ) ≤ uN c n := le_trans h1 h2
  exact_mod_cast this

/-- **Counting step**: the discrete exceptional hypothesis implies `hexc`. -/
theorem hexc_of_discreteExc {c θ ξ K0 : ℝ} (hc : 1 < c) (hθ0 : 0 < θ) (hθ1 : c * θ < c - 1)
    (hθ2 : c * θ < 1) (hξ0 : 0 ≤ ξ) (hξ1 : ξ < 1) (hK0 : 0 ≤ K0)
    (h : DiscreteExcHyp θ ξ K0) :
    ∃ δ K : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ K ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badc c n)).card : ℝ) ≤
        K * (N : ℝ) ^ (1 - δ) := by
  obtain ⟨n0, hn0_2, hside⟩ := side_eventually hc hθ0 hθ1 hθ2
  have hc1 : 0 < c - 1 := by linarith
  have hc0 : 0 < c := by linarith
  set m := max 0 ((c * ξ - 1) / (c - 1)) with hm
  have hm1 : m < 1 := by
    rw [hm]
    apply max_lt (by norm_num)
    rw [div_lt_one hc1]
    nlinarith
  have hm0 : 0 ≤ m := le_max_left _ _
  set a := (1 + m) / 2 with ha
  have ha0 : 0 < a := by linarith
  have ha1 : a < 1 := by linarith
  have ham : (c * ξ - 1) / (c - 1) < a := lt_of_le_of_lt (le_max_right _ _) (by linarith)
  have hgap : 0 < 1 - c * ξ + a * (c - 1) := by
    have := (div_lt_iff₀ hc1).mp ham
    linarith
  set δ := min (1 - a) (1 - c * ξ + a * (c - 1)) with hδ
  have hδ0 : 0 < δ := lt_min (by linarith) hgap
  have hδ1 : δ ≤ 1 := le_trans (min_le_left _ _) (by linarith)
  have hδa : δ ≤ 1 - a := min_le_left _ _
  have hδb : δ ≤ 1 - c * ξ + a * (c - 1) := min_le_right _ _
  set K2 := 10 * K0 * ((2 : ℝ) ^ c + 1) ^ ξ / c with hK2
  have hK2' : 0 ≤ K2 := by positivity
  refine ⟨δ, (n0 : ℝ) + 2 + K2, hδ0, hδ1, by positivity, fun N hN => ?_⟩
  have hNr : (1 : ℝ) ≤ N := by exact_mod_cast hN
  have hNpos : (0 : ℝ) < N := by linarith
  set n1 := max n0 ⌈(N : ℝ) ^ a⌉₊ with hn1
  have hn1_0 : n0 ≤ n1 := le_max_left _ _
  have hn1_a : (N : ℝ) ^ a ≤ n1 := by
    have h1 : (N : ℝ) ^ a ≤ (⌈(N : ℝ) ^ a⌉₊ : ℝ) := Nat.le_ceil _
    have h2 : (⌈(N : ℝ) ^ a⌉₊ : ℝ) ≤ n1 := by exact_mod_cast le_max_right _ _
    linarith
  set B := (Finset.range (N + 1)).filter (fun n => badc c n) with hB
  set L := (Finset.Icc n1 N).filter (fun n => badc c n) with hL
  have hBsub : B ⊆ Finset.range n1 ∪ L := by
    intro n hn
    rw [hB, Finset.mem_filter, Finset.mem_range] at hn
    rw [Finset.mem_union, Finset.mem_range, hL, Finset.mem_filter, Finset.mem_Icc]
    by_cases hlt : n < n1
    · exact Or.inl hlt
    · exact Or.inr ⟨⟨by omega, by omega⟩, hn.2⟩
  have hBcard : (B.card : ℝ) ≤ n1 + L.card := by
    have h1 := Finset.card_le_card hBsub
    have h2 := Finset.card_union_le (Finset.range n1) L
    rw [Finset.card_range] at h2
    exact_mod_cast le_trans h1 h2
  have hn1le : (n1 : ℝ) ≤ n0 + (N : ℝ) ^ a + 1 := by
    have h1 : (⌈(N : ℝ) ^ a⌉₊ : ℝ) < (N : ℝ) ^ a + 1 := Nat.ceil_lt_add_one (by positivity)
    rw [hn1, Nat.cast_max]
    apply max_le
    · have := Real.rpow_nonneg hNpos.le a; linarith
    · linarith [Nat.cast_nonneg (α := ℝ) n0]
  set Z := ⌈((N : ℝ) + 1) ^ c⌉₊ with hZ
  have hZ1 : 1 ≤ Z := by
    have h1 : (1 : ℝ) ≤ ((N : ℝ) + 1) ^ c := Real.one_le_rpow (by linarith) hc0.le
    have h2 : ((N : ℝ) + 1) ^ c ≤ Z := Nat.le_ceil _
    have : (1 : ℝ) ≤ Z := le_trans h1 h2
    exact_mod_cast this
  have hLside : ∀ n ∈ L, Side c θ n ∧ badc c n ∧ n1 ≤ n ∧ n ≤ N := by
    intro n hn
    rw [hL, Finset.mem_filter, Finset.mem_Icc] at hn
    exact ⟨hside n (le_trans hn1_0 hn.1.1), hn.2, hn.1.1, hn.1.2⟩
  have hdisj : ∀ n ∈ L, ∀ n' ∈ L, n ≠ n' → Disjoint (XN c θ n) (XN c θ n') := by
    intro n hn n' hn' hne
    have h1 := (hLside n hn).1.1
    have h2 := (hLside n' hn').1.1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact XN_disjoint hc (by omega) hlt
    · exact (XN_disjoint hc (by omega) hgt).symm
  have hsub : L.biUnion (XN c θ) ⊆ (Finset.Icc 1 Z).filter (discExc θ) := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨n, hn, hxn⟩ := hx
    obtain ⟨⟨hn2, -, -⟩, -, -, hnN⟩ := hLside n hn
    unfold XN at hxn
    rw [Finset.mem_filter, Finset.mem_Icc] at hxn
    rw [Finset.mem_filter, Finset.mem_Icc]
    refine ⟨⟨le_trans (one_le_uN hc0 (by omega)) hxn.1.1, ?_⟩, hxn.2⟩
    have hw := wN_lt hc0 (by omega : 1 ≤ n)
    have hx1 : (x : ℝ) ≤ wN c n + 1 := by exact_mod_cast (by omega : x ≤ wN c n + 1)
    have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
    have h3 : ((n : ℝ) + 1) ^ c ≤ ((N : ℝ) + 1) ^ c :=
      Real.rpow_le_rpow (by positivity) (by linarith) hc0.le
    have h4 : ((N : ℝ) + 1) ^ c ≤ Z := Nat.le_ceil _
    have : (x : ℝ) ≤ Z := by linarith
    exact_mod_cast this
  have hsumle : (∑ n ∈ L, ((XN c θ n).card : ℝ)) ≤ K0 * (Z : ℝ) ^ ξ := by
    have e : (L.biUnion (XN c θ)).card = ∑ n ∈ L, (XN c θ n).card := Finset.card_biUnion hdisj
    have h1 : ((L.biUnion (XN c θ)).card : ℝ) ≤
        (((Finset.Icc 1 Z).filter (discExc θ)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 := h Z hZ1
    have e' : ((L.biUnion (XN c θ)).card : ℝ) = ∑ n ∈ L, ((XN c θ n).card : ℝ) := by
      rw [e]; push_cast; rfl
    linarith
  have heach : ∀ n ∈ L, c * (N : ℝ) ^ (a * (c - 1)) / 10 ≤ ((XN c θ n).card : ℝ) := by
    intro n hn
    obtain ⟨hs, hbad, hn1n, -⟩ := hLside n hn
    have hw := bad_window hc hθ0.le hs hbad
    have hnr : (n1 : ℝ) ≤ n := by exact_mod_cast hn1n
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hs.1
    have hnpos : (0 : ℝ) < n := by linarith
    have hℓ : c * (n : ℝ) ^ (c - 1) ≤ ((n : ℝ) + 1) ^ c - (n : ℝ) ^ c := diff_ge_conv hnpos hc.le
    have hpow : (N : ℝ) ^ (a * (c - 1)) ≤ (n : ℝ) ^ (c - 1) := by
      rw [Real.rpow_mul hNpos.le]
      exact Real.rpow_le_rpow (by positivity) (le_trans hn1_a hnr) hc1.le
    have : c * (N : ℝ) ^ (a * (c - 1)) ≤ c * (n : ℝ) ^ (c - 1) :=
      mul_le_mul_of_nonneg_left hpow hc0.le
    linarith
  have hLlow : (L.card : ℝ) * (c * (N : ℝ) ^ (a * (c - 1)) / 10) ≤ K0 * (Z : ℝ) ^ ξ := by
    have := Finset.card_nsmul_le_sum L (fun n => ((XN c θ n).card : ℝ)) _ heach
    rw [nsmul_eq_mul] at this
    linarith
  have hZle : (Z : ℝ) ≤ ((2 : ℝ) ^ c + 1) * (N : ℝ) ^ c := by
    have h1 : (Z : ℝ) < ((N : ℝ) + 1) ^ c + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : ((N : ℝ) + 1) ^ c ≤ (2 * (N : ℝ)) ^ c :=
      Real.rpow_le_rpow (by positivity) (by linarith) hc0.le
    have h3 : (2 * (N : ℝ)) ^ c = (2 : ℝ) ^ c * (N : ℝ) ^ c := Real.mul_rpow (by norm_num) hNpos.le
    have h4 : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hNr hc0.le
    nlinarith
  have hZξ : (Z : ℝ) ^ ξ ≤ ((2 : ℝ) ^ c + 1) ^ ξ * (N : ℝ) ^ (c * ξ) := by
    calc (Z : ℝ) ^ ξ ≤ (((2 : ℝ) ^ c + 1) * (N : ℝ) ^ c) ^ ξ :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hZle hξ0
      _ = ((2 : ℝ) ^ c + 1) ^ ξ * (N : ℝ) ^ (c * ξ) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hNpos.le]
  have hNac : 0 < (N : ℝ) ^ (a * (c - 1)) := Real.rpow_pos_of_pos hNpos _
  have hLcard : (L.card : ℝ) ≤ K2 * (N : ℝ) ^ (c * ξ - a * (c - 1)) := by
    have hq : 0 < c * (N : ℝ) ^ (a * (c - 1)) / 10 := by positivity
    have h1 : (L.card : ℝ) * (c * (N : ℝ) ^ (a * (c - 1)) / 10) ≤
        K0 * (((2 : ℝ) ^ c + 1) ^ ξ * (N : ℝ) ^ (c * ξ)) :=
      le_trans hLlow (mul_le_mul_of_nonneg_left hZξ hK0)
    have h2 : (L.card : ℝ) ≤ K0 * (((2 : ℝ) ^ c + 1) ^ ξ * (N : ℝ) ^ (c * ξ)) /
        (c * (N : ℝ) ^ (a * (c - 1)) / 10) := (le_div_iff₀ hq).mpr h1
    have e : K0 * (((2 : ℝ) ^ c + 1) ^ ξ * (N : ℝ) ^ (c * ξ)) /
        (c * (N : ℝ) ^ (a * (c - 1)) / 10) = K2 * (N : ℝ) ^ (c * ξ - a * (c - 1)) := by
      rw [Real.rpow_sub hNpos, hK2]
      field_simp
    linarith
  have hY1 : (1 : ℝ) ≤ (N : ℝ) ^ (1 - δ) := Real.one_le_rpow hNr (by linarith)
  have hYa : (N : ℝ) ^ a ≤ (N : ℝ) ^ (1 - δ) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have hYb : (N : ℝ) ^ (c * ξ - a * (c - 1)) ≤ (N : ℝ) ^ (1 - δ) :=
    Real.rpow_le_rpow_of_exponent_le hNr (by linarith)
  have hn0r : (0 : ℝ) ≤ n0 := Nat.cast_nonneg _
  have t1 : (n0 : ℝ) ≤ n0 * (N : ℝ) ^ (1 - δ) := by nlinarith
  have t2 : K2 * (N : ℝ) ^ (c * ξ - a * (c - 1)) ≤ K2 * (N : ℝ) ^ (1 - δ) :=
    mul_le_mul_of_nonneg_left hYb hK2'
  calc (B.card : ℝ) ≤ n1 + L.card := hBcard
    _ ≤ (n0 + (N : ℝ) ^ a + 1) + K2 * (N : ℝ) ^ (c * ξ - a * (c - 1)) := by linarith
    _ ≤ ((n0 : ℝ) + 2 + K2) * (N : ℝ) ^ (1 - δ) := by nlinarith

open Real in
/-- **Golden ratio from the discrete exceptional hypothesis.** The condition
`φ θ < φ - 1` means `θ < 1/φ²`. The cited literature covers `1/3 < θ < 1/φ²`. -/
theorem mills_goldenRatio_of_discreteExc (θ ξ K0 : ℝ) (hθ0 : 0 < θ)
    (hθ : goldenRatio * θ < goldenRatio - 1) (hξ0 : 0 ≤ ξ) (hξ1 : ξ < 1) (hK0 : 0 ≤ K0)
    (h : DiscreteExcHyp θ ξ K0) :
    ∃ B : ℝ, ∀ k, (⌊B ^ goldenRatio ^ k⌋₊).Prime := by
  have hφ2 := goldenRatio_lt_two
  obtain ⟨δ, K, hδ0, hδ1, hK, hexc⟩ :=
    hexc_of_discreteExc one_lt_goldenRatio hθ0 hθ (by linarith) hξ0 hξ1 hK0 h
  exact mills_goldenRatio δ K hδ0 hδ1 hK hexc

end MillsForest
