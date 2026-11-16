import MillsForest.Share

/-!
# Closing the recursion for a constant ratio `c > 1` (in particular `c = φ`)

Exponents `C k = c^k`. The roots are **all** integers in `[Y, 2Y]`; primality is required
from level `1` on, and at the end we pass from `A` to `B = A^c`.

The single analytic hypothesis is an exceptional-set bound in counting form:

  `#{n ≤ N : the interval of n has fewer than ℓ(n)/(5 log (n+1)^c) primes} ≤ K N^{1-δ}`

for every `N ≥ 1`. Here `ℓ(n) = (n+1)^c - n^c`. This is what the literature provides when
`μ(1 - 1/c) < 1`; the passage from `μ` to this count is the informal Markov step of the
paper.

Everything else is proved here: the choice of `ν, β, L`, the recursion, and the existence
of a suitable `Y`.
-/

open Finset Real Filter

namespace MillsForest

section Const

variable (c : ℝ)

/-- The exponent sequence `C k = c^k`. -/
noncomputable def powSeq (k : ℕ) : ℝ := c ^ k

variable {c}

lemma powSeq_pos (hc : 1 < c) (k : ℕ) : 0 < powSeq c k := pow_pos (by linarith) k
lemma powSeq_one_le (hc : 1 < c) (k : ℕ) : 1 ≤ powSeq c k := one_le_pow₀ hc.le
lemma powSeq_mono (hc : 1 < c) (k : ℕ) : powSeq c k ≤ powSeq c (k + 1) :=
  pow_le_pow_right₀ hc.le (Nat.le_succ k)
lemma powSeq_zero : powSeq c 0 = 1 := pow_zero c
lemma powSeq_succ (k : ℕ) : powSeq c (k + 1) = powSeq c k * c := pow_succ c k

lemma ratio_powSeq (hc : 1 < c) (k : ℕ) : ratio (powSeq c) k = c := by
  have h := (powSeq_pos hc k).ne'
  unfold ratio; rw [powSeq_succ]; field_simp

lemma kids_powSeq (hc : 1 < c) (k n : ℕ) : kids (powSeq c) k n = kids (powSeq c) 0 n := by
  unfold kids; rw [ratio_powSeq hc k, ratio_powSeq hc 0]

variable (c)

/-- The exceptional property: the child interval of `n` has too few primes. -/
def badc (n : ℕ) : Prop :=
  ((kids (powSeq c) 0 n).card : ℝ) <
    (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / (5 * Real.log (((n : ℝ) + 1) ^ c))

noncomputable instance badc_dec : DecidablePred (badc c) := fun n => by
  unfold badc; infer_instance

/-- The forest whose roots are all the integers of `[Y, 2Y]`. -/
noncomputable def icForest (Y : ℕ) : WForest := ⟨Finset.Icc Y (2 * Y), kids (powSeq c)⟩

variable {c}

lemma level_range_ic (hc : 1 < c) (Y : ℕ) :
    ∀ k, ∀ p ∈ (icForest c Y).level k,
      ((Y : ℝ) ^ powSeq c k ≤ p ∧ (p : ℝ) + 1 ≤ ((2 * Y + 1 : ℕ) : ℝ) ^ powSeq c k) := by
  have hC := powSeq_pos hc
  intro k
  induction k with
  | zero =>
    intro p hp
    simp only [WForest.level, icForest, Finset.mem_Icc] at hp
    rw [powSeq_zero, Real.rpow_one, Real.rpow_one]
    obtain ⟨h1, h2⟩ := hp
    constructor
    · exact_mod_cast h1
    · push_cast; have : (p : ℝ) ≤ 2 * Y := by exact_mod_cast h2
      linarith
  | succ k ih =>
    intro q hq
    simp only [WForest.level, Finset.mem_biUnion] at hq
    obtain ⟨p, hp, hqp⟩ := hq
    obtain ⟨hp1, hp2⟩ := ih p hp
    obtain ⟨-, hq1, hq2⟩ := mem_kids (powSeq c) hC hqp
    have hr := (ratio_pos (powSeq c) hC k).le
    have hrat : powSeq c k * ratio (powSeq c) k = powSeq c (k + 1) := by
      unfold ratio; field_simp [(hC k).ne']
    constructor
    · calc (Y : ℝ) ^ powSeq c (k + 1) = ((Y : ℝ) ^ powSeq c k) ^ ratio (powSeq c) k := by
            rw [← Real.rpow_mul (Nat.cast_nonneg _), hrat]
        _ ≤ (p : ℝ) ^ ratio (powSeq c) k := Real.rpow_le_rpow (by positivity) hp1 hr
        _ ≤ q := hq1
    · calc (q : ℝ) + 1 ≤ ((p : ℝ) + 1) ^ ratio (powSeq c) k := hq2.le
        _ ≤ ((((2 * Y + 1 : ℕ) : ℝ)) ^ powSeq c k) ^ ratio (powSeq c) k :=
            Real.rpow_le_rpow (by positivity) hp2 hr
        _ = (((2 * Y + 1 : ℕ) : ℝ)) ^ powSeq c (k + 1) := by
            rw [← Real.rpow_mul (Nat.cast_nonneg _), hrat]

lemma level_sub_Rk_ic (hc : 1 < c) (Y k : ℕ) :
    (icForest c Y).level k ⊆ Rk (powSeq c) Y k := by
  intro p hp
  obtain ⟨h1, h2⟩ := level_range_ic hc Y k p hp
  unfold Rk
  rw [Finset.mem_Icc]
  exact ⟨Nat.ceil_le.mpr h1, Nat.le_floor (by linarith)⟩

/-- The forest theorem for `C k = c^k` with roots `[Y, 2Y]`. -/
theorem ic_exists (hc : 1 < c) (Y : ℕ) (hY : 1 ≤ Y) (ν β L : ℕ → ℝ) (hν : ∀ k, 0 ≤ ν k)
    (hL0 : L 0 ≤ (Y : ℝ) + 1) (hLpos : ∀ k, 0 < L k) (hβ : ∀ k, β k ≤ L k / 2)
    (hLsucc : ∀ k, L (k + 1) ≤ (ν k * (1 / 3 : ℝ) ^ ratio (powSeq c) k) * (L k / 2))
    (hbadC : ∀ k, ∑ n ∈ (Rk (powSeq c) Y k).filter (fun n : ℕ =>
        decide (ν k * (((n : ℝ) + 1) ^ ratio (powSeq c) k - (n : ℝ) ^ ratio (powSeq c) k) ≤
          ((kids (powSeq c) k n).card : ℝ)) = false), wt (powSeq c) k n ≤ β k) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ k, (⌊A ^ powSeq c (k + 1)⌋₊).Prime := by
  have hC : ∀ k, 0 < powSeq c k := powSeq_pos hc
  have hC1 : ∀ k, 1 ≤ powSeq c k := powSeq_one_le hc
  have hCm : ∀ k, powSeq c k ≤ powSeq c (k + 1) := powSeq_mono hc
  let F := icForest c Y
  let f : ℕ → ℝ := fun k => ν k * (1 / 3 : ℝ) ^ ratio (powSeq c) k
  let good : ℕ → ℕ → Bool := fun k n =>
    decide (f k * wt (powSeq c) k n ≤ ∑ q ∈ kids (powSeq c) k n, wt (powSeq c) (k + 1) q)
  have hw : ∀ k n, 0 ≤ wt (powSeq c) k n := wt_nonneg (powSeq c) hC
  have hf : ∀ k, 0 ≤ f k := fun k => by have := hν k; positivity
  have hdisj : ∀ k, Set.PairwiseDisjoint (↑(F.level k) : Set ℕ) (F.children k) :=
    fun k => kids_disjoint (powSeq c) hC k _
  have hgood : ∀ k, ∀ p ∈ F.level k, good k p = true →
      f k * wt (powSeq c) k p ≤ ∑ q ∈ F.children k p, wt (powSeq c) (k + 1) q :=
    fun k p _ h => of_decide_eq_true h
  have hbad : ∀ k, ∑ p ∈ (F.level k).filter (fun p => good k p = false),
      wt (powSeq c) k p ≤ β k := by
    intro k
    refine le_trans ?_ (hbadC k)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · intro n hn
      rw [Finset.mem_filter] at hn ⊢
      refine ⟨level_sub_Rk_ic hc Y k hn.1, ?_⟩
      have hn1 : 1 ≤ n := by
        obtain ⟨h1, -⟩ := level_range_ic hc Y k n hn.1
        have hY1 : (1 : ℝ) ≤ (Y : ℝ) ^ powSeq c k :=
          Real.one_le_rpow (by exact_mod_cast hY) (hC k).le
        have : (1 : ℝ) ≤ n := le_trans hY1 h1
        exact_mod_cast this
      have hnot : ¬ (f k * wt (powSeq c) k n ≤
          ∑ q ∈ kids (powSeq c) k n, wt (powSeq c) (k + 1) q) :=
        decide_eq_false_iff_not.mp hn.2
      apply decide_eq_false_iff_not.mpr
      intro hcon
      exact hnot (kids_share (powSeq c) hC hC1 hCm k n hn1 (ν k) (hν k) hcon)
    · intro n _ _; exact hw k n
  have hmass0 : F.mass (wt (powSeq c)) 0 = (Y : ℝ) + 1 := by
    unfold WForest.mass
    have h1 : ∀ n, wt (powSeq c) 0 n = 1 := by
      intro n; unfold wt; rw [powSeq_zero]; simp
    simp only [h1, Finset.sum_const, nsmul_eq_mul, mul_one]
    show ((Finset.Icc Y (2 * Y)).card : ℝ) = (Y : ℝ) + 1
    rw [Nat.card_Icc]
    have : 2 * Y + 1 - Y = Y + 1 := by omega
    rw [this]; push_cast; ring
  have hne := F.levels_nonempty (wt (powSeq c)) good f β L hw hf hdisj hgood hbad
    (by rw [hmass0]; exact hL0) hLpos hβ hLsucc
  obtain ⟨p, hp0, hpath⟩ := F.exists_path hne
  have hchain := fun k => mem_kids (powSeq c) hC (hpath k)
  obtain ⟨A, hA⟩ := mills_of_chain (powSeq c) hC p (fun k => (hchain k).2.1)
    (fun k => (hchain k).2.2)
  refine ⟨A, ?_, fun k => ?_⟩
  · have h0 := hA 0
    rw [powSeq_zero, Real.rpow_one] at h0
    have hp0' : p 0 ∈ Finset.Icc Y (2 * Y) := hp0
    rw [Finset.mem_Icc] at hp0'
    have : 0 < ⌊A⌋₊ := by omega
    exact Nat.floor_pos.mp this
  · rw [hA (k + 1)]
    exact (hchain k).1

/-! ### The concrete choice of `ν, β, L` -/

variable (c)

/-- `ν_k = 1/(5 c^{k+1} log(2Y+2))`. -/
noncomputable def nuSeq (Y k : ℕ) : ℝ := 1 / (5 * (c ^ (k + 1) * Real.log (2 * (Y : ℝ) + 2)))

/-- `L_0 = Y+1`, `L_{k+1} = ν_k 3^{-c} L_k / 2`. -/
noncomputable def LSeq (Y : ℕ) : ℕ → ℝ
  | 0 => (Y : ℝ) + 1
  | k + 1 => nuSeq c Y k * (1 / 3 : ℝ) ^ c * (LSeq Y k / 2)

/-- `q = (2Y+1)^{1-δ} / Y`. -/
noncomputable def qY (δ : ℝ) (Y : ℕ) : ℝ := (2 * (Y : ℝ) + 1) ^ (1 - δ) / Y

/-- `β_k = K (2Y+1) q^{c^k}`. -/
noncomputable def betaSeq (δ K : ℝ) (Y k : ℕ) : ℝ := K * (2 * (Y : ℝ) + 1) * (qY δ Y) ^ powSeq c k

variable {c}

lemma log_pos_Y (Y : ℕ) : 0 < Real.log (2 * (Y : ℝ) + 2) :=
  Real.log_pos (by have : (0 : ℝ) ≤ Y := Nat.cast_nonneg Y; linarith)

lemma nuSeq_pos (hc : 1 < c) (Y k : ℕ) : 0 < nuSeq c Y k := by
  unfold nuSeq
  have := log_pos_Y Y
  have : 0 < c ^ (k + 1) := pow_pos (by linarith) _
  positivity

lemma LSeq_pos (hc : 1 < c) (Y k : ℕ) : 0 < LSeq c Y k := by
  induction k with
  | zero => show (0 : ℝ) < (Y : ℝ) + 1; positivity
  | succ k ih =>
    show 0 < nuSeq c Y k * (1 / 3 : ℝ) ^ c * (LSeq c Y k / 2)
    have := nuSeq_pos hc Y k
    positivity

lemma qY_pos (δ : ℝ) {Y : ℕ} (hY : 1 ≤ Y) : 0 < qY δ Y := by
  unfold qY
  have : (0 : ℝ) < Y := by exact_mod_cast hY
  positivity

/-- The step of the recursion: `q^{c^k (c-1)} ≤ ν_k 3^{-c} / 2`, from the condition `hS`. -/
lemma q_step (hc : 1 < c) (δ : ℝ) {Y : ℕ} (hY : 1 ≤ Y)
    (hS : 1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c ≤ (1 / qY δ Y) ^ (c - 1))
    (k : ℕ) :
    (qY δ Y) ^ (powSeq c k * (c - 1)) ≤ nuSeq c Y k * (1 / 3 : ℝ) ^ c / 2 := by
  have hq := qY_pos δ hY
  set a := Real.log (2 * (Y : ℝ) + 2) with ha
  have ha0 : 0 < a := log_pos_Y Y
  set u := (1 / qY δ Y) ^ (c - 1) with hu
  have hu0 : 0 ≤ u := by positivity
  have hCk := powSeq_one_le hc k
  -- Bernoulli: u^{C_k} ≥ 1 + C_k (u - 1)
  have hbern : 1 + powSeq c k * (u - 1) ≤ u ^ powSeq c k := by
    have := one_add_mul_self_le_rpow_one_add (by linarith : (-1 : ℝ) ≤ u - 1) hCk
    simpa using this
  have h3 : (0 : ℝ) < (3 : ℝ) ^ c := by positivity
  have hck : powSeq c k * c = c ^ (k + 1) := by rw [← powSeq_succ]; rfl
  have hbig : 10 * c ^ (k + 1) * a * (3 : ℝ) ^ c ≤ u ^ powSeq c k := by
    have h1 : 10 * c * a * (3 : ℝ) ^ c ≤ u - 1 := by linarith
    have h2 : powSeq c k * (10 * c * a * (3 : ℝ) ^ c) ≤ powSeq c k * (u - 1) :=
      mul_le_mul_of_nonneg_left h1 (by linarith)
    have h4 : 0 ≤ powSeq c k * (u - 1) := by
      have : 0 ≤ 10 * c * a * (3 : ℝ) ^ c := by have := hc; positivity
      nlinarith
    calc 10 * c ^ (k + 1) * a * (3 : ℝ) ^ c = powSeq c k * (10 * c * a * (3 : ℝ) ^ c) := by
          rw [← hck]; ring
      _ ≤ powSeq c k * (u - 1) := h2
      _ ≤ 1 + powSeq c k * (u - 1) := by linarith
      _ ≤ u ^ powSeq c k := hbern
  have hqx : (qY δ Y) ^ (powSeq c k * (c - 1)) = 1 / u ^ powSeq c k := by
    rw [hu, ← Real.rpow_mul (by positivity), mul_comm (c - 1),
      Real.div_rpow zero_le_one hq.le, Real.one_rpow, one_div_one_div]
  have hm : nuSeq c Y k * (1 / 3 : ℝ) ^ c / 2 = 1 / (10 * c ^ (k + 1) * a * (3 : ℝ) ^ c) := by
    unfold nuSeq
    rw [← ha, Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]
    have : 0 < c ^ (k + 1) := pow_pos (by linarith) _
    field_simp
    ring
  rw [hqx, hm]
  have hpos : 0 < 10 * c ^ (k + 1) * a * (3 : ℝ) ^ c := by
    have : 0 < c ^ (k + 1) := pow_pos (by linarith) _
    positivity
  exact one_div_le_one_div_of_le hpos hbig

lemma beta_le (hc : 1 < c) (δ K : ℝ) (hK : 0 ≤ K) {Y : ℕ} (hY : 1 ≤ Y)
    (hB0 : K * (2 * (Y : ℝ) + 1) * qY δ Y ≤ ((Y : ℝ) + 1) / 2)
    (hS : 1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c ≤ (1 / qY δ Y) ^ (c - 1)) :
    ∀ k, betaSeq c δ K Y k ≤ LSeq c Y k / 2 := by
  have hq := qY_pos δ hY
  intro k
  induction k with
  | zero =>
    unfold betaSeq; rw [powSeq_zero, Real.rpow_one]; exact hB0
  | succ k ih =>
    have hsplit : (qY δ Y) ^ powSeq c (k + 1) =
        (qY δ Y) ^ powSeq c k * (qY δ Y) ^ (powSeq c k * (c - 1)) := by
      rw [← Real.rpow_add hq, powSeq_succ]; congr 1; ring
    have hstep := q_step hc δ hY hS k
    have hpos : 0 ≤ K * (2 * (Y : ℝ) + 1) * (qY δ Y) ^ powSeq c k := by positivity
    show K * (2 * (Y : ℝ) + 1) * (qY δ Y) ^ powSeq c (k + 1) ≤
      nuSeq c Y k * (1 / 3 : ℝ) ^ c * (LSeq c Y k / 2) / 2
    rw [hsplit]
    have ih' : K * (2 * (Y : ℝ) + 1) * (qY δ Y) ^ powSeq c k ≤ LSeq c Y k / 2 := ih
    calc K * (2 * (Y : ℝ) + 1) * ((qY δ Y) ^ powSeq c k * (qY δ Y) ^ (powSeq c k * (c - 1)))
        = (K * (2 * (Y : ℝ) + 1) * (qY δ Y) ^ powSeq c k) *
            (qY δ Y) ^ (powSeq c k * (c - 1)) := by ring
      _ ≤ (LSeq c Y k / 2) * (nuSeq c Y k * (1 / 3 : ℝ) ^ c / 2) :=
          mul_le_mul ih' hstep (by positivity) (by have := LSeq_pos hc Y k; positivity)
      _ = nuSeq c Y k * (1 / 3 : ℝ) ^ c * (LSeq c Y k / 2) / 2 := by ring

/-- The bad weight at level `k` is at most `β_k`, given the exceptional-set count. -/
lemma bad_weight (hc : 1 < c) (δ K : ℝ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K) {Y : ℕ} (hY : 1 ≤ Y)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badc c n)).card : ℝ) ≤ K * (N : ℝ) ^ (1 - δ))
    (k : ℕ) :
    ∑ n ∈ (Rk (powSeq c) Y k).filter (fun n : ℕ =>
        decide (nuSeq c Y k * (((n : ℝ) + 1) ^ ratio (powSeq c) k -
          (n : ℝ) ^ ratio (powSeq c) k) ≤ ((kids (powSeq c) k n).card : ℝ)) = false),
      wt (powSeq c) k n ≤ betaSeq c δ K Y k := by
  classical
  have hC := powSeq_pos hc k
  have hC1 := powSeq_one_le hc k
  set C := powSeq c k with hCdef
  set a := Real.log (2 * (Y : ℝ) + 2) with ha
  have ha0 : 0 < a := log_pos_Y Y
  have hYr : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  set S := (Rk (powSeq c) Y k).filter (fun n : ℕ =>
        decide (nuSeq c Y k * (((n : ℝ) + 1) ^ ratio (powSeq c) k -
          (n : ℝ) ^ ratio (powSeq c) k) ≤ ((kids (powSeq c) k n).card : ℝ)) = false) with hS
  set N := ⌊((2 * Y + 1 : ℕ) : ℝ) ^ C⌋₊ with hN
  have hX1 : (1 : ℝ) ≤ ((2 * Y + 1 : ℕ) : ℝ) ^ C :=
    Real.one_le_rpow (by push_cast; linarith) hC.le
  have hN1 : 1 ≤ N := Nat.le_floor (by exact_mod_cast hX1)
  -- membership facts
  have hmem : ∀ n ∈ S, (Y : ℝ) ^ C ≤ n ∧ (n : ℝ) ≤ ((2 * Y + 1 : ℕ) : ℝ) ^ C ∧ n ≤ N := by
    intro n hn
    rw [hS, Finset.mem_filter] at hn
    have h := hn.1
    unfold Rk at h
    rw [Finset.mem_Icc] at h
    refine ⟨Nat.ceil_le.mp h.1, le_trans (by exact_mod_cast h.2) (Nat.floor_le (by positivity)), h.2⟩
  -- S ⊆ bad set in range (N+1)
  have hsub : S ⊆ (Finset.range (N + 1)).filter (fun n => badc c n) := by
    intro n hn
    obtain ⟨hlo, hhi, hnN⟩ := hmem n hn
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [hS, Finset.mem_filter] at hn
    have hnot := decide_eq_false_iff_not.mp hn.2
    rw [not_le, ratio_powSeq hc k, kids_powSeq hc k n] at hnot
    have hn1 : (1 : ℝ) ≤ n := le_trans (Real.one_le_rpow hYr hC.le) hlo
    have hnp : (0 : ℝ) < n := by linarith
    have hℓ : 0 ≤ ((n : ℝ) + 1) ^ c - (n : ℝ) ^ c := by
      have := Real.rpow_le_rpow (by linarith) (by linarith : (n : ℝ) ≤ n + 1) (by linarith : (0 : ℝ) ≤ c)
      linarith
    -- n+1 ≤ (2Y+2)^C
    have hn2 : (n : ℝ) + 1 ≤ (2 * (Y : ℝ) + 2) ^ C := by
      have hd := diff_ge_conv (by positivity : (0 : ℝ) < 2 * Y + 1) hC1
      have hone : 1 ≤ C * (2 * (Y : ℝ) + 1) ^ (C - 1) := by
        have : 1 ≤ (2 * (Y : ℝ) + 1) ^ (C - 1) := Real.one_le_rpow (by linarith) (by linarith)
        nlinarith
      have e : (2 * (Y : ℝ) + 1) + 1 = 2 * Y + 2 := by ring
      rw [e] at hd
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
    show ((kids (powSeq c) 0 n).card : ℝ) <
      (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / (5 * Real.log (((n : ℝ) + 1) ^ c))
    calc ((kids (powSeq c) 0 n).card : ℝ) < nuSeq c Y k * (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) := hnot
      _ = (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / (5 * (c ^ (k + 1) * a)) := by
          unfold nuSeq; rw [← ha]; ring
      _ ≤ (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / (5 * Real.log (((n : ℝ) + 1) ^ c)) := by
          apply div_le_div_of_nonneg_left hℓ (by positivity) (by linarith)
  -- weight bound
  have hwt : ∀ n ∈ S, wt (powSeq c) k n ≤ (2 * (Y : ℝ) + 1) / (Y : ℝ) ^ C := by
    intro n hn
    obtain ⟨hlo, hhi, -⟩ := hmem n hn
    have hYC : 0 < (Y : ℝ) ^ C := by positivity
    have hnp : (0 : ℝ) < n := lt_of_lt_of_le hYC hlo
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
    have h3 : (1 / C) * ((n : ℝ) ^ (1 / C) / n) ≤ (n : ℝ) ^ (1 / C) / n := by
      have : 0 ≤ (n : ℝ) ^ (1 / C) / n := by positivity
      nlinarith
    calc wt (powSeq c) k n ≤ (n : ℝ) ^ (1 / C) / n := le_trans h1 h3
      _ ≤ (2 * (Y : ℝ) + 1) / n := div_le_div_of_nonneg_right h2 hnp.le
      _ ≤ (2 * (Y : ℝ) + 1) / (Y : ℝ) ^ C := div_le_div_of_nonneg_left (by positivity) hYC hlo
  -- assemble
  have hcard : (S.card : ℝ) ≤ K * (((2 * Y + 1 : ℕ) : ℝ) ^ C) ^ (1 - δ) := by
    have h1 : (S.card : ℝ) ≤ (((Finset.range (N + 1)).filter (fun n => badc c n)).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 := hexc N hN1
    have h3 : (N : ℝ) ^ (1 - δ) ≤ (((2 * Y + 1 : ℕ) : ℝ) ^ C) ^ (1 - δ) :=
      Real.rpow_le_rpow (Nat.cast_nonneg _) (Nat.floor_le (by positivity)) (by linarith)
    calc (S.card : ℝ) ≤ _ := h1
      _ ≤ K * (N : ℝ) ^ (1 - δ) := h2
      _ ≤ _ := mul_le_mul_of_nonneg_left h3 hK
  have hsum : ∑ n ∈ S, wt (powSeq c) k n ≤ S.card * ((2 * (Y : ℝ) + 1) / (Y : ℝ) ^ C) := by
    have := Finset.sum_le_card_nsmul S (wt (powSeq c) k) _ hwt
    rwa [nsmul_eq_mul] at this
  have heq : K * (((2 * Y + 1 : ℕ) : ℝ) ^ C) ^ (1 - δ) * ((2 * (Y : ℝ) + 1) / (Y : ℝ) ^ C) =
      betaSeq c δ K Y k := by
    unfold betaSeq qY
    rw [← hCdef]
    have hYp : (0 : ℝ) < Y := by linarith
    rw [Real.div_rpow (by positivity) hYp.le, ← Real.rpow_mul (by positivity),
      ← Real.rpow_mul (by positivity)]
    push_cast
    rw [mul_comm C (1 - δ)]
    have : (0 : ℝ) < (Y : ℝ) ^ C := by positivity
    field_simp
  calc ∑ n ∈ S, wt (powSeq c) k n ≤ S.card * ((2 * (Y : ℝ) + 1) / (Y : ℝ) ^ C) := hsum
    _ ≤ K * (((2 * Y + 1 : ℕ) : ℝ) ^ C) ^ (1 - δ) * ((2 * (Y : ℝ) + 1) / (Y : ℝ) ^ C) :=
        mul_le_mul_of_nonneg_right hcard (by positivity)
    _ = betaSeq c δ K Y k := heq

/-- **Conditional existence for a fixed `Y`.** -/
theorem exists_of_Y (hc : 1 < c) (δ K : ℝ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badc c n)).card : ℝ) ≤ K * (N : ℝ) ^ (1 - δ))
    (Y : ℕ) (hY : 1 ≤ Y)
    (hB0 : K * (2 * (Y : ℝ) + 1) * qY δ Y ≤ ((Y : ℝ) + 1) / 2)
    (hS : 1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c ≤ (1 / qY δ Y) ^ (c - 1)) :
    ∃ B : ℝ, ∀ k, (⌊B ^ c ^ k⌋₊).Prime := by
  obtain ⟨A, hA1, hA⟩ := ic_exists hc Y hY (nuSeq c Y) (betaSeq c δ K Y) (LSeq c Y)
    (fun k => (nuSeq_pos hc Y k).le) (le_refl _) (LSeq_pos hc Y)
    (beta_le hc δ K hK hY hB0 hS)
    (fun k => by rw [ratio_powSeq hc k]; exact le_refl _)
    (bad_weight hc δ K hδ1 hK hY hexc)
  refine ⟨A ^ c, fun k => ?_⟩
  have hA0 : 0 ≤ A := by linarith
  have e : (A ^ c) ^ (c ^ k) = A ^ powSeq c (k + 1) := by
    rw [← Real.rpow_mul hA0, powSeq_succ, mul_comm]
    rfl
  rw [e]
  exact hA k

/-- A suitable `Y` exists. -/
lemma exists_Y (hc : 1 < c) (δ K : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K) :
    ∃ Y : ℕ, 1 ≤ Y ∧ K * (2 * (Y : ℝ) + 1) * qY δ Y ≤ ((Y : ℝ) + 1) / 2 ∧
      1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c ≤ (1 / qY δ Y) ^ (c - 1) := by
  set ε := δ * (c - 1) with hε
  have hε0 : 0 < ε := mul_pos hδ (by linarith)
  set B := (3 : ℝ) ^ (c - 1) * (10 * c * (3 : ℝ) ^ c) with hB
  have hB0 : 0 < B := by positivity
  set A0 := (3 : ℝ) ^ (c - 1) * (1 + 10 * c * (3 : ℝ) ^ c * Real.log 4) with hA0
  -- eventually: B log x ≤ x^ε / 2
  have hlo := (isLittleO_log_rpow_atTop hε0).def (by positivity : (0 : ℝ) < 1 / (2 * B))
  have hev1 : ∀ᶠ x : ℝ in atTop, B * Real.log x ≤ x ^ ε / 2 := by
    filter_upwards [hlo, eventually_gt_atTop (1 : ℝ)] with x hx hx1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hx1.le),
      abs_of_nonneg (by positivity)] at hx
    have : B * Real.log x ≤ B * (1 / (2 * B) * x ^ ε) := mul_le_mul_of_nonneg_left hx hB0.le
    calc B * Real.log x ≤ B * (1 / (2 * B) * x ^ ε) := this
      _ = x ^ ε / 2 := by field_simp
  have hev2 : ∀ᶠ x : ℝ in atTop, 2 * A0 ≤ x ^ ε :=
    (tendsto_rpow_atTop hε0).eventually (eventually_ge_atTop _)
  have hev3 : ∀ᶠ x : ℝ in atTop, 18 * K + 1 ≤ x ^ δ :=
    (tendsto_rpow_atTop hδ).eventually (eventually_ge_atTop _)
  have hev := (hev1.and (hev2.and (hev3.and (eventually_ge_atTop (1 : ℝ)))))
  obtain ⟨Y, hYev, hY1⟩ := ((tendsto_natCast_atTop_atTop.eventually hev).and
    (eventually_ge_atTop 1)).exists
  obtain ⟨h1, h2, h3, h4⟩ := hYev
  have hYpos : (0 : ℝ) < Y := by linarith
  have hYd : 0 < (Y : ℝ) ^ δ := by positivity
  have hYdne := hYd.ne'
  have hq_le : qY δ Y ≤ 3 / (Y : ℝ) ^ δ := by
    unfold qY
    have e1 : (2 * (Y : ℝ) + 1) ^ (1 - δ) ≤ (3 * (Y : ℝ)) ^ (1 - δ) :=
      Real.rpow_le_rpow (by positivity) (by linarith) (by linarith)
    have e2 : (3 * (Y : ℝ)) ^ (1 - δ) = (3 : ℝ) ^ (1 - δ) * (Y : ℝ) ^ (1 - δ) :=
      Real.mul_rpow (by norm_num) hYpos.le
    have e3 : (3 : ℝ) ^ (1 - δ) ≤ 3 := by
      calc (3 : ℝ) ^ (1 - δ) ≤ (3 : ℝ) ^ (1 : ℝ) :=
            Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
        _ = 3 := Real.rpow_one 3
    have e4 : (Y : ℝ) ^ (1 - δ) = Y / (Y : ℝ) ^ δ := by rw [Real.rpow_sub hYpos, Real.rpow_one]
    rw [div_le_div_iff₀ hYpos hYd]
    calc (2 * (Y : ℝ) + 1) ^ (1 - δ) * (Y : ℝ) ^ δ
        ≤ (3 : ℝ) ^ (1 - δ) * (Y : ℝ) ^ (1 - δ) * (Y : ℝ) ^ δ := by
          rw [← e2]; exact mul_le_mul_of_nonneg_right e1 hYd.le
      _ = (3 : ℝ) ^ (1 - δ) * Y := by rw [e4]; field_simp
      _ ≤ 3 * Y := mul_le_mul_of_nonneg_right e3 hYpos.le
  have hq0 := qY_pos δ hY1
  refine ⟨Y, hY1, ?_, ?_⟩
  · calc K * (2 * (Y : ℝ) + 1) * qY δ Y ≤ K * (3 * Y) * (3 / (Y : ℝ) ^ δ) := by
          apply mul_le_mul (mul_le_mul_of_nonneg_left (by linarith) hK) hq_le hq0.le
          positivity
      _ = 9 * K * Y / (Y : ℝ) ^ δ := by field_simp <;> ring
      _ ≤ 9 * K * Y / (18 * K + 1) :=
          div_le_div_of_nonneg_left (by positivity) (by positivity) h3
      _ ≤ (Y : ℝ) / 2 := by
          rw [div_le_div_iff₀ (by positivity) (by norm_num)]; nlinarith
      _ ≤ ((Y : ℝ) + 1) / 2 := by linarith
  · have hinv : (Y : ℝ) ^ δ / 3 ≤ 1 / qY δ Y := by
      rw [div_le_div_iff₀ (by norm_num) hq0]
      calc (Y : ℝ) ^ δ * qY δ Y ≤ (Y : ℝ) ^ δ * (3 / (Y : ℝ) ^ δ) :=
            mul_le_mul_of_nonneg_left hq_le hYd.le
        _ = 1 * 3 := by field_simp
    have hpow : (Y : ℝ) ^ ε / (3 : ℝ) ^ (c - 1) ≤ (1 / qY δ Y) ^ (c - 1) := by
      have := Real.rpow_le_rpow (by positivity) hinv (by linarith : (0 : ℝ) ≤ c - 1)
      rw [Real.div_rpow hYd.le (by norm_num), ← Real.rpow_mul hYpos.le] at this
      exact this
    have hlog : Real.log (2 * (Y : ℝ) + 2) ≤ Real.log 4 + Real.log Y := by
      rw [← Real.log_mul (by norm_num) hYpos.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    have h3c : (0 : ℝ) < (3 : ℝ) ^ (c - 1) := by positivity
    have key : (1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c) * (3 : ℝ) ^ (c - 1) ≤
        (Y : ℝ) ^ ε := by
      have hBlog : 0 ≤ 10 * c * (3 : ℝ) ^ c * (3 : ℝ) ^ (c - 1) := by
        have : (0 : ℝ) < c := by linarith
        positivity
      have hh : (1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c) * (3 : ℝ) ^ (c - 1)
          ≤ A0 + B * Real.log Y := by
        rw [hA0, hB]
        nlinarith [mul_le_mul_of_nonneg_left hlog hBlog]
      linarith
    calc 1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c
        ≤ (Y : ℝ) ^ ε / (3 : ℝ) ^ (c - 1) := by rw [le_div_iff₀ h3c]; exact key
      _ ≤ (1 / qY δ Y) ^ (c - 1) := hpow

end Const

/-- **Any constant ratio `c > 1`.** Under an exceptional-set bound of power-saving type for
the intervals `[n^c, (n+1)^c)`, there is `B` with `⌊B^{c^k}⌋` prime for every `k ≥ 0`. -/
theorem mills_const {c : ℝ} (hc : 1 < c) (δ K : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badc c n)).card : ℝ) ≤ K * (N : ℝ) ^ (1 - δ)) :
    ∃ B : ℝ, ∀ k, (⌊B ^ c ^ k⌋₊).Prime := by
  obtain ⟨Y, hY, hB0, hS⟩ := exists_Y hc δ K hδ hδ1 hK
  exact exists_of_Y hc δ K hδ1 hK hexc Y hY hB0 hS

open Real in
/-- **Golden ratio.** Under an exceptional-set bound of power-saving type for the
intervals `[n^φ, (n+1)^φ)`, there is `B` with `⌊B^{φ^k}⌋` prime for every `k ≥ 0`. -/
theorem mills_goldenRatio (δ K : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badc goldenRatio n)).card : ℝ) ≤
        K * (N : ℝ) ^ (1 - δ)) :
    ∃ B : ℝ, ∀ k, (⌊B ^ goldenRatio ^ k⌋₊).Prime := by
  obtain ⟨Y, hY, hB0, hS⟩ := exists_Y one_lt_goldenRatio δ K hδ hδ1 hK
  exact exists_of_Y one_lt_goldenRatio δ K hδ1 hK hexc Y hY hB0 hS

end MillsForest
