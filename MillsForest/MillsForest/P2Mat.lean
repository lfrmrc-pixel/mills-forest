import MillsForest.P2
import MillsForest.Exc

/-!
# Tappa 4: from Matomäki's theorem (measure form) to the counting hypothesis for `P2`

`MatomakiHyp` is the faithful statement of Matomäki's theorem (paper, Theorem `thm:Mat22`;
Matomäki, JLMS 2022, Thm 1.1) specialised to `h = X^θ'`: for `X ≥ 2` with
`2 ≤ h ≤ X^{1/100}`, the set of `x ∈ (X/2, X]` with
`#{x - h log X < m ≤ x : Ω(m) ≤ 2, p ∣ m ⇒ p > X^{1/8}} < c_M h` has measure `≤ K X / h`.

Proof (paper, proof of `thm:P2`, steps (ii)–(iii)), arranged as in `Exc.lean`/`Lit.lean`:
* (A) measure → integers. Each integer `x ≥ 1` gets its own dyadic scale
  `matX x = 2^(⌊log₂ x⌋ + 1)`, so `(x, x+1) ⊆ (matX x / 2, matX x]`. An integer is
  exceptional (`excD`) if Matomäki's count at `x` itself is `< c_M h`; then the whole open
  unit interval `(x, x+1)` lies in the exceptional set (the count only decreases inside it).
  Summing the dyadic blocks gives `#{x ≤ Z exceptional} ≤ K0 Z^{1-θ'}`.
* (B) window lemma: a bad `n` (few `P2` in its child interval) has at least `ℓ(n)/2`
  exceptional integers in its child interval (double counting with windows of length
  `⌈(2V)^θ' log(2V)⌉`, `V = (n+1)^c`). Because every `x` uses its own scale, there is no
  need to split `J(n)` between two dyadic blocks.
* (C) counting step, copied from `hexc_of_discreteExc` with `ξ = 1 - θ'`.

The threshold is `ν = c_M / (4 (2·2^{1+c} + 1))` (`matNu`), which depends on `c`; any
`ν > 0` is enough for `mills_P2_of_count`.
-/

open Finset Real Filter MeasureTheory

namespace MillsForest

/-! ### Matomäki's theorem -/

/-- `m` is counted by Matomäki at scale `X`: `Ω(m) ≤ 2` and every prime factor exceeds
`X^{1/8}`. -/
def MatP (X : ℝ) (m : ℕ) : Prop :=
  ArithmeticFunction.cardFactors m ≤ 2 ∧ ∀ p : ℕ, p.Prime → p ∣ m → X ^ (1 / 8 : ℝ) < p

/-- `N_X(x; h) = #{m ∈ ℕ : x - h log X < m ≤ x, Ω(m) ≤ 2, p ∣ m ⇒ p > X^{1/8}}`. -/
noncomputable def matCount (X h x : ℝ) : ℕ := by
  classical
  exact ((Finset.range (⌊x⌋₊ + 1)).filter
    (fun m : ℕ => x - h * Real.log X < m ∧ (m : ℝ) ≤ x ∧ MatP X m)).card

/-- The exceptional set `E_X(h) = {x ∈ (X/2, X] : N_X(x; h) < c_M h}`. -/
def matExc (cM X h : ℝ) : Set ℝ :=
  {x | x ∈ Set.Ioc (X / 2) X ∧ (matCount X h x : ℝ) < cM * h}

/-- **Matomäki's hypothesis** with `h = X^θ'` (one-sided count, window `(x - h log X, x]`,
exceptional measure `≤ K X / h`), for every `X ≥ 2` with `2 ≤ h ≤ X^{1/100}`. -/
def MatomakiHyp (θ' cM K : ℝ) : Prop :=
  ∀ X : ℝ, 2 ≤ X → 2 ≤ X ^ θ' → X ^ θ' ≤ X ^ (1 / 100 : ℝ) →
    volume (matExc cM X (X ^ θ')) ≤ ENNReal.ofReal (K * X / X ^ θ')

/-! ### (A) From the measure to exceptional integers -/

/-- The dyadic scale of `x`: `2^(⌊log₂ x⌋ + 1)`. -/
noncomputable def matX (x : ℕ) : ℝ := (2 : ℝ) ^ (Nat.log 2 x + 1)

/-- Exceptional integer: Matomäki's count at `x`, at the scale `matX x`, is `< c_M h`. -/
def excD (cM θ' : ℝ) (x : ℕ) : Prop :=
  (matCount (matX x) (matX x ^ θ') x : ℝ) < cM * matX x ^ θ'

noncomputable instance excD_dec (cM θ' : ℝ) : DecidablePred (excD cM θ') := fun x => by
  unfold excD; infer_instance

lemma matX_bounds {x : ℕ} (hx : 1 ≤ x) :
    (2 : ℝ) ^ Nat.log 2 x ≤ x ∧ (x : ℝ) + 1 ≤ matX x ∧ matX x ≤ 2 * x := by
  have h1 : 2 ^ Nat.log 2 x ≤ x := Nat.pow_log_le_self 2 (by omega)
  have h2 : x < 2 ^ (Nat.log 2 x + 1) := Nat.lt_pow_succ_log_self (by norm_num) x
  unfold matX
  refine ⟨by exact_mod_cast h1, ?_, ?_⟩
  · have : x + 1 ≤ 2 ^ (Nat.log 2 x + 1) := h2
    exact_mod_cast this
  · rw [pow_succ]
    have : ((2 ^ Nat.log 2 x : ℕ) : ℝ) ≤ x := by exact_mod_cast h1
    push_cast at this
    linarith

/-- Inside `[x, x + 1)` Matomäki's count is at most its value at `x`. -/
lemma matCount_shift {X h t : ℝ} {x : ℕ} (ht1 : (x : ℝ) ≤ t) (ht2 : t < x + 1) :
    matCount X h t ≤ matCount X h x := by
  classical
  unfold matCount
  apply Finset.card_le_card
  intro m hm
  rw [Finset.mem_filter, Finset.mem_range] at hm ⊢
  obtain ⟨-, h1, h2, h3⟩ := hm
  have hmx : (m : ℝ) < x + 1 := lt_of_le_of_lt h2 ht2
  have hmx' : m ≤ x := by
    have : m < x + 1 := by exact_mod_cast hmx
    omega
  refine ⟨?_, by linarith, by exact_mod_cast hmx', h3⟩
  rw [Nat.floor_natCast]; omega

lemma Ioo_sub_matExc {cM θ' : ℝ} {x : ℕ} (hx : 1 ≤ x) (he : excD cM θ' x) :
    Set.Ioo (x : ℝ) (x + 1) ⊆ matExc cM (matX x) (matX x ^ θ') := by
  intro t ht
  obtain ⟨ht1, ht2⟩ := ht
  obtain ⟨hb1, hb2, -⟩ := matX_bounds hx
  refine ⟨⟨?_, by linarith⟩, ?_⟩
  · have : matX x / 2 = (2 : ℝ) ^ Nat.log 2 x := by unfold matX; rw [pow_succ]; ring
    rw [this]; linarith
  · refine lt_of_le_of_lt ?_ he
    exact_mod_cast matCount_shift ht1.le ht2

lemma two_pow_rpow (j : ℕ) (ξ : ℝ) : ((2 : ℝ) ^ j) ^ ξ = ((2 : ℝ) ^ ξ) ^ j := by
  rw [← Real.rpow_natCast, ← Real.rpow_natCast, ← Real.rpow_mul (by norm_num),
    ← Real.rpow_mul (by norm_num), mul_comm]

/-- **(A)** Matomäki's measure bound gives `#{1 ≤ x ≤ Z : excD x} ≤ K0 Z^{1-θ'}`. -/
theorem discrete_of_Matomaki {θ' cM K : ℝ} (hθ0 : 0 < θ') (hθ1 : θ' < 1 / 100) (hK : 0 ≤ K)
    (hM : MatomakiHyp θ' cM K) :
    ∃ K0 : ℝ, 0 ≤ K0 ∧ ∀ Z : ℕ, 1 ≤ Z →
      (((Finset.Icc 1 Z).filter (excD cM θ')).card : ℝ) ≤ K0 * (Z : ℝ) ^ (1 - θ') := by
  set ξ := 1 - θ' with hξ
  have hξ0 : 0 < ξ := by linarith
  set r := (2 : ℝ) ^ ξ with hr
  have hr1 : 1 < r := Real.one_lt_rpow (by norm_num) hξ0
  set X0 := (2 : ℝ) ^ (1 / θ') with hX0
  have hX0pos : 0 ≤ X0 := by positivity
  set C0 := (K + X0) * r with hC0
  have hC00 : 0 ≤ C0 := by positivity
  set C := C0 * r / (r - 1) with hC
  have hC0' : 0 ≤ C := by
    have : 0 < r - 1 := by linarith
    positivity
  refine ⟨C, hC0', fun Z hZ => ?_⟩
  set E := (Finset.Icc 1 Z).filter (excD cM θ') with hE
  set J := Nat.log 2 Z with hJ
  have hfib : E.card = ∑ j ∈ Finset.range (J + 1), (E.filter (fun x => Nat.log 2 x = j)).card := by
    apply Finset.card_eq_sum_card_fiberwise
    intro x hx
    rw [Finset.mem_coe, hE, Finset.mem_filter, Finset.mem_Icc] at hx
    rw [Finset.mem_coe, Finset.mem_range]
    exact Nat.lt_succ_of_le (Nat.log_mono_right hx.1.2)
  have hblock : ∀ j : ℕ, ((E.filter (fun x => Nat.log 2 x = j)).card : ℝ) ≤ C0 * r ^ j := by
    intro j
    set D := E.filter (fun x => Nat.log 2 x = j) with hD
    set X := (2 : ℝ) ^ (j + 1) with hXdef
    have hX2 : (2 : ℝ) ≤ X := by
      rw [hXdef, pow_succ]
      have : (1 : ℝ) ≤ 2 ^ j := one_le_pow₀ (by norm_num)
      linarith
    have hXpos : 0 < X := by linarith
    have hXξ : X ^ ξ = r * r ^ j := by
      rw [hXdef, two_pow_rpow, ← hr, pow_succ']
    have hcover : (⋃ x ∈ D, Set.Ioo (x : ℝ) (x + 1)) ⊆ matExc cM X (X ^ θ') := by
      intro t ht
      simp only [Set.mem_iUnion] at ht
      obtain ⟨x, hx, htx⟩ := ht
      rw [hD, Finset.mem_filter, hE, Finset.mem_filter, Finset.mem_Icc] at hx
      obtain ⟨⟨⟨hx1, -⟩, hex⟩, hlog⟩ := hx
      have hmx : matX x = X := by unfold matX; rw [hlog]
      have := Ioo_sub_matExc hx1 hex htx
      rwa [hmx] at this
    have hdisj : Set.PairwiseDisjoint (↑D) (fun x : ℕ => Set.Ioo (x : ℝ) (x + 1)) := by
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
    have hvol : volume (⋃ x ∈ D, Set.Ioo (x : ℝ) (x + 1)) = (D.card : ENNReal) := by
      rw [measure_biUnion_finset hdisj (fun _ _ => measurableSet_Ioo)]
      simp only [Real.volume_Ioo, add_sub_cancel_left, ENNReal.ofReal_one, Finset.sum_const,
        nsmul_eq_mul, mul_one]
    have hbound : volume (matExc cM X (X ^ θ')) ≤ ENNReal.ofReal ((K + X0) * X ^ ξ) := by
      by_cases hX : X0 ≤ X
      · have h2 : 2 ≤ X ^ θ' := by
          have e : X0 ^ θ' = 2 := by
            rw [hX0, ← Real.rpow_mul (by norm_num), one_div_mul_cancel hθ0.ne', Real.rpow_one]
          calc (2 : ℝ) = X0 ^ θ' := e.symm
            _ ≤ X ^ θ' := Real.rpow_le_rpow hX0pos hX hθ0.le
        have h3 : X ^ θ' ≤ X ^ (1 / 100 : ℝ) :=
          Real.rpow_le_rpow_of_exponent_le (by linarith) hθ1.le
        calc volume (matExc cM X (X ^ θ')) ≤ ENNReal.ofReal (K * X / X ^ θ') := hM X hX2 h2 h3
          _ ≤ ENNReal.ofReal ((K + X0) * X ^ ξ) := by
            apply ENNReal.ofReal_le_ofReal
            have e : K * X / X ^ θ' = K * X ^ ξ := by
              rw [hξ, Real.rpow_sub hXpos, Real.rpow_one]; ring
            rw [e]
            have : 0 ≤ X ^ ξ := by positivity
            nlinarith
      · push_neg at hX
        calc volume (matExc cM X (X ^ θ')) ≤ volume (Set.Ioc (X / 2) X) :=
              measure_mono (fun t ht => ht.1)
          _ = ENNReal.ofReal (X / 2) := by rw [Real.volume_Ioc]; congr 1; ring
          _ ≤ ENNReal.ofReal ((K + X0) * X ^ ξ) := by
            apply ENNReal.ofReal_le_ofReal
            have e : X ^ θ' * X ^ ξ = X := by
              rw [← Real.rpow_add hXpos, hξ, show θ' + (1 - θ') = 1 by ring, Real.rpow_one]
            have hθX : X ^ θ' ≤ X := by
              have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ X)
                (by linarith : θ' ≤ 1)
              rwa [Real.rpow_one] at this
            have hXξ0 : 0 ≤ X ^ ξ := by positivity
            have h1 : X ^ θ' * X ^ ξ ≤ X0 * X ^ ξ :=
              mul_le_mul_of_nonneg_right (by linarith) hXξ0
            have h2 : 0 ≤ K * X ^ ξ := mul_nonneg hK hXξ0
            nlinarith
    have hmain : (D.card : ENNReal) ≤ ENNReal.ofReal ((K + X0) * X ^ ξ) := by
      rw [← hvol]; exact le_trans (measure_mono hcover) hbound
    have hDR : (D.card : ℝ) ≤ (K + X0) * X ^ ξ := by
      rw [← ENNReal.ofReal_natCast] at hmain
      exact (ENNReal.ofReal_le_ofReal_iff (by positivity)).mp hmain
    rw [hXξ] at hDR
    calc (D.card : ℝ) ≤ (K + X0) * (r * r ^ j) := hDR
      _ = C0 * r ^ j := by rw [hC0]; ring
  have hgeom : ∑ j ∈ Finset.range (J + 1), C0 * r ^ j ≤ C * (Z : ℝ) ^ ξ := by
    rw [← Finset.mul_sum, geom_sum_eq hr1.ne' (J + 1)]
    have hrJ : r ^ J ≤ (Z : ℝ) ^ ξ := by
      have h1 : 2 ^ J ≤ Z := Nat.pow_log_le_self 2 (by omega)
      have h2 : ((2 : ℝ) ^ J) ≤ Z := by exact_mod_cast h1
      rw [hr, ← two_pow_rpow]
      exact Real.rpow_le_rpow (by positivity) h2 hξ0.le
    have hr0 : 0 < r - 1 := by linarith
    have key : (r ^ (J + 1) - 1) / (r - 1) ≤ r * (Z : ℝ) ^ ξ / (r - 1) := by
      apply div_le_div_of_nonneg_right _ hr0.le
      rw [pow_succ]
      have : 0 ≤ r ^ J := by positivity
      nlinarith
    calc C0 * ((r ^ (J + 1) - 1) / (r - 1))
        ≤ C0 * (r * (Z : ℝ) ^ ξ / (r - 1)) := mul_le_mul_of_nonneg_left key hC00
      _ = C * (Z : ℝ) ^ ξ := by rw [hC]; ring
  have hsum : (E.card : ℝ) ≤ ∑ j ∈ Finset.range (J + 1), C0 * r ^ j := by
    rw [hfib]; push_cast
    exact Finset.sum_le_sum (fun j _ => hblock j)
  linarith

/-! ### (B) Window lemma -/

/-- Window length used in the double counting: `⌈(2V)^θ' log(2V)⌉`, `V = (n+1)^c`. -/
noncomputable def HM (c θ' : ℝ) (n : ℕ) : ℕ :=
  ⌈(2 * ((n : ℝ) + 1) ^ c) ^ θ' * Real.log (2 * ((n : ℝ) + 1) ^ c)⌉₊

/-- Exceptional integers in the child interval of `n`, after the first `HM` points. -/
noncomputable def XM (c θ' cM : ℝ) (n : ℕ) : Finset ℕ :=
  (Finset.Icc (uN c n + HM c θ' n) (wN c n)).filter (excD cM θ')

/-- Side conditions at `n` (they hold for all large `n`). -/
def SideM (c θ' : ℝ) (n : ℕ) : Prop :=
  2 ≤ n ∧ (2 * ((n : ℝ) + 1) ^ c) ^ θ' * Real.log (2 * ((n : ℝ) + 1) ^ c) + 4 ≤
    (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / 4

/-- `2·2^{1+c} + 1`. -/
noncomputable def matR (c : ℝ) : ℝ := 2 * (2 : ℝ) ^ (1 + c) + 1

/-- The threshold `ν = c_M / (4 (2·2^{1+c} + 1))`. -/
noncomputable def matNu (c cM : ℝ) : ℝ := cM / (4 * matR c)

lemma matR_pos (c : ℝ) : 0 < matR c := by unfold matR; positivity

lemma matNu_pos {c cM : ℝ} (hcM : 0 < cM) : 0 < matNu c cM := by
  unfold matNu; have := matR_pos c; positivity

/-- Double counting: each `m` is seen by at most `H` windows `[x - H, x]`. -/
lemma sum_window_le (X S : Finset ℕ) (H : ℕ) :
    ∑ x ∈ X, (S.filter (fun m => m ≤ x ∧ x < m + H)).card ≤ H * S.card := by
  have h2 : ∀ x ∈ X, (S.filter (fun m => m ≤ x ∧ x < m + H)).card =
      ∑ m ∈ S, if (m ≤ x ∧ x < m + H) then 1 else 0 := fun x _ => Finset.card_filter _ _
  rw [Finset.sum_congr rfl h2, Finset.sum_comm]
  have h3 : ∀ m ∈ S, ∑ x ∈ X, (if (m ≤ x ∧ x < m + H) then 1 else 0) ≤ H := by
    intro m _
    rw [← Finset.card_filter]
    calc (X.filter (fun x => m ≤ x ∧ x < m + H)).card ≤ (Finset.Ico m (m + H)).card := by
          apply Finset.card_le_card
          intro x hx
          simp only [Finset.mem_filter, Finset.mem_Ico] at hx ⊢
          omega
      _ = H := by rw [Nat.card_Ico]; omega
  calc ∑ m ∈ S, ∑ x ∈ X, (if (m ≤ x ∧ x < m + H) then 1 else 0)
      ≤ ∑ _m ∈ S, H := Finset.sum_le_sum h3
    _ = H * S.card := by rw [Finset.sum_const, smul_eq_mul, mul_comm]

/-- **(B) Window lemma.** A bad `n` with the side conditions has at least `ℓ(n)/2`
exceptional integers in its child interval. -/
lemma bad_windowM {c θ' cM : ℝ} (hc : 1 < c) (hθ0 : 0 < θ') (hθ1 : θ' ≤ 1) (hcM : 0 < cM)
    {n : ℕ} (hs : SideM c θ' n) (hbad : badNu P2 (matNu c cM) c n) :
    (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / 2 ≤ ((XM c θ' cM n).card : ℝ) := by
  obtain ⟨hn2, hside⟩ := hs
  have hc0 : 0 < c := by linarith
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2
  have hnpos : (0 : ℝ) < n := by linarith
  have hnc : (n : ℝ) ≤ (n : ℝ) ^ c := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ n) hc.le
    rwa [Real.rpow_one] at this
  have hu1 : (n : ℝ) ^ c ≤ uN c n := Nat.le_ceil _
  have hu2 : (uN c n : ℝ) < (n : ℝ) ^ c + 1 := Nat.ceil_lt_add_one (by positivity)
  have hw1 : ((n : ℝ) + 1) ^ c - 2 ≤ (wN c n : ℝ) := le_wN (c := c) n
  have hw2 : (wN c n : ℝ) ≤ ((n : ℝ) + 1) ^ c - 1 := wN_le hc0 n
  have hSb : (((Finset.Icc (uN c n) (wN c n)).filter P2).card : ℝ) <
      matNu c cM * (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / Real.log (((n : ℝ) + 1) ^ c) := hbad
  have hHn1 : (HM c θ' n : ℝ) < (2 * ((n : ℝ) + 1) ^ c) ^ θ' *
      Real.log (2 * ((n : ℝ) + 1) ^ c) + 1 := by
    unfold HM
    apply Nat.ceil_lt_add_one
    have : (0 : ℝ) ≤ Real.log (2 * ((n : ℝ) + 1) ^ c) := Real.log_nonneg (by
      have : (1 : ℝ) ≤ ((n : ℝ) + 1) ^ c := Real.one_le_rpow (by linarith) hc0.le
      linarith)
    positivity
  have hHn0 : (2 * ((n : ℝ) + 1) ^ c) ^ θ' * Real.log (2 * ((n : ℝ) + 1) ^ c) ≤
      (HM c θ' n : ℝ) := by unfold HM; exact Nat.le_ceil _
  have hXM : XM c θ' cM n =
      (Finset.Icc (uN c n + HM c θ' n) (wN c n)).filter (excD cM θ') := rfl
  rw [hXM]
  set V := ((n : ℝ) + 1) ^ c with hV
  set ℓ := V - (n : ℝ) ^ c with hℓ
  set u := uN c n with hu_def
  set w := wN c n with hw_def
  set Hn := HM c θ' n with hHn_def
  set S := (Finset.Icc u w).filter P2 with hS_def
  set Kset := Finset.Icc (u + Hn) w with hK_def
  set hl := (u : ℝ) ^ θ' with hhl
  set B := (2 * V) ^ θ' * Real.log (2 * V) with hB
  have hu2' : (2 : ℝ) ≤ u := by linarith
  have hu2n : 2 ≤ u := by exact_mod_cast hu2'
  have hV3 : (3 : ℝ) ≤ V := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1) hc.le
    rw [Real.rpow_one] at this; linarith
  have hlogV : 1 ≤ Real.log V := by
    rw [Real.le_log_iff_exp_le (by linarith)]
    have := Real.exp_one_lt_d9
    linarith
  have hlogV0 : 0 < Real.log V := by linarith
  have hhl1 : 1 ≤ hl := Real.one_le_rpow (by linarith) hθ0.le
  have hlog2V0 : 0 ≤ Real.log (2 * V) := Real.log_nonneg (by linarith)
  have hB0 : 0 ≤ B := by positivity
  -- `Hn ≤ matR c · hl · log V`
  have hHnR : (Hn : ℝ) ≤ matR c * hl * Real.log V := by
    have h2V : 2 * V ≤ (2 : ℝ) ^ (1 + c) * u := by
      have h1 : V ≤ (2 * (n : ℝ)) ^ c := Real.rpow_le_rpow (by positivity) (by linarith) hc0.le
      have h2 : (2 * (n : ℝ)) ^ c = (2 : ℝ) ^ c * (n : ℝ) ^ c := Real.mul_rpow (by norm_num) hnpos.le
      have h3 : (2 : ℝ) ^ (1 + c) = 2 * (2 : ℝ) ^ c := by
        rw [Real.rpow_add (by norm_num), Real.rpow_one]
      have h4 : (0 : ℝ) ≤ (2 : ℝ) ^ c := by positivity
      rw [h3]
      have h5 : (2 : ℝ) ^ c * (n : ℝ) ^ c ≤ (2 : ℝ) ^ c * u := mul_le_mul_of_nonneg_left hu1 h4
      linarith
    have hb1 : (1 : ℝ) ≤ (2 : ℝ) ^ (1 + c) := Real.one_le_rpow (by norm_num) (by linarith)
    have hpow : (2 * V) ^ θ' ≤ (2 : ℝ) ^ (1 + c) * hl := by
      calc (2 * V) ^ θ' ≤ ((2 : ℝ) ^ (1 + c) * u) ^ θ' :=
            Real.rpow_le_rpow (by positivity) h2V hθ0.le
        _ = ((2 : ℝ) ^ (1 + c)) ^ θ' * hl := Real.mul_rpow (by positivity) (by positivity)
        _ ≤ (2 : ℝ) ^ (1 + c) * hl := by
            apply mul_le_mul_of_nonneg_right _ (by positivity)
            have := Real.rpow_le_rpow_of_exponent_le hb1 hθ1
            rwa [Real.rpow_one] at this
    have hlog2 : Real.log (2 * V) ≤ 2 * Real.log V := by
      rw [Real.log_mul (by norm_num) (by linarith)]
      have : Real.log 2 ≤ Real.log V := Real.log_le_log (by norm_num) (by linarith)
      linarith
    have hBle : B ≤ (2 : ℝ) ^ (1 + c) * hl * (2 * Real.log V) := by
      calc B = (2 * V) ^ θ' * Real.log (2 * V) := rfl
        _ ≤ ((2 : ℝ) ^ (1 + c) * hl) * Real.log (2 * V) :=
            mul_le_mul_of_nonneg_right hpow hlog2V0
        _ ≤ ((2 : ℝ) ^ (1 + c) * hl) * (2 * Real.log V) :=
            mul_le_mul_of_nonneg_left hlog2 (by positivity)
    have h1le : (1 : ℝ) ≤ hl * Real.log V := by nlinarith
    have e : (2 : ℝ) ^ (1 + c) * hl * (2 * Real.log V) + hl * Real.log V =
        matR c * hl * Real.log V := by unfold matR; ring
    linarith
  -- matCount at a point of `Kset` is at most the window count
  have hwin : ∀ x ∈ Kset, matCount (matX x) (matX x ^ θ') x ≤
      (S.filter (fun m => m ≤ x ∧ x < m + Hn)).card := by
    intro x hx
    rw [hK_def, Finset.mem_Icc] at hx
    have hx1 : 1 ≤ x := by omega
    obtain ⟨-, hb2, hb3⟩ := matX_bounds hx1
    have hxr : (x : ℝ) ≤ w := by exact_mod_cast hx.2
    have hxpos : (1 : ℝ) ≤ x := by exact_mod_cast hx1
    have hXpos : 0 < matX x := by linarith
    have hX1 : 1 ≤ matX x := by linarith
    have hX2V : matX x ≤ 2 * V := by linarith
    have hHx : matX x ^ θ' * Real.log (matX x) ≤ B :=
      mul_le_mul (Real.rpow_le_rpow hXpos.le hX2V hθ0.le) (Real.log_le_log hXpos hX2V)
        (Real.log_nonneg hX1) (by positivity)
    have hHxn : matX x ^ θ' * Real.log (matX x) ≤ Hn := le_trans hHx hHn0
    have hux : ((u + Hn : ℕ) : ℝ) ≤ x := by exact_mod_cast hx.1
    push_cast at hux
    classical
    unfold matCount
    apply Finset.card_le_card
    intro m hm
    rw [Finset.mem_filter] at hm
    obtain ⟨-, h1, h2, h3⟩ := hm
    have hmu : (u : ℝ) < m := by linarith
    have hmu' : u < m := by exact_mod_cast hmu
    have hmx : m ≤ x := by exact_mod_cast h2
    rw [Finset.mem_filter, hS_def, Finset.mem_filter, Finset.mem_Icc]
    have hP2 : P2 m := by unfold P2; exact ⟨by omega, h3.1⟩
    refine ⟨⟨⟨by omega, by omega⟩, hP2⟩, hmx, ?_⟩
    have : (x : ℝ) < m + Hn := by linarith
    exact_mod_cast this
  -- non-exceptional points carry at least `c_M hl`
  set NE := Kset.filter (fun x => ¬ excD cM θ' x) with hNE_def
  have hNE : ∀ x ∈ NE, cM * hl ≤ ((S.filter (fun m => m ≤ x ∧ x < m + Hn)).card : ℝ) := by
    intro x hx
    rw [hNE_def, Finset.mem_filter] at hx
    obtain ⟨hxK, hne⟩ := hx
    unfold excD at hne
    push_neg at hne
    have hxK' := hxK
    rw [hK_def, Finset.mem_Icc] at hxK'
    have hx1 : 1 ≤ x := by omega
    obtain ⟨-, hb2, -⟩ := matX_bounds hx1
    have hxu : (u : ℝ) ≤ x := by exact_mod_cast (by omega : u ≤ x)
    have hhx : hl ≤ matX x ^ θ' := Real.rpow_le_rpow (by positivity) (by linarith) hθ0.le
    calc cM * hl ≤ cM * matX x ^ θ' := mul_le_mul_of_nonneg_left hhx hcM.le
      _ ≤ matCount (matX x) (matX x ^ θ') x := hne
      _ ≤ _ := by exact_mod_cast hwin x hxK
  have hsumw := sum_window_le Kset S Hn
  have hcnt : (NE.card : ℝ) * (cM * hl) ≤ (Hn : ℝ) * S.card := by
    have h1 := Finset.card_nsmul_le_sum NE
      (fun x => ((S.filter (fun m => m ≤ x ∧ x < m + Hn)).card : ℝ)) _ hNE
    rw [nsmul_eq_mul] at h1
    calc (NE.card : ℝ) * (cM * hl)
        ≤ ∑ x ∈ NE, ((S.filter (fun m => m ≤ x ∧ x < m + Hn)).card : ℝ) := h1
      _ ≤ ∑ x ∈ Kset, ((S.filter (fun m => m ≤ x ∧ x < m + Hn)).card : ℝ) :=
          Finset.sum_le_sum_of_subset_of_nonneg (Finset.filter_subset _ _)
            (fun _ _ _ => Nat.cast_nonneg _)
      _ ≤ (Hn : ℝ) * S.card := by exact_mod_cast hsumw
  have hR0 := matR_pos c
  have hHnS : (Hn : ℝ) * S.card ≤ matR c * hl * Real.log V * (matNu c cM * ℓ / Real.log V) :=
    mul_le_mul hHnR hSb.le (Nat.cast_nonneg _)
      (mul_nonneg (mul_nonneg hR0.le (by positivity)) hlogV0.le)
  have e : matR c * hl * Real.log V * (matNu c cM * ℓ / Real.log V) = ℓ / 4 * (cM * hl) := by
    unfold matNu
    field_simp
  rw [e] at hHnS
  have hNEle : (NE.card : ℝ) ≤ ℓ / 4 :=
    le_of_mul_le_mul_right (le_trans hcnt hHnS) (by positivity)
  have hsplit := Finset.card_filter_add_card_filter_not (s := Kset) (excD cM θ')
  have hle : u + Hn ≤ w + 1 := by
    have : (u : ℝ) + Hn ≤ w + 1 := by linarith
    exact_mod_cast this
  have hKc : Kset.card = w + 1 - (u + Hn) := by rw [hK_def, Nat.card_Icc]
  have hKR : ((w + 1 - (u + Hn) : ℕ) : ℝ) = (w : ℝ) + 1 - u - Hn := by
    rw [Nat.cast_sub hle]; push_cast; ring
  have hsplitR : ((Kset.filter (excD cM θ')).card : ℝ) + (NE.card : ℝ) = Kset.card := by
    rw [hNE_def]; exact_mod_cast hsplit
  rw [hKc, hKR] at hsplitR
  linarith

/-! ### Side conditions hold eventually -/

lemma sideM_eventually {c θ' : ℝ} (hc : 1 < c) (hθ0 : 0 < θ') (hθc : θ' < 1 - 1 / c) :
    ∃ n0 : ℕ, 2 ≤ n0 ∧ ∀ n ≥ n0, SideM c θ' n := by
  have hc0 : 0 < c := by linarith
  have hcθ : c * θ' < c - 1 := by
    have h := mul_lt_mul_of_pos_left hθc hc0
    have e : c * (1 - 1 / c) = c - 1 := by field_simp
    linarith
  set ε := (c - 1 - c * θ') / (2 * c) with hε
  have hε0 : 0 < ε := by apply div_pos <;> linarith
  set s := c * (θ' + ε) with hs
  have hs0 : 0 < s := by positivity
  have hse : s = c * θ' + (c - 1 - c * θ') / 2 := by rw [hs, hε]; field_simp
  set e := c - 1 - s with he
  have he0 : 0 < e := by rw [he, hse]; linarith
  set M2 := 4 * ((4 : ℝ) ^ s + 4) / c with hM2
  have hlo := (isLittleO_log_rpow_atTop hε0).def (by norm_num : (0 : ℝ) < 1)
  have hev1 : ∀ᶠ y : ℝ in atTop, Real.log y ≤ y ^ ε := by
    filter_upwards [hlo, eventually_gt_atTop (1 : ℝ)] with y hy hy1
    rw [Real.norm_eq_abs, Real.norm_eq_abs, abs_of_nonneg (Real.log_nonneg hy1.le),
      abs_of_nonneg (by positivity)] at hy
    linarith
  obtain ⟨y0, hy0⟩ := Filter.eventually_atTop.mp hev1
  have t2 := (tendsto_rpow_atTop he0).comp tendsto_natCast_atTop_atTop
  obtain ⟨n2, hn2⟩ := Filter.eventually_atTop.mp (t2.eventually (eventually_ge_atTop M2))
  refine ⟨max (max n2 2) ⌈y0⌉₊, le_trans (le_max_right _ _) (le_max_left _ _), fun n hn => ?_⟩
  have hn2' : n2 ≤ n := le_trans (le_trans (le_max_left _ _) (le_max_left _ _)) hn
  have hn2'' : 2 ≤ n := le_trans (le_trans (le_max_right _ _) (le_max_left _ _)) hn
  have hny : y0 ≤ n := le_trans (Nat.le_ceil y0)
    (by exact_mod_cast le_trans (le_max_right _ _) hn)
  have hM : M2 ≤ (n : ℝ) ^ e := by
    have := hn2 n hn2'
    simpa [Function.comp] using this
  refine ⟨hn2'', ?_⟩
  set V := ((n : ℝ) + 1) ^ c with hV
  have hnr : (2 : ℝ) ≤ n := by exact_mod_cast hn2''
  have hnpos : (0 : ℝ) < n := by linarith
  have hVn : (n : ℝ) + 1 ≤ V := by
    have := Real.rpow_le_rpow_of_exponent_le (by linarith : (1 : ℝ) ≤ (n : ℝ) + 1) hc.le
    rwa [Real.rpow_one] at this
  have h2Vpos : 0 < 2 * V := by linarith
  have hlog : Real.log (2 * V) ≤ (2 * V) ^ ε := hy0 _ (by linarith)
  have hA : (2 * V) ^ θ' * Real.log (2 * V) ≤ (2 * V) ^ (θ' + ε) := by
    rw [Real.rpow_add h2Vpos]
    exact mul_le_mul_of_nonneg_left hlog (by positivity)
  have h2V : 2 * V ≤ (4 * (n : ℝ)) ^ c := by
    have h1 : V ≤ (2 * (n : ℝ)) ^ c := Real.rpow_le_rpow (by positivity) (by linarith) hc0.le
    have h2 : (2 : ℝ) ≤ (2 : ℝ) ^ c := by
      have := Real.rpow_le_rpow_of_exponent_le (by norm_num : (1 : ℝ) ≤ 2) hc.le
      rwa [Real.rpow_one] at this
    have h3 : (4 * (n : ℝ)) ^ c = (2 : ℝ) ^ c * (2 * (n : ℝ)) ^ c := by
      rw [← Real.mul_rpow (by norm_num) (by positivity)]; congr 1; ring
    have h4 : 0 ≤ (2 * (n : ℝ)) ^ c := by positivity
    rw [h3]; nlinarith
  have hB : (2 * V) ^ (θ' + ε) ≤ (4 : ℝ) ^ s * (n : ℝ) ^ s := by
    calc (2 * V) ^ (θ' + ε) ≤ ((4 * (n : ℝ)) ^ c) ^ (θ' + ε) :=
          Real.rpow_le_rpow h2Vpos.le h2V (by positivity)
      _ = (4 * (n : ℝ)) ^ s := by rw [← Real.rpow_mul (by positivity)]
      _ = (4 : ℝ) ^ s * (n : ℝ) ^ s := Real.mul_rpow (by norm_num) hnpos.le
  have hns1 : 1 ≤ (n : ℝ) ^ s := Real.one_le_rpow (by linarith) hs0.le
  have hℓ : c * (n : ℝ) ^ (c - 1) ≤ V - (n : ℝ) ^ c := diff_ge_conv hnpos hc.le
  have hsplit : (n : ℝ) ^ (c - 1) = (n : ℝ) ^ e * (n : ℝ) ^ s := by
    rw [← Real.rpow_add hnpos]; congr 1; rw [he]; ring
  have hM2c : c * M2 = 4 * ((4 : ℝ) ^ s + 4) := by rw [hM2]; field_simp
  have h1 := mul_le_mul_of_nonneg_right hM (by positivity : (0 : ℝ) ≤ (n : ℝ) ^ s)
  have h2 := mul_le_mul_of_nonneg_left h1 hc0.le
  have hcn : 4 * ((4 : ℝ) ^ s + 4) * (n : ℝ) ^ s ≤ c * (n : ℝ) ^ (c - 1) := by
    rw [hsplit, ← hM2c]; linarith
  linarith

/-! ### (C) Counting step -/

lemma XM_disjoint {c θ' cM : ℝ} (hc : 1 < c) {n n' : ℕ} (hn : 1 ≤ n) (h : n < n') :
    Disjoint (XM c θ' cM n) (XM c θ' cM n') := by
  rw [Finset.disjoint_left]
  intro x hx hx'
  unfold XM at hx hx'
  rw [Finset.mem_filter, Finset.mem_Icc] at hx hx'
  have h1 : (x : ℝ) ≤ wN c n + 1 := by exact_mod_cast (by omega : x ≤ wN c n + 1)
  have h2 := wN_lt (by linarith : (0 : ℝ) < c) hn
  have h3 : ((n : ℝ) + 1) ^ c ≤ (n' : ℝ) ^ c :=
    Real.rpow_le_rpow (by positivity) (by exact_mod_cast h) (by linarith)
  have h4 : (n' : ℝ) ^ c ≤ uN c n' := Nat.le_ceil _
  have h5 : (uN c n' : ℝ) ≤ x := by exact_mod_cast (by omega : uN c n' ≤ x)
  linarith

set_option maxHeartbeats 1000000 in
/-- **Tappa 4: Matomäki's theorem implies the counting hypothesis for `P2`**, with
`ν = matNu c cM = c_M / (4 (2·2^{1+c} + 1))` and `δ` depending on `c, θ'`. -/
theorem hexc_P2_of_Matomaki {c θ' cM K : ℝ} (hc : 1 < c) (hθ0 : 0 < θ') (hθ1 : θ' < 1 / 100)
    (hθc : θ' < 1 - 1 / c) (hcM : 0 < cM) (hK : 0 ≤ K) (hM : MatomakiHyp θ' cM K) :
    ∃ δ K' : ℝ, 0 < δ ∧ δ ≤ 1 ∧ 0 ≤ K' ∧ ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badNu P2 (matNu c cM) c n)).card : ℝ) ≤
        K' * (N : ℝ) ^ (1 - δ) := by
  obtain ⟨K0, hK0, hD⟩ := discrete_of_Matomaki hθ0 hθ1 hK hM
  obtain ⟨n0, hn0_2, hside⟩ := sideM_eventually hc hθ0 hθc
  have hθle : θ' ≤ 1 := by linarith
  set ξ := 1 - θ' with hξ
  have hξ0 : 0 ≤ ξ := by linarith
  have hξ1 : ξ < 1 := by linarith
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
  set K2 := 2 * K0 * ((2 : ℝ) ^ c + 1) ^ ξ / c with hK2
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
  set B := (Finset.range (N + 1)).filter (fun n => badNu P2 (matNu c cM) c n) with hB
  set L := (Finset.Icc n1 N).filter (fun n => badNu P2 (matNu c cM) c n) with hL
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
  have hLside : ∀ n ∈ L, SideM c θ' n ∧ badNu P2 (matNu c cM) c n ∧ n1 ≤ n ∧ n ≤ N := by
    intro n hn
    rw [hL, Finset.mem_filter, Finset.mem_Icc] at hn
    exact ⟨hside n (le_trans hn1_0 hn.1.1), hn.2, hn.1.1, hn.1.2⟩
  have hdisj : ∀ n ∈ L, ∀ n' ∈ L, n ≠ n' → Disjoint (XM c θ' cM n) (XM c θ' cM n') := by
    intro n hn n' hn' hne
    have h1 := (hLside n hn).1.1
    have h2 := (hLside n' hn').1.1
    rcases lt_or_gt_of_ne hne with hlt | hgt
    · exact XM_disjoint hc (by omega) hlt
    · exact (XM_disjoint hc (by omega) hgt).symm
  have hsub : L.biUnion (XM c θ' cM) ⊆ (Finset.Icc 1 Z).filter (excD cM θ') := by
    intro x hx
    rw [Finset.mem_biUnion] at hx
    obtain ⟨n, hn, hxn⟩ := hx
    obtain ⟨⟨hn2, -⟩, -, -, hnN⟩ := hLside n hn
    unfold XM at hxn
    rw [Finset.mem_filter, Finset.mem_Icc] at hxn
    rw [Finset.mem_filter, Finset.mem_Icc]
    have hun : uN c n ≤ x := by omega
    refine ⟨⟨le_trans (one_le_uN (c := c) (n := n) hc0 (by omega)) hun, ?_⟩, hxn.2⟩
    have hw := wN_lt hc0 (by omega : 1 ≤ n)
    have hx1 : (x : ℝ) ≤ wN c n + 1 := by exact_mod_cast (by omega : x ≤ wN c n + 1)
    have hnN' : (n : ℝ) ≤ N := by exact_mod_cast hnN
    have h3 : ((n : ℝ) + 1) ^ c ≤ ((N : ℝ) + 1) ^ c :=
      Real.rpow_le_rpow (by positivity) (by linarith) hc0.le
    have h4 : ((N : ℝ) + 1) ^ c ≤ Z := Nat.le_ceil _
    have : (x : ℝ) ≤ Z := by linarith
    exact_mod_cast this
  have hsumle : (∑ n ∈ L, ((XM c θ' cM n).card : ℝ)) ≤ K0 * (Z : ℝ) ^ ξ := by
    have e : (L.biUnion (XM c θ' cM)).card = ∑ n ∈ L, (XM c θ' cM n).card :=
      Finset.card_biUnion hdisj
    have h1 : ((L.biUnion (XM c θ' cM)).card : ℝ) ≤
        (((Finset.Icc 1 Z).filter (excD cM θ')).card : ℝ) := by
      exact_mod_cast Finset.card_le_card hsub
    have h2 := hD Z hZ1
    have e' : ((L.biUnion (XM c θ' cM)).card : ℝ) = ∑ n ∈ L, ((XM c θ' cM n).card : ℝ) := by
      rw [e]; push_cast; rfl
    linarith
  have heach : ∀ n ∈ L, c * (N : ℝ) ^ (a * (c - 1)) / 2 ≤ ((XM c θ' cM n).card : ℝ) := by
    intro n hn
    obtain ⟨hs, hbad, hn1n, -⟩ := hLside n hn
    have hw := bad_windowM hc hθ0 hθle hcM hs hbad
    have hnr : (n1 : ℝ) ≤ n := by exact_mod_cast hn1n
    have hn2 : (2 : ℝ) ≤ n := by exact_mod_cast hs.1
    have hnpos : (0 : ℝ) < n := by linarith
    have hℓ : c * (n : ℝ) ^ (c - 1) ≤ ((n : ℝ) + 1) ^ c - (n : ℝ) ^ c :=
      diff_ge_conv hnpos hc.le
    have hpow : (N : ℝ) ^ (a * (c - 1)) ≤ (n : ℝ) ^ (c - 1) := by
      rw [Real.rpow_mul hNpos.le]
      exact Real.rpow_le_rpow (by positivity) (le_trans hn1_a hnr) hc1.le
    have : c * (N : ℝ) ^ (a * (c - 1)) ≤ c * (n : ℝ) ^ (c - 1) :=
      mul_le_mul_of_nonneg_left hpow hc0.le
    linarith
  have hLlow : (L.card : ℝ) * (c * (N : ℝ) ^ (a * (c - 1)) / 2) ≤ K0 * (Z : ℝ) ^ ξ := by
    have := Finset.card_nsmul_le_sum L (fun n => ((XM c θ' cM n).card : ℝ)) _ heach
    rw [nsmul_eq_mul] at this
    linarith
  have hZle : (Z : ℝ) ≤ ((2 : ℝ) ^ c + 1) * (N : ℝ) ^ c := by
    have h1 : (Z : ℝ) < ((N : ℝ) + 1) ^ c + 1 := Nat.ceil_lt_add_one (by positivity)
    have h2 : ((N : ℝ) + 1) ^ c ≤ (2 * (N : ℝ)) ^ c :=
      Real.rpow_le_rpow (by positivity) (by linarith) hc0.le
    have h3 : (2 * (N : ℝ)) ^ c = (2 : ℝ) ^ c * (N : ℝ) ^ c :=
      Real.mul_rpow (by norm_num) hNpos.le
    have h4 : (1 : ℝ) ≤ (N : ℝ) ^ c := Real.one_le_rpow hNr hc0.le
    nlinarith
  have hZξ : (Z : ℝ) ^ ξ ≤ ((2 : ℝ) ^ c + 1) ^ ξ * (N : ℝ) ^ (c * ξ) := by
    calc (Z : ℝ) ^ ξ ≤ (((2 : ℝ) ^ c + 1) * (N : ℝ) ^ c) ^ ξ :=
          Real.rpow_le_rpow (Nat.cast_nonneg _) hZle hξ0
      _ = ((2 : ℝ) ^ c + 1) ^ ξ * (N : ℝ) ^ (c * ξ) := by
          rw [Real.mul_rpow (by positivity) (by positivity), ← Real.rpow_mul hNpos.le]
  have hNac : 0 < (N : ℝ) ^ (a * (c - 1)) := Real.rpow_pos_of_pos hNpos _
  have hLcard : (L.card : ℝ) ≤ K2 * (N : ℝ) ^ (c * ξ - a * (c - 1)) := by
    have hq : 0 < c * (N : ℝ) ^ (a * (c - 1)) / 2 := by positivity
    have h1 : (L.card : ℝ) * (c * (N : ℝ) ^ (a * (c - 1)) / 2) ≤
        K0 * (((2 : ℝ) ^ c + 1) ^ ξ * (N : ℝ) ^ (c * ξ)) :=
      le_trans hLlow (mul_le_mul_of_nonneg_left hZξ hK0)
    have h2 : (L.card : ℝ) ≤ K0 * (((2 : ℝ) ^ c + 1) ^ ξ * (N : ℝ) ^ (c * ξ)) /
        (c * (N : ℝ) ^ (a * (c - 1)) / 2) := (le_div_iff₀ hq).mpr h1
    have e : K0 * (((2 : ℝ) ^ c + 1) ^ ξ * (N : ℝ) ^ (c * ξ)) /
        (c * (N : ℝ) ^ (a * (c - 1)) / 2) = K2 * (N : ℝ) ^ (c * ξ - a * (c - 1)) := by
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

/-- **Theorem `thm:P2`, conditional only on Matomäki's theorem.** For `c > 1`, if Matomäki's
theorem holds with some `h = X^θ'`, `0 < θ' < min(1/100, 1 - 1/c)`, then there is `B` with
`Ω(⌊B^{c^k}⌋) ≤ 2` and `⌊B^{c^k}⌋ ≥ 2` for every `k`. -/
theorem mills_P2_of_Matomaki {c θ' cM K : ℝ} (hc : 1 < c) (hθ0 : 0 < θ') (hθ1 : θ' < 1 / 100)
    (hθc : θ' < 1 - 1 / c) (hcM : 0 < cM) (hK : 0 ≤ K) (hM : MatomakiHyp θ' cM K) :
    ∃ B : ℝ, ∀ k, 2 ≤ ⌊B ^ c ^ k⌋₊ ∧ ArithmeticFunction.cardFactors ⌊B ^ c ^ k⌋₊ ≤ 2 := by
  obtain ⟨δ, K', hδ, hδ1, hK', hexc⟩ := hexc_P2_of_Matomaki hc hθ0 hθ1 hθc hcM hK hM
  exact mills_P2_of_count hc (matNu c cM) (matNu_pos hcM) δ K' hδ hδ1 hK' hexc

end MillsForest
