import MillsForest.Phi

/-!
# Generalisation to an arbitrary predicate `P` and log-power `m`

All the forest/recursion machinery of `Main`, `Share` and `Phi`, with
* the children of `p` being the `q` with `P q` (instead of `q` prime) in the same interval;
* the bad threshold `ell/(5 log((n+1)^c)^m)` (instead of `m = 1`).

`m = 1`, `P = Nat.Prime` is the prime case. `m = 2`, `P q := q.Prime ∧ (q+2).Prime` gives
**twin primes**: under a power-saving exceptional-set hypothesis for twins (a conjecture,
an "almost all short intervals" form of Hardy–Littlewood), there is `B` with
`⌊B^{c^k}⌋` and `⌊B^{c^k}⌋ + 2` both prime for every `k`.
-/

open Finset Real Filter

namespace MillsForest

section Gen

variable (P : ℕ → Prop) [DecidablePred P]

/-- Children with property `P`: `q` with `⌈p^r⌉ ≤ q ≤ ⌈(p+1)^r⌉ - 2` and `P q`. -/
noncomputable def kidsG (C : ℕ → ℝ) (k p : ℕ) : Finset ℕ :=
  (Finset.Icc ⌈(p : ℝ) ^ ratio C k⌉₊ (⌈((p : ℝ) + 1) ^ ratio C k⌉₊ - 2)).filter P

/-- The `P`-forest with roots `[Y, 2Y]`. -/
noncomputable def icForestG (c : ℝ) (Y : ℕ) : WForest := ⟨Finset.Icc Y (2 * Y), kidsG P (powSeq c)⟩

/-- Exceptional property with log-power `m`. -/
def badcG (m : ℕ) (c : ℝ) (n : ℕ) : Prop :=
  ((kidsG P (powSeq c) 0 n).card : ℝ) <
    (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / (5 * Real.log (((n : ℝ) + 1) ^ c) ^ m)

noncomputable instance badcG_dec (m : ℕ) (c : ℝ) : DecidablePred (badcG P m c) := fun n => by
  unfold badcG; infer_instance

/-- `ν_k = 1/(5 (c^{k+1} log(2Y+2))^m)`. -/
noncomputable def nuSeqG (c : ℝ) (m Y k : ℕ) : ℝ :=
  1 / (5 * (c ^ (k + 1) * Real.log (2 * (Y : ℝ) + 2)) ^ m)

/-- `L_0 = Y+1`, `L_{k+1} = ν_k 3^{-c} L_k / 2`. -/
noncomputable def LSeqG (c : ℝ) (m Y : ℕ) : ℕ → ℝ
  | 0 => (Y : ℝ) + 1
  | k + 1 => nuSeqG c m Y k * (1 / 3 : ℝ) ^ c * (LSeqG c m Y k / 2)

lemma nuSeqG_pos {c : ℝ} (hc : 1 < c) (m Y k : ℕ) : 0 < nuSeqG c m Y k := by
  unfold nuSeqG
  have := log_pos_Y Y
  have : 0 < c ^ (k + 1) := pow_pos (by linarith) _
  positivity

lemma LSeqG_pos {c : ℝ} (hc : 1 < c) (m Y k : ℕ) : 0 < LSeqG c m Y k := by
  induction k with
  | zero => show (0 : ℝ) < (Y : ℝ) + 1; positivity
  | succ k ih =>
    show 0 < nuSeqG c m Y k * (1 / 3 : ℝ) ^ c * (LSeqG c m Y k / 2)
    have := nuSeqG_pos hc m Y k
    positivity

/-- The step of the recursion with log-power `m`. -/
lemma q_stepG {c : ℝ} (hc : 1 < c) (m : ℕ) (hm : 1 ≤ m) (δ : ℝ) {Y : ℕ} (hY : 1 ≤ Y)
    (hS : 1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c ≤ (1 / qY δ Y) ^ ((c - 1) / m))
    (k : ℕ) :
    (qY δ Y) ^ (powSeq c k * (c - 1)) ≤ nuSeqG c m Y k * (1 / 3 : ℝ) ^ c / 2 := by
  have hq := qY_pos δ hY
  set a := Real.log (2 * (Y : ℝ) + 2) with ha
  have ha0 : 0 < a := log_pos_Y Y
  have hmr : (0 : ℝ) < m := by exact_mod_cast hm
  set v := (1 / qY δ Y) ^ ((c - 1) / m) with hv
  have hv0 : 0 ≤ v := by positivity
  have hCk := powSeq_one_le hc k
  have hbern : 1 + powSeq c k * (v - 1) ≤ v ^ powSeq c k := by
    have := one_add_mul_self_le_rpow_one_add (by linarith : (-1 : ℝ) ≤ v - 1) hCk
    simpa using this
  have hc0 : (0 : ℝ) < c := by linarith
  have hck : powSeq c k * c = c ^ (k + 1) := by rw [← powSeq_succ]; rfl
  have hck0 : 0 < c ^ (k + 1) := pow_pos hc0 _
  set Q := 10 * (3 : ℝ) ^ c * (c ^ (k + 1) * a) with hQ
  have hQ0 : 0 < Q := by positivity
  have hvQ : Q ≤ v ^ powSeq c k := by
    have h1 : 10 * c * a * (3 : ℝ) ^ c ≤ v - 1 := by linarith
    calc Q = powSeq c k * (10 * c * a * (3 : ℝ) ^ c) := by rw [hQ, ← hck]; ring
      _ ≤ powSeq c k * (v - 1) := mul_le_mul_of_nonneg_left h1 (by linarith)
      _ ≤ v ^ powSeq c k := by linarith
  have hpowm : (v ^ powSeq c k) ^ m = (1 / qY δ Y) ^ (powSeq c k * (c - 1)) := by
    rw [hv, ← Real.rpow_mul (by positivity), ← Real.rpow_natCast,
      ← Real.rpow_mul (by positivity)]
    congr 1
    field_simp
  have hbig : 10 * (3 : ℝ) ^ c * (c ^ (k + 1) * a) ^ m ≤ (v ^ powSeq c k) ^ m := by
    have h1 : Q ^ m ≤ (v ^ powSeq c k) ^ m := pow_le_pow_left₀ hQ0.le hvQ m
    have h10 : (1 : ℝ) ≤ 10 * (3 : ℝ) ^ c := by
      have := Real.one_le_rpow (by norm_num : (1 : ℝ) ≤ 3) hc0.le
      linarith
    have h2 : 10 * (3 : ℝ) ^ c ≤ (10 * (3 : ℝ) ^ c) ^ m := le_self_pow₀ h10 (by omega)
    have h4 : 0 ≤ (c ^ (k + 1) * a) ^ m := by positivity
    calc 10 * (3 : ℝ) ^ c * (c ^ (k + 1) * a) ^ m
        ≤ (10 * (3 : ℝ) ^ c) ^ m * (c ^ (k + 1) * a) ^ m := mul_le_mul_of_nonneg_right h2 h4
      _ = Q ^ m := by rw [hQ]; ring
      _ ≤ _ := h1
  have hqx : (qY δ Y) ^ (powSeq c k * (c - 1)) = 1 / (v ^ powSeq c k) ^ m := by
    rw [hpowm, Real.div_rpow zero_le_one hq.le, Real.one_rpow, one_div_one_div]
  have hm' : nuSeqG c m Y k * (1 / 3 : ℝ) ^ c / 2 =
      1 / (10 * (3 : ℝ) ^ c * (c ^ (k + 1) * a) ^ m) := by
    unfold nuSeqG
    rw [← ha, Real.div_rpow (by norm_num) (by norm_num), Real.one_rpow]
    field_simp
    ring
  rw [hqx, hm']
  have hpos : 0 < 10 * (3 : ℝ) ^ c * (c ^ (k + 1) * a) ^ m := by positivity
  exact one_div_le_one_div_of_le hpos hbig

lemma beta_leG {c : ℝ} (hc : 1 < c) (m : ℕ) (hm : 1 ≤ m) (δ K : ℝ) (hK : 0 ≤ K) {Y : ℕ}
    (hY : 1 ≤ Y)
    (hB0 : K * (2 * (Y : ℝ) + 1) * qY δ Y ≤ ((Y : ℝ) + 1) / 2)
    (hS : 1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c ≤ (1 / qY δ Y) ^ ((c - 1) / m)) :
    ∀ k, betaSeq c δ K Y k ≤ LSeqG c m Y k / 2 := by
  have hq := qY_pos δ hY
  intro k
  induction k with
  | zero =>
    unfold betaSeq; rw [powSeq_zero, Real.rpow_one]; exact hB0
  | succ k ih =>
    have hsplit : (qY δ Y) ^ powSeq c (k + 1) =
        (qY δ Y) ^ powSeq c k * (qY δ Y) ^ (powSeq c k * (c - 1)) := by
      rw [← Real.rpow_add hq, powSeq_succ]; congr 1; ring
    have hstep := q_stepG hc m hm δ hY hS k
    show K * (2 * (Y : ℝ) + 1) * (qY δ Y) ^ powSeq c (k + 1) ≤
      nuSeqG c m Y k * (1 / 3 : ℝ) ^ c * (LSeqG c m Y k / 2) / 2
    rw [hsplit]
    have ih' : K * (2 * (Y : ℝ) + 1) * (qY δ Y) ^ powSeq c k ≤ LSeqG c m Y k / 2 := ih
    calc K * (2 * (Y : ℝ) + 1) * ((qY δ Y) ^ powSeq c k * (qY δ Y) ^ (powSeq c k * (c - 1)))
        = (K * (2 * (Y : ℝ) + 1) * (qY δ Y) ^ powSeq c k) *
            (qY δ Y) ^ (powSeq c k * (c - 1)) := by ring
      _ ≤ (LSeqG c m Y k / 2) * (nuSeqG c m Y k * (1 / 3 : ℝ) ^ c / 2) :=
          mul_le_mul ih' hstep (by positivity) (by have := LSeqG_pos hc m Y k; positivity)
      _ = nuSeqG c m Y k * (1 / 3 : ℝ) ^ c * (LSeqG c m Y k / 2) / 2 := by ring


/-- A suitable `Y` exists (log-power `m`). -/
lemma exists_YG {c : ℝ} (hc : 1 < c) (m : ℕ) (hm : 1 ≤ m) (δ K : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K) :
    ∃ Y : ℕ, 1 ≤ Y ∧ K * (2 * (Y : ℝ) + 1) * qY δ Y ≤ ((Y : ℝ) + 1) / 2 ∧
      1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c ≤ (1 / qY δ Y) ^ ((c - 1) / m) := by
  set ε := δ * ((c - 1) / m) with hε
  have hε0 : 0 < ε := mul_pos hδ (div_pos (by linarith) (by exact_mod_cast hm))
  set B := (3 : ℝ) ^ ((c - 1) / m) * (10 * c * (3 : ℝ) ^ c) with hB
  have hB0 : 0 < B := by positivity
  set A0 := (3 : ℝ) ^ ((c - 1) / m) * (1 + 10 * c * (3 : ℝ) ^ c * Real.log 4) with hA0
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
    have hpow : (Y : ℝ) ^ ε / (3 : ℝ) ^ ((c - 1) / m) ≤ (1 / qY δ Y) ^ ((c - 1) / m) := by
      have := Real.rpow_le_rpow (by positivity) hinv
        (div_nonneg (by linarith) (Nat.cast_nonneg m) : (0 : ℝ) ≤ (c - 1) / m)
      rw [Real.div_rpow hYd.le (by norm_num), ← Real.rpow_mul hYpos.le] at this
      exact this
    have hlog : Real.log (2 * (Y : ℝ) + 2) ≤ Real.log 4 + Real.log Y := by
      rw [← Real.log_mul (by norm_num) hYpos.ne']
      exact Real.log_le_log (by positivity) (by linarith)
    have h3c : (0 : ℝ) < (3 : ℝ) ^ ((c - 1) / m) := by positivity
    have key : (1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c) * (3 : ℝ) ^ ((c - 1) / m) ≤
        (Y : ℝ) ^ ε := by
      have hBlog : 0 ≤ 10 * c * (3 : ℝ) ^ c * (3 : ℝ) ^ ((c - 1) / m) := by
        have : (0 : ℝ) < c := by linarith
        positivity
      have hh : (1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c) * (3 : ℝ) ^ ((c - 1) / m)
          ≤ A0 + B * Real.log Y := by
        rw [hA0, hB]
        nlinarith [mul_le_mul_of_nonneg_left hlog hBlog]
      linarith
    calc 1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c
        ≤ (Y : ℝ) ^ ε / (3 : ℝ) ^ ((c - 1) / m) := by rw [le_div_iff₀ h3c]; exact key
      _ ≤ (1 / qY δ Y) ^ ((c - 1) / m) := hpow

variable (hP2 : ∀ q, P q → 2 ≤ q)
include hP2

section
variable (C : ℕ → ℝ) (hC : ∀ k, 0 < C k)
include hC

lemma mem_kidsG {k p q : ℕ} (hq : q ∈ kidsG P C k p) :
    P q ∧ (p : ℝ) ^ ratio C k ≤ q ∧ (q : ℝ) + 1 < ((p : ℝ) + 1) ^ ratio C k := by
  unfold kidsG at hq
  rw [Finset.mem_filter, Finset.mem_Icc] at hq
  obtain ⟨⟨h1, h2⟩, hp⟩ := hq
  refine ⟨hp, Nat.ceil_le.mp h1, ?_⟩
  have h2' : q + 2 ≤ ⌈((p : ℝ) + 1) ^ ratio C k⌉₊ := by have := hP2 q hp; omega
  have hlt : (⌈((p : ℝ) + 1) ^ ratio C k⌉₊ : ℝ) < ((p : ℝ) + 1) ^ ratio C k + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
  have : ((q + 2 : ℕ) : ℝ) ≤ ⌈((p : ℝ) + 1) ^ ratio C k⌉₊ := by exact_mod_cast h2'
  push_cast at this
  linarith

lemma kids_ltG {k p p' q q' : ℕ} (hpp : p < p') (hq : q ∈ kidsG P C k p) (hq' : q' ∈ kidsG P C k p') :
    q < q' := by
  obtain ⟨-, -, hq2⟩ := mem_kidsG P hP2 C hC hq
  obtain ⟨-, hq'1, -⟩ := mem_kidsG P hP2 C hC hq'
  have hle : ((p : ℝ) + 1) ^ ratio C k ≤ (p' : ℝ) ^ ratio C k := by
    apply Real.rpow_le_rpow (by positivity) _ (ratio_pos C hC k).le
    exact_mod_cast hpp
  have : (q : ℝ) < q' := by linarith
  exact_mod_cast this

lemma kids_disjointG (k : ℕ) (s : Set ℕ) : s.PairwiseDisjoint (kidsG P C k) := by
  intro p _ p' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro q hq hq'
  rcases lt_or_gt_of_ne hne with h | h
  · exact (lt_irrefl q) (kids_ltG P hP2 C hC h hq hq')
  · exact (lt_irrefl q) (kids_ltG P hP2 C hC h hq' hq)

end

section
variable (C : ℕ → ℝ) (hC : ∀ k, 0 < C k) (hC1 : ∀ k, 1 ≤ C k) (hCm : ∀ k, C k ≤ C (k + 1))
include hC hC1 hCm

/-- **Share of the prime children.** -/
theorem kids_shareG (k p : ℕ) (hp : 1 ≤ p) (ν : ℝ) (hν : 0 ≤ ν)
    (hN : ν * (((p : ℝ) + 1) ^ ratio C k - (p : ℝ) ^ ratio C k) ≤ ((kidsG P C k p).card : ℝ)) :
    ν * (1 / 3 : ℝ) ^ ratio C k * wt C k p ≤ ∑ q ∈ kidsG P C k p, wt C (k + 1) q := by
  set r := ratio C k with hr_def
  set t := 1 / C k with ht_def
  set s := 1 / C (k + 1) with hs_def
  have hCk := hC k
  have hCk1 := hC (k + 1)
  have hr1 : 1 ≤ r := by rw [hr_def, ratio, one_le_div hCk]; exact hCm k
  have ht0 : 0 ≤ t := by positivity
  have ht1 : t ≤ 1 := by rw [ht_def, div_le_one hCk]; exact hC1 k
  have hs0 : 0 ≤ s := by positivity
  have hs1 : s ≤ 1 := by rw [hs_def, div_le_one hCk1]; exact hC1 (k + 1)
  have hrs : r * s = t := by
    rw [hr_def, hs_def, ht_def, ratio]; field_simp
  have hP : (0 : ℝ) < p := by exact_mod_cast hp
  have hp1 : (1 : ℝ) ≤ p := by exact_mod_cast hp
  set T := ((p : ℝ) + 1) ^ r with hT_def
  -- Step A: lower bound for each child weight.
  have hA : ∀ q ∈ kidsG P C k p, s * (T + 1) ^ (s - 1) ≤ wt C (k + 1) q := by
    intro q hq
    obtain ⟨-, -, hq2⟩ := mem_kidsG P hP2 C hC hq
    have h1 := diff_ge (Nat.cast_nonneg q) hs0 hs1
    have h2 : (T + 1) ^ (s - 1) ≤ ((q : ℝ) + 1) ^ (s - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    unfold wt
    calc s * (T + 1) ^ (s - 1) ≤ s * ((q : ℝ) + 1) ^ (s - 1) :=
          mul_le_mul_of_nonneg_left h2 hs0
      _ ≤ _ := h1
  -- Step B: sum over the children.
  have hB : ((kidsG P C k p).card : ℝ) * (s * (T + 1) ^ (s - 1)) ≤
      ∑ q ∈ kidsG P C k p, wt C (k + 1) q := by
    have := Finset.card_nsmul_le_sum (kidsG P C k p) (wt C (k + 1)) _ hA
    rwa [nsmul_eq_mul] at this
  -- Step C: T + 1 ≤ (p+2)^r, hence (T+1)^{s-1} ≥ (p+2)^{t-r}.
  have hC' : T + 1 ≤ ((p : ℝ) + 2) ^ r := by
    have h := diff_ge_conv (by linarith : (0 : ℝ) < p + 1) hr1
    have h1 : 1 ≤ ((p : ℝ) + 1) ^ (r - 1) := Real.one_le_rpow (by linarith) (by linarith)
    have h2 : 1 ≤ r * ((p : ℝ) + 1) ^ (r - 1) := by nlinarith
    have e : (p : ℝ) + 1 + 1 = p + 2 := by ring
    rw [e] at h
    linarith
  have hC'' : ((p : ℝ) + 2) ^ (t - r) ≤ (T + 1) ^ (s - 1) := by
    have h := Real.rpow_le_rpow_of_nonpos (by positivity) hC' (by linarith : s - 1 ≤ 0)
    rwa [← Real.rpow_mul (by positivity), mul_sub, hrs, mul_one] at h
  -- Step D: the number of children.
  have hD : ν * (r * (p : ℝ) ^ (r - 1)) ≤ ((kidsG P C k p).card : ℝ) :=
    le_trans (mul_le_mul_of_nonneg_left (diff_ge_conv hP hr1) hν) hN
  -- Step E: the weight of p.
  have hE : wt C k p ≤ t * (p : ℝ) ^ (t - 1) := by
    unfold wt; exact diff_le hP ht0 ht1
  -- Step F: (1/3)^r p^{t-1} ≤ p^{r-1} (p+2)^{t-r}.
  have hF : (1 / 3 : ℝ) ^ r * (p : ℝ) ^ (t - 1) ≤ (p : ℝ) ^ (r - 1) * ((p : ℝ) + 2) ^ (t - r) := by
    have h3p : (3 * (p : ℝ)) ^ (t - r) ≤ ((p : ℝ) + 2) ^ (t - r) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    have hsplit : (3 * (p : ℝ)) ^ (t - r) = (3 : ℝ) ^ (t - r) * (p : ℝ) ^ (t - r) :=
      Real.mul_rpow (by norm_num) hP.le
    have hpp : (p : ℝ) ^ (r - 1) * (p : ℝ) ^ (t - r) = (p : ℝ) ^ (t - 1) := by
      rw [← Real.rpow_add hP]; congr 1; ring
    have h3 : (1 / 3 : ℝ) ^ r ≤ (3 : ℝ) ^ (t - r) := by
      have : (1 / 3 : ℝ) ^ r = (3 : ℝ) ^ (-r) := by
        rw [Real.rpow_neg (by norm_num), one_div, Real.inv_rpow (by norm_num)]
      rw [this]
      exact Real.rpow_le_rpow_of_exponent_le (by norm_num) (by linarith)
    have hpt : 0 ≤ (p : ℝ) ^ (t - 1) := by positivity
    calc (1 / 3 : ℝ) ^ r * (p : ℝ) ^ (t - 1) ≤ (3 : ℝ) ^ (t - r) * (p : ℝ) ^ (t - 1) :=
          mul_le_mul_of_nonneg_right h3 hpt
      _ = (p : ℝ) ^ (r - 1) * (3 * (p : ℝ)) ^ (t - r) := by rw [hsplit, ← hpp]; ring
      _ ≤ (p : ℝ) ^ (r - 1) * ((p : ℝ) + 2) ^ (t - r) :=
          mul_le_mul_of_nonneg_left h3p (by positivity)
  -- Assembly.
  have hG : 0 ≤ s * ((p : ℝ) + 2) ^ (t - r) := by positivity
  have hcard0 : 0 ≤ ν * (r * (p : ℝ) ^ (r - 1)) := by positivity
  calc ν * (1 / 3 : ℝ) ^ r * wt C k p
      ≤ ν * (1 / 3 : ℝ) ^ r * (t * (p : ℝ) ^ (t - 1)) :=
        mul_le_mul_of_nonneg_left hE (by positivity)
    _ = ν * t * ((1 / 3 : ℝ) ^ r * (p : ℝ) ^ (t - 1)) := by ring
    _ ≤ ν * t * ((p : ℝ) ^ (r - 1) * ((p : ℝ) + 2) ^ (t - r)) :=
        mul_le_mul_of_nonneg_left hF (by positivity)
    _ = ν * (r * (p : ℝ) ^ (r - 1)) * (s * ((p : ℝ) + 2) ^ (t - r)) := by
        rw [← hrs]; ring
    _ ≤ ((kidsG P C k p).card : ℝ) * (s * (T + 1) ^ (s - 1)) :=
        mul_le_mul hD (mul_le_mul_of_nonneg_left hC'' hs0) hG (Nat.cast_nonneg _)
    _ ≤ ∑ q ∈ kidsG P C k p, wt C (k + 1) q := hB


end

variable {c : ℝ}

lemma kids_powSeqG (hc : 1 < c) (k n : ℕ) : kidsG P (powSeq c) k n = kidsG P (powSeq c) 0 n := by
  unfold kidsG; rw [ratio_powSeq hc k, ratio_powSeq hc 0]

lemma level_range_icG (hc : 1 < c) (Y : ℕ) :
    ∀ k, ∀ p ∈ (icForestG P c Y).level k,
      ((Y : ℝ) ^ powSeq c k ≤ p ∧ (p : ℝ) + 1 ≤ ((2 * Y + 1 : ℕ) : ℝ) ^ powSeq c k) := by
  have hC := powSeq_pos hc
  intro k
  induction k with
  | zero =>
    intro p hp
    simp only [WForest.level, icForestG, Finset.mem_Icc] at hp
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
    obtain ⟨-, hq1, hq2⟩ := mem_kidsG P hP2 (powSeq c) hC hqp
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

lemma level_sub_Rk_icG (hc : 1 < c) (Y k : ℕ) :
    (icForestG P c Y).level k ⊆ Rk (powSeq c) Y k := by
  intro p hp
  obtain ⟨h1, h2⟩ := level_range_icG P hP2 hc Y k p hp
  unfold Rk
  rw [Finset.mem_Icc]
  exact ⟨Nat.ceil_le.mpr h1, Nat.le_floor (by linarith)⟩

/-- The forest theorem for `C k = c^k` with roots `[Y, 2Y]`. -/
theorem ic_existsG (hc : 1 < c) (Y : ℕ) (hY : 1 ≤ Y) (ν β L : ℕ → ℝ) (hν : ∀ k, 0 ≤ ν k)
    (hL0 : L 0 ≤ (Y : ℝ) + 1) (hLpos : ∀ k, 0 < L k) (hβ : ∀ k, β k ≤ L k / 2)
    (hLsucc : ∀ k, L (k + 1) ≤ (ν k * (1 / 3 : ℝ) ^ ratio (powSeq c) k) * (L k / 2))
    (hbadC : ∀ k, ∑ n ∈ (Rk (powSeq c) Y k).filter (fun n : ℕ =>
        decide (ν k * (((n : ℝ) + 1) ^ ratio (powSeq c) k - (n : ℝ) ^ ratio (powSeq c) k) ≤
          ((kidsG P (powSeq c) k n).card : ℝ)) = false), wt (powSeq c) k n ≤ β k) :
    ∃ A : ℝ, 1 ≤ A ∧ ∀ k, P ⌊A ^ powSeq c (k + 1)⌋₊ := by
  have hC : ∀ k, 0 < powSeq c k := powSeq_pos hc
  have hC1 : ∀ k, 1 ≤ powSeq c k := powSeq_one_le hc
  have hCm : ∀ k, powSeq c k ≤ powSeq c (k + 1) := powSeq_mono hc
  let F := icForestG P c Y
  let f : ℕ → ℝ := fun k => ν k * (1 / 3 : ℝ) ^ ratio (powSeq c) k
  let good : ℕ → ℕ → Bool := fun k n =>
    decide (f k * wt (powSeq c) k n ≤ ∑ q ∈ kidsG P (powSeq c) k n, wt (powSeq c) (k + 1) q)
  have hw : ∀ k n, 0 ≤ wt (powSeq c) k n := wt_nonneg (powSeq c) hC
  have hf : ∀ k, 0 ≤ f k := fun k => by have := hν k; positivity
  have hdisj : ∀ k, Set.PairwiseDisjoint (↑(F.level k) : Set ℕ) (F.children k) :=
    fun k => kids_disjointG P hP2 (powSeq c) hC k _
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
      refine ⟨level_sub_Rk_icG P hP2 hc Y k hn.1, ?_⟩
      have hn1 : 1 ≤ n := by
        obtain ⟨h1, -⟩ := level_range_icG P hP2 hc Y k n hn.1
        have hY1 : (1 : ℝ) ≤ (Y : ℝ) ^ powSeq c k :=
          Real.one_le_rpow (by exact_mod_cast hY) (hC k).le
        have : (1 : ℝ) ≤ n := le_trans hY1 h1
        exact_mod_cast this
      have hnot : ¬ (f k * wt (powSeq c) k n ≤
          ∑ q ∈ kidsG P (powSeq c) k n, wt (powSeq c) (k + 1) q) :=
        decide_eq_false_iff_not.mp hn.2
      apply decide_eq_false_iff_not.mpr
      intro hcon
      exact hnot (kids_shareG P hP2 (powSeq c) hC hC1 hCm k n hn1 (ν k) (hν k) hcon)
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
  have hchain := fun k => mem_kidsG P hP2 (powSeq c) hC (hpath k)
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

/-- The bad weight at level `k` is at most `β_k`, given the exceptional-set count. -/
lemma bad_weightG (m : ℕ) (hc : 1 < c) (δ K : ℝ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K) {Y : ℕ} (hY : 1 ≤ Y)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badcG P m c n)).card : ℝ) ≤ K * (N : ℝ) ^ (1 - δ))
    (k : ℕ) :
    ∑ n ∈ (Rk (powSeq c) Y k).filter (fun n : ℕ =>
        decide (nuSeqG c m Y k * (((n : ℝ) + 1) ^ ratio (powSeq c) k -
          (n : ℝ) ^ ratio (powSeq c) k) ≤ ((kidsG P (powSeq c) k n).card : ℝ)) = false),
      wt (powSeq c) k n ≤ betaSeq c δ K Y k := by
  classical
  have hC := powSeq_pos hc k
  have hC1 := powSeq_one_le hc k
  set C := powSeq c k with hCdef
  set a := Real.log (2 * (Y : ℝ) + 2) with ha
  have ha0 : 0 < a := log_pos_Y Y
  have hYr : (1 : ℝ) ≤ Y := by exact_mod_cast hY
  set S := (Rk (powSeq c) Y k).filter (fun n : ℕ =>
        decide (nuSeqG c m Y k * (((n : ℝ) + 1) ^ ratio (powSeq c) k -
          (n : ℝ) ^ ratio (powSeq c) k) ≤ ((kidsG P (powSeq c) k n).card : ℝ)) = false) with hS
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
  have hsub : S ⊆ (Finset.range (N + 1)).filter (fun n => badcG P m c n) := by
    intro n hn
    obtain ⟨hlo, hhi, hnN⟩ := hmem n hn
    rw [Finset.mem_filter, Finset.mem_range]
    refine ⟨by omega, ?_⟩
    rw [hS, Finset.mem_filter] at hn
    have hnot := decide_eq_false_iff_not.mp hn.2
    rw [not_le, ratio_powSeq hc k, kids_powSeqG P hP2 hc k n] at hnot
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
    show ((kidsG P (powSeq c) 0 n).card : ℝ) <
      (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / (5 * Real.log (((n : ℝ) + 1) ^ c) ^ m)
    calc ((kidsG P (powSeq c) 0 n).card : ℝ) < nuSeqG c m Y k * (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) := hnot
      _ = (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / (5 * (c ^ (k + 1) * a) ^ m) := by
          unfold nuSeqG; rw [← ha]; ring
      _ ≤ (((n : ℝ) + 1) ^ c - (n : ℝ) ^ c) / (5 * Real.log (((n : ℝ) + 1) ^ c) ^ m) := by
          apply div_le_div_of_nonneg_left hℓ (by have := pow_pos hlogpos m; linarith)
            (by have := pow_le_pow_left₀ hlogpos.le hlogn m; linarith)
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
    have h1 : (S.card : ℝ) ≤ (((Finset.range (N + 1)).filter (fun n => badcG P m c n)).card : ℝ) := by
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


/-- **Conditional existence for a fixed `Y`** (predicate `P`, log-power `m`). -/
theorem exists_of_YG (m : ℕ) (hm : 1 ≤ m) (hc : 1 < c) (δ K : ℝ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badcG P m c n)).card : ℝ) ≤
        K * (N : ℝ) ^ (1 - δ))
    (Y : ℕ) (hY : 1 ≤ Y)
    (hB0 : K * (2 * (Y : ℝ) + 1) * qY δ Y ≤ ((Y : ℝ) + 1) / 2)
    (hS : 1 + 10 * c * Real.log (2 * (Y : ℝ) + 2) * (3 : ℝ) ^ c ≤ (1 / qY δ Y) ^ ((c - 1) / m)) :
    ∃ B : ℝ, ∀ k, P ⌊B ^ c ^ k⌋₊ := by
  obtain ⟨A, hA1, hA⟩ := ic_existsG P hP2 hc Y hY (nuSeqG c m Y) (betaSeq c δ K Y) (LSeqG c m Y)
    (fun k => (nuSeqG_pos hc m Y k).le) (le_refl _) (LSeqG_pos hc m Y)
    (beta_leG hc m hm δ K hK hY hB0 hS)
    (fun k => by rw [ratio_powSeq hc k]; exact le_refl _)
    (bad_weightG P hP2 m hc δ K hδ1 hK hY hexc)
  refine ⟨A ^ c, fun k => ?_⟩
  have hA0 : 0 ≤ A := by linarith
  have e : (A ^ c) ^ (c ^ k) = A ^ powSeq c (k + 1) := by
    rw [← Real.rpow_mul hA0, powSeq_succ, mul_comm]
    rfl
  rw [e]
  exact hA k

/-- **General forest theorem**: any predicate `P` (with `P q → 2 ≤ q`), log-power `m ≥ 1`,
ratio `c > 1`. -/
theorem mills_constG (m : ℕ) (hm : 1 ≤ m) (hc : 1 < c) (δ K : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hK : 0 ≤ K)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badcG P m c n)).card : ℝ) ≤
        K * (N : ℝ) ^ (1 - δ)) :
    ∃ B : ℝ, ∀ k, P ⌊B ^ c ^ k⌋₊ := by
  obtain ⟨Y, hY, hB0, hS⟩ := exists_YG hc m hm δ K hδ hδ1 hK
  exact exists_of_YG P hP2 m hm hc δ K hδ1 hK hexc Y hY hB0 hS

end Gen

/-! ### Twin primes -/

/-- `q` is the smaller member of a twin-prime pair. -/
def TwinP (q : ℕ) : Prop := q.Prime ∧ (q + 2).Prime

instance : DecidablePred TwinP := fun q => by unfold TwinP; infer_instance

lemma twin_two_le : ∀ q, TwinP q → 2 ≤ q := fun _ h => h.1.two_le

/-- **Twin Mills constants (conditional).** If, for ratio `c > 1`, the integers `n` whose
child interval contains fewer than `ℓ(n)/(5 log²(n+1)^c)` lower twin primes have a
power-saving count, then there is `B` with `⌊B^{c^k}⌋` and `⌊B^{c^k}⌋ + 2` both prime for
every `k`. The hypothesis is a conjecture: an "almost all short intervals" form of
Hardy–Littlewood for twins. -/
theorem mills_twin_const {c : ℝ} (hc : 1 < c) (δ K : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hK : 0 ≤ K)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badcG TwinP 2 c n)).card : ℝ) ≤
        K * (N : ℝ) ^ (1 - δ)) :
    ∃ B : ℝ, ∀ k, (⌊B ^ c ^ k⌋₊).Prime ∧ (⌊B ^ c ^ k⌋₊ + 2).Prime :=
  mills_constG TwinP twin_two_le 2 (by norm_num) hc δ K hδ hδ1 hK hexc

open Real in
/-- Twin Mills constant for the golden ratio (conditional). -/
theorem mills_twin_goldenRatio (δ K : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badcG TwinP 2 goldenRatio n)).card : ℝ) ≤
        K * (N : ℝ) ^ (1 - δ)) :
    ∃ B : ℝ, ∀ k, (⌊B ^ goldenRatio ^ k⌋₊).Prime ∧ (⌊B ^ goldenRatio ^ k⌋₊ + 2).Prime :=
  mills_twin_const one_lt_goldenRatio δ K hδ hδ1 hK hexc

/-- Sanity check: the prime case `m = 1` of the general theorem. -/
theorem mills_constG_prime {c : ℝ} (hc : 1 < c) (δ K : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hK : 0 ≤ K)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badcG Nat.Prime 1 c n)).card : ℝ) ≤
        K * (N : ℝ) ^ (1 - δ)) :
    ∃ B : ℝ, ∀ k, (⌊B ^ c ^ k⌋₊).Prime :=
  mills_constG Nat.Prime (fun _ h => h.two_le) 1 le_rfl hc δ K hδ hδ1 hK hexc

end MillsForest
