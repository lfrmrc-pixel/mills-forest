import MillsForest.Forest
import MillsForest.Mills

/-!
# The forest of Mills chains

For an exponent sequence `C` with `C 0 = 1` and `C k > 0`, the roots are the primes in
`[Y, 2Y]`. The children of `p` at level `k` are the primes `q` with
`p ^ r_k ≤ q` and `q + 1 < (p+1) ^ r_k`, where `r_k = C(k+1)/C k`. The weight of `n` at
level `k` is the length of `[n^{1/C_k}, (n+1)^{1/C_k})`.

The main theorem `exists_prime_representing` says that, for **any** choice of a
propagation factor `f`, a bad-mass bound `β` and a lower bound `L` that satisfy the
numerical recursion, a prime-representing constant exists. The single number-theoretic
input is `hbadR`: an upper bound for the total weight of the bad integers in an
**explicit** range `R_k`, which does not depend on the tree. No condition of the form
"every chosen prime has a good child" is assumed.

What remains outside this file, and comes from analytic number theory (see the paper),
is the verification of `hbadR` and of the recursion for concrete `f, β, L`:
* the good nodes are those whose interval carries `≥ ℓ/4` of `ψ`, which gives
  `f k ≍ 1/log X`;
* the bad mass is controlled by the exceptional set `μ(θ) < 1`, or by Selberg's
  bound under RH.
-/

open Finset

namespace MillsForest

/-- The exponent ratio `r_k = C(k+1)/C k`. -/
noncomputable def ratio (C : ℕ → ℝ) (k : ℕ) : ℝ := C (k + 1) / C k

/-- Children of `p` at level `k`: primes `q` with `⌈p^r⌉ ≤ q ≤ ⌈(p+1)^r⌉ - 2`. -/
noncomputable def kids (C : ℕ → ℝ) (k p : ℕ) : Finset ℕ :=
  (Finset.Icc ⌈(p : ℝ) ^ ratio C k⌉₊ (⌈((p : ℝ) + 1) ^ ratio C k⌉₊ - 2)).filter Nat.Prime

/-- The forest of Mills chains with roots the primes in `[Y, 2Y]`. -/
noncomputable def millsForest (C : ℕ → ℝ) (Y : ℕ) : WForest :=
  ⟨(Finset.Icc Y (2 * Y)).filter Nat.Prime, kids C⟩

/-- Weight of `n` at level `k`: the length of `[n^{1/C_k}, (n+1)^{1/C_k})`. -/
noncomputable def wt (C : ℕ → ℝ) (k n : ℕ) : ℝ :=
  ((n : ℝ) + 1) ^ (1 / C k) - (n : ℝ) ^ (1 / C k)

section

variable (C : ℕ → ℝ) (hC : ∀ k, 0 < C k)
include hC

lemma ratio_pos (k : ℕ) : 0 < ratio C k := div_pos (hC (k + 1)) (hC k)

lemma wt_nonneg (k n : ℕ) : 0 ≤ wt C k n := by
  unfold wt
  have : 0 ≤ 1 / C k := by have := hC k; positivity
  linarith [Real.rpow_le_rpow (Nat.cast_nonneg n) (by linarith : (n : ℝ) ≤ n + 1) this]

lemma mem_kids {k p q : ℕ} (hq : q ∈ kids C k p) :
    q.Prime ∧ (p : ℝ) ^ ratio C k ≤ q ∧ (q : ℝ) + 1 < ((p : ℝ) + 1) ^ ratio C k := by
  unfold kids at hq
  rw [Finset.mem_filter, Finset.mem_Icc] at hq
  obtain ⟨⟨h1, h2⟩, hp⟩ := hq
  refine ⟨hp, Nat.ceil_le.mp h1, ?_⟩
  have h2' : q + 2 ≤ ⌈((p : ℝ) + 1) ^ ratio C k⌉₊ := by have := hp.two_le; omega
  have hlt : (⌈((p : ℝ) + 1) ^ ratio C k⌉₊ : ℝ) < ((p : ℝ) + 1) ^ ratio C k + 1 :=
    Nat.ceil_lt_add_one (Real.rpow_nonneg (by positivity) _)
  have : ((q + 2 : ℕ) : ℝ) ≤ ⌈((p : ℝ) + 1) ^ ratio C k⌉₊ := by exact_mod_cast h2'
  push_cast at this
  linarith

lemma kids_lt {k p p' q q' : ℕ} (hpp : p < p') (hq : q ∈ kids C k p) (hq' : q' ∈ kids C k p') :
    q < q' := by
  obtain ⟨-, -, hq2⟩ := mem_kids C hC hq
  obtain ⟨-, hq'1, -⟩ := mem_kids C hC hq'
  have hle : ((p : ℝ) + 1) ^ ratio C k ≤ (p' : ℝ) ^ ratio C k := by
    apply Real.rpow_le_rpow (by positivity) _ (ratio_pos C hC k).le
    exact_mod_cast hpp
  have : (q : ℝ) < q' := by linarith
  exact_mod_cast this

lemma kids_disjoint (k : ℕ) (s : Set ℕ) : s.PairwiseDisjoint (kids C k) := by
  intro p _ p' _ hne
  rw [Function.onFun, Finset.disjoint_left]
  intro q hq hq'
  rcases lt_or_gt_of_ne hne with h | h
  · exact (lt_irrefl q) (kids_lt C hC h hq hq')
  · exact (lt_irrefl q) (kids_lt C hC h hq' hq)

/-- Every node of level `k` lies in `[Y^{C_k}, (2Y+1)^{C_k} - 1]`. -/
lemma level_range (hC0 : C 0 = 1) (Y : ℕ) :
    ∀ k, ∀ p ∈ (millsForest C Y).level k,
      ((Y : ℝ) ^ C k ≤ p ∧ (p : ℝ) + 1 ≤ ((2 * Y + 1 : ℕ) : ℝ) ^ C k) := by
  intro k
  induction k with
  | zero =>
    intro p hp
    simp only [WForest.level, millsForest, Finset.mem_filter, Finset.mem_Icc] at hp
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
    obtain ⟨-, hq1, hq2⟩ := mem_kids C hC hqp
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

/-- The explicit range `R_k`, which does not depend on the tree. -/
noncomputable def Rk (Y k : ℕ) : Finset ℕ :=
  Finset.Icc ⌈(Y : ℝ) ^ C k⌉₊ ⌊(((2 * Y + 1 : ℕ) : ℝ)) ^ C k⌋₊

omit hC in
lemma level_sub_Rk (hC : ∀ k, 0 < C k) (hC0 : C 0 = 1) (Y k : ℕ) :
    (millsForest C Y).level k ⊆ Rk C Y k := by
  intro p hp
  obtain ⟨h1, h2⟩ := level_range C hC hC0 Y k p hp
  unfold Rk
  rw [Finset.mem_Icc]
  exact ⟨Nat.ceil_le.mpr h1, Nat.le_floor (by linarith)⟩

end

/-- **Main theorem (formal skeleton).** Let `C 0 = 1`, `C k > 0`, and let
`good k n` be the statement that `n` passes the fraction `f k` of its weight to its
prime children. Suppose the bad integers of the explicit range `R_k` have total weight
at most `β k`, and that `f, β, L` satisfy the recursion. Then there is `A` with
`⌊A ^ C k⌋` prime for every `k`. -/
theorem exists_prime_representing (C : ℕ → ℝ) (hC : ∀ k, 0 < C k) (hC0 : C 0 = 1)
    (Y : ℕ) (f β L : ℕ → ℝ) (hf : ∀ k, 0 ≤ f k)
    (hL0 : L 0 ≤ (((Finset.Icc Y (2 * Y)).filter Nat.Prime).card : ℝ))
    (hLpos : ∀ k, 0 < L k) (hβ : ∀ k, β k ≤ L k / 2)
    (hLsucc : ∀ k, L (k + 1) ≤ f k * (L k / 2))
    (hbadR : ∀ k, ∑ n ∈ (Rk C Y k).filter (fun n =>
        decide (f k * wt C k n ≤ ∑ q ∈ kids C k n, wt C (k + 1) q) = false),
        wt C k n ≤ β k) :
    ∃ A : ℝ, ∀ k, (⌊A ^ C k⌋₊).Prime := by
  set F := millsForest C Y with hF
  let good : ℕ → ℕ → Bool := fun k n =>
    decide (f k * wt C k n ≤ ∑ q ∈ kids C k n, wt C (k + 1) q)
  have hw : ∀ k n, 0 ≤ wt C k n := wt_nonneg C hC
  have hdisj : ∀ k, Set.PairwiseDisjoint (↑(F.level k) : Set ℕ) (F.children k) :=
    fun k => kids_disjoint C hC k _
  have hgood : ∀ k, ∀ p ∈ F.level k, good k p = true →
      f k * wt C k p ≤ ∑ q ∈ F.children k p, wt C (k + 1) q := by
    intro k p _ h
    exact of_decide_eq_true h
  have hbad : ∀ k, ∑ p ∈ (F.level k).filter (fun p => good k p = false), wt C k p ≤ β k := by
    intro k
    refine le_trans ?_ (hbadR k)
    apply Finset.sum_le_sum_of_subset_of_nonneg
    · exact Finset.filter_subset_filter _ (level_sub_Rk C hC hC0 Y k)
    · intro n _ _; exact hw k n
  have hmass0 : F.mass (wt C) 0 = (((Finset.Icc Y (2 * Y)).filter Nat.Prime).card : ℝ) := by
    unfold WForest.mass
    have : ∀ n, wt C 0 n = 1 := by
      intro n; unfold wt; rw [hC0]; simp
    simp only [this, Finset.sum_const, nsmul_eq_mul, mul_one]
    rfl
  have hne := F.levels_nonempty (wt C) good f β L hw hf hdisj hgood hbad
    (by rw [hmass0]; exact hL0) hLpos hβ hLsucc
  obtain ⟨p, hp0, hpath⟩ := F.exists_path hne
  have hchain : ∀ k, (p (k + 1)).Prime ∧ (p k : ℝ) ^ ratio C k ≤ p (k + 1) ∧
      (p (k + 1) : ℝ) + 1 < ((p k : ℝ) + 1) ^ ratio C k :=
    fun k => mem_kids C hC (hpath k)
  obtain ⟨A, hA⟩ := mills_of_chain C hC p (fun k => (hchain k).2.1) (fun k => (hchain k).2.2)
  refine ⟨A, fun k => ?_⟩
  rw [hA k]
  cases k with
  | zero =>
    have : p 0 ∈ (Finset.Icc Y (2 * Y)).filter Nat.Prime := hp0
    exact (Finset.mem_filter.mp this).2
  | succ k => exact (hchain k).1

end MillsForest
