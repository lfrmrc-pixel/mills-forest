import MillsForest.Main

/-!
# The share of the prime children (Lemma "level" of the paper)

If the child interval of `p` contains at least `ν · ℓ(p)` primes, where
`ℓ(p) = (p+1)^r - p^r`, then the prime children carry at least the fraction
`ν · 3^{-r}` of the weight `|I_k(p)|`.

As a consequence, `exists_prime_representing_count` replaces the weight hypothesis of
`exists_prime_representing` by a hypothesis on **prime counts in short intervals**. This
is exactly the kind of statement given by exceptional-set estimates (`μ(θ) < 1`
unconditionally for `θ > 2/15`, or Selberg's bound under RH).

The only elementary inputs are Bernoulli's inequalities for real exponents, which are
already in Mathlib.
-/

open Finset

namespace MillsForest

/-- `s (x+1)^{s-1} ≤ (x+1)^s - x^s` for `0 ≤ s ≤ 1`. -/
lemma diff_ge {x s : ℝ} (hx : 0 ≤ x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    s * (x + 1) ^ (s - 1) ≤ (x + 1) ^ s - x ^ s := by
  have hy : 0 < x + 1 := by linarith
  have hu : -1 ≤ -1 / (x + 1) := by
    rw [neg_div, neg_le_neg_iff, div_le_one hy]; linarith
  have hb := rpow_one_add_le_one_add_mul_self hu hs0 hs1
  have h1 : 1 + -1 / (x + 1) = x / (x + 1) := by field_simp <;> ring
  rw [h1, Real.div_rpow hx hy.le] at hb
  have hys : 0 < (x + 1) ^ s := Real.rpow_pos_of_pos hy s
  rw [div_le_iff₀ hys] at hb
  rw [Real.rpow_sub_one hy.ne']
  have e : (1 + s * (-1 / (x + 1))) * (x + 1) ^ s = (x + 1) ^ s - s * ((x + 1) ^ s / (x + 1)) := by
    field_simp <;> ring
  linarith [e]

/-- `(x+1)^s - x^s ≤ s x^{s-1}` for `0 ≤ s ≤ 1`, `x > 0`. -/
lemma diff_le {x s : ℝ} (hx : 0 < x) (hs0 : 0 ≤ s) (hs1 : s ≤ 1) :
    (x + 1) ^ s - x ^ s ≤ s * x ^ (s - 1) := by
  have hu : -1 ≤ 1 / x := by have : 0 < 1 / x := by positivity
                             linarith
  have hb := rpow_one_add_le_one_add_mul_self hu hs0 hs1
  have h1 : 1 + 1 / x = (x + 1) / x := by field_simp <;> ring
  rw [h1, Real.div_rpow (by linarith) hx.le] at hb
  have hxs : 0 < x ^ s := Real.rpow_pos_of_pos hx s
  rw [div_le_iff₀ hxs] at hb
  rw [Real.rpow_sub_one hx.ne']
  have e : (1 + s * (1 / x)) * x ^ s = x ^ s + s * (x ^ s / x) := by field_simp
  linarith [e]

/-- `r x^{r-1} ≤ (x+1)^r - x^r` for `r ≥ 1`, `x > 0`. -/
lemma diff_ge_conv {x r : ℝ} (hx : 0 < x) (hr : 1 ≤ r) :
    r * x ^ (r - 1) ≤ (x + 1) ^ r - x ^ r := by
  have hu : -1 ≤ 1 / x := by have : 0 < 1 / x := by positivity
                             linarith
  have hb := one_add_mul_self_le_rpow_one_add hu hr
  have h1 : 1 + 1 / x = (x + 1) / x := by field_simp <;> ring
  rw [h1, Real.div_rpow (by linarith) hx.le] at hb
  have hxs : 0 < x ^ r := Real.rpow_pos_of_pos hx r
  rw [le_div_iff₀ hxs] at hb
  rw [Real.rpow_sub_one hx.ne']
  have e : (1 + r * (1 / x)) * x ^ r = x ^ r + r * (x ^ r / x) := by field_simp
  linarith [e]

section

variable (C : ℕ → ℝ) (hC : ∀ k, 0 < C k) (hC1 : ∀ k, 1 ≤ C k) (hCm : ∀ k, C k ≤ C (k + 1))
include hC hC1 hCm

/-- **Share of the prime children.** -/
theorem kids_share (k p : ℕ) (hp : 1 ≤ p) (ν : ℝ) (hν : 0 ≤ ν)
    (hN : ν * (((p : ℝ) + 1) ^ ratio C k - (p : ℝ) ^ ratio C k) ≤ ((kids C k p).card : ℝ)) :
    ν * (1 / 3 : ℝ) ^ ratio C k * wt C k p ≤ ∑ q ∈ kids C k p, wt C (k + 1) q := by
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
  have hA : ∀ q ∈ kids C k p, s * (T + 1) ^ (s - 1) ≤ wt C (k + 1) q := by
    intro q hq
    obtain ⟨-, -, hq2⟩ := mem_kids C hC hq
    have h1 := diff_ge (Nat.cast_nonneg q) hs0 hs1
    have h2 : (T + 1) ^ (s - 1) ≤ ((q : ℝ) + 1) ^ (s - 1) :=
      Real.rpow_le_rpow_of_nonpos (by positivity) (by linarith) (by linarith)
    unfold wt
    calc s * (T + 1) ^ (s - 1) ≤ s * ((q : ℝ) + 1) ^ (s - 1) :=
          mul_le_mul_of_nonneg_left h2 hs0
      _ ≤ _ := h1
  -- Step B: sum over the children.
  have hB : ((kids C k p).card : ℝ) * (s * (T + 1) ^ (s - 1)) ≤
      ∑ q ∈ kids C k p, wt C (k + 1) q := by
    have := Finset.card_nsmul_le_sum (kids C k p) (wt C (k + 1)) _ hA
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
  have hD : ν * (r * (p : ℝ) ^ (r - 1)) ≤ ((kids C k p).card : ℝ) :=
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
    _ ≤ ((kids C k p).card : ℝ) * (s * (T + 1) ^ (s - 1)) :=
        mul_le_mul hD (mul_le_mul_of_nonneg_left hC'' hs0) hG (Nat.cast_nonneg _)
    _ ≤ ∑ q ∈ kids C k p, wt C (k + 1) q := hB

end

/-- **Main theorem, prime-count form.** The single remaining hypothesis concerns the
integers `n` of the explicit range `R_k` whose child interval contains fewer than
`ν_k · ℓ_k(n)` primes: their total weight must be at most `β k`. -/
theorem exists_prime_representing_count (C : ℕ → ℝ) (hC : ∀ k, 0 < C k)
    (hC1 : ∀ k, 1 ≤ C k) (hCm : ∀ k, C k ≤ C (k + 1)) (hC0 : C 0 = 1)
    (Y : ℕ) (hY : 1 ≤ Y) (ν β L : ℕ → ℝ) (hν : ∀ k, 0 ≤ ν k)
    (hL0 : L 0 ≤ (((Finset.Icc Y (2 * Y)).filter Nat.Prime).card : ℝ))
    (hLpos : ∀ k, 0 < L k) (hβ : ∀ k, β k ≤ L k / 2)
    (hLsucc : ∀ k, L (k + 1) ≤ (ν k * (1 / 3 : ℝ) ^ ratio C k) * (L k / 2))
    (hbadC : ∀ k, ∑ n ∈ (Rk C Y k).filter (fun n : ℕ =>
        decide (ν k * (((n : ℝ) + 1) ^ ratio C k - (n : ℝ) ^ ratio C k) ≤
          ((kids C k n).card : ℝ)) = false), wt C k n ≤ β k) :
    ∃ A : ℝ, ∀ k, (⌊A ^ C k⌋₊).Prime := by
  apply exists_prime_representing C hC hC0 Y (fun k => ν k * (1 / 3 : ℝ) ^ ratio C k) β L
    (fun k => by have := hν k; positivity) hL0 hLpos hβ hLsucc
  intro k
  refine le_trans ?_ (hbadC k)
  apply Finset.sum_le_sum_of_subset_of_nonneg
  · intro n hn
    rw [Finset.mem_filter] at hn ⊢
    refine ⟨hn.1, ?_⟩
    have hn1 : 1 ≤ n := by
      have hmem := hn.1
      unfold Rk at hmem
      rw [Finset.mem_Icc] at hmem
      have hpos : 0 < (Y : ℝ) ^ C k := Real.rpow_pos_of_pos (by exact_mod_cast hY) _
      have := Nat.ceil_pos.mpr hpos
      omega
    have hbad := hn.2
    simp only [decide_eq_false_iff_not, not_le] at hbad ⊢
    by_contra hc
    push_neg at hc
    have := kids_share C hC hC1 hCm k n hn1 (ν k) (hν k) hc
    linarith
  · intro n _ _
    exact wt_nonneg C hC k n

end MillsForest
