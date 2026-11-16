import MillsForest.Gen

/-!
# Mills constants in an arithmetic progression

Instance of `mills_constG` with `P q := q.Prime ∧ q % Q = a` and log-power `m = 2`.
With `m = 1` the bad threshold `ℓ/(5 log)` exceeds the expected count `ℓ/(φ(Q) log)` as soon as
`φ(Q) ≥ 5`, so almost every interval would be bad; `m = 2` keeps the threshold below the
expectation for every fixed `Q`.

The hypothesis `hexc` is the analytic input: a power-saving count of the `n` whose child
interval contains fewer than `ℓ(n)/(5 log²(n+1)^c)` primes `≡ a (mod Q)`. It is expected to
follow from zero-density estimates for the Dirichlet `L`-functions mod `Q` (not formalized).
-/

open Real

namespace MillsForest

/-- `q` is a prime congruent to `a` modulo `Q`. -/
def APP (Q a : ℕ) (q : ℕ) : Prop := q.Prime ∧ q % Q = a

instance (Q a : ℕ) : DecidablePred (APP Q a) := fun q => by unfold APP; infer_instance

lemma APP_two_le (Q a : ℕ) : ∀ q, APP Q a q → 2 ≤ q := fun _ h => h.1.two_le

/-- **Mills constants in an arithmetic progression (conditional on `hexc`).** -/
theorem mills_AP_const {c : ℝ} (hc : 1 < c) (Q a : ℕ) (δ K : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1)
    (hK : 0 ≤ K)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badcG (APP Q a) 2 c n)).card : ℝ) ≤
        K * (N : ℝ) ^ (1 - δ)) :
    ∃ B : ℝ, ∀ k, (⌊B ^ c ^ k⌋₊).Prime ∧ ⌊B ^ c ^ k⌋₊ % Q = a :=
  mills_constG (APP Q a) (APP_two_le Q a) 2 (by norm_num) hc δ K hδ hδ1 hK hexc

/-- The golden-ratio case. -/
theorem mills_AP_goldenRatio (Q a : ℕ) (δ K : ℝ) (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badcG (APP Q a) 2 goldenRatio n)).card : ℝ) ≤
        K * (N : ℝ) ^ (1 - δ)) :
    ∃ B : ℝ, ∀ k, (⌊B ^ goldenRatio ^ k⌋₊).Prime ∧ ⌊B ^ goldenRatio ^ k⌋₊ % Q = a :=
  mills_AP_const one_lt_goldenRatio Q a δ K hδ hδ1 hK hexc

end MillsForest
