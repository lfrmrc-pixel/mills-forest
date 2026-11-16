import MillsForest.GenS

/-!
# Mills constants with almost-prime values (`Ω ≤ 2`)

Instance of `mills_constS` with `S = P2 := {n ≥ 2 : Ω(n) ≤ 2}`
(`Ω = ArithmeticFunction.cardFactors`). The hypothesis `hexc` is the counting form of the
analytic input (in the paper it comes from Matomäki's theorem on almost primes in almost all
very short intervals, Theorem `thm:Mat22`; that passage is **not** formalized here).
-/

open Real

namespace MillsForest

/-- `n ≥ 2` with at most two prime factors counted with multiplicity. -/
def P2 (n : ℕ) : Prop := 2 ≤ n ∧ ArithmeticFunction.cardFactors n ≤ 2

instance : DecidablePred P2 := fun n => by unfold P2; infer_instance

lemma P2_two_le : ∀ q, P2 q → 2 ≤ q := fun _ h => h.1

lemma P2_of_prime {p : ℕ} (hp : p.Prime) : P2 p :=
  ⟨hp.two_le, by rw [ArithmeticFunction.cardFactors_apply_prime hp]; norm_num⟩

/-- **Tappa 3: almost-prime Mills constants from the counting hypothesis.** -/
theorem mills_P2_of_count {c : ℝ} (hc : 1 < c) (ν : ℝ) (hν : 0 < ν) (δ K : ℝ) (hδ : 0 < δ)
    (hδ1 : δ ≤ 1) (hK : 0 ≤ K)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badNu P2 ν c n)).card : ℝ) ≤
        K * (N : ℝ) ^ (1 - δ)) :
    ∃ B : ℝ, ∀ k, 2 ≤ ⌊B ^ c ^ k⌋₊ ∧ ArithmeticFunction.cardFactors ⌊B ^ c ^ k⌋₊ ≤ 2 :=
  mills_constS P2 P2_two_le hc ν hν δ K hδ hδ1 hK hexc

/-- Monotonicity: a larger set has fewer bad integers. -/
lemma badNu_mono {S T : ℕ → Prop} [DecidablePred S] [DecidablePred T]
    (hST : ∀ n, S n → T n) {ν c : ℝ} {n : ℕ} (h : badNu T ν c n) : badNu S ν c n := by
  unfold badNu at h ⊢
  refine lt_of_le_of_lt ?_ h
  refine Nat.cast_le.mpr (Finset.card_le_card (fun x hx => ?_))
  unfold childS at hx ⊢
  rw [Finset.mem_filter] at hx ⊢
  exact ⟨hx.1, hST x hx.2⟩

/-- The prime counting hypothesis implies the `P2` one (primes are in `P2`). -/
theorem mills_P2_of_prime_count {c : ℝ} (hc : 1 < c) (ν : ℝ) (hν : 0 < ν) (δ K : ℝ)
    (hδ : 0 < δ) (hδ1 : δ ≤ 1) (hK : 0 ≤ K)
    (hexc : ∀ N : ℕ, 1 ≤ N →
      (((Finset.range (N + 1)).filter (fun n => badNu Nat.Prime ν c n)).card : ℝ) ≤
        K * (N : ℝ) ^ (1 - δ)) :
    ∃ B : ℝ, ∀ k, 2 ≤ ⌊B ^ c ^ k⌋₊ ∧ ArithmeticFunction.cardFactors ⌊B ^ c ^ k⌋₊ ≤ 2 := by
  refine mills_P2_of_count hc ν hν δ K hδ hδ1 hK (fun N hN => le_trans ?_ (hexc N hN))
  refine Nat.cast_le.mpr (Finset.card_le_card (fun n hn => ?_))
  rw [Finset.mem_filter] at hn ⊢
  exact ⟨hn.1, badNu_mono (S := Nat.Prime) (T := P2) (fun _ h => P2_of_prime h) hn.2⟩

end MillsForest
