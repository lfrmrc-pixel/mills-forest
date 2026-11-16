# MillsForest: Lean 4 / Mathlib formalization

This is the formal companion to *Mills-type prime-representing constants for exponents below two: a compactness argument* (L. F. Marcelino).

## Status

For constant ratios `c`, every deduction is formally verified, starting from the literature's measure-theoretic definition of the exceptional set (Bazzanella–Perelli 2000; Gafni–Tao 2026, Def. 1.1) and ending with the existence of a prime-representing constant. The proofs use only the standard axioms (`propext`, `Classical.choice`, `Quot.sound`), and there is no `sorry`.

The single input taken from the literature is `μ(θ) < 1` for a suitable `θ`. For `c = φ` one needs `θ ∈ (1/3, 1/φ²)`, for example `θ = 0.37`, where `μ(0.37) ≤ 4/3 − 0.37 ≈ 0.963`. This comes from Gafni–Tao Thm 1.2 with the Ingham–Huxley bounds, or from Bazzanella–Perelli Thm 2(i) plus Cor. 1(i).

The paper's result under RH with exponents `k^{2+η}` is **not** formalized.

## Main statements

```
mills_goldenRatio_of_litExc : ∀ (θ ξ K X0 : ℝ), 0 < θ → φ * θ < φ - 1 →
  0 < ξ → ξ < 1 → 0 ≤ K → 0 ≤ X0 → LitExcHyp θ ξ K X0 →
  ∃ B, ∀ k : ℕ, Nat.Prime ⌊B ^ φ ^ k⌋₊

LitExcHyp θ ξ K X0 := ∀ X ≥ X0,
  volume {t ∈ [X, 2X] : |ψ(t + t^θ) - ψ(t) - t^θ| ≥ t^θ / 8} ≤ K · X^ξ

mills_const_of_litExc : the same for any 1 < c, under θ ≤ 1/2, c θ < 1, c θ < c - 1
mills_twin_goldenRatio : twin-prime analogue (Gen.lean), conditional on a conjecture
```

Here ψ is Mathlib's `Chebyshev.psi`.

## Files

| file | content |
|---|---|
| `Forest.lean` | König's lemma for finitely branching forests; global mass recursion (`levels_nonempty`) |
| `Mills.lean` | Mills' nested-interval construction for arbitrary exponents (`mills_of_chain`) |
| `Main.lean` | Forest of Mills chains, weight form (`exists_prime_representing`) |
| `Share.lean` | Share of the prime children, via Bernoulli (`kids_share`); prime-count form |
| `Phi.lean` | Closing of the recursion for constant `c > 1` (`mills_const`, `mills_goldenRatio`) |
| `Exc.lean` | Discrete exceptional hypothesis ⇒ `hexc` (window lemma by double counting; counting step) |
| `Psi.lean` | From ψ to prime counts: Λ-window = ψ difference, prime-power count, `discreteExc_of_psiExc` |
| `Lit.lean` | From the measure of real exceptional points to integer counts, and from window `t^θ` to `⌊x^θ⌋`: `psiExc_of_litExc`, `mills_goldenRatio_of_litExc`, `mills_const_of_litExc` |
| `Gen.lean` | Generalisation to any predicate `P` and log-power `m`; twin primes (conditional) |

## Build

```
lake exe cache get   # Mathlib build cache
lake build
lake env lean Check.lean   # prints axioms and statements
```

The toolchain is pinned in `lean-toolchain`, and the Mathlib revision in `lake-manifest.json`. Building needs several GB of RAM.
