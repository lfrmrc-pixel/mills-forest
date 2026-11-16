# Mills forest: formal companion and primality certificates

Supplementary material for the paper

> L. F. Marcelino, *Mills-type prime-representing constants for exponents below two: a compactness argument* (submitted).

## Contents

| folder | content | license |
|---|---|---|
| [`MillsForest/`](MillsForest/) | Lean 4 / Mathlib formalization of the deduction (see its own README for the statements and how to build) | Apache License 2.0 (`LICENSE`) |
| [`certificates/`](certificates/) | ECPP primality certificates for the primes of the explicit chain for the golden ratio (Section 6 of the paper) | CC BY 4.0 |

## Building the Lean project

Install [elan](https://github.com/leanprover/elan), then:

```
cd MillsForest
lake exe cache get
lake build
```

The toolchain is pinned in `MillsForest/lean-toolchain`.

## Licenses

- The Lean code is released under the Apache License 2.0 (see `LICENSE`), the same license as Mathlib.
- The certificates in `certificates/` are released under the Creative Commons Attribution 4.0 International License (CC BY 4.0, https://creativecommons.org/licenses/by/4.0/).

## Use of AI

The formalization and the certificates were produced with the substantial assistance of an AI system (Claude, Anthropic), as stated in the paper. The formal proofs are checked by the Lean kernel; the certificates can be checked with PARI/GP (`primecertisvalid`) or Primo.
