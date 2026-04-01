# Machine-Checked Formalizations for the Twin-Prime Program

**To:** Research team (mirror-prime-pairs project)  
**From:** ugp-lean formalization  
**Date:** 2026-03-31  
**Build:** `lake build` — 8187 jobs, 0 errors, 0 sorry

---

## Summary

We have machine-checked (in Lean 4 + Mathlib) the algebraic infrastructure
that the twin-prime program builds on. These results are in two modules:

| Module | File |
|--------|------|
| `UgpLean.GTE.MirrorDualConjecture` | `UgpLean/GTE/MirrorDualConjecture.lean` |
| `UgpLean.GTE.ResonantFactory` | `UgpLean/GTE/ResonantFactory.lean` |

Repository: <https://github.com/novaspivack/ugp-lean>

---

## Formalized Theorems

### 1. Exact divisor-count formula (strengthens note 048 §R1)

**Lean name:** `tau_ridge_exact`  
**Statement:** For all n ≥ 5: τ(2ⁿ − 16) = 5 · τ(2^(n−4) − 1).  
**Proof:** Ridge factorization (2ⁿ−16 = 16·(2^(n−4)−1)) + coprimality
of 2^4 and 2^k−1 (odd) + Mathlib's `Nat.Coprime.card_divisors_mul`.  
**Location:** `MirrorDualConjecture.lean`, line 269.  
**Relevance:** Quantifies the divisor-pair "raw material" at each ridge level.

### 2. Branch linearization (formalizes note 042, Theorem 9)

**Lean name:** `branch_linearization`  
**Statement:** c₁(b₂, q₂) = b₂·(q₂ − 13) + B(q₂), where B(q) = (q+7)(q−13)+20.  
**Location:** `ResonantFactory.lean`, line 46.  
**Relevance:** This is the algebraic identity that makes c₁ affine in the
divisor b₂ for fixed q₂ — the foundation of the branch linearization used
to construct the resonant factory.

### 3. Factory gap-2 property

**Lean name:** `factory_gap_two`  
**Statement:** Q₊(t) = Q₋(t) + 2 for all t ∈ ℕ.  
**Location:** `ResonantFactory.lean`, line 87.  
**Relevance:** Machine-checks that the factory quadratics produce exact
gap-2 candidates. Also: D₊ = 119513 is proved prime (`factoryDp_prime`).

### 4. Local density / Hasse check (formalizes note 049 §local-density)

**Lean names:** `localDensity_3` through `localDensity_43`, `hasse_check_no_obstruction`  
**Statement:** For each good prime p ∈ {3, 7, 13, 23, 29, 31, 37, 41, 43}:
ρ_F(p) is computed exactly, and ρ_F(p) < p (no local obstruction).  
**Location:** `ResonantFactory.lean`, lines 115–157.  
**Relevance:** Machine-checks the Hasse condition that the singular series
S = ∏(1 − ρ(p)/p)/(1−1/p)⁴ > 0. The residue computations are verified
against the actual factory constants L = 13501400, D₋ = 119511, D₊ = 119513.

### 5. Product algebra factorization (formalizes note 059, Proposition 1)

**Lean name:** `factory_product_factorization`  
**Statement:** F(t) = Q₋(t) · Q₊(t), definitionally, with both factors > 0.  
**Location:** `ResonantFactory.lean`, line 170.  
**Relevance:** The structural identity that the factory quartic factors
through the product algebra A = K₋ × K₊. Since λ is completely
multiplicative, λ(F(t)) = λ(Q₋(t)) · λ(Q₊(t)).

### 6. Supporting coprimality lemma

**Lean name:** `coprime_pow2_mersenne`  
**Statement:** Nat.Coprime (2^a) (2^b − 1) for b ≥ 1.  
**Location:** `MirrorDualConjecture.lean`, line 251.  
**Relevance:** Used in the τ exact formula; also a general-purpose lemma
(any power of 2 is coprime to any Mersenne-like odd number).

---

## What is NOT formalized (and why)

- **The Liouville cancellation Σλ(F(t)) = o(T):** This is the single open
  conjecture (R3 / Ray Buchstab-Selberg-Delange). It cannot be formalized
  because it is not proved.

- **Norm-representation Q±(t) = N_{K±}(Lt+β±)/L:** This requires formalizing
  imaginary quadratic fields in Lean, which is beyond current scope.

- **Ω-additivity on F(t):** Mathlib v4.29.0-rc6 does not export `Nat.Ω`
  (the big-omega function). The factorization F = Q₋·Q₊ is proved
  definitionally; the Ω-additivity follows from any formalization of
  complete multiplicativity of λ.

---

## How to cite

Reference these by Lean theorem name and module path:
```
UgpLean.tau_ridge_exact              — MirrorDualConjecture.lean:269
UgpLean.branch_linearization         — ResonantFactory.lean:46
UgpLean.factory_gap_two              — ResonantFactory.lean:87
UgpLean.localDensity_3..43           — ResonantFactory.lean:115-140
UgpLean.hasse_check_no_obstruction   — ResonantFactory.lean:152
UgpLean.factory_product_factorization — ResonantFactory.lean:170
UgpLean.coprime_pow2_mersenne        — MirrorDualConjecture.lean:251
```
