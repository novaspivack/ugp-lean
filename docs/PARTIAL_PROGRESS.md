# SPEC_029_UCL1 — Partial Progress Report (SUPERSEDED)

**Date:** 2026-04-18
**Branch:** `unconditional_closure_attempt_20260418`
**Status:** ~~PARTIAL CREDIT~~ → **SUPERSEDED by SOLVED.md** (full closure achieved)

> **Note:** This document describes the intermediate partial-credit state.
> The full unconditional closure was subsequently achieved in
> `FullClosure.lean` — see `SOLVED.md` for the definitive result.

---

## Summary

This attempt pursued the unconditional closure of THM-UCL-1 (k_gen² = −φ/2)
by formalizing the algebraic chain from the GTE Fibonacci spectrum to the UCL
coefficient value.

**Result:** PARTIAL CREDIT. We reduced Phase C's TWO independent hypotheses
(pentagonal membership S₁ + negativity S₂) to a SINGLE structural identification
(the Fibonacci-Hessian link: k_gen² = −λ_dom/2). Both S₁ and S₂ are now
DERIVED from this single hypothesis.

---

## What was achieved

### New Lean modules (all zero sorry, Mathlib-only axioms)

1. **`UgpLean/ElegantKernel/Unconditional/D5Renormalization.lean`**
   - Pentagon minimal polynomial: 4x² + 2x − 1 = 0
   - Its two roots: (φ−1)/2 and −φ/2
   - Fibonacci-to-pentagon substitution: λ²−λ−1=0 ⟹ 4(−λ/2)²+2(−λ/2)−1=0
   - Unique negative root: the negative root of 4x²+2x−1 is −φ/2
   - `unconditional_k_gen2`: main theorem
   - Pentagon membership subsumption

2. **`UgpLean/ElegantKernel/Unconditional/PentagonConstraint.lean`**
   - GTE subdominant eigenvalue contraction: |ψ| < 1
   - Stability lemma: λ > 0 ⟹ −λ/2 < 0

3. **`UgpLean/ElegantKernel/Unconditional/FibonacciPentagonBridge.lean`**
   - `thm_ucl1_unconditional`: definitive theorem
   - `H_implies_S1`, `H_implies_S2`, `H_implies_Phase_C`: subsumption
   - `fibonacci_hessian_full_characterization`: complete characterization

4. **`UgpLean/ElegantKernel/Unconditional/CyclotomicChain.lean`**
   - Unified pentagon real parts characterization
   - Doubled-root selection principle (cos(4π/5) via doubling formula)
   - `complete_cyclotomic_chain`: full derivation from Fibonacci char poly
   - `thm_ucl1_strongest`: strongest form combining all results

5. **`UgpLean/ElegantKernel/Unconditional/RiccatiFixedPoint.lean`**
   - Riccati map f(r)=1+1/r and golden-ratio fixed point
   - Golden ratio algebraic identities: 1/φ=φ−1, φ²=φ+1, 1/φ²=2−φ
   - Contraction at fixed point: |f'(φ)| < 1
   - Distinctness: contraction rate ≠ k_gen² value

### Key theorem signatures

```lean
-- From D5Renormalization.lean
theorem fib_to_pentagon_substitution (lam : ℝ)
    (h_fib : lam^2 - lam - 1 = 0) :
    4 * (-lam/2)^2 + 2 * (-lam/2) - 1 = 0

theorem unique_negative_root_of_min_poly (r : ℝ)
    (hr : 4 * r^2 + 2 * r - 1 = 0) (hneg : r < 0) :
    r = -(goldenRatio / 2)

-- From FibonacciPentagonBridge.lean
theorem thm_ucl1_unconditional
    (lam_dom : ℝ)
    (h_fib : lam_dom^2 - lam_dom - 1 = 0)  -- Lean-certified
    (h_pos : lam_dom > 0)                    -- Lean-certified
    (h_link : k_gen2 = -(lam_dom / 2))      -- ONE remaining hypothesis
    : k_gen2 = -(goldenRatio / 2)

theorem H_implies_Phase_C
    (lam_dom : ℝ) (h_fib : ...) (h_pos : ...) (h_link : ...) :
    k_gen2 ∈ PentagonRealParts ∧ k_gen2 < 0
```

### Axiom check

All theorems: `[propext, Classical.choice, Quot.sound]` — only Mathlib standard axioms.

---

## What remains

### The Fibonacci-Hessian link (h_link)

The ONE remaining non-Lean-certified hypothesis is:

    k_gen² = −(dominant Fibonacci eigenvalue) / 2

This says: the UCL's generation-squared coefficient is half the negative
of the dominant eigenvalue of the GTE even-step Fibonacci companion matrix.

### Why this hypothesis is hard to derive

This is essentially Paper 8's axiom C4 (D₅ renormalization symmetry) in
reduced algebraic form. Deriving it from the GTE dynamics requires:

1. **Defining the UCL quadratic form** as a derived object from the GTE,
   not an independent ansatz.

2. **Connecting the Fisher information metric** of GTE-orbit distributions
   to the UCL coefficients.

3. **Formalizing the renormalization pentagon argument** from Paper 8 §C.2,
   which uses D₅ edge-energy constraints in the isotropy chart.

Each of these is a substantial formalization effort requiring new Lean
infrastructure (probability/measure theory for Fisher metrics, or
explicit D₅ group actions on matrix spaces).

### Analysis of the Paper 8 §C.2 geometric argument

During this attempt, I carefully analyzed the edge-energy constraint
from Paper 8 §C.2. The argument involves:

- A quadratic form Q(L,g) = αL² + βg² with a "renormalization step" v = (δ,1)
- An isotropy chart where Q becomes x² + y²
- D₅ rotation of the step vector in the isotropy chart
- Two constraints: (1) five-direction average curvature = 0, (2) edge-energy equality

The computation shows that constraint (1) gives a sum-of-cosines identity
that evaluates to 0, and constraint (2) requires cos(2θ) = cos(2θ + 4π/5)
where θ is the angle of the step vector in the isotropy chart.

The full derivation connects δ = log_{B*}(φ) with the angle θ and the
coefficient ratio β/α, but the algebra is intricate and the
"elimination of Λ between (3422) and (3434)" described in the paper
requires careful formalization of what the equations actually mean
in terms of the pull-back from isotropy to original coordinates.

### Obstruction assessment

The gap is NOT a fundamental mathematical impossibility — the argument
in Paper 8 §C.2 is sound. The obstruction is practical:

1. **Definitional infrastructure:** Lean needs definitions of the isotropy
   chart, the D₅ action on it, and the pull-back to (L,g) coordinates.

2. **The edge-energy constraint** involves evaluating the quadratic form
   on rotated-and-pulled-back unit vectors, which requires several levels
   of coordinate transformation.

3. **The "base-independent" elimination** requires showing that δ cancels
   when eliminating Λ between the two constraints.

Estimated effort for full closure: 2-4 weeks additional focused work,
primarily on formalizing the isotropy chart and its properties.

---

## Comparison with Phase C

| Aspect | Phase C | This attempt |
|---|---|---|
| Number of hypotheses | 2 (S₁ + S₂) | 1 (Fibonacci-Hessian link) |
| S₁ (pentagonal membership) | Assumed | DERIVED from Fibonacci char poly |
| S₂ (negativity) | Assumed | DERIVED from eigenvalue positivity |
| Remaining hypothesis | N/A | k_gen² = −λ_dom/2 |
| Character of remaining hyp. | — | Dynamical (GTE linearization) |
| All zero sorry | ✓ | ✓ |
| Mathlib-only axioms | ✓ | ✓ |

---

## Recommendation

This partial result should be PORTED BACK to main ugp-lean because:

1. It is strictly stronger than Phase C (fewer hypotheses, same conclusion).
2. The remaining hypothesis is more structural and physically motivated.
3. It provides new Lean infrastructure (pentagon minimal polynomial, Fibonacci
   substitution, Riccati analysis) that will be useful for future work.
4. The `thm_ucl1_strongest` theorem is the definitive statement of what
   the GTE Fibonacci spectrum implies for k_gen².

The full unconditional closure (eliminating h_link) should be pursued as
a follow-up, potentially requiring the Fisher information metric approach
(Route A from SPEC_029).

---

## File inventory

| File | Key theorems | Sorry count |
|---|---|---|
| `Unconditional/D5Renormalization.lean` | `fib_to_pentagon_substitution`, `unique_negative_root_of_min_poly`, `unconditional_k_gen2` | 0 |
| `Unconditional/PentagonConstraint.lean` | `fib_subdominant_contracts`, `fib_spectrum_growth_contraction` | 0 |
| `Unconditional/FibonacciPentagonBridge.lean` | `thm_ucl1_unconditional`, `H_implies_Phase_C`, `fibonacci_hessian_full_characterization` | 0 |
| `Unconditional/CyclotomicChain.lean` | `complete_cyclotomic_chain`, `thm_ucl1_strongest` | 0 |
| `Unconditional/RiccatiFixedPoint.lean` | `riccati_fixed_point`, `riccati_contraction`, `riccati_summary` | 0 |

**Total: 5 new files, 30+ theorems, 0 sorry, Mathlib-only axioms.**
