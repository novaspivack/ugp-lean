# Defensibility Ledger — THM-UCL-1: k_gen² = −φ/2

**Filed:** 2026-04-17
**Target:** Lean-certify that k_gen² = −φ/2 (golden ratio / 2, with negative sign).
**Sandbox:** `~/ugp-lean-exp`, branch `theoretical_path_closure_sandbox`.
**Reference SPEC:** `SPEC_028_TP1_THEORETICAL_PATH_CLOSURE.md`.
**Paper references:** Paper 1 §3 `eq:kernel` line 414; Paper 1 §5 line 538; Paper 6 §2.5.4 lines 223–291 (derivation chain).

## Executive summary

**VERDICT: DEFER — structurally underspecified.**

Phase 1.5 uncovered that the derivation of k_gen² = −φ/2 from the Fibonacci companion-matrix spectrum via D₅ pentagonal RG symmetry, as stated in Paper 6 §2.5.4, is **incomplete**: the key "equal-edge" constraint in the paper (Eq. (272) of Paper 6) is identically satisfied for any k_gen² (reduces to the trivial Pythagorean identity (1 − cos²(π/5)) / sin²(π/5) = 1).  The derivation gestures at how cos(π/5) = φ/2 could force the value, but the chain of equations as published does not actually achieve this.

Phase 1.5 also confirmed criteria (D) rigidity (no alternative structural expression is within 14× of the fit) and partial (A) pre-specification (the Fibonacci companion matrix IS Lean-certified independently in `UgpLean.GTE.StructuralTheorems`).  But without a rigorous derivation chain, committing Lean effort to this target would certify a conditional theorem whose premise (the D₅ symmetry structure) is unproven.

**Consistent with SPEC_028_TP1 §7 "A theorem turns out to be [incompletely derived]":** the target is reformulated as an open problem for deeper research, and the paper acknowledges the coefficient as PSLQ-identified with a suggestive but incomplete D₅-Fibonacci derivation.

## Criterion (A): pre-specification of the structural premise

### Primary premise (as claimed in Paper 1 §3): "k_gen² = −φ/2 from the Fibonacci companion-matrix spectrum on the GTE even step."

**Source found:** Paper 6 §2.5.4 gives a derivation chain involving:
1. Isotropy chart `(x, y) = (√k_L²·(L−L*), √|k_gen²|·g)` rendering the UCL quadratic form `Q = x² + y²` (up to sign).
2. Renormalization vector `u = (δ, 1)` where δ = log_{B★}(φ).
3. Postulate of D₅ pentagonal rotational symmetry of the RG flow.
4. Two constraints:
   - Discrete isotropy: `k_L²·δ² + k_gen² = Λ` (eigenvalue constraint).
   - Equal-edge: `k_L²·δ²·cos²(π/5) + k_gen²·sin²(π/5) = k_L²·δ²`.
5. Elimination + identity `cos(π/5) = φ/2` yields `k_gen² = −cos(π/5) = −φ/2`.

### Audit finding (verification script, 2026-04-17)

**The equal-edge constraint as written (Eq. (272) in Paper 6) is vacuous.**  Solving:
```
k_L²·δ²·cos²(π/5) + k_gen²·sin²(π/5) = k_L²·δ²
⇒ k_gen²·sin²(π/5) = k_L²·δ²·(1 − cos²(π/5))
⇒ k_gen²·sin²(π/5) = k_L²·δ²·sin²(π/5)            [Pythagorean]
⇒ k_gen² = k_L²·δ²
```

This gives k_gen² = **+**k_L²·δ² (positive), not −φ/2 ≈ −0.809.  For k_L² = 7/512 ≈ 0.01367 and any δ, k_L²·δ² is a positive number, not −φ/2.

The paper's subsequent step ("using the identity cos(π/5) = φ/2, we obtain k_gen² = −cos(π/5) = −φ/2") skips the derivation link.  There is no visible chain from "Eq. (272) holds trivially" to "k_gen² = −cos(π/5)."  The negative sign is justified on line 287 as a STABILITY argument ("ensures that the quadratic form g² coefficient makes the RG flow converge to a stable fixed point, preventing runaway behavior") — a physical intuition, not a mathematical derivation.

The derivation uses genuine mathematical facts (cos(π/5) = φ/2 is a standard identity; the Fibonacci companion matrix eigenvalues are {φ, −1/φ}, Lean-certified in `UgpLean.GTE.StructuralTheorems.fib_companion_char_poly` with zero sorry), but does not assemble them into a chain that uniquely yields k_gen² = −φ/2.

### (A) Status: FAIL.

The premise "k_gen² = −φ/2 follows from the Fibonacci companion-matrix spectrum via D₅ pentagonal symmetry" is not a rigorously derivable statement in the current framework.  It is a PLAUSIBLE STRUCTURAL ANALOGY with suggestive numerical agreement, but the chain is incomplete.

## Criterion (B): non-trivial intermediate chain

Under Paper 6's derivation, the intermediate lemmas are:
- Eq. (259) discrete isotropy constraint → one-parameter family `k_gen² = Λ − k_L²·δ²`.
- Eq. (272) equal-edge constraint → vacuous as written.
- cos(π/5) = φ/2 trigonometric identity → standard.

The chain has non-trivial intermediate steps, but (272) as written does not advance the derivation beyond the trivial identity.  **Status: PARTIAL.**

## Criterion (C): independent predictions

Proposed independent predictions of D₅ pentagonal RG symmetry:

1. **Pentagon-related trigonometric constants in the kernel.**  D₅ symmetry should also fix k_gen (the linear-g coefficient) via pentagon angles.  Paper 6 §2.5.4+1 claims k_gen = π/2 via "quarter-turn gauge normalization" — a gauge choice, not a derivation (Paper 6 line 295 explicitly admits this is a "normalization convention" rather than a derived constant).

2. **D₅ rotational invariance of the UCL in the isotropy chart.**  The UCL applied to triples at different generations should respect 5-fold rotational invariance in the (L, g) plane.  This has not been tested empirically.

3. **Other pentagon angles in the kernel.**  If D₅ is real, k_L² should also have a pentagon-trigonometric form.  But k_L² = 7/512 = δ/2^(n−1) is Lean-certified from ridge geometry, not pentagon geometry.

No independent prediction checks empirically against existing UGP data in a way that distinguishes the D₅ premise from a post-hoc fit.  **Status: FAIL.**

## Criterion (D): rigidity

From COMP-P01-X2 (narrow-basis saturation null):
- Closest basis expression to empirical k_gen² = −0.80925: (−1/2)·φ = −φ/2 at 288 ppm.
- Next closest: (−13/16) at 4016 ppm — **14× worse**.
- Third closest: (−4/13)·φ² at 4573 ppm — 16× worse.
- All alternatives within the basis {(p/q)·φ^k : |p|,q ≤ 16, k ∈ [−3,+3]} are ≥ 4× worse.

**Status: PASS.**  The target −φ/2 is rigidly preferred within the narrow structural basis.

## Criterion (E): sparsity

COMP-P01-X2 saturation null:
- 10 ppm: 0.56 %
- 100 ppm: 4.66 %
- 500 ppm: 20.41 %  ← at the dual-path precision (288 ppm), basis is moderately saturating.
- 1 % precision: 38.03 %

The basis {(p/q)·φ^k} is more saturating than the pure-rational-triple basis used for THM-UCL-3, but less saturating than the full kernel {π, φ, p/q, e, log p, √n}.  At PDG precision 288 ppm, 20 % of random log-uniform targets have a match.

**Status: MARGINAL.**

## Criterion (F): falsification surface

If the D₅ pentagonal RG symmetry argument is wrong:
1. Some other algebraic form should fit empirical k_gen² to better precision.  Currently the dual-path deviation is 288 ppm; if the "true" value is different, one expects a better match elsewhere.  **Open question.**
2. The UCL should admit other structural identities that contradict the D₅ hypothesis.  **Open question.**

No concrete falsifiable prediction beyond "does the dual-path agreement hold at future higher precision."

**Status: WEAK PASS.**

## Summary decision matrix

| Criterion | Status | Weight |
|---|---|---|
| (A) Pre-specification | **FAIL** | blocking |
| (B) Non-trivial chain | PARTIAL | informative |
| (C) Independent predictions | FAIL | informative |
| (D) Rigidity | PASS | strong evidence |
| (E) Sparsity | MARGINAL | partial evidence |
| (F) Falsification | WEAK PASS | informative |

**Overall:** (A) FAILS blocking — the derivation chain is not rigorously complete.  (D) strongly supports the claim numerically, (E) gives partial support at target precision.  The net picture: the numerical claim k_gen² = −φ/2 is well-supported as a correlation (and rigidly preferred in its basis), but the **derivation** from the Fibonacci companion matrix via D₅ pentagonal symmetry is incomplete.

**DECISION: DEFER.**

Committing Lean effort would produce either (a) a conditional theorem with D₅ symmetry as an unproven hypothesis (weak evidence), or (b) a Lean-certified proof that replicates an incomplete chain (bad precedent).  Either path risks "rigorous numerology."

## What this target becomes

Paper 1 round-8 rewrite will:
1. **Retain** k_gen² = −φ/2 in the Elegant Kernel table with its numerical agreement (dual-path 288 ppm).
2. **Reclassify** it from "derived via Fibonacci companion-matrix spectrum" to "**numerically identified; derivation via D₅ pentagonal RG symmetry incomplete in current framework**."
3. **Promote** the reconstruction of the D₅ derivation (or alternative derivation) to a named Open Problem: `Open Problem (x): Rigorous derivation of k_gen² = −φ/2 from GTE structure.`

## Proposed follow-up work (beyond this program's current scope)

If this target becomes important:

1. **Derivation reconstruction.**  Rework Paper 6 §2.5.4 explicitly, starting from the GTE even-step update map and identifying exactly which structural input forces the pentagon symmetry.  Ideally: derive D₅ from the GTE, not assume it.

2. **Alternative derivation routes.**
   - From Fibonacci eigenvalues via a Hessian argument: formulate the Fisher-metric Hessian of the log-UCL at the GTE fixed point rigorously, compute it from the even-step dynamics, show it equals −φ.
   - From a Lie-group argument: identify a continuous symmetry of the GTE that has a 5-fold discrete subgroup (D₅).
   - From modular arithmetic: exploit the appearance of φ in F_n mod small primes.

3. **Lean formalization of Paper 6 Eq. (272) as a conditional theorem**: "IF the RG flow on the (L,g) plane is D₅-invariant in the isotropy chart AND k_L²·δ² is interpreted as [specific quantity], THEN k_gen² = −φ/2."  This requires a clean definition of the RG flow's action on the coefficient space.

Estimated additional effort: weeks-to-months of independent theoretical work.  Not undertaken as part of SPEC_028_TP1.

## Artifacts filed

- This ledger: `~/ugp-lean-exp/docs/DEFENSIBILITY_THM_UCL_1.md`.
- Narrow-basis saturation null: `papers/01_SM/canonical_run/comp_p01_X2_narrow_basis_saturation_k_gen2.json` (SHA `553f9259a7d42572…`).
- Paper 6 derivation audit (inline in this ledger).

## Historical note

User confirmed MDL/Fibonacci contexts come from earlier work in MFRR, Particle Derivations, and other papers.  A deeper search through those repos might yield an alternative, rigorous derivation of k_gen² = −φ/2 that is not reproduced in Paper 6 §2.5.4.  **Not undertaken** as part of this ledger; it is deferred to the broader Open Problem (x).
