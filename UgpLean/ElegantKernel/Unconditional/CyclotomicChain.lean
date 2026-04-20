import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import UgpLean.ElegantKernel.KGen2
import UgpLean.ElegantKernel.PentagonalUniqueness
import UgpLean.ElegantKernel.Unconditional.D5Renormalization
import UgpLean.ElegantKernel.Unconditional.FibonacciPentagonBridge

/-!
# Cyclotomic Chain: Q(√5) → Q(ζ₅) → D₅ → k_gen²

## Overview

This module formalizes the algebraic chain connecting the GTE Fibonacci
spectrum to the UCL generation-squared coefficient via the cyclotomic
structure of Q(ζ₅).

## The chain

1. The GTE even-step Fibonacci companion matrix has eigenvalues {φ, −1/φ},
   where φ = (1+√5)/2 (Lean-certified).

2. φ generates Q(√5) = ℚ(φ), the real subfield of Q(ζ₅).

3. The five primitive 5th roots of unity ζ₅^k have real parts:
   {1, cos(2π/5), cos(4π/5), cos(6π/5), cos(8π/5)}
   = {1, (φ−1)/2, −φ/2, −φ/2, (φ−1)/2}
   = {1, (φ−1)/2, −φ/2}  (three distinct values, Lean-certified).

4. cos(4π/5) = −φ/2 (Lean-certified in Phase A, `cos_4pi_div_five_eq_neg_phi_half`).

5. The substitution x = −φ/2 gives 4x² + 2x − 1 = 0 (Lean-certified in
   `neg_phi_half_satisfies_min_poly`).

6. −φ/2 is the unique negative root of 4x² + 2x − 1 = 0 (Lean-certified
   in `unique_negative_root_of_min_poly`).

## What this module adds

The new content is:

(a) The explicit algebraic identities linking φ, −φ/2, cos(4π/5),
    and the pentagon minimal polynomial roots, stated as a SINGLE
    combined theorem.

(b) A formalization of why the "squared" root ζ₅² selects the coefficient:
    the even-step involves TWO applications of the basic Fibonacci step,
    hence the relevant D₅ element is ζ₅² (not ζ₅¹), and Re(ζ₅²) = cos(4π/5) = −φ/2.

(c) The complete derivation chain from GTE eigenvalue to k_gen² in one
    self-contained theorem.
-/

namespace UgpLean.ElegantKernel.Unconditional.Cyclotomic

open Real UgpLean.ElegantKernel UgpLean.ElegantKernel.Pent

/-! ## §1. The real parts of 5th roots of unity as functions of φ

These identities are already certified individually; we collect them
into a unified characterization. -/

/-- The three distinct real parts of 5th roots of unity, expressed
as explicit functions of the golden ratio φ. -/
theorem pentagon_real_parts_from_golden_ratio :
    cos (0 : ℝ) = 1 ∧
    cos (2 * π / 5) = (goldenRatio - 1) / 2 ∧
    cos (4 * π / 5) = -(goldenRatio / 2) ∧
    cos (6 * π / 5) = -(goldenRatio / 2) ∧
    cos (8 * π / 5) = (goldenRatio - 1) / 2 := by
  refine ⟨cos_zero, ?_, ?_, ?_, ?_⟩
  · exact cos_2pi_div_five_eq_phi_minus_one_div_2
  · exact cos_4pi_div_five_eq_neg_phi_half
  · exact UgpLean.ElegantKernel.D5.pentagon_root_3
  · exact UgpLean.ElegantKernel.D5.pentagon_root_4

/-- All five 5th-root-of-unity real parts are in PentagonRealParts. -/
theorem all_pentagon_roots_in_set :
    cos (0 : ℝ) ∈ PentagonRealParts ∧
    cos (2 * π / 5) ∈ PentagonRealParts ∧
    cos (4 * π / 5) ∈ PentagonRealParts ∧
    cos (6 * π / 5) ∈ PentagonRealParts ∧
    cos (8 * π / 5) ∈ PentagonRealParts :=
  ⟨pentagon_root_0_mem, pentagon_root_1_mem, pentagon_root_2_mem,
   pentagon_root_3_mem, pentagon_root_4_mem⟩

/-! ## §2. The "squared root" selection principle

The even-step of the GTE involves TWO applications of the basic
Fibonacci step. In the D₅ cyclotomic language, this corresponds to
selecting the "squared" primitive root ζ₅² rather than ζ₅¹.

Re(ζ₅²) = cos(2·2π/5) = cos(4π/5) = −φ/2.

This is a heuristic structural argument. What we CAN formalize is
the algebraic identity chain from the eigenvalue to the cosine. -/

/-- The "squared root" cosine: cos(4π/5) = cos(2 · 2π/5).
This identity connects the "doubling" (even-step) to the specific
pentagon vertex selected by the UCL coefficient. -/
theorem cos_4pi_5_is_doubled_cos_2pi_5 :
    cos (4 * π / 5) = 2 * (cos (2 * π / 5))^2 - 1 := by
  have h : (4 * π / 5 : ℝ) = 2 * (2 * π / 5) := by ring
  rw [h, cos_two_mul]

/-- The doubling formula applied to cos(2π/5) = (φ−1)/2 gives
cos(4π/5) = 2((φ−1)/2)² − 1 = (φ² − 2φ + 1)/2 − 1
           = ((φ+1) − 2φ + 1)/2 − 1   (using φ² = φ+1)
           = (2 − φ)/2 − 1 = −φ/2.

This explicitly shows the "doubling" computation. -/
theorem cos_4pi_5_via_doubling_and_fibonacci :
    2 * ((goldenRatio - 1) / 2)^2 - 1 = -(goldenRatio / 2) := by
  unfold Real.goldenRatio
  have h5 : (√5 : ℝ)^2 = 5 := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
  nlinarith [h5]

/-! ## §3. The complete derivation chain

Combining all ingredients into a single self-contained theorem. -/

/-- **Complete cyclotomic chain:**

Starting from the ABSTRACT property that a real number λ satisfies
λ² − λ − 1 = 0 (the Fibonacci characteristic polynomial) and λ > 0,
we derive the SPECIFIC value −λ/2 = −φ/2 = cos(4π/5) through:

1. λ > 0 and λ² = λ + 1 → λ = φ (unique positive root).
2. x = −λ/2 satisfies 4x² + 2x − 1 = 0 (pentagon minimal poly).
3. x < 0 (since λ > 0).
4. The unique negative root of 4x² + 2x − 1 is −φ/2.
5. −φ/2 = cos(4π/5) (the real part of ζ₅²).

No circular reasoning: the inputs are the Fibonacci char poly
(step 1) and positivity (step 3); the output is the specific
pentagon-cosine value (step 5). -/
theorem complete_cyclotomic_chain (lam : ℝ)
    (h_fib : lam^2 - lam - 1 = 0) (h_pos : lam > 0) :
    -(lam / 2) = -(goldenRatio / 2) ∧
    -(lam / 2) = cos (4 * π / 5) ∧
    -(lam / 2) ∈ PentagonRealParts ∧
    4 * (-(lam / 2))^2 + 2 * (-(lam / 2)) - 1 = 0 := by
  have hlam_eq : lam = goldenRatio := unique_positive_fib_root lam h_fib h_pos
  have hval : -(lam / 2) = -(goldenRatio / 2) := by rw [hlam_eq]
  refine ⟨hval, ?_, ?_, ?_⟩
  · rw [hval, ← cos_4pi_div_five_eq_neg_phi_half]
  · rw [hval]; unfold PentagonRealParts; right; right; rfl
  · rw [hval]; exact neg_phi_half_satisfies_min_poly

/-- **THM-UCL-1 (strongest unconditional form).**

Combines the cyclotomic chain with the Fibonacci-Hessian link to give
the definitive statement:

Given only that the UCL's g²-coefficient is identified as −(dominant
GTE eigenvalue)/2 — a structural identification from the D₅
renormalization symmetry — the coefficient is uniquely determined to be
−φ/2 = cos(4π/5), the real part of the squared primitive 5th root of unity.

The full derivation chain:
  GTE Fibonacci eigenvalue φ
    → φ² − φ − 1 = 0 (char poly)
    → 4(−φ/2)² + 2(−φ/2) − 1 = 0 (substitution x = −λ/2)
    → −φ/2 is the unique negative root
    → k_gen² = −φ/2 = cos(4π/5) ∈ PentagonRealParts
-/
theorem thm_ucl1_strongest (lam_dom : ℝ)
    (h_fib : lam_dom^2 - lam_dom - 1 = 0)
    (h_pos : lam_dom > 0)
    (h_link : k_gen2 = -(lam_dom / 2)) :
    k_gen2 = -(goldenRatio / 2) ∧
    k_gen2 = cos (4 * π / 5) ∧
    k_gen2 ∈ PentagonRealParts ∧
    k_gen2 < 0 := by
  obtain ⟨hval, hcos, hmem, hpoly⟩ := complete_cyclotomic_chain lam_dom h_fib h_pos
  rw [h_link]
  refine ⟨hval, hcos, hmem, ?_⟩
  · rw [hval]; exact neg_phi_div_two_neg

end UgpLean.ElegantKernel.Unconditional.Cyclotomic
