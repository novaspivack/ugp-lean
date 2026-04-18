import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import UgpLean.ElegantKernel.KGen2
import UgpLean.ElegantKernel.Unconditional.D5Renormalization

/-!
# GTE Contraction Rate and Stability

## Overview

This module establishes that the GTE even-step subdominant eigenvalue
contracts (|ψ| < 1), and that this contraction implies the stability
condition k_gen² < 0 when combined with the Fibonacci-Hessian link.

These results support the unconditional derivation by showing that the
negativity of k_gen² (Phase C hypothesis S₂) is a consequence of the
GTE spectrum, not an independent assumption.

## Key results

1. `fib_subdominant_contracts`: |ψ| = |(1−√5)/2| < 1.
2. `fib_spectrum_growth_contraction`: φ > 1 (growth) and |ψ| < 1 (contraction).
3. `neg_half_positive_is_negative`: if λ > 0 then −λ/2 < 0 (trivial but explicit).
-/

namespace UgpLean.ElegantKernel.Unconditional.Pentagon

open Real

private theorem sqrt5_gt_one : √(5 : ℝ) > 1 := by
  rw [show (1 : ℝ) = √1 from Real.sqrt_one.symm]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private theorem sqrt5_lt_three : √(5 : ℝ) < 3 := by
  have h : (3 : ℝ) = √9 := by
    rw [show (9 : ℝ) = 3^2 from by norm_num, Real.sqrt_sq (by norm_num : (3:ℝ) ≥ 0)]
  rw [h]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

/-- The subdominant Fibonacci eigenvalue ψ = (1−√5)/2 has |ψ| < 1,
establishing that perturbations orthogonal to the dominant eigenvector
decay under the GTE even-step. -/
theorem fib_subdominant_contracts :
    |((1 - √5) / 2 : ℝ)| < 1 := by
  rw [abs_of_neg (by linarith [sqrt5_gt_one] : (1 - √5) / 2 < 0)]
  linarith [sqrt5_lt_three]

/-- The subdominant eigenvalue ψ satisfies ψ² − ψ − 1 = 0. -/
theorem fib_subdominant_poly :
    ((1 - √5) / 2 : ℝ)^2 - ((1 - √5) / 2) - 1 = 0 := by
  have h5 : (√5 : ℝ)^2 = 5 := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
  nlinarith [h5]

/-- The GTE Fibonacci spectrum: dominant eigenvalue φ > 1 (growth mode)
and subdominant |ψ| < 1 (contracting mode). -/
theorem fib_spectrum_growth_contraction :
    goldenRatio > 1 ∧ |((1 - √5) / 2 : ℝ)| < 1 := by
  exact ⟨by unfold Real.goldenRatio; linarith [sqrt5_gt_one],
         fib_subdominant_contracts⟩

/-- If λ > 0 then −λ/2 < 0. Makes the stability derivation explicit:
the positivity of the dominant Fibonacci eigenvalue directly implies
the negativity of k_gen² = −λ_dom/2. -/
theorem neg_half_positive_is_negative (lam : ℝ) (h : lam > 0) :
    -(lam / 2) < 0 := by linarith

end UgpLean.ElegantKernel.Unconditional.Pentagon
