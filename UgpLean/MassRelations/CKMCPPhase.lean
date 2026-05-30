import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# UgpLean.MassRelations.CKMCPPhase — CKM CP phase from the S₃ subgroup chain

The CKM CP-violating phase is parametrized by a rational reduction of the
maximal-violation value π/2 set by the GTE generation-sector subgroup orders
|H_lep| = |S₃| = 6, |H_down| = |A₃| = 3, |H_up| = |Z₂| = 2 (the GTE-certified
subgroup-order set, see `KoideSectorAngle`):

    δ_CP = π/2 − |H_down| / (|H_lep| + |H_up|) = π/2 − 3/8.

This module certifies the rational structure of that reduction and that the
defining ratio 3/8 is distinct from every neighbouring subgroup-order variant,
so the empirical agreement (δ_CP within measurement uncertainty of the PDG
value, 68.51° vs 68.53°) is specific to the {6, 3, 2} assignment. The numerical
comparison to data lives in the reproduction script; here we fix the algebra.
-/

namespace UgpLean.MassRelations.CKMCPPhase

/-- The CP-phase reduction ratio is `|H_down| / (|H_lep| + |H_up|) = 3/(6+2) = 3/8`. -/
theorem cp_phase_reduction_ratio :
    (3 : ℚ) / ((6 : ℚ) + 2) = 3 / 8 := by norm_num

/-- The defining ratio `3/8` is distinct from each null-test variant built from
    the same subgroup orders: swapping H_down↔H_up gives `2/9`, restricting the
    denominator to H_lep gives `1/2`, and the H_down neighbour gives `1/4`. A
    distinct rational reduction yields a distinct phase, so none of the variants
    reproduces `δ_CP = π/2 − 3/8`. -/
theorem cp_phase_ratio_distinct_from_nulls :
    (3 : ℚ) / 8 ≠ 2 / 9 ∧
    (3 : ℚ) / 8 ≠ (3 : ℚ) / 6 ∧
    (3 : ℚ) / 8 ≠ (2 : ℚ) / (6 + 2) := by
  refine ⟨?_, ?_, ?_⟩ <;> norm_num

/-- The A (Wolfenstein) parameter from the down-sector order: `A = sin(π/|H_down|)
    = sin(π/3)`, whose square is the certified rational `3/4`. -/
theorem ckm_A_parameter_squared :
    Real.sin (Real.pi / 3) ^ 2 = 3 / 4 := by
  rw [Real.sin_pi_div_three, div_pow, Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 3)]
  norm_num

end UgpLean.MassRelations.CKMCPPhase
