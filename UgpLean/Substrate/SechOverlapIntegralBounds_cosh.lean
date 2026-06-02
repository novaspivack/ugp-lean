import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Series

/-!
Taylor and rational helpers for sech overlap mesh certification.
-/

namespace UgpLean.Substrate.PhiMDLFluctuationSpectrum

open Real

/-- For `x ≥ 0`, `cosh x ≤ exp x` (since `exp x = cosh x + sinh x`). -/
lemma cosh_le_exp_nonneg (x : ℝ) (hx : 0 ≤ x) : cosh x ≤ exp x := by
  have := congrArg (fun z => z + sinh x) (cosh_add_sinh x)
  have hsinh : 0 ≤ sinh x := sinh_nonneg_iff.mpr hx
  linarith [exp_pos x, hsinh]

end UgpLean.Substrate.PhiMDLFluctuationSpectrum
