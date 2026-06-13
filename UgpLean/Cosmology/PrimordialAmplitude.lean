import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic

/-!
# Primordial Scalar Amplitude — Conditional Formula

Documents the structural form of the GTE primordial amplitude `A_s` as a Lean
definition parametrized by the Hubble rate `H*` at primordial horizon crossing.

When `H*` is derived from the per-cell energy-pricing premise, the formula closes
automatically. This module certifies the algebraic form independently of that premise.

All theorems: zero sorry, zero custom axioms.
-/

namespace UgpLean.Cosmology.PrimordialAmplitude

open Real

/-- Reduced Planck mass `M_Pl / √8π` (Planck units convention). -/
noncomputable def M_Pl_red : ℝ := 1

/-- **PrimordialAmplitude** (CatAL definition):
    `A_s(H*) = H*² / (4 π² M_Pl_red²)`. -/
noncomputable def PrimordialAmplitude (H_star : ℝ) : ℝ :=
  H_star ^ 2 / (4 * Real.pi ^ 2 * M_Pl_red ^ 2)

/-- **as_conditional_formula_premise** (CatAL):
    The primordial amplitude equals the standard slow-roll horizon formula in terms
    of `H*` and the reduced Planck mass. -/
theorem as_conditional_formula_premise (H_star : ℝ) :
    PrimordialAmplitude H_star = H_star ^ 2 / (4 * Real.pi ^ 2 * M_Pl_red ^ 2) := rfl

/-- At unit reduced Planck mass the formula reduces to `H*² / (4π²)`. -/
theorem primordial_amplitude_unit_planck (H_star : ℝ) :
    PrimordialAmplitude H_star = H_star ^ 2 / (4 * Real.pi ^ 2) := by
  simp [PrimordialAmplitude, M_Pl_red]

/-- Positivity on nonzero horizon crossing rate. -/
theorem primordial_amplitude_pos (H_star : ℝ) (hH : H_star ≠ 0) :
    0 < PrimordialAmplitude H_star := by
  unfold PrimordialAmplitude M_Pl_red
  apply div_pos (sq_pos_of_ne_zero hH)
  positivity

end UgpLean.Cosmology.PrimordialAmplitude
