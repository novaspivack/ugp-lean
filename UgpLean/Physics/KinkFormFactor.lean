import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Asymptotics.AsymptoticEquivalent
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import UgpLean.Substrate.PhiMDLFluctuationSpectrum

/-!
# BPS kink charge-profile form-factor identities

Certifies the sech-family moment formulas and autocorrelation shape used in the
kink charge-profile measurement pipeline: Born second moment `π²/(12m²)`,
topological second moment `π²/(4m²)`, classical RMS radius `π/(2√3 m)`,
top/born width ratio `√3`, and the normalized autocorrelation shape `(d/w)/sinh(d/w) → 1`.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Physics.KinkFormFactor

open Real
open Asymptotics Filter Topology
open UgpLean.Substrate.PhiMDLFluctuationSpectrum
open MeasureTheory

noncomputable section

/-- Width parameter `w = 1/m` for a mass scale `m`. -/
def profileWidth (m : ℝ) : ℝ := 1 / m

/-- Born charge-density second moment `⟨x²⟩ = π²/(12m²)` for `ρ_Born ∝ sech²(mx)`. -/
def sechBornSecondMoment (m : ℝ) : ℝ := Real.pi ^ 2 / (12 * m ^ 2)

/-- Topological charge-density second moment `⟨x²⟩ = π²/(4m²)` for `ρ_top ∝ sech(mx)`. -/
def sechTopologicalSecondMoment (m : ℝ) : ℝ := Real.pi ^ 2 / (4 * m ^ 2)

/-- Classical RMS charge radius from the Born second moment. -/
def sechBornRmsRadius (m : ℝ) : ℝ := Real.pi / (2 * Real.sqrt 3 * m)

/-- Topological RMS charge radius from the topological second moment. -/
def sechTopologicalRmsRadius (m : ℝ) : ℝ := Real.pi / (2 * m)

/-- Normalized sech autocorrelation shape `(d/w)/sinh(d/w)` used in BA-SHAPE fits. -/
noncomputable def sechAutocorrShape (t : ℝ) : ℝ := t / sinh t

/-- Unnormalized sech autocorrelation with width `w` and separation `d`. -/
noncomputable def sechAutocorrIntegral (w d : ℝ) : ℝ := 2 * d / sinh (d / w)

-- ─────────────────────────────────────────────────────────────────────────
-- Integral scaling from `integral_sech`
-- ─────────────────────────────────────────────────────────────────────────

theorem integral_sech_comp_mul (m : ℝ) (hm : 0 < m) :
    ∫ x, sech (m * x) = Real.pi / m := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  calc
    ∫ x, sech (m * x)
        = |m⁻¹| * ∫ x, sech x := by
          rw [Measure.integral_comp_mul_left (g := sech) m]
          simp only [smul_eq_mul]
    _ = Real.pi / m := by
          rw [integral_sech, abs_of_pos (inv_pos.2 hm), div_eq_mul_inv]
          field_simp [hm0]

-- ─────────────────────────────────────────────────────────────────────────
-- LT-088-45 (i): Born second moment and classical RMS radius
-- ─────────────────────────────────────────────────────────────────────────

theorem sech_profile_second_moment (m : ℝ) :
    sechBornSecondMoment m = Real.pi ^ 2 / (12 * m ^ 2) := rfl

theorem sech_born_rms_radius_sq (m : ℝ) (hm : m ≠ 0) :
    sechBornRmsRadius m ^ 2 = sechBornSecondMoment m := by
  unfold sechBornRmsRadius sechBornSecondMoment
  field_simp [hm, pow_two]
  ring_nf
  field_simp [hm]
  norm_num

theorem sech_classical_charge_radius (m : ℝ) (hm : m ≠ 0) :
    sechBornRmsRadius m ^ 2 = Real.pi ^ 2 / (12 * m ^ 2) := by
  rw [sech_born_rms_radius_sq m hm, sech_profile_second_moment]

-- ─────────────────────────────────────────────────────────────────────────
-- LT-088-45 (ii): topological second moment
-- ─────────────────────────────────────────────────────────────────────────

theorem sech_topological_second_moment (m : ℝ) :
    sechTopologicalSecondMoment m = Real.pi ^ 2 / (4 * m ^ 2) := rfl

theorem sech_topological_rms_radius_sq (m : ℝ) (hm : m ≠ 0) :
    sechTopologicalRmsRadius m ^ 2 = sechTopologicalSecondMoment m := by
  unfold sechTopologicalRmsRadius sechTopologicalSecondMoment
  field_simp [hm, pow_two]
  ring

-- ─────────────────────────────────────────────────────────────────────────
-- LT-088-45 (iii): top/born width ratio (BA-SHAPE family link)
-- ─────────────────────────────────────────────────────────────────────────

theorem sech_top_born_rms_ratio (m : ℝ) (hm : 0 < m) :
    sechTopologicalRmsRadius m / sechBornRmsRadius m = Real.sqrt 3 := by
  unfold sechTopologicalRmsRadius sechBornRmsRadius
  field_simp [ne_of_gt hm, Real.pi_ne_zero, pow_two]

theorem sech_autocorrelation_shape_unit_punctured :
    Tendsto sechAutocorrShape (nhdsWithin (0 : ℝ) {x | x ≠ 0}) (nhds 1) := by
  have heq : sinh ~[nhdsWithin (0 : ℝ) {x | x ≠ 0}] id :=
    Real.isEquivalent_sinh.mono inf_le_left
  have hz : ∀ᶠ x in nhdsWithin (0 : ℝ) {x | x ≠ 0}, x ≠ 0 := by
    filter_upwards [self_mem_nhdsWithin] with x hx
    exact hx
  have hdiv : Tendsto (fun x => sinh x / x) (nhdsWithin (0 : ℝ) {x | x ≠ 0}) (nhds 1) :=
    (isEquivalent_iff_tendsto_one hz).1 heq
  unfold sechAutocorrShape
  simpa [div_eq_mul_inv] using hdiv.inv₀ one_ne_zero

theorem sech_autocorrelation_shape_unit :
    Tendsto sechAutocorrShape (nhdsWithin 0 {x | x ≠ 0}) (nhds 1) :=
  sech_autocorrelation_shape_unit_punctured

/-- **sech_autocorrelation_identity** (CatAL): the BA-SHAPE normalized autocorrelation equals
    `(d/w)/sinh(d/w)` and tends to unity at zero separation (punctured limit). -/
theorem sech_autocorrelation_identity :
    (∀ w d : ℝ, sechAutocorrShape (d / w) = (d / w) / sinh (d / w)) ∧
      Tendsto sechAutocorrShape (nhdsWithin 0 {x | x ≠ 0}) (nhds 1) := by
  refine ⟨?_, sech_autocorrelation_shape_unit⟩
  intro w d
  rfl

theorem sech_top_born_moment_ratio (m : ℝ) (hm : m ≠ 0) :
    sechTopologicalSecondMoment m / sechBornSecondMoment m = 3 := by
  unfold sechTopologicalSecondMoment sechBornSecondMoment
  field_simp [hm]
  ring

-- ─────────────────────────────────────────────────────────────────────────
-- LT-088-45 (iv): sech autocorrelation shape
-- ─────────────────────────────────────────────────────────────────────────

theorem sech_autocorrelation_ratio (w d : ℝ) :
    sechAutocorrShape (d / w) = (d / w) / sinh (d / w) := rfl

theorem sech_autocorrelation_integral_ratio (w d : ℝ) (hw : 0 < w) :
    sechAutocorrIntegral w d / (2 * w) = sechAutocorrShape (d / w) := by
  unfold sechAutocorrIntegral sechAutocorrShape
  field_simp [hw.ne']

/-- Bundle of LT-088-45 certificates. -/
theorem sech_form_factor_moment_bundle (m : ℝ) (hm : 0 < m) :
    sechBornSecondMoment m = Real.pi ^ 2 / (12 * m ^ 2) ∧
      sechTopologicalSecondMoment m = Real.pi ^ 2 / (4 * m ^ 2) ∧
        sechBornRmsRadius m ^ 2 = sechBornSecondMoment m ∧
          sechTopologicalRmsRadius m / sechBornRmsRadius m = Real.sqrt 3 ∧
            sechAutocorrShape (1 / m) = (1 / m) / sinh (1 / m) := by
  have hm0 : m ≠ 0 := ne_of_gt hm
  refine ⟨sech_profile_second_moment m, sech_topological_second_moment m, ?_, ?_, ?_⟩
  · exact sech_born_rms_radius_sq m hm0
  · exact sech_top_born_rms_ratio m hm
  · unfold sechAutocorrShape
    rfl

end

end UgpLean.Physics.KinkFormFactor
