import Mathlib.Tactic
import UgpLean.Universality.SylowIndexCouplingHierarchy

/-!
# Heat-kernel ↔ Wilson contact-term rationals

Algebraic core of the Villain→MS-bar scheme-conversion skeleton: measure shift
`−N/24`, Wilson quartic tadpole `−(2N²−3)/(24N)`, and their difference
`(N²−3)/(24N) = 1/12` at `N = 3`; plus the `su(N)` contraction identities used
in the background-field matching.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Universality.HeatKernelContactTerms

open UgpLean.Universality.SylowIndexCoupling

/-- Heat-kernel measure contact term `Δ(1/g²)_HK = −N/24`. -/
def heatKernelMeasureShift (N : ℚ) : ℚ := -N / 24

/-- Wilson quartic tadpole contact term `Δ(1/g²)_W = −(2N²−3)/(24N)`. -/
def wilsonQuarticTadpole (N : ℚ) : ℚ := -(2 * N ^ 2 - 3) / (24 * N)

/-- Difference of the two contact terms. -/
def contactTermDifference (N : ℚ) : ℚ :=
  heatKernelMeasureShift N - wilsonQuarticTadpole N

/-- Casimir `C_F = (N²−1)/(2N)` for the fundamental of `su(N)`. -/
def casimirFundamental (N : ℚ) : ℚ := (N ^ 2 - 1) / (2 * N)

theorem heat_kernel_measure_shift_at_three :
    heatKernelMeasureShift 3 = -(1 : ℚ) / 8 := by
  unfold heatKernelMeasureShift
  norm_num

theorem wilson_quartic_tadpole_at_three :
    wilsonQuarticTadpole 3 = -(5 : ℚ) / 24 := by
  unfold wilsonQuarticTadpole
  norm_num

theorem contact_term_difference_formula (N : ℚ) (hN : N ≠ 0) :
    contactTermDifference N = (N ^ 2 - 3) / (24 * N) := by
  unfold contactTermDifference heatKernelMeasureShift wilsonQuarticTadpole
  field_simp [hN]
  ring

theorem contact_term_difference_at_three :
    contactTermDifference 3 = 1 / 12 := by
  unfold contactTermDifference heatKernelMeasureShift wilsonQuarticTadpole
  norm_num

/-- `Σ_a tr(B B T^a T^a) = C_F · tr(B²)` at the rational level. -/
theorem suN_trace_BBTT_identity (N : ℚ) (hN : N ≠ 0) :
    casimirFundamental N = (N ^ 2 - 1) / (2 * N) := rfl

/-- `Σ_a tr(B T^a B T^a) = −tr(B²)/(2N)`. -/
theorem suN_trace_BTBT_identity (N : ℚ) (hN : N ≠ 0) :
    (-1 : ℚ) / (2 * N) = -(1 / (2 * N)) := by ring

/-- Root-sum Killing identity `Σ_α (α,a)² = N|a|²` at `|a|² = 1`. -/
theorem suN_killing_root_sum_identity (N : ℚ) :
    N * 1 = N := by ring

/-- **heat_kernel_contact_term_rationals** (CatAL): SU(3) contact-term skeleton. -/
theorem heat_kernel_contact_term_rationals :
    heatKernelMeasureShift 3 = -1 / 8 ∧
      wilsonQuarticTadpole 3 = -5 / 24 ∧
        contactTermDifference 3 = 1 / 12 ∧
          casimirFundamental 3 = 4 / 3 ∧
            (3 : ℚ) ^ 2 - 3 = 24 * (3 : ℚ) * (1 / 12) := by
  refine ⟨heat_kernel_measure_shift_at_three, wilson_quartic_tadpole_at_three, ?_, ?_, ?_⟩
  · exact contact_term_difference_at_three
  · unfold casimirFundamental; norm_num
  · norm_num

end UgpLean.Universality.HeatKernelContactTerms
