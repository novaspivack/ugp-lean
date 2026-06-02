import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import UgpLean.ElegantKernel
import UgpLean.QuarterLock
import UgpLean.ElegantKernel.Unconditional.KLFullClosure
import UgpLean.ElegantKernel.Unconditional.KGenFullClosure
import UgpLean.ElegantKernel.Unconditional.KConstFullClosure
import UgpLean.ElegantKernel.Unconditional.UCLLogBounds

/-!
Tight interval bounds on the UCL coefficients entering generation-difference
inequalities. `k_const` is omitted because it cancels in same-sector comparisons.
-/

namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCoeffBounds

open Real
open UgpLean.ElegantKernel
open UgpLean
open UgpLean.ElegantKernel.Unconditional.KLFullClosure
open UgpLean.ElegantKernel.Unconditional.KGenFullClosure
open UgpLean.ElegantKernel.Unconditional.KConstFullClosure

private lemma sqrt5_lo : (22360679755 : ℝ) / 10^10 < Real.sqrt 5 := by
  have hx : 0 ≤ (22360679755 : ℝ) / 10^10 := by norm_num
  rw [Real.lt_sqrt hx]
  norm_num

private lemma sqrt5_hi : Real.sqrt 5 < (22360679790 : ℝ) / 10^10 := by
  have hy : 0 ≤ (22360679790 : ℝ) / 10^10 := by norm_num
  have h := Real.sqrt_lt_sqrt (by norm_num : 0 ≤ (5 : ℝ))
      (by norm_num : (5 : ℝ) < ((22360679790 : ℝ) / 10^10) ^ 2)
  rwa [Real.sqrt_sq hy] at h

theorem goldenRatio_lo : (16180339877 : ℝ) / 10^10 < goldenRatio := by
  unfold goldenRatio
  nlinarith [sqrt5_lo]

theorem goldenRatio_hi : goldenRatio < (1 + (22360679790 : ℝ) / 10^10) / 2 := by
  unfold goldenRatio
  nlinarith [sqrt5_hi]

private lemma goldenRatio_hi_val : goldenRatio < (16180339895 : ℝ) / 10^10 := by
  have h : (1 + (22360679790 : ℝ) / 10^10) / 2 = (16180339895 : ℝ) / 10^10 := by norm_num
  nlinarith [goldenRatio_hi, h]

private lemma exp_481211_lt_phi_lo :
    Real.exp ((481211 : ℝ) / 10^6) < (16180339877 : ℝ) / 10^10 := by
  set x : ℝ := (481211 : ℝ) / 10^6
  have hx0 : 0 ≤ x := by norm_num
  have hx1 : x ≤ 1 := by norm_num
  have hupper := Real.exp_bound' hx0 hx1 (n := 10) (by norm_num)
  have htaylor :
      (∑ m ∈ Finset.range 10, x ^ m / (Nat.factorial m)) +
          x ^ 10 * 11 / (Nat.factorial 10 * 10) <
        (16180339877 : ℝ) / 10^10 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  linarith [hupper, htaylor]

private lemma phi_hi_lt_exp_481212 :
    (161803399 : ℝ) / 10^8 < Real.exp ((481212 : ℝ) / 10^6) := by
  set x : ℝ := (481212 : ℝ) / 10^6
  have hx0 : 0 ≤ x := by norm_num
  have hlower := Real.sum_le_exp_of_nonneg hx0 10
  have htaylor :
      (161803399 : ℝ) / 10^8 <
        ∑ m ∈ Finset.range 10, x ^ m / (Nat.factorial m) := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  linarith [hlower, htaylor]

theorem log_goldenRatio_lo : (481211 : ℝ) / 10^6 < Real.log goldenRatio := by
  have hφ : Real.exp ((481211 : ℝ) / 10^6) < goldenRatio := by
    nlinarith [goldenRatio_lo, exp_481211_lt_phi_lo]
  exact (Real.lt_log_iff_exp_lt (by nlinarith [goldenRatio_lo])).2 hφ

theorem log_goldenRatio_hi : Real.log goldenRatio < (481212 : ℝ) / 10^6 := by
  have hφ : goldenRatio < Real.exp ((481212 : ℝ) / 10^6) := by
    nlinarith [goldenRatio_hi_val, phi_hi_lt_exp_481212]
  exact (Real.log_lt_iff_lt_exp (by nlinarith [goldenRatio_lo])).2 hφ

private lemma k_L_at_log_lo :
    (197371699 : ℝ) / 10^10 < (21 / 512 : ℝ) * ((481211 : ℝ) / 10^6) := by norm_num

private lemma k_L_at_log_hi :
    (21 / 512 : ℝ) * ((481212 : ℝ) / 10^6) < (197372211 : ℝ) / 10^10 := by norm_num

theorem k_L_derived_lo : (197371699 : ℝ) / 10^10 < k_L_derived := by
  rw [k_L_derived_closed_form]
  nlinarith [log_goldenRatio_lo, k_L_at_log_lo]

theorem k_L_derived_hi : k_L_derived < (197372211 : ℝ) / 10^10 := by
  rw [k_L_derived_closed_form]
  nlinarith [log_goldenRatio_hi, k_L_at_log_hi]

private lemma k_gen_sq_at_phi_lo :
    ((15388417674 : ℝ) / 10^10) ^ 2 < ((16180339877 : ℝ) / 10^10) ^ 2 - (1 / 4 : ℝ) := by norm_num

private lemma k_gen_sq_at_phi_hi :
    ((16180339895 : ℝ) / 10^10) ^ 2 - (1 / 4 : ℝ) < ((15388417694 : ℝ) / 10^10) ^ 2 := by norm_num

private lemma goldenRatio_lo_val : (16180339877 : ℝ) / 10^10 < goldenRatio := goldenRatio_lo

theorem k_gen_derived_lo : (15388417674 : ℝ) / 10^10 < k_gen_derived := by
  have hsq : k_gen_derived ^ 2 = goldenRatio ^ 2 - 1 / 4 := by
    rw [k_gen_derived_sq, k_gen_sq_derived_eq_phi_sq_minus_quarter]
  have hkpos : 0 < k_gen_derived := k_gen_derived_pos
  have hlo : 0 ≤ (15388417674 : ℝ) / 10^10 := by norm_num
  have htarget : ((15388417674 : ℝ) / 10^10) ^ 2 < goldenRatio ^ 2 - 1 / 4 := by
    nlinarith [goldenRatio_lo_val, k_gen_sq_at_phi_lo]
  have hsq_gt : ((15388417674 : ℝ) / 10^10) ^ 2 < k_gen_derived ^ 2 := by
    rw [hsq]; exact htarget
  exact (sq_lt_sq₀ hlo (le_of_lt hkpos)).1 hsq_gt

theorem k_gen_derived_hi : k_gen_derived < (15388417694 : ℝ) / 10^10 := by
  have hsq : k_gen_derived ^ 2 = goldenRatio ^ 2 - 1 / 4 := by
    rw [k_gen_derived_sq, k_gen_sq_derived_eq_phi_sq_minus_quarter]
  have hkpos : 0 < k_gen_derived := k_gen_derived_pos
  have hφ2 : goldenRatio ^ 2 < ((16180339895 : ℝ) / 10^10) ^ 2 := by
    nlinarith [goldenRatio_lo_val, goldenRatio_hi_val]
  have htarget : goldenRatio ^ 2 - 1 / 4 < ((15388417694 : ℝ) / 10^10) ^ 2 := by
    nlinarith [hφ2, k_gen_sq_at_phi_hi]
  have hsq_lt : k_gen_derived ^ 2 < ((15388417694 : ℝ) / 10^10) ^ 2 := by
    rw [hsq]; exact htarget
  have hhi : 0 ≤ (15388417694 : ℝ) / 10^10 := by norm_num
  exact (sq_lt_sq₀ (le_of_lt hkpos) hhi).1 hsq_lt

theorem k_gen2_lo : (-8090169949 : ℝ) / 10^10 < k_gen2 := by
  rw [k_gen2_eq_neg_phi_half]
  nlinarith [goldenRatio_hi_val]

theorem k_gen2_hi : k_gen2 < (-8090169938 : ℝ) / 10^10 := by
  rw [k_gen2_eq_neg_phi_half]
  nlinarith [goldenRatio_lo_val]

theorem k_M_lo : (-805599027 : ℝ) / 10^9 < k_M := by
  rw [k_M_eq_neg_phi_half_plus_seven_2048]
  nlinarith [goldenRatio_hi_val]

theorem k_M_hi : k_M < (-805599025 : ℝ) / 10^9 := by
  rw [k_M_eq_neg_phi_half_plus_seven_2048]
  nlinarith [goldenRatio_lo_val]

/-! ## k_const (needed for S-value bounds) -/

open UCLLogBounds

theorem k_const_lo : (-1520316357 : ℝ) / 10^10 < k_const_derived :=
  k_const_derived_lo

theorem k_const_hi : k_const_derived < (-1520316060 : ℝ) / 10^10 :=
  k_const_derived_hi

end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCoeffBounds
