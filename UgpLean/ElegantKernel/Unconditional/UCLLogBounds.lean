import Mathlib.Algebra.Order.GroupWithZero.Unbundled.Basic
import Mathlib.Analysis.Complex.Exponential
import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.NumberTheory.Real.GoldenRatio
import UgpLean.ElegantKernel.Unconditional.KConstFullClosure

/-!
Numerical interval bounds for logarithms entering UCL mass-ordering proofs.

Golden-ratio and `log(2π)` bounds follow the Mathlib `Real.pi_gt_d*` / Taylor
`exp_bound'` pattern from `Mathlib/Analysis/Real/Pi/Bounds.lean`.
-/

namespace UgpLean.ElegantKernel.Unconditional.UCLLogBounds

open Real
open UgpLean.ElegantKernel.Unconditional.KConstFullClosure

/-! ## √5 and φ -/

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

/-! ## log φ -/

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

alias log_goldenRatio_lower := log_goldenRatio_lo
alias log_goldenRatio_upper := log_goldenRatio_hi

/-! ## log(2π) -/

private lemma two_pi_lo : (6283 : ℝ) / 1000 < 2 * Real.pi := by
  nlinarith [Real.pi_gt_d4]

private lemma two_pi_hi : 2 * Real.pi < (62832 : ℝ) / 10000 := by
  nlinarith [Real.pi_lt_d4]

private lemma exp_837_hi : Real.exp ((837 : ℝ) / 1000) < (2310 : ℝ) / 1000 := by
  set x : ℝ := (837 : ℝ) / 1000
  have hx0 : 0 ≤ x := by norm_num
  have hx1 : x ≤ 1 := by norm_num
  have hupper := Real.exp_bound' hx0 hx1 (n := 10) (by norm_num)
  have htaylor :
      (∑ m ∈ Finset.range 10, x ^ m / (Nat.factorial m)) +
          x ^ 10 * 11 / (Nat.factorial 10 * 10) <
        (2310 : ℝ) / 1000 := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  linarith [hupper, htaylor]

private lemma exp_1837_lt_6283 : Real.exp ((1837 : ℝ) / 1000) < (6283 : ℝ) / 1000 := by
  have hsplit : (1837 : ℝ) / 1000 = 1 + (837 : ℝ) / 1000 := by norm_num
  have hmul :
      Real.exp ((1837 : ℝ) / 1000) = Real.exp 1 * Real.exp ((837 : ℝ) / 1000) := by
    rw [hsplit, Real.exp_add]
  have h2 := exp_837_hi
  have hstep1 :
      Real.exp 1 * Real.exp ((837 : ℝ) / 1000) < Real.exp 1 * ((2310 : ℝ) / 1000) :=
    mul_lt_mul_of_pos_left h2 (Real.exp_pos 1)
  have hstep2 :
      Real.exp 1 * ((2310 : ℝ) / 1000) <
        (2.7182818286 : ℝ) * ((2310 : ℝ) / 1000) := by
    apply mul_lt_mul_of_pos_right Real.exp_one_lt_d9 (by norm_num : 0 < (2310 : ℝ) / 1000)
  have hstep3 : (2.7182818286 : ℝ) * ((2310 : ℝ) / 1000) < (6283 : ℝ) / 1000 := by norm_num
  rw [hmul]
  exact lt_trans hstep1 (lt_trans hstep2 hstep3)

private lemma exp_839_lo : (2314 : ℝ) / 1000 < Real.exp ((839 : ℝ) / 1000) := by
  set x : ℝ := (839 : ℝ) / 1000
  have hx0 : 0 ≤ x := by norm_num
  have hlower := Real.sum_le_exp_of_nonneg hx0 10
  have htaylor :
      (2314 : ℝ) / 1000 <
        ∑ m ∈ Finset.range 10, x ^ m / (Nat.factorial m) := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  linarith [hlower, htaylor]

private lemma exp_1839_lo : (62832 : ℝ) / 10000 < Real.exp ((1839 : ℝ) / 1000) := by
  have hsplit : (1839 : ℝ) / 1000 = 1 + (839 : ℝ) / 1000 := by norm_num
  have hmul :
      Real.exp ((1839 : ℝ) / 1000) = Real.exp 1 * Real.exp ((839 : ℝ) / 1000) := by
    rw [hsplit, Real.exp_add]
  have h2 := exp_839_lo
  have hstep1 :
      (62832 : ℝ) / 10000 <
        (2.7182818283 : ℝ) * ((2314 : ℝ) / 1000) := by norm_num
  have hstep2 :
      (2.7182818283 : ℝ) * ((2314 : ℝ) / 1000) <
        Real.exp 1 * ((2314 : ℝ) / 1000) := by
    apply mul_lt_mul_of_pos_right Real.exp_one_gt_d9 (by norm_num : 0 < (2314 : ℝ) / 1000)
  have hstep3 :
      Real.exp 1 * ((2314 : ℝ) / 1000) < Real.exp 1 * Real.exp ((839 : ℝ) / 1000) :=
    mul_lt_mul_of_pos_left h2 (Real.exp_pos 1)
  rw [hmul]
  exact lt_trans hstep1 (lt_trans hstep2 hstep3)

theorem log_two_pi_lo : (1837 : ℝ) / 1000 < Real.log (2 * Real.pi) := by
  rw [Real.lt_log_iff_exp_lt (by positivity)]
  exact lt_trans exp_1837_lt_6283 two_pi_lo

theorem log_two_pi_hi : Real.log (2 * Real.pi) < (1839 : ℝ) / 1000 := by
  rw [Real.log_lt_iff_lt_exp (by positivity)]
  exact lt_trans two_pi_hi exp_1839_lo

/-! ## −1/(2π) and k_const corners -/

private lemma one_div_two_pi_gt_recip_pi_hi :
    (50000000000000000000 : ℝ) / (314159265358979323847 : ℝ) < (1 : ℝ) / (2 * Real.pi) := by
  have hpi : Real.pi < (314159265358979323847 : ℝ) / 10^20 := by
    convert Real.pi_lt_d20 using 1
    norm_num
  rw [div_lt_div_iff₀ (by norm_num) (by positivity)]
  nlinarith [hpi]

private lemma one_div_two_pi_lt_recip_pi_lo :
    (1 : ℝ) / (2 * Real.pi) < (25000000000000000000 : ℝ) / (157079632679489661923 : ℝ) := by
  have hpi : (314159265358979323846 : ℝ) / 10^20 < Real.pi := by
    convert Real.pi_gt_d20 using 1
    norm_num
  rw [div_lt_div_iff₀ (by positivity) (by norm_num)]
  nlinarith [hpi]

private lemma log_goldenRatio_sq_lo :
    ((481211 : ℝ) / 10^6) ^ 2 < (Real.log goldenRatio) ^ 2 := by
  have hφ : 0 < Real.log goldenRatio := by
    nlinarith [log_goldenRatio_lo, goldenRatio_lo]
  nlinarith [log_goldenRatio_lo, sq_nonneg ((481211 : ℝ) / 10^6 - Real.log goldenRatio)]

private lemma log_phi_lo_lt_log_goldenRatio :
    Real.log ((16180339877 : ℝ) / 10^10) < Real.log goldenRatio := by
  apply Real.log_lt_log (by norm_num) (by nlinarith [goldenRatio_lo])

private lemma log_goldenRatio_lt_log_phi_hi :
    Real.log goldenRatio < Real.log ((16180339895 : ℝ) / 10^10) := by
  apply Real.log_lt_log (by nlinarith [goldenRatio_lo]) (by nlinarith [goldenRatio_hi_val])

private lemma log_goldenRatio_sq_hi :
    (Real.log goldenRatio) ^ 2 < ((481212 : ℝ) / 10^6) ^ 2 := by
  have hφ : 0 < Real.log goldenRatio := by
    nlinarith [log_goldenRatio_lo, goldenRatio_lo]
  nlinarith [log_goldenRatio_hi, sq_nonneg (Real.log goldenRatio - (481212 : ℝ) / 10^6)]

private lemma exp_481211824_lt_phi_lo :
    Real.exp ((481211824 : ℝ) / 10^9) < (16180339877 : ℝ) / 10^10 := by
  set x : ℝ := (481211824 : ℝ) / 10^9
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

private lemma phi_hi_lt_exp_481211826 :
    (16180339895 : ℝ) / 10^10 < Real.exp ((481211826 : ℝ) / 10^9) := by
  set x : ℝ := (481211826 : ℝ) / 10^9
  have hx0 : 0 ≤ x := by norm_num
  have hlower := Real.sum_le_exp_of_nonneg hx0 10
  have htaylor :
      (16180339895 : ℝ) / 10^10 <
        ∑ m ∈ Finset.range 10, x ^ m / (Nat.factorial m) := by
    simp [Finset.sum_range_succ, Nat.factorial]
    norm_num
  linarith [hlower, htaylor]

private lemma log_481211824_lt_log_phi_lo :
    (481211824 : ℝ) / 10^9 < Real.log ((16180339877 : ℝ) / 10^10) := by
  rw [Real.lt_log_iff_exp_lt (by norm_num)]
  exact exp_481211824_lt_phi_lo

private lemma log_phi_hi_lt_481211826 :
    Real.log ((16180339895 : ℝ) / 10^10) < (481211826 : ℝ) / 10^9 := by
  rw [Real.log_lt_iff_lt_exp (by norm_num)]
  exact phi_hi_lt_exp_481211826

private lemma log_goldenRatio_gt_481211824 :
    (481211824 : ℝ) / 10^9 < Real.log goldenRatio := by
  linarith [log_481211824_lt_log_phi_lo, log_phi_lo_lt_log_goldenRatio]

private lemma log_goldenRatio_sq_margin_lo :
    (1 : ℝ) / 10^9 <
      (63 / 2048 : ℝ) * (Real.log goldenRatio) ^ 2 -
        (63 / 2048 : ℝ) * ((481211 : ℝ) / 10^6) ^ 2 := by
  have hmid : (1 : ℝ) / 10^9 <
      (63 / 2048 : ℝ) * ((481211824 : ℝ) / 10^9) ^ 2 -
        (63 / 2048 : ℝ) * ((481211 : ℝ) / 10^6) ^ 2 := by norm_num
  have hsq : ((481211824 : ℝ) / 10^9) ^ 2 < (Real.log goldenRatio) ^ 2 := by
    have hlog : 0 < Real.log goldenRatio := by nlinarith [log_goldenRatio_lo, goldenRatio_lo]
    exact pow_lt_pow_left₀ log_goldenRatio_gt_481211824 (by norm_num : 0 ≤ (481211824 : ℝ) / 10^9)
      (by norm_num : (2 : ℕ) ≠ 0)
  linarith [hmid, hsq]

private lemma log_goldenRatio_lt_481211826 :
    Real.log goldenRatio < (481211826 : ℝ) / 10^9 := by
  linarith [log_goldenRatio_lt_log_phi_hi, log_phi_hi_lt_481211826]

private lemma log_goldenRatio_sq_margin_hi :
    (1 : ℝ) / 10^9 <
      (63 / 2048 : ℝ) * ((481212 : ℝ) / 10^6) ^ 2 -
        (63 / 2048 : ℝ) * (Real.log goldenRatio) ^ 2 := by
  have hmid : (1 : ℝ) / 10^9 <
      (63 / 2048 : ℝ) * ((481212 : ℝ) / 10^6) ^ 2 -
        (63 / 2048 : ℝ) * ((481211826 : ℝ) / 10^9) ^ 2 := by norm_num
  have hsq : (Real.log goldenRatio) ^ 2 < ((481211826 : ℝ) / 10^9) ^ 2 := by
    have hlog : 0 < Real.log goldenRatio := by nlinarith [log_goldenRatio_lo, goldenRatio_lo]
    exact pow_lt_pow_left₀ log_goldenRatio_lt_481211826 (by nlinarith [log_goldenRatio_lo]) (by norm_num : (2 : ℕ) ≠ 0)
  linarith [hmid, hsq]

private lemma one_div_two_pi_rational_gap :
    (25000000000000000000 : ℝ) / (157079632679489661923 : ℝ) -
        (50000000000000000000 : ℝ) / (314159265358979323847 : ℝ) <
      (1 : ℝ) / 10^21 := by norm_num

private lemma one_div_two_pi_sub_recip_lo :
    (1 : ℝ) / (2 * Real.pi) -
        (50000000000000000000 : ℝ) / (314159265358979323847 : ℝ) <
      (25000000000000000000 : ℝ) / (157079632679489661923 : ℝ) -
        (50000000000000000000 : ℝ) / (314159265358979323847 : ℝ) := by
  linarith [one_div_two_pi_gt_recip_pi_hi, one_div_two_pi_lt_recip_pi_lo]

private lemma one_div_two_pi_sub_recip_hi :
    -(1 / (2 * Real.pi)) + (25000000000000000000 : ℝ) / (157079632679489661923 : ℝ) <
      (25000000000000000000 : ℝ) / (157079632679489661923 : ℝ) -
        (50000000000000000000 : ℝ) / (314159265358979323847 : ℝ) := by
  linarith [one_div_two_pi_gt_recip_pi_hi]

private lemma k_const_corner_lo_lt :
    (-1520316357 : ℝ) / 10^10 <
      (-50000000000000000000 : ℝ) / (314159265358979323847 : ℝ) +
        (63 / 2048 : ℝ) * ((481211 : ℝ) / 10^6) ^ 2 := by norm_num

private lemma k_const_corner_hi_gt :
    (-50000000000000000000 : ℝ) / (314159265358979323847 : ℝ) +
        (63 / 2048 : ℝ) * ((481212 : ℝ) / 10^6) ^ 2 <
      (-1520316060 : ℝ) / 10^10 := by norm_num

theorem k_const_derived_lo : (-1520316357 : ℝ) / 10^10 < k_const_derived := by
  have hcorner := k_const_corner_lo_lt
  have hgap : (0 : ℝ) < (63 / 2048 : ℝ) * (Real.log goldenRatio) ^ 2 -
      (63 / 2048 : ℝ) * ((481211 : ℝ) / 10^6) ^ 2 -
      ((1 : ℝ) / (2 * Real.pi) -
        (50000000000000000000 : ℝ) / (314159265358979323847 : ℝ)) := by
    linarith [log_goldenRatio_sq_margin_lo, one_div_two_pi_sub_recip_lo,
      one_div_two_pi_rational_gap]
  have hcore :
      (-50000000000000000000 : ℝ) / (314159265358979323847 : ℝ) +
          (63 / 2048 : ℝ) * ((481211 : ℝ) / 10^6) ^ 2 <
        k_const_derived := by
    rw [k_const_derived_closed_form]
    linarith [hgap]
  linarith [hcorner, hcore]

theorem k_const_derived_hi : k_const_derived < (-1520316060 : ℝ) / 10^10 := by
  have hcorner := k_const_corner_hi_gt
  have hpi : -(1 / (2 * Real.pi)) <
      (-50000000000000000000 : ℝ) / (314159265358979323847 : ℝ) := by
    linarith [one_div_two_pi_gt_recip_pi_hi]
  have hlog :
      (63 / 2048 : ℝ) * (Real.log goldenRatio) ^ 2 <
        (63 / 2048 : ℝ) * ((481212 : ℝ) / 10^6) ^ 2 := by
    nlinarith [log_goldenRatio_sq_hi]
  have hcore :
      k_const_derived <
        (-50000000000000000000 : ℝ) / (314159265358979323847 : ℝ) +
          (63 / 2048 : ℝ) * ((481212 : ℝ) / 10^6) ^ 2 := by
    rw [k_const_derived_closed_form]
    linarith [hpi, hlog]
  exact lt_trans hcore hcorner

end UgpLean.ElegantKernel.Unconditional.UCLLogBounds
