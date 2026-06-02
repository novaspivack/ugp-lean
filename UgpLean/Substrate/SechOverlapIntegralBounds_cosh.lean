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

private lemma exp_two_eq : exp 2 = exp 1 * exp 1 := by
  rw [← exp_add, show (1 : ℝ) + 1 = 2 by norm_num]

private lemma exp_three_eq : exp 3 = exp 1 * exp 1 * exp 1 := by
  calc exp 3 = exp (2 + 1) := by norm_num
    _ = exp 2 * exp 1 := exp_add 2 1
    _ = exp 1 * exp 1 * exp 1 := by rw [exp_two_eq, mul_assoc]

private lemma exp_four_eq : exp 4 = exp 1 * exp 1 * exp 1 * exp 1 := by
  calc exp 4 = exp (2 + 2) := by norm_num
    _ = exp 2 * exp 2 := exp_add 2 2
    _ = exp 1 * exp 1 * exp 1 * exp 1 := by rw [exp_two_eq]; ring_nf

private lemma exp_five_eq : exp 5 = exp 1 * exp 1 * exp 1 * exp 1 * exp 1 := by
  calc exp 5 = exp (4 + 1) := by norm_num
    _ = exp 4 * exp 1 := exp_add 4 1
    _ = exp 1 * exp 1 * exp 1 * exp 1 * exp 1 := by
      rw [exp_four_eq, mul_assoc, mul_assoc, mul_assoc]

/-- Certified upper bound on `exp 2`. -/
lemma exp_two_le : exp 2 ≤ 7390 / 1000 := by
  rw [exp_two_eq]
  have he := exp_one_lt_d9
  nlinarith [he, exp_pos 1]

/-- Certified upper bound on `exp 3`. -/
lemma exp_three_le : exp 3 ≤ 20086 / 1000 := by
  rw [exp_three_eq]
  have he := exp_one_lt_d9
  nlinarith [he, exp_pos 1, exp_two_le, sq_nonneg (exp 1)]

/-- Certified upper bound on `exp 4`. -/
lemma exp_four_le : exp 4 ≤ 54599 / 1000 := by
  rw [exp_four_eq]
  have he := exp_one_lt_d9
  have h11 : exp 1 * exp 1 < (2.7182818286 : ℝ) * (2.7182818286) := by nlinarith [he, exp_pos 1]
  have h1111 : (exp 1 * exp 1) * (exp 1 * exp 1) < (2.7182818286 : ℝ) ^ 4 := by
    nlinarith [h11, mul_pos (exp_pos 1) (exp_pos 1)]
  have hnum : (2.7182818286 : ℝ) ^ 4 ≤ 54599 / 1000 := by norm_num
  nlinarith [h1111, hnum, mul_pos (exp_pos 1) (exp_pos 1)]

/-- Certified upper bound on `exp 5`. -/
lemma exp_five_le : exp 5 ≤ 148414 / 1000 := by
  rw [exp_five_eq]
  have he := exp_one_lt_d9
  have h11 : exp 1 * exp 1 < (2.7182818286 : ℝ) * (2.7182818286) := by nlinarith [he, exp_pos 1]
  have h1111 : (exp 1 * exp 1) * (exp 1 * exp 1) < (2.7182818286 : ℝ) ^ 4 := by
    nlinarith [h11, mul_pos (exp_pos 1) (exp_pos 1)]
  have h11111 : exp 1 * ((exp 1 * exp 1) * (exp 1 * exp 1)) < (2.7182818286 : ℝ) ^ 5 := by
    nlinarith [h1111, he, exp_pos 1, mul_pos (exp_pos 1) (exp_pos 1)]
  have hnum : (2.7182818286 : ℝ) ^ 5 ≤ 148414 / 1000 := by norm_num
  nlinarith [h11111, hnum, mul_pos (exp_pos 1) (exp_pos 1)]

/-- Lower bound on `exp 2` for reciprocal bounds. -/
lemma exp_two_gt : (7389 / 1000 : ℝ) < exp 2 := by
  rw [exp_two_eq]
  have := exp_one_gt_d9
  nlinarith [exp_pos 1]

/-- `exp 1 ≤ 2719/1000`. -/
lemma exp_one_le : exp 1 ≤ 2719 / 1000 := by linarith [exp_one_lt_d9]

/-- `exp(-1) ≤ 368/1000`. -/
lemma exp_neg_one_le : exp (-1) ≤ 368 / 1000 := by linarith [exp_neg_one_lt_d9]

/-- `exp(-2) ≤ 136/1000`. -/
lemma exp_neg_two_le : exp (-2) ≤ 136 / 1000 := by
  have hpos : 0 < exp 2 := exp_pos 2
  have h2 : (1000 / 136 : ℝ) < exp 2 := by
    rw [exp_two_eq]
    have := exp_one_gt_d9
    nlinarith [exp_pos 1]
  rw [exp_neg, inv_le_comm₀ hpos (by norm_num)]
  linarith

/-- `exp(-3) ≤ 50/1000`. -/
lemma exp_neg_three_le : exp (-3) ≤ 50 / 1000 := by
  have hpos : 0 < exp 3 := exp_pos 3
  have h3 : (20 : ℝ) < exp 3 := by
    rw [exp_three_eq]
    have := exp_one_gt_d9
    nlinarith [exp_pos 1, sq_nonneg (exp 1)]
  rw [exp_neg, inv_le_comm₀ hpos (by norm_num)]
  linarith

private lemma exp_four_gt_thousand_div_19 : (1000 / 19 : ℝ) < exp 4 := by
  rw [exp_four_eq]
  have h1 := exp_one_gt_d9
  have h11 : (2.7182818283 : ℝ) * (2.7182818283 : ℝ) < exp 1 * exp 1 := by
    nlinarith [h1, exp_pos 1]
  have h1111 : (2.7182818283 : ℝ) ^ 4 < (exp 1 * exp 1) * (exp 1 * exp 1) := by
    nlinarith [h11, mul_pos (exp_pos 1) (exp_pos 1)]
  have hnum : (1000 / 19 : ℝ) < (2.7182818283 : ℝ) ^ 4 := by norm_num
  nlinarith [h1111, hnum, mul_pos (exp_pos 1) (exp_pos 1)]

/-- `exp(-4) ≤ 19/1000`. -/
lemma exp_neg_four_le : exp (-4) ≤ 19 / 1000 := by
  have hpos : 0 < exp 4 := exp_pos 4
  have h4 := exp_four_gt_thousand_div_19
  rw [exp_neg, inv_le_comm₀ hpos (by norm_num)]
  linarith

private lemma exp_five_gt_125 : (125 : ℝ) < exp 5 := by
  have h4 := exp_four_gt_thousand_div_19
  have h1 := exp_one_gt_d9
  calc 125 < (1000 / 19) * (2.7182818283 : ℝ) := by norm_num
    _ < exp 4 * exp 1 := by nlinarith [h4, h1, exp_pos 4, exp_pos 1]
    _ = exp 5 := by rw [← exp_add, show (4 : ℝ) + 1 = 5 by norm_num]

/-- `exp(-5) ≤ 8/1000`. -/
lemma exp_neg_five_le : exp (-5) ≤ 8 / 1000 := by
  have hpos : 0 < exp 5 := exp_pos 5
  have h5 := exp_five_gt_125
  rw [exp_neg, inv_le_comm₀ hpos (by norm_num)]
  linarith

/-- `cosh(2) ≤ 3763/1000` (actual ≈ 3.7622). -/
lemma cosh_two_le : cosh 2 ≤ 3763 / 1000 := by
  rw [cosh_eq]
  nlinarith [exp_two_le, exp_neg_two_le, exp_pos 2, exp_pos (-2)]

/-- `cosh(3) ≤ 10068/1000` (actual ≈ 10.0677). -/
lemma cosh_three_le : cosh 3 ≤ 10068 / 1000 := by
  rw [cosh_eq]
  nlinarith [exp_three_le, exp_neg_three_le, exp_pos 3, exp_pos (-3)]

/-- `cosh(4) ≤ 27309/1000` (actual ≈ 27.3077). -/
lemma cosh_four_le : cosh 4 ≤ 27309 / 1000 := by
  rw [cosh_eq]
  nlinarith [exp_four_le, exp_neg_four_le, exp_pos 4, exp_pos (-4)]

/-- `cosh(5) ≤ 74211/1000` (actual ≈ 74.2099). -/
lemma cosh_five_le : cosh 5 ≤ 74211 / 1000 := by
  rw [cosh_eq]
  nlinarith [exp_five_le, exp_neg_five_le, exp_pos 5, exp_pos (-5)]

end UgpLean.Substrate.PhiMDLFluctuationSpectrum
