import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.Complex.ExponentialBounds
import UgpLean.ElegantKernel.Unconditional.UCLCalibration
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts

/-!
Helpers for closing `UCLMassOrdering`: compare generation-scaled masses via log-space
inequalities, and link rational certificates to `Real.log 4`.
-/

namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds

open Real
open UgpLean.ElegantKernel.Unconditional.UCLCalibration
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts

theorem log_four_lo_lt_log_four :
    (logFourLo : ℝ) < Real.log 4 := by
  have h2 := Real.log_two_gt_d9
  have h : Real.log 4 = 2 * Real.log 2 := by
    rw [show (4 : ℝ) = 2 ^ 2 by norm_num, Real.log_pow]; ring
  rw [h]
  unfold logFourLo
  norm_cast
  linarith

/-- From `S₁ < log 4 + S₂`, generation `1 < 2` when each generation has its own triple. -/
theorem ucl_mass_lt_gen12_diff
    {μ1_a μ1_b μ1_c μ2_a μ2_b μ2_c : ℤ} {L1 L2 : ℝ} {S₁ S₂ : ℝ}
    (hS₁ : uclLogCalibration μ1_a μ1_b μ1_c L1 1 = S₁)
    (hS₂ : uclLogCalibration μ2_a μ2_b μ2_c L2 2 = S₂)
    (h : S₁ < Real.log 4 + S₂) :
    uclGenerationScaledMass μ1_a μ1_b μ1_c L1 1 <
      uclGenerationScaledMass μ2_a μ2_b μ2_c L2 2 := by
  unfold uclGenerationScaledMass uclGenerationScale uclCalibrationFactor
  rw [hS₁, hS₂]
  have h1 : (4 : ℝ) ^ (1 - 1) = 1 := by norm_num
  have h2 : (4 : ℝ) ^ (2 - 1) = 4 := by norm_num
  simp [h1, h2, one_mul]
  have hfour : Real.exp (Real.log 4 + S₂) = (4 : ℝ) * Real.exp S₂ := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [← hfour]
  exact Real.exp_lt_exp.2 h

/-- From `S₂ < log 4 + S₃`, generation `2 < 3` when each generation has its own triple. -/
theorem ucl_mass_lt_gen23_diff
    {μ2_a μ2_b μ2_c μ3_a μ3_b μ3_c : ℤ} {L2 L3 : ℝ} {S₂ S₃ : ℝ}
    (hS₂ : uclLogCalibration μ2_a μ2_b μ2_c L2 2 = S₂)
    (hS₃ : uclLogCalibration μ3_a μ3_b μ3_c L3 3 = S₃)
    (h : S₂ < Real.log 4 + S₃) :
    uclGenerationScaledMass μ2_a μ2_b μ2_c L2 2 <
      uclGenerationScaledMass μ3_a μ3_b μ3_c L3 3 := by
  unfold uclGenerationScaledMass uclGenerationScale uclCalibrationFactor
  rw [hS₂, hS₃]
  have h2 : (4 : ℝ) ^ (2 - 1) = 4 := by norm_num
  have h3 : (4 : ℝ) ^ (3 - 1) = 16 := by norm_num
  simp [h2, h3]
  have hexp : Real.exp S₂ < Real.exp (Real.log 4 + S₃) := Real.exp_lt_exp.2 h
  have hmul : (4 : ℝ) * Real.exp S₂ < (4 : ℝ) * Real.exp (Real.log 4 + S₃) :=
    mul_lt_mul_of_pos_left hexp (by norm_num)
  have h16 : (16 : ℝ) * Real.exp S₃ = (4 : ℝ) * Real.exp (Real.log 4 + S₃) := by
    calc
      (16 : ℝ) * Real.exp S₃ = (4 : ℝ) * (4 * Real.exp S₃) := by ring
      _ = (4 : ℝ) * Real.exp (Real.log 4 + S₃) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  linarith

/-- From `S₁ < log 4 + S₂`, generation `1 < 2` for the scaled mass proxy. -/
theorem ucl_mass_lt_gen12 {μ_a μ_b μ_c : ℤ} {L : ℝ} {S₁ S₂ : ℝ}
    (hS₁ : uclLogCalibration μ_a μ_b μ_c L 1 = S₁)
    (hS₂ : uclLogCalibration μ_a μ_b μ_c L 2 = S₂)
    (h : S₁ < Real.log 4 + S₂) :
    uclGenerationScaledMass μ_a μ_b μ_c L 1 < uclGenerationScaledMass μ_a μ_b μ_c L 2 := by
  unfold uclGenerationScaledMass uclGenerationScale uclCalibrationFactor
  rw [hS₁, hS₂]
  have h1 : (4 : ℝ) ^ (1 - 1) = 1 := by norm_num
  have h2 : (4 : ℝ) ^ (2 - 1) = 4 := by norm_num
  simp [h1, h2, one_mul]
  have hfour : Real.exp (Real.log 4 + S₂) = (4 : ℝ) * Real.exp S₂ := by
    rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  rw [← hfour]
  exact Real.exp_lt_exp.2 h

/-- From `S₂ < log 4 + S₃`, generation `2 < 3` for the scaled mass proxy. -/
theorem ucl_mass_lt_gen23 {μ_a μ_b μ_c : ℤ} {L : ℝ} {S₂ S₃ : ℝ}
    (hS₂ : uclLogCalibration μ_a μ_b μ_c L 2 = S₂)
    (hS₃ : uclLogCalibration μ_a μ_b μ_c L 3 = S₃)
    (h : S₂ < Real.log 4 + S₃) :
    uclGenerationScaledMass μ_a μ_b μ_c L 2 < uclGenerationScaledMass μ_a μ_b μ_c L 3 := by
  unfold uclGenerationScaledMass uclGenerationScale uclCalibrationFactor
  rw [hS₂, hS₃]
  have h2 : (4 : ℝ) ^ (2 - 1) = 4 := by norm_num
  have h3 : (4 : ℝ) ^ (3 - 1) = 16 := by norm_num
  simp [h2, h3]
  have hexp : Real.exp S₂ < Real.exp (Real.log 4 + S₃) := Real.exp_lt_exp.2 h
  have hmul : (4 : ℝ) * Real.exp S₂ < (4 : ℝ) * Real.exp (Real.log 4 + S₃) :=
    mul_lt_mul_of_pos_left hexp (by norm_num)
  have h16 : (16 : ℝ) * Real.exp S₃ = (4 : ℝ) * Real.exp (Real.log 4 + S₃) := by
    calc
      (16 : ℝ) * Real.exp S₃ = (4 : ℝ) * (4 * Real.exp S₃) := by ring
      _ = (4 : ℝ) * Real.exp (Real.log 4 + S₃) := by
        rw [Real.exp_add, Real.exp_log (by norm_num : (0 : ℝ) < 4)]
  linarith

end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds
