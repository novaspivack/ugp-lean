import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import UgpLean.ElegantKernel.Unconditional.UCLCalibration
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCoeffBounds
import UgpLean.ElegantKernel.Unconditional.KLFullClosure
import UgpLean.ElegantKernel.Unconditional.KConstFullClosure

namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingSBounds

open Real
open UgpLean.ElegantKernel
open UgpLean.ElegantKernel.Unconditional.UCLCalibration
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCoeffBounds
open UgpLean.ElegantKernel.Unconditional.KLFullClosure
open UgpLean.ElegantKernel.Unconditional.KConstFullClosure

/-! S-value interval bounds. -/


private theorem lep1_f_lo : (12374531 : ℝ) / 50000000 < k_L_derived * (Real.log (73 : ℝ) - Real.log (823 : ℝ)) + (7 / 512 : ℝ) * (Real.log (73 : ℝ) - Real.log (823 : ℝ)) ^ 2 + k_gen_derived * 1 + k_gen2 * (1 : ℝ) ^ 2 + k_M * (1 : ℝ) * (-1 : ℝ) * (-1 : ℝ) + (1 / 8 : ℝ) * (1 : ℤ) + (-3 / 2 : ℝ) * (-1 : ℤ) + (4 / 3 : ℝ) * (-1 : ℤ) := by
  have hLlo := L_lep1_lo
  have hLhi := L_lep1_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem lep1_f_hi : k_L_derived * (Real.log (73 : ℝ) - Real.log (823 : ℝ)) + (7 / 512 : ℝ) * (Real.log (73 : ℝ) - Real.log (823 : ℝ)) ^ 2 + k_gen_derived * 1 + k_gen2 * (1 : ℝ) ^ 2 + k_M * (1 : ℝ) * (-1 : ℝ) * (-1 : ℝ) + (1 / 8 : ℝ) * (1 : ℤ) + (-3 / 2 : ℝ) * (-1 : ℤ) + (4 / 3 : ℝ) * (-1 : ℤ) < (25473819 : ℝ) / 100000000 := by
  have hLlo := L_lep1_lo
  have hLhi := L_lep1_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

theorem lep1_S_lo : (-64125469 : ℝ) / 50000000 < uclLogCalibration (1 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (73 : ℝ) - Real.log (823 : ℝ)) 1 := by
  have hf := lep1_f_lo
  have hk := k_const_lo
  unfold uclLogCalibration
  linarith [hf, hk]

theorem lep1_S_hi : uclLogCalibration (1 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (73 : ℝ) - Real.log (823 : ℝ)) 1 < (-125526181 : ℝ) / 100000000 := by
  have hf := lep1_f_hi
  have hk := k_const_hi
  unfold uclLogCalibration
  linarith [hf, hk]

private theorem lep2_f_lo : (8017609 : ℝ) / 100000000 < k_L_derived * (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) + (7 / 512 : ℝ) * (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) ^ 2 + k_gen_derived * 2 + k_gen2 * (2 : ℝ) ^ 2 + k_M * (0 : ℝ) * (-1 : ℝ) * (-1 : ℝ) + (1 / 8 : ℝ) * (0 : ℤ) + (-3 / 2 : ℝ) * (-1 : ℤ) + (4 / 3 : ℝ) * (-1 : ℤ) := by
  have hLlo := L_lep2_lo
  have hLhi := L_lep2_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem lep2_f_hi : k_L_derived * (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) + (7 / 512 : ℝ) * (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) ^ 2 + k_gen_derived * 2 + k_gen2 * (2 : ℝ) ^ 2 + k_M * (0 : ℝ) * (-1 : ℝ) * (-1 : ℝ) + (1 / 8 : ℝ) * (0 : ℤ) + (-3 / 2 : ℝ) * (-1 : ℤ) + (4 / 3 : ℝ) * (-1 : ℤ) < (2667759 : ℝ) / 25000000 := by
  have hLlo := L_lep2_lo
  have hLhi := L_lep2_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

theorem lep2_S_lo : (-144982391 : ℝ) / 100000000 < uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) 2 := by
  have hf := lep2_f_lo
  have hk := k_const_lo
  unfold uclLogCalibration
  linarith [hf, hk]

theorem lep2_S_hi : uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) 2 < (-35082241 : ℝ) / 25000000 := by
  have hf := lep2_f_hi
  have hk := k_const_hi
  unfold uclLogCalibration
  linarith [hf, hk]

private theorem lep3_f_lo : (-57924427 : ℝ) / 50000000 < k_L_derived * (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) + (7 / 512 : ℝ) * (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) ^ 2 + k_gen_derived * 3 + k_gen2 * (3 : ℝ) ^ 2 + k_M * (-1 : ℝ) * (0 : ℝ) * (1 : ℝ) + (1 / 8 : ℝ) * (-1 : ℤ) + (-3 / 2 : ℝ) * (0 : ℤ) + (4 / 3 : ℝ) * (1 : ℤ) := by
  have hLlo := L_lep3_lo
  have hLhi := L_lep3_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem lep3_f_hi : k_L_derived * (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) + (7 / 512 : ℝ) * (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) ^ 2 + k_gen_derived * 3 + k_gen2 * (3 : ℝ) ^ 2 + k_M * (-1 : ℝ) * (0 : ℝ) * (1 : ℝ) + (1 / 8 : ℝ) * (-1 : ℤ) + (-3 / 2 : ℝ) * (0 : ℤ) + (4 / 3 : ℝ) * (1 : ℤ) < (-111355927 : ℝ) / 100000000 := by
  have hLlo := L_lep3_lo
  have hLhi := L_lep3_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

theorem lep3_S_lo : (-134424427 : ℝ) / 50000000 < uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 3 := by
  have hf := lep3_f_lo
  have hk := k_const_lo
  unfold uclLogCalibration
  linarith [hf, hk]

theorem lep3_S_hi : uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 3 < (-262355927 : ℝ) / 100000000 := by
  have hf := lep3_f_hi
  have hk := k_const_hi
  unfold uclLogCalibration
  linarith [hf, hk]

private theorem up1_f_lo : (69666783 : ℝ) / 100000000 < k_L_derived * (Real.log (9 : ℝ) - Real.log (275 : ℝ)) + (7 / 512 : ℝ) * (Real.log (9 : ℝ) - Real.log (275 : ℝ)) ^ 2 + k_gen_derived * 1 + k_gen2 * (1 : ℝ) ^ 2 + k_M * (-1 : ℝ) * (0 : ℝ) * (0 : ℝ) + (1 / 8 : ℝ) * (-1 : ℤ) + (-3 / 2 : ℝ) * (0 : ℤ) + (4 / 3 : ℝ) * (0 : ℤ) := by
  have hLlo := L_up1_lo
  have hLhi := L_up1_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem up1_f_hi : k_L_derived * (Real.log (9 : ℝ) - Real.log (275 : ℝ)) + (7 / 512 : ℝ) * (Real.log (9 : ℝ) - Real.log (275 : ℝ)) ^ 2 + k_gen_derived * 1 + k_gen2 * (1 : ℝ) ^ 2 + k_M * (-1 : ℝ) * (0 : ℝ) * (0 : ℝ) + (1 / 8 : ℝ) * (-1 : ℤ) + (-3 / 2 : ℝ) * (0 : ℤ) + (4 / 3 : ℝ) * (0 : ℤ) < (6974057 : ℝ) / 10000000 := by
  have hLlo := L_up1_lo
  have hLhi := L_up1_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

theorem up1_S_lo : (-83333217 : ℝ) / 100000000 < uclLogCalibration (-1 : ℤ) (0 : ℤ) (0 : ℤ) (Real.log (9 : ℝ) - Real.log (275 : ℝ)) 1 := by
  have hf := up1_f_lo
  have hk := k_const_lo
  unfold uclLogCalibration
  linarith [hf, hk]

theorem up1_S_hi : uclLogCalibration (-1 : ℤ) (0 : ℤ) (0 : ℤ) (Real.log (9 : ℝ) - Real.log (275 : ℝ)) 1 < (-8125943 : ℝ) / 10000000 := by
  have hf := up1_f_hi
  have hk := k_const_hi
  unfold uclLogCalibration
  linarith [hf, hk]

private theorem up2_f_lo : (134775467 : ℝ) / 100000000 < k_L_derived * (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) + (7 / 512 : ℝ) * (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) ^ 2 + k_gen_derived * 2 + k_gen2 * (2 : ℝ) ^ 2 + k_M * (-1 : ℝ) * (0 : ℝ) * (1 : ℝ) + (1 / 8 : ℝ) * (-1 : ℤ) + (-3 / 2 : ℝ) * (0 : ℤ) + (4 / 3 : ℝ) * (1 : ℤ) := by
  have hLlo := L_up2_lo
  have hLhi := L_up2_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem up2_f_hi : k_L_derived * (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) + (7 / 512 : ℝ) * (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) ^ 2 + k_gen_derived * 2 + k_gen2 * (2 : ℝ) ^ 2 + k_M * (-1 : ℝ) * (0 : ℝ) * (1 : ℝ) + (1 / 8 : ℝ) * (-1 : ℤ) + (-3 / 2 : ℝ) * (0 : ℤ) + (4 / 3 : ℝ) * (1 : ℤ) < (139268393 : ℝ) / 100000000 := by
  have hLlo := L_up2_lo
  have hLhi := L_up2_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

theorem up2_S_lo : (-18224533 : ℝ) / 100000000 < uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 2 := by
  have hf := up2_f_lo
  have hk := k_const_lo
  unfold uclLogCalibration
  linarith [hf, hk]

theorem up2_S_hi : uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 2 < (-11731607 : ℝ) / 100000000 := by
  have hf := up2_f_hi
  have hk := k_const_hi
  unfold uclLogCalibration
  linarith [hf, hk]

private theorem up3_f_lo : (113523589 : ℝ) / 100000000 < k_L_derived * (Real.log (337920 : ℝ) - Real.log 1) + (7 / 512 : ℝ) * (Real.log (337920 : ℝ) - Real.log 1) ^ 2 + k_gen_derived * 3 + k_gen2 * (3 : ℝ) ^ 2 + k_M * (0 : ℝ) * (0 : ℝ) * (1 : ℝ) + (1 / 8 : ℝ) * (0 : ℤ) + (-3 / 2 : ℝ) * (0 : ℤ) + (4 / 3 : ℝ) * (1 : ℤ) := by
  have hLlo := L_up3_lo
  have hLhi := L_up3_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem up3_f_hi : k_L_derived * (Real.log (337920 : ℝ) - Real.log 1) + (7 / 512 : ℝ) * (Real.log (337920 : ℝ) - Real.log 1) ^ 2 + k_gen_derived * 3 + k_gen2 * (3 : ℝ) ^ 2 + k_M * (0 : ℝ) * (0 : ℝ) * (1 : ℝ) + (1 / 8 : ℝ) * (0 : ℤ) + (-3 / 2 : ℝ) * (0 : ℤ) + (4 / 3 : ℝ) * (1 : ℤ) < (114868057 : ℝ) / 100000000 := by
  have hLlo := L_up3_lo
  have hLhi := L_up3_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

theorem up3_S_lo : (-39476411 : ℝ) / 100000000 < uclLogCalibration (0 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (337920 : ℝ) - Real.log 1) 3 := by
  have hf := up3_f_lo
  have hk := k_const_lo
  unfold uclLogCalibration
  linarith [hf, hk]

theorem up3_S_hi : uclLogCalibration (0 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (337920 : ℝ) - Real.log 1) 3 < (-36131943 : ℝ) / 100000000 := by
  have hf := up3_f_hi
  have hk := k_const_hi
  unfold uclLogCalibration
  linarith [hf, hk]

private theorem dn1_f_lo : (45766269 : ℝ) / 50000000 < k_L_derived * (Real.log (5 : ℝ) - Real.log (42 : ℝ)) + (7 / 512 : ℝ) * (Real.log (5 : ℝ) - Real.log (42 : ℝ)) ^ 2 + k_gen_derived * 1 + k_gen2 * (1 : ℝ) ^ 2 + k_M * (0 : ℝ) * (-1 : ℝ) * (-1 : ℝ) + (1 / 8 : ℝ) * (0 : ℤ) + (-3 / 2 : ℝ) * (-1 : ℤ) + (4 / 3 : ℝ) * (-1 : ℤ) := by
  have hLlo := L_dn1_lo
  have hLhi := L_dn1_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem dn1_f_hi : k_L_derived * (Real.log (5 : ℝ) - Real.log (42 : ℝ)) + (7 / 512 : ℝ) * (Real.log (5 : ℝ) - Real.log (42 : ℝ)) ^ 2 + k_gen_derived * 1 + k_gen2 * (1 : ℝ) ^ 2 + k_M * (0 : ℝ) * (-1 : ℝ) * (-1 : ℝ) + (1 / 8 : ℝ) * (0 : ℤ) + (-3 / 2 : ℝ) * (-1 : ℤ) + (4 / 3 : ℝ) * (-1 : ℤ) < (91803017 : ℝ) / 100000000 := by
  have hLlo := L_dn1_lo
  have hLhi := L_dn1_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

theorem dn1_S_lo : (-30733731 : ℝ) / 50000000 < uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (5 : ℝ) - Real.log (42 : ℝ)) 1 := by
  have hf := dn1_f_lo
  have hk := k_const_lo
  unfold uclLogCalibration
  linarith [hf, hk]

theorem dn1_S_hi : uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (5 : ℝ) - Real.log (42 : ℝ)) 1 < (-59196983 : ℝ) / 100000000 := by
  have hf := dn1_f_hi
  have hk := k_const_hi
  unfold uclLogCalibration
  linarith [hf, hk]

private theorem dn2_f_lo : (291947 : ℝ) / 25000000 < k_L_derived * (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) + (7 / 512 : ℝ) * (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) ^ 2 + k_gen_derived * 2 + k_gen2 * (2 : ℝ) ^ 2 + k_M * (0 : ℝ) * (-1 : ℝ) * (-1 : ℝ) + (1 / 8 : ℝ) * (0 : ℤ) + (-3 / 2 : ℝ) * (-1 : ℤ) + (4 / 3 : ℝ) * (-1 : ℤ) := by
  have hLlo := L_dn2_lo
  have hLhi := L_dn2_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem dn2_f_hi : k_L_derived * (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) + (7 / 512 : ℝ) * (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) ^ 2 + k_gen_derived * 2 + k_gen2 * (2 : ℝ) ^ 2 + k_M * (0 : ℝ) * (-1 : ℝ) * (-1 : ℝ) + (1 / 8 : ℝ) * (0 : ℤ) + (-3 / 2 : ℝ) * (-1 : ℤ) + (4 / 3 : ℝ) * (-1 : ℤ) < (240197 : ℝ) / 10000000 := by
  have hLlo := L_dn2_lo
  have hLhi := L_dn2_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

theorem dn2_S_lo : (-37958053 : ℝ) / 25000000 < uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) 2 := by
  have hf := dn2_f_lo
  have hk := k_const_lo
  unfold uclLogCalibration
  linarith [hf, hk]

theorem dn2_S_hi : uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) 2 < (-14859803 : ℝ) / 10000000 := by
  have hf := dn2_f_hi
  have hk := k_const_hi
  unfold uclLogCalibration
  linarith [hf, hk]

private theorem dn3_f_lo : (-18866653 : ℝ) / 25000000 < k_L_derived * (Real.log (8191 : ℝ) - Real.log (65535 : ℝ)) + (7 / 512 : ℝ) * (Real.log (8191 : ℝ) - Real.log (65535 : ℝ)) ^ 2 + k_gen_derived * 3 + k_gen2 * (3 : ℝ) ^ 2 + k_M * (-1 : ℝ) * (-1 : ℝ) * (1 : ℝ) + (1 / 8 : ℝ) * (-1 : ℤ) + (-3 / 2 : ℝ) * (-1 : ℤ) + (4 / 3 : ℝ) * (1 : ℤ) := by
  have hLlo := L_dn3_lo
  have hLhi := L_dn3_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem dn3_f_hi : k_L_derived * (Real.log (8191 : ℝ) - Real.log (65535 : ℝ)) + (7 / 512 : ℝ) * (Real.log (8191 : ℝ) - Real.log (65535 : ℝ)) ^ 2 + k_gen_derived * 3 + k_gen2 * (3 : ℝ) ^ 2 + k_M * (-1 : ℝ) * (-1 : ℝ) * (1 : ℝ) + (1 / 8 : ℝ) * (-1 : ℤ) + (-3 / 2 : ℝ) * (-1 : ℤ) + (4 / 3 : ℝ) * (1 : ℤ) < (-4562003 : ℝ) / 6250000 := by
  have hLlo := L_dn3_lo
  have hLhi := L_dn3_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  rw [k_L_derived_closed_form]
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]

theorem dn3_S_lo : (-57116653 : ℝ) / 25000000 < uclLogCalibration (-1 : ℤ) (-1 : ℤ) (1 : ℤ) (Real.log (8191 : ℝ) - Real.log (65535 : ℝ)) 3 := by
  have hf := dn3_f_lo
  have hk := k_const_lo
  unfold uclLogCalibration
  linarith [hf, hk]

theorem dn3_S_hi : uclLogCalibration (-1 : ℤ) (-1 : ℤ) (1 : ℤ) (Real.log (8191 : ℝ) - Real.log (65535 : ℝ)) 3 < (-13999503 : ℝ) / 6250000 := by
  have hf := dn3_f_hi
  have hk := k_const_hi
  unfold uclLogCalibration
  linarith [hf, hk]

end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingSBounds
