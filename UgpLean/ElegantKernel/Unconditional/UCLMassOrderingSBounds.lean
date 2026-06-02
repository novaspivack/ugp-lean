import Mathlib.Analysis.SpecialFunctions.Log.Basic
import UgpLean.ElegantKernel.Unconditional.UCLCalibration
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCoeffBounds
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts
import UgpLean.ElegantKernel.Unconditional.KLFullClosure

namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingSBounds

open Real
open UgpLean.ElegantKernel
open UgpLean.ElegantKernel.Unconditional.UCLCalibration
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCoeffBounds
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts
open UgpLean.ElegantKernel.Unconditional.KLFullClosure

/-! Coupled-corner delta bounds: `S_g1 - S_g2 < R` with rational `R`, then `R < log 4`. -/

private theorem lepton_delta12_sub :
    uclLogCalibration (1 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (73 : ℝ) - Real.log (823 : ℝ)) 1 -
        uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) 2 <
      (4364049 : ℝ) / 25000000 := by
  have hL1lo := L_lep1_lo
  have hL1hi := L_lep1_hi
  have hL2lo := L_lep2_lo
  have hL2hi := L_lep2_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  unfold uclLogCalibration
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  ring_nf
  nlinarith [hL1lo, hL1hi, hL2lo, hL2hi, hkLlo, hkLhi, hkgenlo, hkgenhi,
    hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem lepton_delta12_bound_lt_logFourLo :
    (4364049 : ℚ) / 25000000 < logFourLo := by
  unfold logFourLo
  norm_num

private theorem lepton_delta12_bound_lt_log4 : (4364049 : ℝ) / 25000000 < Real.log 4 := by
  have hlog4 := log_four_lo_lt_log_four
  have hlo : (4364049 : ℝ) / 25000000 < (6931471803 : ℝ) / 5000000000 := by norm_num
  have hcast : (6931471803 : ℝ) / 5000000000 = (↑logFourLo : ℝ) := by
    unfold logFourLo
    norm_num
  linarith [hlo, hcast, hlog4]

/-- Log-space ordering `1 < 2` for the lepton sector. -/
theorem lepton_log_delta12 :
    uclLogCalibration (1 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (73 : ℝ) - Real.log (823 : ℝ)) 1 <
      Real.log 4 + uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) 2 := by
  linarith [lepton_delta12_sub, lepton_delta12_bound_lt_log4]

private theorem lepton_delta23_sub :
    uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) 2 -
        uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 3 <
      (126519871 : ℝ) / 100000000 := by
  have hL1lo := L_lep2_lo
  have hL1hi := L_lep2_hi
  have hL2lo := L_lep3_lo
  have hL2hi := L_lep3_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  unfold uclLogCalibration
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  ring_nf
  nlinarith [hL1lo, hL1hi, hL2lo, hL2hi, hkLlo, hkLhi, hkgenlo, hkgenhi,
    hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem lepton_delta23_bound_lt_logFourLo :
    (126519871 : ℚ) / 100000000 < logFourLo := by
  unfold logFourLo
  norm_num

private theorem lepton_delta23_bound_lt_log4 : (126519871 : ℝ) / 100000000 < Real.log 4 := by
  have hlog4 := log_four_lo_lt_log_four
  have hlo : (126519871 : ℝ) / 100000000 < (6931471803 : ℝ) / 5000000000 := by norm_num
  have hcast : (6931471803 : ℝ) / 5000000000 = (↑logFourLo : ℝ) := by
    unfold logFourLo
    norm_num
  linarith [hlo, hcast, hlog4]

/-- Log-space ordering `2 < 3` for the lepton sector. -/
theorem lepton_log_delta23 :
    uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) 2 <
      Real.log 4 + uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 3 := by
  linarith [lepton_delta23_sub, lepton_delta23_bound_lt_log4]

private theorem up_delta12_sub :
    uclLogCalibration (-1 : ℤ) (0 : ℤ) (0 : ℤ) (Real.log (9 : ℝ) - Real.log (275 : ℝ)) 1 -
        uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 2 <
      (-13006983 : ℝ) / 20000000 := by
  have hL1lo := L_up1_lo
  have hL1hi := L_up1_hi
  have hL2lo := L_lep3_lo
  have hL2hi := L_lep3_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  unfold uclLogCalibration
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  ring_nf
  nlinarith [hL1lo, hL1hi, hL2lo, hL2hi, hkLlo, hkLhi, hkgenlo, hkgenhi,
    hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem up_delta12_bound_lt_logFourLo :
    (-13006983 : ℚ) / 20000000 < logFourLo := by
  unfold logFourLo
  norm_num

private theorem up_delta12_bound_lt_log4 : (-13006983 : ℝ) / 20000000 < Real.log 4 := by
  have hlog4 := log_four_lo_lt_log_four
  have hlo : (-13006983 : ℝ) / 20000000 < (6931471803 : ℝ) / 5000000000 := by norm_num
  have hcast : (6931471803 : ℝ) / 5000000000 = (↑logFourLo : ℝ) := by
    unfold logFourLo
    norm_num
  linarith [hlo, hcast, hlog4]

/-- Log-space ordering `1 < 2` for the up sector. -/
theorem up_log_delta12 :
    uclLogCalibration (-1 : ℤ) (0 : ℤ) (0 : ℤ) (Real.log (9 : ℝ) - Real.log (275 : ℝ)) 1 <
      Real.log 4 + uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 2 := by
  linarith [up_delta12_sub, up_delta12_bound_lt_log4]

private theorem up_delta23_sub :
    uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 2 -
        uclLogCalibration (0 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (337920 : ℝ) - Real.log 1) 3 <
      (12872401 : ℝ) / 50000000 := by
  have hL1lo := L_lep3_lo
  have hL1hi := L_lep3_hi
  have hL2lo := L_up3_lo
  have hL2hi := L_up3_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  unfold uclLogCalibration
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  ring_nf
  nlinarith [hL1lo, hL1hi, hL2lo, hL2hi, hkLlo, hkLhi, hkgenlo, hkgenhi,
    hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem up_delta23_bound_lt_logFourLo :
    (12872401 : ℚ) / 50000000 < logFourLo := by
  unfold logFourLo
  norm_num

private theorem up_delta23_bound_lt_log4 : (12872401 : ℝ) / 50000000 < Real.log 4 := by
  have hlog4 := log_four_lo_lt_log_four
  have hlo : (12872401 : ℝ) / 50000000 < (6931471803 : ℝ) / 5000000000 := by norm_num
  have hcast : (6931471803 : ℝ) / 5000000000 = (↑logFourLo : ℝ) := by
    unfold logFourLo
    norm_num
  linarith [hlo, hcast, hlog4]

/-- Log-space ordering `2 < 3` for the up sector. -/
theorem up_log_delta23 :
    uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 2 <
      Real.log 4 + uclLogCalibration (0 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (337920 : ℝ) - Real.log 1) 3 := by
  linarith [up_delta23_sub, up_delta23_bound_lt_log4]

private theorem down_delta12_sub :
    uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (5 : ℝ) - Real.log (42 : ℝ)) 1 -
        uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) 2 <
      (4531761 : ℝ) / 5000000 := by
  have hL1lo := L_dn1_lo
  have hL1hi := L_dn1_hi
  have hL2lo := L_dn2_lo
  have hL2hi := L_dn2_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  unfold uclLogCalibration
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  ring_nf
  nlinarith [hL1lo, hL1hi, hL2lo, hL2hi, hkLlo, hkLhi, hkgenlo, hkgenhi,
    hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem down_delta12_bound_lt_logFourLo :
    (4531761 : ℚ) / 5000000 < logFourLo := by
  unfold logFourLo
  norm_num

private theorem down_delta12_bound_lt_log4 : (4531761 : ℝ) / 5000000 < Real.log 4 := by
  have hlog4 := log_four_lo_lt_log_four
  have hlo : (4531761 : ℝ) / 5000000 < (6931471803 : ℝ) / 5000000000 := by norm_num
  have hcast : (6931471803 : ℝ) / 5000000000 = (↑logFourLo : ℝ) := by
    unfold logFourLo
    norm_num
  linarith [hlo, hcast, hlog4]

/-- Log-space ordering `1 < 2` for the down sector. -/
theorem down_log_delta12 :
    uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (5 : ℝ) - Real.log (42 : ℝ)) 1 <
      Real.log 4 + uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) 2 := by
  linarith [down_delta12_sub, down_delta12_bound_lt_log4]

private theorem down_delta23_sub :
    uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) 2 -
        uclLogCalibration (-1 : ℤ) (-1 : ℤ) (1 : ℤ) (Real.log (8191 : ℝ) - Real.log (65535 : ℝ)) 3 <
      (19467143 : ℝ) / 25000000 := by
  have hL1lo := L_dn2_lo
  have hL1hi := L_dn2_hi
  have hL2lo := L_dn3_lo
  have hL2hi := L_dn3_hi
  have hkLlo := k_L_derived_lo
  have hkLhi := k_L_derived_hi
  have hkgenlo := k_gen_derived_lo
  have hkgenhi := k_gen_derived_hi
  have hkgen2lo := k_gen2_lo
  have hkgen2hi := k_gen2_hi
  have hkMlo := k_M_lo
  have hkMhi := k_M_hi
  unfold uclLogCalibration
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]
  ring_nf
  nlinarith [hL1lo, hL1hi, hL2lo, hL2hi, hkLlo, hkLhi, hkgenlo, hkgenhi,
    hkgen2lo, hkgen2hi, hkMlo, hkMhi]

private theorem down_delta23_bound_lt_logFourLo :
    (19467143 : ℚ) / 25000000 < logFourLo := by
  unfold logFourLo
  norm_num

private theorem down_delta23_bound_lt_log4 : (19467143 : ℝ) / 25000000 < Real.log 4 := by
  have hlog4 := log_four_lo_lt_log_four
  have hlo : (19467143 : ℝ) / 25000000 < (6931471803 : ℝ) / 5000000000 := by norm_num
  have hcast : (6931471803 : ℝ) / 5000000000 = (↑logFourLo : ℝ) := by
    unfold logFourLo
    norm_num
  linarith [hlo, hcast, hlog4]

/-- Log-space ordering `2 < 3` for the down sector. -/
theorem down_log_delta23 :
    uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) 2 <
      Real.log 4 + uclLogCalibration (-1 : ℤ) (-1 : ℤ) (1 : ℤ) (Real.log (8191 : ℝ) - Real.log (65535 : ℝ)) 3 := by
  linarith [down_delta23_sub, down_delta23_bound_lt_log4]

end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingSBounds
