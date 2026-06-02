import Mathlib.Analysis.SpecialFunctions.Log.Basic
import UgpLean.ElegantKernel.Unconditional.UCLCalibration
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCoeffBounds
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds
import UgpLean.ElegantKernel.Unconditional.KLFullClosure

namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingDelta

open Real
open UgpLean.ElegantKernel
open UgpLean.ElegantKernel.Unconditional.UCLCalibration
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCoeffBounds
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds
open UgpLean.ElegantKernel.Unconditional.KLFullClosure

/-- Log-space ordering `1 < 2` for the lepton sector. -/
theorem lepton_log_delta12 :
    uclLogCalibration (1 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (73 : ℝ) - Real.log (823 : ℝ)) 1 <
      Real.log 4 + uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) 2 := by
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
  have hlog4 := log_four_lo_lt_log_four
  unfold uclLogCalibration
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq, k_L_derived_closed_form]
  ring_nf
  nlinarith [hL1lo, hL1hi, hL2lo, hL2hi, hkLlo, hkLhi, hkgenlo, hkgenhi,
    hkgen2lo, hkgen2hi, hkMlo, hkMhi, hlog4]

/-- Log-space ordering `2 < 3` for the lepton sector. -/
theorem lepton_log_delta23 :
    uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) 2 <
      Real.log 4 + uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 3 := by
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
  have hlog4 := log_four_lo_lt_log_four
  unfold uclLogCalibration
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq, k_L_derived_closed_form]
  ring_nf
  nlinarith [hL1lo, hL1hi, hL2lo, hL2hi, hkLlo, hkLhi, hkgenlo, hkgenhi,
    hkgen2lo, hkgen2hi, hkMlo, hkMhi, hlog4]

/-- Log-space ordering `1 < 2` for the up sector. -/
theorem up_log_delta12 :
    uclLogCalibration (-1 : ℤ) (0 : ℤ) (0 : ℤ) (Real.log (9 : ℝ) - Real.log (275 : ℝ)) 1 <
      Real.log 4 + uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 2 := by
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
  have hlog4 := log_four_lo_lt_log_four
  unfold uclLogCalibration
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq, k_L_derived_closed_form]
  ring_nf
  nlinarith [hL1lo, hL1hi, hL2lo, hL2hi, hkLlo, hkLhi, hkgenlo, hkgenhi,
    hkgen2lo, hkgen2hi, hkMlo, hkMhi, hlog4]

/-- Log-space ordering `2 < 3` for the up sector. -/
theorem up_log_delta23 :
    uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 2 <
      Real.log 4 + uclLogCalibration (0 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (337920 : ℝ) - Real.log 1) 3 := by
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
  have hlog4 := log_four_lo_lt_log_four
  unfold uclLogCalibration
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq, k_L_derived_closed_form]
  ring_nf
  nlinarith [hL1lo, hL1hi, hL2lo, hL2hi, hkLlo, hkLhi, hkgenlo, hkgenhi,
    hkgen2lo, hkgen2hi, hkMlo, hkMhi, hlog4]

/-- Log-space ordering `1 < 2` for the down sector. -/
theorem down_log_delta12 :
    uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (5 : ℝ) - Real.log (42 : ℝ)) 1 <
      Real.log 4 + uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) 2 := by
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
  have hlog4 := log_four_lo_lt_log_four
  unfold uclLogCalibration
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq, k_L_derived_closed_form]
  ring_nf
  nlinarith [hL1lo, hL1hi, hL2lo, hL2hi, hkLlo, hkLhi, hkgenlo, hkgenhi,
    hkgen2lo, hkgen2hi, hkMlo, hkMhi, hlog4]

/-- Log-space ordering `2 < 3` for the down sector. -/
theorem down_log_delta23 :
    uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) 2 <
      Real.log 4 + uclLogCalibration (-1 : ℤ) (-1 : ℤ) (1 : ℤ) (Real.log (8191 : ℝ) - Real.log (65535 : ℝ)) 3 := by
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
  have hlog4 := log_four_lo_lt_log_four
  unfold uclLogCalibration
  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq, k_L_derived_closed_form]
  ring_nf
  nlinarith [hL1lo, hL1hi, hL2lo, hL2hi, hkLlo, hkLhi, hkgenlo, hkgenhi,
    hkgen2lo, hkgen2hi, hkMlo, hkMhi, hlog4]

end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingDelta
