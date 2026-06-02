import UgpLean.ElegantKernel.Unconditional.UCLCalibration
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingSBounds

namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingDelta

open Real
open UgpLean.ElegantKernel.Unconditional.UCLCalibration
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingSBounds

/-- Log-space ordering `1 < 2` for the lepton sector. -/
theorem lepton_log_delta12 :
    uclLogCalibration (1 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (73 : ℝ) - Real.log (823 : ℝ)) 1 <
      Real.log 4 + uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) 2 := by
  have hS1hi := lep1_S_hi
  have hS2lo := lep2_S_lo
  have hcert : (-6276309 : ℝ) / 5000000 <
      (↑logFourLo : ℝ) + (-18122799 : ℝ) / 12500000 := by
    exact_mod_cast lepton_cert_S1_lt_log4_plus_S2
  have hlog4 := log_four_lo_lt_log_four
  linarith [hS1hi, hS2lo, hcert, hlog4]

/-- Log-space ordering `2 < 3` for the lepton sector. -/
theorem lepton_log_delta23 :
    uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (42 : ℝ) - Real.log (1023 : ℝ)) 2 <
      Real.log 4 + uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 3 := by
  have hS1hi := lep2_S_hi
  have hS2lo := lep3_S_lo
  have hcert : (-140328963 : ℝ) / 100000000 <
      (↑logFourLo : ℝ) + (-53769771 : ℝ) / 20000000 := by
    exact_mod_cast lepton_cert_S2_lt_log4_plus_S3
  have hlog4 := log_four_lo_lt_log_four
  linarith [hS1hi, hS2lo, hcert, hlog4]

/-- Log-space ordering `1 < 2` for the up sector. -/
theorem up_log_delta12 :
    uclLogCalibration (-1 : ℤ) (0 : ℤ) (0 : ℤ) (Real.log (9 : ℝ) - Real.log (275 : ℝ)) 1 <
      Real.log 4 + uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 2 := by
  have hS1hi := up1_S_hi
  have hS2lo := up2_S_lo
  have hcert : (-81259429 : ℝ) / 100000000 <
      (↑logFourLo : ℝ) + (-9112267 : ℝ) / 50000000 := by
    exact_mod_cast up_cert_S1_lt_log4_plus_S2
  have hlog4 := log_four_lo_lt_log_four
  linarith [hS1hi, hS2lo, hcert, hlog4]

/-- Log-space ordering `2 < 3` for the up sector. -/
theorem up_log_delta23 :
    uclLogCalibration (-1 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (275 : ℝ) - Real.log (65535 : ℝ)) 2 <
      Real.log 4 + uclLogCalibration (0 : ℤ) (0 : ℤ) (1 : ℤ) (Real.log (337920 : ℝ) - Real.log 1) 3 := by
  have hS1hi := up2_S_hi
  have hS2lo := up3_S_lo
  have hcert : (-5865803 : ℝ) / 50000000 <
      (↑logFourLo : ℝ) + (-9869103 : ℝ) / 25000000 := by
    exact_mod_cast up_cert_S2_lt_log4_plus_S3
  have hlog4 := log_four_lo_lt_log_four
  linarith [hS1hi, hS2lo, hcert, hlog4]

/-- Log-space ordering `1 < 2` for the down sector. -/
theorem down_log_delta12 :
    uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (5 : ℝ) - Real.log (42 : ℝ)) 1 <
      Real.log 4 + uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) 2 := by
  have hS1hi := dn1_S_hi
  have hS2lo := dn2_S_lo
  have hcert : (-29598491 : ℝ) / 50000000 <
      (↑logFourLo : ℝ) + (-151832213 : ℝ) / 100000000 := by
    exact_mod_cast down_cert_S1_lt_log4_plus_S2
  have hlog4 := log_four_lo_lt_log_four
  linarith [hS1hi, hS2lo, hcert, hlog4]

/-- Log-space ordering `2 < 3` for the down sector. -/
theorem down_log_delta23 :
    uclLogCalibration (0 : ℤ) (-1 : ℤ) (-1 : ℤ) (Real.log (186 : ℝ) - Real.log (1023 : ℝ)) 2 <
      Real.log 4 + uclLogCalibration (-1 : ℤ) (-1 : ℤ) (1 : ℤ) (Real.log (8191 : ℝ) - Real.log (65535 : ℝ)) 3 := by
  have hS1hi := dn2_S_hi
  have hS2lo := dn3_S_lo
  have hcert : (-148598029 : ℝ) / 100000000 <
      (↑logFourLo : ℝ) + (-228466613 : ℝ) / 100000000 := by
    exact_mod_cast down_cert_S2_lt_log4_plus_S3
  have hlog4 := log_four_lo_lt_log_four
  linarith [hS1hi, hS2lo, hcert, hlog4]

end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingDelta
