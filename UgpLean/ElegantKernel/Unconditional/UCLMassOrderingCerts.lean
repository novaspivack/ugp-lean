import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts

def logFourLo : ℚ := 2 * 6931471803 / 10^10

theorem log_four_lo_pos : 0 < logFourLo := by
  unfold logFourLo
  norm_num

theorem lepton_cert_S1_lt_log4_plus_S2 :
    (-6276309 : ℚ) / 5000000 < (-317647797 : ℚ) / 5000000000 := by
  norm_num

theorem lepton_cert_S2_lt_log4_plus_S3 :
    (-140328963 : ℚ) / 100000000 < (-6510970947 : ℚ) / 5000000000 := by
  norm_num

theorem up_cert_S1_lt_log4_plus_S2 :
    (-81259429 : ℚ) / 100000000 < (6020245103 : ℚ) / 5000000000 := by
  norm_num

theorem up_cert_S2_lt_log4_plus_S3 :
    (-5865803 : ℚ) / 50000000 < (4957651203 : ℚ) / 5000000000 := by
  norm_num

theorem down_cert_S1_lt_log4_plus_S2 :
    (-29598491 : ℚ) / 50000000 < (-660138847 : ℚ) / 5000000000 := by
  norm_num

theorem down_cert_S2_lt_log4_plus_S3 :
    (-148598029 : ℚ) / 100000000 < (-4491858847 : ℚ) / 5000000000 := by
  norm_num

end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts
