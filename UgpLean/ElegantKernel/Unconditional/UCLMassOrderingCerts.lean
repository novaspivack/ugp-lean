import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts

def logFourLo : ℚ := 2 * 6931471803 / 10^10

theorem log_four_lo_pos : 0 < logFourLo := by
  unfold logFourLo
  norm_num

theorem lepton_cert_S1_lt_log4_plus_S2 :
    (10270659 : ℚ) / 100000000 < (6572194003 : ℚ) / 5000000000 := by
  norm_num

theorem lepton_cert_S2_lt_log4_plus_S3 :
    (-4532123 : ℚ) / 100000000 < (378870853 : ℚ) / 5000000000 := by
  norm_num

theorem up_cert_S1_lt_log4_plus_S2 :
    (54537411 : ℚ) / 100000000 < (12910086903 : ℚ) / 5000000000 := by
  norm_num

theorem up_cert_S2_lt_log4_plus_S3 :
    (124065233 : ℚ) / 100000000 < (11847493053 : ℚ) / 5000000000 := by
  norm_num

theorem down_cert_S1_lt_log4_plus_S2 :
    (76599857 : ℚ) / 100000000 < (6229703003 : ℚ) / 5000000000 := by
  norm_num

theorem down_cert_S2_lt_log4_plus_S3 :
    (-12801189 : ℚ) / 100000000 < (2397982953 : ℚ) / 5000000000 := by
  norm_num

end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts
