import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
Rational certificates for UCL generation-scaled mass ordering in log space.

If `S₁ < log 4 + S₂` and `S₂ < log 4 + S₃` with conservative rational brackets on
each `S_g`, then `m̃₁ < m̃₂ < m̃₃` (see `UCLMassOrderingBounds`).
-/

namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts

/-- Lower bound on `log 4` from Mathlib `log_two_gt_d9`. -/
def logFourLo : ℚ := 2 * 6931471803 / 10^10

theorem log_four_lo_pos : 0 < logFourLo := by
  unfold logFourLo
  norm_num

theorem log_four_lo_lt_four : logFourLo < 4 := by
  unfold logFourLo
  norm_num

/-! ### Lepton sector certificates -/

theorem lepton_cert_S1_lt_log4_plus_S2 :
    (966387 : ℚ) / 10^8 < logFourLo + (-1356301 : ℚ) / (2 * 10^7) := by
  unfold logFourLo
  norm_num

theorem lepton_cert_S2_lt_log4_plus_S3 :
    (-6697279 : ℚ) / 10^8 < logFourLo + (-26147167 : ℚ) / (2 * 10^7) := by
  unfold logFourLo
  norm_num

/-! ### Up-quark sector certificates -/

theorem up_cert_S1_lt_log4_plus_S2 :
    (1705031 : ℚ) / 3125000 < logFourLo + (23977697 : ℚ) / (2 * 10^7) := by
  unfold logFourLo
  norm_num

theorem up_cert_S2_lt_log4_plus_S3 :
    (120010129 : ℚ) / 10^8 < logFourLo + (49124989 : ℚ) / (5 * 10^7) := by
  unfold logFourLo
  norm_num

/-! ### Down-quark sector certificates -/

theorem down_cert_S1_lt_log4_plus_S2 :
    (76471327 : ℚ) / 10^8 < logFourLo + (-13796267 : ℚ) / 10^8 := by
  unfold logFourLo
  norm_num

theorem down_cert_S2_lt_log4_plus_S3 :
    (-2747291 : ℚ) / (2 * 10^7) < logFourLo + (-89617491 : ℚ) / 10^8 := by
  unfold logFourLo
  norm_num

end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts
