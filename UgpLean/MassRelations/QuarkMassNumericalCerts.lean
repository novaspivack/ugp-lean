import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import UgpLean.MassRelations.PhysicalMasses
import UgpLean.MassRelations.TranscendentalMassBounds

/-!
# PDG interval certificates for the six-quark TT+VV cascade

Transcendental factors are bounded in `TranscendentalMassBounds`; products close
by `nlinarith`. Masses use the MeV-scale PDG anchor convention (electron 0.51099895).
-/

namespace UgpLean.MassRelations.QuarkMassNumericalCerts

open Real
open UgpLean.MassRelations.PhysicalMasses
open TranscendentalMassBounds

noncomputable section

private lemma pdg_m_e_interval :
    (5109989 : ℝ) / 10 ^ 7 < pdg_m_e_mev ∧ pdg_m_e_mev < (5109991 : ℝ) / 10 ^ 7 := by
  unfold pdg_m_e_mev; constructor <;> norm_num

private lemma pdg_m_mu_interval :
    (1056583754 : ℝ) / 10 ^ 7 < pdg_m_mu_mev ∧ pdg_m_mu_mev < (1056583756 : ℝ) / 10 ^ 7 := by
  unfold pdg_m_mu_mev; constructor <;> norm_num

theorem m_u_pdg_interval :
    (209 : ℝ) / 100 < predictedUpType pdg_m_e_mev pdg_m_mu_mev 0 ∧
    predictedUpType pdg_m_e_mev pdg_m_mu_mev 0 < (223 : ℝ) / 100 := by
  unfold predictedUpType predictedLepton
  rcases pdg_m_e_interval with ⟨he_lo, he_hi⟩
  rcases tt_exp_g0_bounds with ⟨hexp_lo, hexp_hi⟩
  constructor <;> nlinarith

theorem m_c_pdg_interval : (1261 : ℝ) < predictedUpType pdg_m_e_mev pdg_m_mu_mev 1 ∧
    predictedUpType pdg_m_e_mev pdg_m_mu_mev 1 < (1279 : ℝ) :=
  m_c_predicted_interval

theorem m_t_pdg_interval : (172320 : ℝ) < predictedUpType pdg_m_e_mev pdg_m_mu_mev 2 ∧
    predictedUpType pdg_m_e_mev pdg_m_mu_mev 2 < (172820 : ℝ) :=
  m_t_predicted_interval

theorem m_d_pdg_interval : (436 : ℝ) / 100 < predictedDownType pdg_m_e_mev pdg_m_mu_mev 0 ∧
    predictedDownType pdg_m_e_mev pdg_m_mu_mev 0 < (504 : ℝ) / 100 :=
  m_d_predicted_interval

theorem m_s_pdg_interval : (8765 : ℝ) / 100 < predictedDownType pdg_m_e_mev pdg_m_mu_mev 1 ∧
    predictedDownType pdg_m_e_mev pdg_m_mu_mev 1 < (9935 : ℝ) / 100 :=
  m_s_predicted_interval

theorem m_b_pdg_interval : (4175 : ℝ) < predictedDownType pdg_m_e_mev pdg_m_mu_mev 2 ∧
    predictedDownType pdg_m_e_mev pdg_m_mu_mev 2 < (4191 : ℝ) :=
  m_b_predicted_interval

end

end UgpLean.MassRelations.QuarkMassNumericalCerts
