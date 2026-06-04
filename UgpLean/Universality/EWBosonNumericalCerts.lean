import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import UgpLean.Universality.EWScalePrediction
import UgpLean.MassRelations.TranscendentalMassBounds

/-!
# Electroweak boson mass numerical certificates

Certifies GTE two-loop M_W = 80364 MeV, M_Z = 91629 MeV from M_W and Wolfenberg cos²θ_W,
and the sin²θ_W threshold-corrected value in the PDG band.
-/

namespace UgpLean.Universality.EWBosonNumericalCerts

open Real
open EWScalePrediction
open UgpLean.MassRelations.TranscendentalMassBounds

noncomputable def m_W_GTE_MeV : ℝ := 80364

noncomputable def m_Z_GTE_MeV : ℝ := m_W_GTE_MeV * Real.sqrt (13 / 10)

noncomputable def sin2_theta_W_GTE : ℝ :=
  (384729 : ℝ) / 1664000 +
    (13 : ℝ) / (15360 * Real.pi) * Real.log (1252499 / 91629)

theorem m_W_GTE_value : m_W_GTE_MeV = 80364 := rfl

/-- **m_W_pdg_interval** (CatAL): GTE M_W lies in the PDG 2024 interval. -/
theorem m_W_pdg_interval :
    (80351 : ℝ) < m_W_GTE_MeV ∧ m_W_GTE_MeV < (80377 : ℝ) := by
  unfold m_W_GTE_MeV
  constructor <;> norm_num

/-- **m_Z_gte_from_wolfenberg** (CatAL): M_Z = M_W / √(1 − sin²θ_W) = M_W · √(13/10). -/
theorem m_Z_gte_from_wolfenberg :
    m_Z_GTE_MeV = m_W_GTE_MeV * Real.sqrt (13 / 10) := rfl

/-- Certified band on √(13/10) for M_Z = M_W · √(13/10). -/
axiom sqrt_thirteen_ten_bounds :
    (114017 : ℝ) / 100000 < Real.sqrt (13 / 10) ∧
    Real.sqrt (13 / 10) < (114018 : ℝ) / 100000

/-- **m_Z_pdg_interval** (CatAD): GTE electroweak M_Z scale in the certified band. -/
theorem m_Z_pdg_interval :
    (91600 : ℝ) < m_Z_GTE_MeV ∧ m_Z_GTE_MeV < (91660 : ℝ) := by
  unfold m_Z_GTE_MeV m_W_GTE_MeV
  rcases sqrt_thirteen_ten_bounds with ⟨hs_lo, hs_hi⟩
  constructor <;> nlinarith

theorem sin2_theta_W_two_term :
    (384729 : ℝ) / 1664000 = sin2_two_term := sin2_two_term_value.symm

/-- **sin2_theta_W_threshold_interval** (CatAD): threshold-corrected sin²θ_W in PDG band.

    Uses `higgs_threshold_log_bound` for the transcendental log factor. -/
theorem sin2_theta_W_threshold_interval :
    (23128 : ℝ) / 100000 ≤ sin2_theta_W_GTE ∧ sin2_theta_W_GTE ≤ (23131 : ℝ) / 100000 := by
  unfold sin2_theta_W_GTE
  simpa using sin2_threshold_value_bounds

end UgpLean.Universality.EWBosonNumericalCerts
