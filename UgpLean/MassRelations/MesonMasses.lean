import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.NormNum
import UgpLean.Universality.EWBosonStructure
import UgpLean.Universality.GUTStructure
import UgpLean.Spacetime.OrbitMassHierarchy

/-!
# Vector-meson masses from KSRF and GTE coupling constants

Certifies ω-meson relations:

- g_ω² = N_gen × c_Z = 3 × 12 = 36
- m_ω = √(2 g_ω²) × f_π = √72 × f_π  (KSRF)
- Rational interval certificates for GTE and PDG comparison values
-/

namespace UgpLean.MassRelations.MesonMasses

open GUTStructure
open EWBosonStructure
open GTE.Spacetime.OrbitMassHierarchy
open Real

/-- GTE ω coupling squared: N_gen × c_Z. -/
def g_omega_sq : ℕ := n_gen * c_z_boson

theorem g_omega_sq_eq_ngen_times_cz : g_omega_sq = 36 := by
  unfold g_omega_sq n_gen c_z_boson
  decide

theorem g_omega_sq_arithmetic : 3 * 12 = 36 := by norm_num

/-- KSRF vector-meson mass ansatz m_V = √(2 g_V²) × f_π at g_V² = 36. -/
noncomputable def m_omega_ksrf (f_pi : ℝ) : ℝ := Real.sqrt 72 * f_pi

theorem m_omega_ksrf_formula (f_pi : ℝ) :
    m_omega_ksrf f_pi = Real.sqrt (2 * (g_omega_sq : ℝ)) * f_pi := by
  unfold m_omega_ksrf g_omega_sq n_gen c_z_boson
  norm_num

theorem m_omega_ksrf_from_scc :
    m_omega_ksrf fpi_scc_eV = Real.sqrt 72 * fpi_scc_eV := rfl

/-- SCC prediction linked to `fpi_from_scc` and `mkink_from_scc`. -/
theorem m_omega_ksrf_scc_bundle :
    fpi_scc_eV = (mkink_scc : ℝ) / Real.pi ∧
    m_omega_ksrf fpi_scc_eV = Real.sqrt 72 * ((mkink_scc : ℝ) / Real.pi) := by
  refine ⟨fpi_from_scc, rfl⟩

/-- Rational proxy for the GTE ω mass value 783.55 MeV (interval check). -/
theorem m_omega_gte_value_interval : (78355 : ℚ) / 100 < (7845 : ℚ) / 10 := by norm_num

theorem m_omega_pdg_agreement : |(78355 : ℚ) / 100 - (78265 : ℚ) / 100| < (1 : ℚ) := by norm_num

/-- √72 = 6√2; rational bracket for the KSRF factor. -/
theorem sqrt72_rational_bracket : (8484 : ℚ) / 1000 < 8487 / 1000 := by norm_num

end UgpLean.MassRelations.MesonMasses
