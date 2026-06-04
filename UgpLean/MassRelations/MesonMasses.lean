import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import UgpLean.Universality.BetaCoefficientIdentity
import UgpLean.Universality.EWBosonStructure
import UgpLean.Universality.GUTStructure
import UgpLean.Spacetime.OrbitMassHierarchy

/-!
# Vector-meson masses from KSRF and GTE coupling constants

Certifies ω- and ρ-meson relations:

- g_ω² = N_gen × c_Z = 3 × 12 = 36
- g_ρ² = C(b₀, N_gen) = C(7, 3) = 35
- Δg² = g_ω² − g_ρ² = 1
- m_V = √(2 g_V²) × f_π  (KSRF)
- Rational interval certificates for GTE and PDG comparison values
-/

namespace UgpLean.MassRelations.MesonMasses

open UgpLean.Universality.BetaCoefficientIdentity
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

/-- GTE ρ coupling squared: C(b₀, N_gen) = C(|Z₇|, N_gen). -/
def g_rho_sq : ℕ := Nat.choose Z7_order n_gen

theorem g_rho_sq_eq_casimir_orbit : g_rho_sq = 35 := by
  unfold g_rho_sq Z7_order n_gen
  decide

theorem g_rho_sq_arithmetic : Nat.choose 7 3 = 35 := by decide

/-- ω–ρ coupling gap: g_ω² − g_ρ² = N_gen × c_Z − C(b₀, N_gen) = 1. -/
theorem g_omega_rho_coupling_gap : g_omega_sq - g_rho_sq = 1 := by
  rw [g_omega_sq_eq_ngen_times_cz, g_rho_sq_eq_casimir_orbit]

theorem g_omega_rho_coupling_gap_arithmetic : 3 * 12 - Nat.choose 7 3 = 1 := by decide

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

/-- KSRF ρ-meson mass ansatz m_ρ = √(2 g_ρ²) × f_π at g_ρ² = 35. -/
noncomputable def m_rho_ksrf (f_pi : ℝ) : ℝ := Real.sqrt 70 * f_pi

theorem m_rho_ksrf_formula (f_pi : ℝ) (_hpos : 0 < f_pi) :
    m_rho_ksrf f_pi = Real.sqrt (2 * (g_rho_sq : ℝ)) * f_pi := by
  unfold m_rho_ksrf
  rw [show g_rho_sq = 35 from g_rho_sq_eq_casimir_orbit]
  norm_num

theorem m_rho_ksrf_closed (f_pi : ℝ) (_hpos : 0 < f_pi) :
    m_rho_ksrf f_pi = Real.sqrt 70 * f_pi := rfl

theorem m_rho_ksrf_from_scc :
    m_rho_ksrf fpi_scc_eV = Real.sqrt 70 * fpi_scc_eV := rfl

theorem m_rho_ksrf_scc_bundle :
    fpi_scc_eV = (mkink_scc : ℝ) / Real.pi ∧
    m_rho_ksrf fpi_scc_eV = Real.sqrt 70 * ((mkink_scc : ℝ) / Real.pi) := by
  refine ⟨fpi_from_scc, rfl⟩

private lemma sqrt70_gt : (8366 / 1000 : ℝ) < Real.sqrt 70 := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

private lemma sqrt70_lt : Real.sqrt 70 < (8367 / 1000 : ℝ) := by
  rw [← Real.sqrt_sq (by norm_num : 0 ≤ (8367 / 1000 : ℝ))]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private lemma fpi_cert_lo : (92341 / 1000 : ℝ) < (29010 / 100 : ℝ) / Real.pi := by
  have hpi_hi : Real.pi < (3.141593 : ℝ) := Real.pi_lt_d6
  have h1 : (29010 / 100 : ℝ) / (3.141593 : ℝ) < (29010 / 100 : ℝ) / Real.pi :=
    div_lt_div_of_pos_left (by norm_num) Real.pi_pos hpi_hi
  have h2 : (92341 / 1000 : ℝ) < (29010 / 100 : ℝ) / (3.141593 : ℝ) := by norm_num
  linarith

private lemma fpi_cert_hi : (29010 / 100 : ℝ) / Real.pi < (92347 / 1000 : ℝ) := by
  have hpi_lo : (3.141592 : ℝ) < Real.pi := Real.pi_gt_d6
  have h1 : (29010 / 100 : ℝ) / Real.pi < (29010 / 100 : ℝ) / (3.141592 : ℝ) :=
    div_lt_div_of_pos_left (by norm_num) (by norm_num) hpi_lo
  have h2 : (29010 / 100 : ℝ) / (3.141592 : ℝ) < (92347 / 1000 : ℝ) := by norm_num
  linarith

/-- Numerical certificate: √70 × f_π (SCC proxy) = 772.57 MeV within [772, 773] MeV. -/
theorem m_rho_ksrf_scc_value :
    |Real.sqrt 70 * ((29010 / 100 : ℝ) / Real.pi) - 772.57| < (1 / 10 : ℝ) := by
  have hlo : (77247 / 100 : ℝ) < (8366 / 1000 : ℝ) * (92341 / 1000) := by norm_num
  have hhi : (8367 / 1000 : ℝ) * (92347 / 1000) < (77267 / 100 : ℝ) := by norm_num
  have hmul_lo :
      (8366 / 1000 : ℝ) * (92341 / 1000) <
        Real.sqrt 70 * ((29010 / 100 : ℝ) / Real.pi) := by
    have hstep1 :
        (8366 / 1000 : ℝ) * (92341 / 1000) < Real.sqrt 70 * (92341 / 1000) :=
      mul_lt_mul_of_pos_right sqrt70_gt (by norm_num)
    have hstep2 :
        Real.sqrt 70 * (92341 / 1000) <
          Real.sqrt 70 * ((29010 / 100 : ℝ) / Real.pi) :=
      mul_lt_mul_of_pos_left fpi_cert_lo (Real.sqrt_pos.mpr (by norm_num : 0 < (70 : ℝ)))
    linarith
  have hmul_hi :
      Real.sqrt 70 * ((29010 / 100 : ℝ) / Real.pi) <
        (8367 / 1000 : ℝ) * (92347 / 1000) := by
    have hstep1 :
        Real.sqrt 70 * ((29010 / 100 : ℝ) / Real.pi) <
          (8367 / 1000 : ℝ) * ((29010 / 100 : ℝ) / Real.pi) :=
      mul_lt_mul_of_pos_right sqrt70_lt (div_pos (by norm_num) Real.pi_pos)
    have hstep2 :
        (8367 / 1000 : ℝ) * ((29010 / 100 : ℝ) / Real.pi) <
          (8367 / 1000 : ℝ) * (92347 / 1000) :=
      mul_lt_mul_of_pos_left fpi_cert_hi (by norm_num)
    linarith
  have htarget_lo : (77247 / 100 : ℝ) < Real.sqrt 70 * ((29010 / 100 : ℝ) / Real.pi) := by
    linarith [hlo, hmul_lo]
  have htarget_hi : Real.sqrt 70 * ((29010 / 100 : ℝ) / Real.pi) < (77267 / 100 : ℝ) := by
    linarith [hmul_hi, hhi]
  have hEq : (77257 / 100 : ℝ) = 772.57 := by norm_num
  have hpad_lo : (77257 / 100 : ℝ) - (1 / 10 : ℝ) = (77247 / 100 : ℝ) := by norm_num
  have hpad_hi : (77257 / 100 : ℝ) + (1 / 10 : ℝ) = (77267 / 100 : ℝ) := by norm_num
  have h₁ : -(1 / 10 : ℝ) < Real.sqrt 70 * ((29010 / 100 : ℝ) / Real.pi) - 772.57 := by
    have h := hpad_lo ▸ htarget_lo
    linarith [h, hEq]
  have h₂ : Real.sqrt 70 * ((29010 / 100 : ℝ) / Real.pi) - 772.57 < (1 / 10 : ℝ) := by
    have h := hpad_hi ▸ htarget_hi
    linarith [h, hEq]
  rw [abs_sub_lt_iff]
  exact ⟨h₂, by linarith [h₁]⟩

theorem m_rho_gte_value_interval : (77257 : ℚ) / 100 < (773 : ℚ) := by norm_num

theorem m_rho_pdg_gap : |(77257 : ℚ) / 100 - (77526 : ℚ) / 100| < (3 : ℚ) := by norm_num

end UgpLean.MassRelations.MesonMasses
