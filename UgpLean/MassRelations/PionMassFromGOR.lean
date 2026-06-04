import Mathlib.Algebra.Order.Group.Abs
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import UgpLean.QFT.ChiralSymmetryBreaking
import UgpLean.Spacetime.OrbitMassHierarchy

/-!
# Pion mass from GOR, SCC kink condensate, and `fpi_from_scc`

Certifies the GTE pion mass formula

  m_π = π √( (m_u + m_d) M_kink )

from the Gell-Mann–Oakes–Renner relation with
`⟨ψ̄ψ⟩_GTE = −M_kink³` and `f_π = M_kink/π` (`fpi_from_scc`, CatAL).
-/

namespace UgpLean.MassRelations.PionMassFromGOR

open GTE.Spacetime.OrbitMassHierarchy
open UgpLean.QFT.ChiralSSB
open Real

noncomputable section

/-- BPS kink mass scale (SCC) as a real. -/
noncomputable def M_kink : ℝ := (mkink_scc : ℝ)

theorem M_kink_pos : 0 < M_kink := by
  unfold M_kink mkink_scc mphi_scc m_tau_pdg_eV
  norm_num

/-- GTE chiral condensate: minus the kink vacuum energy-density scale M_kink³.

    Physical content: the φ_MDL kink ground state carries characteristic energy
    density M_kink³, identified with the QCD chiral condensate magnitude in the GOR
    relation. -/
noncomputable def chiralCondensateGTE : ℝ := -M_kink ^ 3

/-- **chiral_condensate_kink_identification** (CatAL):
    |⟨ψ̄ψ⟩_GTE| = M_kink³. -/
theorem chiral_condensate_kink_identification :
    |chiralCondensateGTE| = M_kink ^ 3 := by
  simp [chiralCondensateGTE, abs_neg, M_kink_pos.le]

/-- GOR pion mass with explicit f_π and condensate magnitude:
    m_π = √((m_u+m_d) |⟨ψ̄ψ⟩| / f_π²). -/
noncomputable def gor_pion_mass_with_fpi (m_u m_d f_pi cond_mag : ℝ) : ℝ :=
  Real.sqrt ((m_u + m_d) * cond_mag / f_pi ^ 2)

/-- GTE pion mass from the closed GOR–SCC formula. -/
noncomputable def m_pi_GTE (m_u m_d : ℝ) : ℝ :=
  Real.pi * Real.sqrt ((m_u + m_d) * M_kink)

/-- GTE light-quark mass sum used for the numerical certificate (MeV):
    m_u + m_d = 6.8040 MeV from the GTE cascade (not individual PDG splits). -/
noncomputable def gte_m_ud_sum_mev : ℝ := 6.8040

/-- Rational proxy for SCC M_kink ≈ 290.10 MeV in the numerical certificate. -/
noncomputable def mkink_cert_mev : ℝ := 290.10

/-- GTE pion mass prediction at the certified MeV inputs. -/
noncomputable def m_pi_gte_cert_mev : ℝ :=
  Real.pi * Real.sqrt (gte_m_ud_sum_mev * mkink_cert_mev)

/-- **pion_mass_from_gor** (CatAL):
    GOR with ⟨ψ̄ψ⟩_GTE = −M_kink³ and f_π = M_kink/π gives
    m_π = π √((m_u+m_d) M_kink). -/
theorem pion_mass_from_gor (m_u m_d : ℝ) (hMq : 0 < m_u + m_d) :
    m_pi_GTE m_u m_d =
      gor_pion_mass_with_fpi m_u m_d ((mkink_scc : ℝ) / Real.pi) (M_kink ^ 3) := by
  unfold m_pi_GTE gor_pion_mass_with_fpi M_kink
  have hMk : 0 < (mkink_scc : ℝ) := M_kink_pos
  have hfpi : 0 < (mkink_scc : ℝ) / Real.pi := div_pos hMk Real.pi_pos
  have hden : ((mkink_scc : ℝ) / Real.pi) ^ 2 = (mkink_scc : ℝ) ^ 2 / Real.pi ^ 2 := by
    field_simp [hfpi.ne']
  have hinner :
      (m_u + m_d) * (mkink_scc : ℝ) ^ 3 / ((mkink_scc : ℝ) / Real.pi) ^ 2 =
        (m_u + m_d) * (mkink_scc : ℝ) * Real.pi ^ 2 := by
    rw [hden]
    field_simp [hMk.ne']
  rw [hinner, Real.sqrt_mul' ((m_u + m_d) * (mkink_scc : ℝ)) (sq_nonneg Real.pi),
    Real.sqrt_sq Real.pi_pos.le, mul_comm]

theorem pion_mass_from_gor_closed (m_u m_d : ℝ) (_hMq : 0 < m_u + m_d) :
    m_pi_GTE m_u m_d = Real.pi * Real.sqrt ((m_u + m_d) * M_kink) := rfl

theorem pion_mass_fpi_scc_link (m_u m_d : ℝ) (hMq : 0 < m_u + m_d) :
    m_pi_GTE m_u m_d =
      gor_pion_mass_with_fpi m_u m_d fpi_scc_eV (M_kink ^ 3) ∧
    fpi_scc_eV = M_kink / Real.pi := by
  refine ⟨?_, fpi_from_scc⟩
  unfold gor_pion_mass_with_fpi M_kink at *
  simpa [fpi_from_scc, div_eq_mul_inv] using pion_mass_from_gor m_u m_d hMq

private lemma sqrt_cert_radicand_lt : Real.sqrt (19738404 / 10000 : ℝ) < 4443 / 100 := by
  rw [← Real.sqrt_sq (by norm_num : 0 ≤ (4443 / 100 : ℝ))]
  exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)

private lemma sqrt_cert_radicand_gt : (4442 / 100 : ℝ) < Real.sqrt (19738404 / 10000 : ℝ) := by
  rw [Real.lt_sqrt (by norm_num)]
  norm_num

/-- **pion_mass_numerical_certificate** (CatAL):
    With GTE m_u+m_d = 6.8040 MeV and M_kink = 290.10 MeV,
    π√(6.8040×290.10) agrees with 139.57 MeV to within 0.1 MeV.

    Uses GTE-derived quark sum only (not individual m_u, m_d PDG values). -/
theorem pion_mass_numerical_certificate :
    |m_pi_gte_cert_mev - 139.57| < (1 / 10 : ℝ) := by
  unfold m_pi_gte_cert_mev gte_m_ud_sum_mev mkink_cert_mev
  have hprod : (6.8040 : ℝ) * 290.10 = (19738404 / 10000 : ℝ) := by norm_num
  have hsqrt_lo := sqrt_cert_radicand_gt
  have hsqrt_hi := sqrt_cert_radicand_lt
  have hpi_lo := Real.pi_gt_d6
  have hpi_hi := Real.pi_lt_d6
  have hmul_gt : (13947 / 100 : ℝ) < (3141592 / 10 ^ 6) * (4442 / 100) := by norm_num
  have hmul_lt : (3141593 / 10 ^ 6) * (4443 / 100) < (13967 / 100) := by norm_num
  have hpi_mul_lo : (3141592 / 10 ^ 6) * (4442 / 100) <
      Real.pi * Real.sqrt (19738404 / 10000 : ℝ) := by
    nlinarith [hpi_lo, hsqrt_lo]
  have hpi_mul_hi : Real.pi * Real.sqrt (19738404 / 10000 : ℝ) <
      (3141593 / 10 ^ 6) * (4443 / 100) := by
    nlinarith [hpi_hi, hsqrt_hi]
  have hlo : (13947 / 100 : ℝ) < Real.pi * Real.sqrt (19738404 / 10000) := by
    linarith [hmul_gt, hpi_mul_lo]
  have hhi : Real.pi * Real.sqrt (19738404 / 10000) < (13967 / 100) := by
    linarith [hpi_mul_hi, hmul_lt]
  have hEq : (13957 / 100 : ℝ) = 139.57 := by norm_num
  have hpad_lo : (13957 / 100 : ℝ) - (1 / 10 : ℝ) = (13947 / 100 : ℝ) := by norm_num
  have hpad_hi : (13957 / 100 : ℝ) + (1 / 10 : ℝ) = (13967 / 100 : ℝ) := by norm_num
  have h₁ : -(1 / 10 : ℝ) < Real.pi * Real.sqrt (19738404 / 10000) - 139.57 := by
    have h := hpad_lo ▸ hlo
    linarith [h, hEq]
  have h₂ : Real.pi * Real.sqrt (19738404 / 10000) - 139.57 < (1 / 10 : ℝ) := by
    have h := hpad_hi ▸ hhi
    linarith [h, hEq]
  rw [hprod, abs_sub_lt_iff]
  exact ⟨h₂, by linarith [h₁]⟩

end

end UgpLean.MassRelations.PionMassFromGOR
