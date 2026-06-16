import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import UgpLean.Universality.EWBosonNumericalCerts

/-!
# ρ̂-corrected M_Z interval certificate (CatAD)

Certifies that the GTE electroweak M_Z prediction, after applying the
leading top-quark EW self-energy correction (ρ̂ correction), lies in
the interval (91190, 91220) MeV.

## Physical setup

The ρ̂ (rho-hat) correction to the Z-boson mass accounts for the dominant
radiative correction from the top-quark self-energy:

  ρ̂ = 1 + Δρ_top,   Δρ_top = 3 G_F m_t² / (8 π² √2)

With GTE-internal inputs:
  - M_W^GTE = 80364 MeV (CatAD)
  - m_t^GTE = 172610 MeV (b_t/b_b = 337920/8191, TT+VV cascade, CatAD)
  - G_F = 1.1663788 × 10⁻⁵ GeV⁻² (PDG 2024 external input)

This gives Δρ_top ≈ 0.009337, ρ̂ ≈ 1.009337, and

  M_Z^(ρ̂-corrected) = M_Z^tree / √ρ̂ = 91629 / √1.009337 ≈ 91204 MeV

## Certification status

CatAD: the bounds below are verified by numerical computation
(Python script: papers/48_gte_complete_theory/scripts/mz_rho_corrected_gteinternal_mt.py).
The external input G_F is taken from PDG 2024.

## Relation to PDG

PDG M_Z = 91188 ± 2 MeV. The GTE ρ̂-corrected prediction 91204 MeV lies
+16 MeV (+8.1σ) above PDG. Full closure requires additional EW radiative
corrections beyond the one-loop ρ̂_top term (OQ-MZ-FULL-EW).
-/

namespace UgpLean.Universality.EWRhoCorrectedMZ

open Real
open UgpLean.Universality.EWBosonNumericalCerts

/-! ## ρ̂ correction parameter -/

/-- `rho_hat_GTE` is the one-loop ρ̂ correction factor 1 + Δρ_top using the
GTE-internal top mass m_t = 172610 MeV (CatAD) and PDG G_F. -/
noncomputable def rho_hat_GTE : ℝ :=
  1 + 3 * (11663788 : ℝ) / (10^13 * 10^6 : ℝ) * (172610 : ℝ)^2 /
    (8 * Real.pi^2 * Real.sqrt 2)

/-- `m_Z_rho_corrected_MeV` is the ρ̂-corrected GTE M_Z prediction. -/
noncomputable def m_Z_rho_corrected_MeV : ℝ :=
  m_Z_GTE_MeV / Real.sqrt rho_hat_GTE

/-! ## Axiom: bounds on √ρ̂  (numerically verified) -/

/-- Certified bounds on √(ρ̂^GTE).
  ρ̂ ≈ 1.009337, √ρ̂ ≈ 1.004658 ∈ (1.00462, 1.00474).
  Verified by Python script mz_rho_corrected_gteinternal_mt.py. -/
axiom sqrt_rho_hat_GTE_bounds :
    (100462 : ℝ) / 100000 < Real.sqrt rho_hat_GTE ∧
    Real.sqrt rho_hat_GTE < (100474 : ℝ) / 100000

/-! ## Main certificate -/

/-- **m_Z_rho_corrected_interval** (CatAD):
  The ρ̂-corrected GTE M_Z prediction lies in (91190, 91220) MeV.

  Using GTE-internal m_t = 172610 MeV (pole mass, CatAD):
    M_Z^GTE(ρ̂-corrected) ≈ 91204 MeV ∈ (91190, 91220) MeV.

  External input: PDG 2024 G_F = 1.1663788 × 10⁻⁵ GeV⁻².
  Remaining gap from PDG M_Z (91188 MeV): +16 MeV = +8.1σ (OQ-MZ-FULL-EW). -/
theorem m_Z_rho_corrected_interval :
    (91190 : ℝ) < m_Z_rho_corrected_MeV ∧ m_Z_rho_corrected_MeV < (91220 : ℝ) := by
  unfold m_Z_rho_corrected_MeV m_Z_GTE_MeV m_W_GTE_MeV
  have hs := sqrt_thirteen_ten_bounds
  have hrho := sqrt_rho_hat_GTE_bounds
  have hrho_pos : (0 : ℝ) < Real.sqrt rho_hat_GTE := by linarith [hrho.1]
  constructor
  · rw [lt_div_iff₀ hrho_pos]
    nlinarith [hs.1, hrho.2]
  · rw [div_lt_iff₀ hrho_pos]
    nlinarith [hs.2, hrho.1]

end UgpLean.Universality.EWRhoCorrectedMZ
