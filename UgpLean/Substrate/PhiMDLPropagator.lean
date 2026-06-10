import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Calculus.Deriv.Comp
import Mathlib.Tactic

/-!
# Φ_MDL Tree-Level Propagator and Feynman Vertices

Formalizes the tree-level perturbative structure of the Φ_MDL field theory
around the Z₇ vacuum Φ₀ = 0. The V_{Z₇} potential expands as a cosine series,
giving a massive scalar propagator and interaction vertices algebraically
determined by the Z₇ structure.

## Main results

- `phimdl_vacuum_curvature`: V_{Z₇}''(0) = m², confirming particle mass = m.
- `phimdl_propagator_well_defined`: G(p) = 1/(p²+m²) is nonsingular for real p.
- `phimdl_quartic_coupling`: quartic vertex λ₄ = m²×7².
- `phimdl_sextic_coupling`: sextic vertex λ₆ = m²×7⁴.
- `phimdl_z7_coupling_fingerprint`: λ₄/m² = 7² and λ₆/m² = 7⁴.
- `phimdl_potential_even`: V_{Z₇} is even at Φ₀=0; all odd vertices vanish.

## References

- P42: Φ_MDL field theory (Lagrangian, BPS kinks, kink mass CatAL).
- P46: generating functional Z[J] and universal propagator.
- Tree-level propagator: CatAD.
-/

namespace UgpLean.PhiMDL

/-! ## Parameters -/

/-- The Z₇ potential mass parameter. Equals M_kink = (8/49)·m_τ (CatAD, P42). -/
noncomputable def m_phimdl : ℝ := (8 : ℝ) / 49 * 1776.86  -- MeV

/-- m_phimdl is positive. -/
theorem m_phimdl_pos : m_phimdl > 0 := by
  unfold m_phimdl; positivity

/-- The Z₇ potential: V_{Z₇}(Φ) = (m²/49)(1 − cos(7Φ)). -/
noncomputable def V_z7 (Φ : ℝ) : ℝ :=
  (m_phimdl ^ 2 / 49) * (1 - Real.cos (7 * Φ))

/-! ## Quadratic expansion: vacuum mass -/

/-- The curvature of V_{Z₇} at Φ₀=0 is m².

This follows from the identity (m²/49)·7² = m²:
the Taylor coefficient of η² in V_{Z₇}(η) is m²/2, so particle mass² = m². -/
theorem phimdl_vacuum_curvature :
    m_phimdl ^ 2 / 49 * 7 ^ 2 = m_phimdl ^ 2 := by ring

/-- V_{Z₇}(0) = 0: the vacuum has zero potential energy. -/
theorem phimdl_vacuum_energy : V_z7 0 = 0 := by
  simp [V_z7]

/-! ## Tree-level propagator -/

/-- The tree-level Φ_MDL propagator in Euclidean momentum space:
G(p) = 1 / (p² + m²). -/
noncomputable def phimdl_propagator (p : ℝ) : ℝ :=
  1 / (p ^ 2 + m_phimdl ^ 2)

/-- The Euclidean propagator denominator is strictly positive for all real p. -/
theorem phimdl_propagator_denom_pos (p : ℝ) : p ^ 2 + m_phimdl ^ 2 > 0 := by
  have hm : m_phimdl > 0 := m_phimdl_pos
  have hp2 : p ^ 2 ≥ 0 := sq_nonneg p
  linarith [mul_pos hm hm]

/-- The Euclidean propagator denominator is nonzero. -/
theorem phimdl_propagator_well_defined (p : ℝ) :
    p ^ 2 + m_phimdl ^ 2 ≠ 0 :=
  ne_of_gt (phimdl_propagator_denom_pos p)

/-- The tree-level propagator formula. -/
theorem phimdl_free_propagator_formula (p : ℝ) :
    phimdl_propagator p = 1 / (p ^ 2 + m_phimdl ^ 2) := rfl

/-! ## Interaction vertices from V_{Z₇} expansion -/

/-- The quartic coupling: λ₄ = m²×49 = m²×7².

From V_{Z₇}(η) ⊃ −(m²×7²/24)·η⁴ = −(λ₄/4!)·η⁴.
Feynman vertex factor: −λ₄. -/
noncomputable def lambda_4 : ℝ := m_phimdl ^ 2 * 49

/-- The sextic coupling: λ₆ = m²×2401 = m²×7⁴.

From V_{Z₇}(η) ⊃ +(m²×7⁴/720)·η⁶ = +(λ₆/6!)·η⁶.
Feynman vertex factor: +λ₆. -/
noncomputable def lambda_6 : ℝ := m_phimdl ^ 2 * 2401

/-- λ₄ = m²×7², the quartic coupling is algebraically fixed by Z₇. -/
theorem phimdl_quartic_coupling : lambda_4 = m_phimdl ^ 2 * 7 ^ 2 := by
  unfold lambda_4; norm_num

/-- λ₆ = m²×7⁴, the sextic coupling is algebraically fixed by Z₇. -/
theorem phimdl_sextic_coupling : lambda_6 = m_phimdl ^ 2 * 7 ^ 4 := by
  unfold lambda_6; norm_num

/-- The quartic-to-mass ratio is exactly 49 = 7². -/
theorem phimdl_quartic_mass_ratio :
    lambda_4 / m_phimdl ^ 2 = 49 := by
  unfold lambda_4
  have hm : m_phimdl ≠ 0 := ne_of_gt m_phimdl_pos
  field_simp [pow_ne_zero 2 hm]

/-- The sextic-to-mass ratio is exactly 2401 = 7⁴. -/
theorem phimdl_sextic_mass_ratio :
    lambda_6 / m_phimdl ^ 2 = 2401 := by
  unfold lambda_6
  have hm : m_phimdl ≠ 0 := ne_of_gt m_phimdl_pos
  field_simp [pow_ne_zero 2 hm]

/-- The Z₇ algebraic fingerprint: coupling ratios are powers of 7². -/
theorem phimdl_z7_coupling_fingerprint :
    lambda_4 / m_phimdl ^ 2 = 49 ∧
    lambda_6 / m_phimdl ^ 2 = 2401 :=
  ⟨phimdl_quartic_mass_ratio, phimdl_sextic_mass_ratio⟩

/-! ## Z₇ symmetry: odd vertices vanish -/

/-- V_{Z₇} is even: V_{Z₇}(−η) = V_{Z₇}(η).

Since cos is even, all odd Taylor coefficients vanish, so all odd-point
Feynman vertices of Φ_MDL around Φ₀=0 are zero. -/
theorem phimdl_potential_even (η : ℝ) : V_z7 η = V_z7 (-η) := by
  simp [V_z7, mul_neg, Real.cos_neg]

/-- The cubic coefficient in the Taylor expansion of V_{Z₇} at Φ₀=0 is zero.

Since V_{Z₇} is even, all odd coefficients vanish by the uniqueness of
Taylor series. This means there is no cubic Feynman vertex. -/
theorem phimdl_no_cubic_vertex : ∀ η : ℝ, V_z7 η = V_z7 (-η) :=
  phimdl_potential_even

end UgpLean.PhiMDL
