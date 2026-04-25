import Mathlib
import UgpLean.MassRelations.KoideAngle

/-!
# UgpLean.MassRelations.ScaleTransport — UGP as UV Boundary Condition

Formalizes the abstract scale transport from UGP bare masses to physical masses.

The central insight: UGP provides UV boundary conditions (bare masses at μ₀),
while physical masses at lower scales μ are obtained via:

  m_phys(μ) = Z(μ, μ₀) · m_UGP(μ₀)

The key structural theorem: **mass ratios are Z-independent**. This formally
justifies why ratio-grade predictions (Koide Q=2/3, neutrino splitting ratio,
TT/VV log-mass relations) are the most reliable UGP predictions — the Z-factor
cancels exactly in ratios, leaving only the UGP arithmetic.

This separates:
- **Ratio-grade predictions** [T]: Z-independent, provably robust
- **Absolute-scale predictions** [A/D]: Z-dependent, require calibration
-/

namespace UgpLean.MassRelations

-- ════════════════════════════════════════════════════════════════
-- §1  The wave-function renormalization factor
-- ════════════════════════════════════════════════════════════════

/-- Abstract renormalization factor connecting UGP bare masses to physical masses.
 Z(μ, μ₀) > 0 encodes all scheme-dependent running from the UGP scale μ₀
 to the physical scale μ. Its precise value is computed by SM RGE (Spec 018);
 the structural theorems here are Z-independent. -/
structure WFRenorm where
  zFactor    : ℝ
  zFactor_pos : 0 < zFactor

/-- Transport a UGP bare mass to the physical mass at scale μ. -/
def transportMass (m_ugp : ℝ) (Z : WFRenorm) : ℝ :=
  Z.zFactor * m_ugp

/-- A UGP mass value is always transported to a positive value when m_ugp > 0. -/
theorem transportMass_pos (m_ugp : ℝ) (hm : 0 < m_ugp) (Z : WFRenorm) :
    0 < transportMass m_ugp Z := by
  unfold transportMass
  exact mul_pos Z.zFactor_pos hm

-- ════════════════════════════════════════════════════════════════
-- §2  The key theorem: mass ratios are Z-independent
-- ════════════════════════════════════════════════════════════════

/-- **The Z-Independence Theorem**: mass ratios are preserved under transport.

 If m₁ and m₂ both undergo the same renormalization Z, their ratio is unchanged:
   m₁_phys / m₂_phys = (Z · m₁) / (Z · m₂) = m₁ / m₂.

 This is the formal justification for why Koide (Q = 2/3 for any θ),
 TT/VV log-mass relations, and the neutrino splitting ratio are the
 programme's most robust predictions — they are pure ratios, Z-independent. -/
theorem mass_ratio_Z_independent (m1 m2 : ℝ) (Z : WFRenorm)
    (hm2 : m2 ≠ 0) :
    transportMass m1 Z / transportMass m2 Z = m1 / m2 := by
  unfold transportMass
  have hZ : Z.zFactor ≠ 0 := ne_of_gt Z.zFactor_pos
  have hZm2 : Z.zFactor * m2 ≠ 0 := mul_ne_zero hZ hm2
  field_simp [hZ, hm2, hZm2]

/-- Log-mass differences are also Z-independent (since log(m1/m2) = log m1 - log m2). -/
theorem log_mass_diff_Z_independent (m1 m2 : ℝ) (Z : WFRenorm)
    (hm1 : 0 < m1) (hm2 : 0 < m2) :
    Real.log (transportMass m1 Z) - Real.log (transportMass m2 Z) =
    Real.log m1 - Real.log m2 := by
  unfold transportMass
  have hZ := ne_of_gt Z.zFactor_pos
  rw [Real.log_mul hZ (ne_of_gt hm1), Real.log_mul hZ (ne_of_gt hm2)]
  ring

-- ════════════════════════════════════════════════════════════════
-- §3  The claim-type taxonomy
-- ════════════════════════════════════════════════════════════════

/-- Koide ratio is Z-independent: any equality between mass ratios is
 preserved under the same renormalization factor.
 Direct consequence of mass_ratio_Z_independent. -/
theorem ratio_pred_Z_independent (m1 m2 r : ℝ) (Z : WFRenorm) (hm2 : m2 ≠ 0) :
    m1 / m2 = r ↔ transportMass m1 Z / transportMass m2 Z = r := by
  rw [mass_ratio_Z_independent m1 m2 Z hm2]

end UgpLean.MassRelations
