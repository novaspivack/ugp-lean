import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.ExpDeriv
import Mathlib.Analysis.Complex.Exponential
import Mathlib.NumberTheory.Harmonic.EulerMascheroni
import UgpLean.Universality.BetaCoefficientIdentity
import UgpLean.Universality.SylowIndexCouplingHierarchy

/-!
# Kink vacuum-polarization algebraic core

Certifies the Cartan charge sum `t_kink = 3`, the abelian beta coefficient
`b̂ = −4` matching the CatAL slope-continuity identity `7 = 11 − 4`, the
tree-reading instance `c^{S1,tree} = 8 ln(8/7)`, and the sign-positivity
criterion `m_φ < e^{γ/2} · Λ_GTE` on the tree ratio `Λ_GTE/m_φ = 8/7`.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Physics.KinkVacuumPolarization

open Real
open UgpLean.Universality.BetaCoefficientIdentity
open UgpLean.Universality.SylowIndexCoupling

noncomputable section

/-- Cartan generator `H_A = (−T³ + √3·T⁸)/2` eigenvalues on the SU(3) fundamental. -/
def cartanHAWeight0 : ℚ := 0
def cartanHAWeight1 : ℚ := 1 / 2
def cartanHAWeight2 : ℚ := -1 / 2

/-- Sum of squared Cartan charges per Dirac flavor in the fundamental. -/
def cartanChargeSquaredSumPerFlavor : ℚ :=
  cartanHAWeight0 ^ 2 + cartanHAWeight1 ^ 2 + cartanHAWeight2 ^ 2

/-- Kink species count: six Dirac flavors in the SU(3) fundamental (CatAL `b₀` continuity). -/
def kinkDiracFlavorCount : ℕ := 6

/-- Total squared Cartan charge entering the abelian kink vacuum polarization. -/
def tKink : ℚ := kinkDiracFlavorCount * cartanChargeSquaredSumPerFlavor

/-- Abelian kink beta coefficient `b̂ = −(4/3)·t_kink`. -/
def bHatKink : ℚ := -(4 : ℚ) / 3 * tKink

/-- Tree-reading GTE scale ratio `Λ_GTE / m_φ = 8/7` (SCC identification). -/
def lambdaGTEOverMphiTree : ℝ := (8 : ℝ) / 7

/-- Primary S1 Pauli–Villars instance `c^{S1,tree} = 8 ln(Λ_GTE/m_φ)`. -/
def cKinkS1Tree : ℝ := 8 * log lambdaGTEOverMphiTree

-- ─────────────────────────────────────────────────────────────────────────
-- Cartan charge sum
-- ─────────────────────────────────────────────────────────────────────────

theorem cartan_ha_weights :
    cartanHAWeight0 = 0 ∧
      cartanHAWeight1 = 1 / 2 ∧
        cartanHAWeight2 = -1 / 2 := by
  norm_num [cartanHAWeight0, cartanHAWeight1, cartanHAWeight2]

theorem cartan_charge_squared_sum_per_flavor :
    cartanChargeSquaredSumPerFlavor = 1 / 2 := by
  unfold cartanChargeSquaredSumPerFlavor cartanHAWeight0 cartanHAWeight1 cartanHAWeight2
  norm_num

/-- **kink_cartan_charge_trepresentation** (CatAL): six fundamental flavors with
    `H_A` weights `{0, ±1/2}` give `t_kink = 3`. -/
theorem kink_cartan_charge_trepresentation :
    tKink = 3 ∧
      cartanChargeSquaredSumPerFlavor = 1 / 2 ∧
        kinkDiracFlavorCount = 6 := by
  unfold tKink kinkDiracFlavorCount
  exact ⟨by
    rw [cartan_charge_squared_sum_per_flavor]
    norm_num, cartan_charge_squared_sum_per_flavor, rfl⟩

-- ─────────────────────────────────────────────────────────────────────────
-- slope-continuity identity
-- ─────────────────────────────────────────────────────────────────────────

theorem b_hat_kink_eq_neg_four : bHatKink = -4 := by
  unfold bHatKink tKink kinkDiracFlavorCount
  rw [cartan_charge_squared_sum_per_flavor]
  norm_num

theorem b0_minus_eleven_eq_neg_four : (7 : ℚ) - 11 = -4 := by norm_num

/-- **b_hat_continuity_identity** (CatAL): `b̂ = −4 = 7 − 11`, matching the certified
    one-loop coefficient `b₀ = |Z₇| = 7` (`b0_eq_z7_order`) against the naive EFT value
    `11 − 4`. -/
theorem b_hat_continuity_identity :
    bHatKink = -4 ∧
      bHatKink = (7 : ℚ) - 11 ∧
        (11 * (3 : ℕ) - 2 * 6) / 3 = 7 := by
  refine ⟨b_hat_kink_eq_neg_four, ?_, ?_⟩
  · rw [b_hat_kink_eq_neg_four, b0_minus_eleven_eq_neg_four]
  · exact b0_eq_z7_order

-- ─────────────────────────────────────────────────────────────────────────
-- tree S1 rational-log instance
-- ─────────────────────────────────────────────────────────────────────────

theorem lambda_gte_over_mphi_tree_pos : 0 < lambdaGTEOverMphiTree := by
  unfold lambdaGTEOverMphiTree
  norm_num

theorem lambda_gte_over_mphi_tree_gt_one : (1 : ℝ) < lambdaGTEOverMphiTree := by
  unfold lambdaGTEOverMphiTree
  norm_num

/-- **c_kink_s1tree_rational_log** (CatAL): at the tree reading `Λ_GTE/m_φ = 8/7`,
    the primary S1 scheme constant is `c^{S1,tree} = 8 ln(8/7)`. -/
theorem c_kink_s1tree_rational_log :
    cKinkS1Tree = 8 * log ((8 : ℝ) / 7) ∧
      cKinkS1Tree = 8 * log lambdaGTEOverMphiTree := by
  unfold cKinkS1Tree lambdaGTEOverMphiTree
  exact ⟨rfl, rfl⟩

-- ─────────────────────────────────────────────────────────────────────────
-- sign-positivity inequality
-- ─────────────────────────────────────────────────────────────────────────

theorem euler_gamma_pos : 0 < eulerMascheroniConstant :=
  lt_trans (by norm_num : (0 : ℝ) < 1 / 2) one_half_lt_eulerMascheroniConstant

theorem exp_half_gamma_pos : 0 < exp (eulerMascheroniConstant / 2) :=
  exp_pos _

theorem exp_half_gamma_gt_one : (1 : ℝ) < exp (eulerMascheroniConstant / 2) :=
  (one_lt_exp_iff).2 (div_pos euler_gamma_pos (by norm_num))

theorem eight_sevenths_mul_exp_half_gamma_gt_one :
    (1 : ℝ) < (8 / 7) * exp (eulerMascheroniConstant / 2) := by
  have h8 : (1 : ℝ) < 8 / 7 := by norm_num
  have hexp := exp_half_gamma_gt_one
  have hpos : (0 : ℝ) < exp (eulerMascheroniConstant / 2) := exp_pos _
  nlinarith

/-- **kink_positivity_inequality** (CatAL): on the tree reading `Λ_GTE = (8/7)m_φ`,
    the L2 sign criterion `m_φ < e^{γ/2} · Λ_GTE` holds. -/
theorem kink_positivity_inequality (m_phi Lambda : ℝ) (hm : 0 < m_phi)
    (hL : Lambda = lambdaGTEOverMphiTree * m_phi) :
    m_phi < exp (eulerMascheroniConstant / 2) * Lambda := by
  rw [hL]
  have h := eight_sevenths_mul_exp_half_gamma_gt_one
  calc
    m_phi = 1 * m_phi := by ring
    _ < ((8 / 7) * exp (eulerMascheroniConstant / 2)) * m_phi := by
      exact mul_lt_mul_of_pos_right h hm
    _ = exp (eulerMascheroniConstant / 2) * (lambdaGTEOverMphiTree * m_phi) := by
      unfold lambdaGTEOverMphiTree
      ring

/-- Bundle of the four kink vacuum-polarization certificates. -/
theorem kink_vacuum_polarization_algebraic_core :
    tKink = 3 ∧
      bHatKink = -4 ∧
        cKinkS1Tree = 8 * log ((8 : ℝ) / 7) ∧
          (∀ m_phi Lambda : ℝ, 0 < m_phi → Lambda = lambdaGTEOverMphiTree * m_phi →
            m_phi < exp (eulerMascheroniConstant / 2) * Lambda) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · exact kink_cartan_charge_trepresentation.1
  · exact b_hat_continuity_identity.1
  · exact c_kink_s1tree_rational_log.1
  · intro m_phi Lambda hm hL
    exact kink_positivity_inequality m_phi Lambda hm hL

end

end UgpLean.Physics.KinkVacuumPolarization
