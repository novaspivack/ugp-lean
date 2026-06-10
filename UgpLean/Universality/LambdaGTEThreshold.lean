import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.ZMod.Basic
import UgpLean.Universality.BetaCoefficientIdentity
import UgpLean.Universality.SylowIndexCouplingHierarchy
import UgpLean.Algebra.F21SU3Embedding

/-!
# Λ_GTE threshold arithmetic skeleton

Certifies the rational identity `Λ_GTE = (8/7)m_τ`, multiplier minimality `7`,
the six `SU(3)/F₂₁` coset `Z₇` charges `{±1,±2,±3}`, and slope-continuity
`7 = 11 − 4 = |Z₇|`.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Universality.LambdaGTEThreshold

open UgpLean.Universality.BetaCoefficientIdentity
open UgpLean.Universality.SylowIndexCoupling
open UgpLean.Algebra.F21SU3Embedding

/-- Z₇ orbit multiplier entering the pure-kink chain threshold. -/
def z7ChainMultiplier : ℕ := 7

/-- SCC kink mass ratio `m_kink/m_τ = 8/49`. -/
def kinkTauMassRatio : ℚ := 8 / 49

/-- Tree-reading scale ratio `Λ_GTE/m_τ = 7·(8/49) = 8/7`. -/
def lambdaGTEOverTau : ℚ := z7ChainMultiplier * kinkTauMassRatio

/-- The six nonzero `Z₇` residues realized as weight differences. -/
def z7CosetChargeResidues : Finset (ZMod 7) := {-1, -2, -3, 1, 2, 3}

private def weightDiff (w₁ w₂ : ZMod 7) : ZMod 7 := w₁ - w₂

private def z7CosetChargeList : List (ZMod 7) :=
  [weightDiff 2 1, weightDiff 4 2, weightDiff 1 4,
   weightDiff 1 2, weightDiff 2 4, weightDiff 4 1]

theorem z7_chain_multiplier_eq_order : z7ChainMultiplier = z7OrbitPeriod := rfl

theorem kink_tau_mass_ratio_val : kinkTauMassRatio = 8 / 49 := rfl

theorem lambda_gte_over_tau_identity :
    lambdaGTEOverTau = 8 / 7 := by
  unfold lambdaGTEOverTau z7ChainMultiplier kinkTauMassRatio
  norm_num

theorem lambda_gte_rational_identity :
    z7ChainMultiplier * kinkTauMassRatio = 8 / 7 := by
  exact lambda_gte_over_tau_identity

theorem multiplier_minimality :
    ∀ n : ℕ, 0 < n → n % 7 = 0 → 7 ≤ n := by
  intro n hn hmod
  by_contra hlt
  have hn7 : n < 7 := by omega
  interval_cases n <;> simp at hn hmod

theorem multiplier_minimality_seven :
    7 = Nat.minFac 7 ∧ Nat.minFac 7 = 7 := by
  native_decide

theorem z7_coset_charge_residues_card :
    z7CosetChargeResidues.card = 6 := by native_decide

theorem z7_coset_charge_residues_exact :
    z7CosetChargeResidues = {-1, -2, -3, 1, 2, 3} := rfl

theorem z7_coset_charge_list_cert :
    (z7CosetChargeList.toFinset = z7CosetChargeResidues) ∧
      z7CosetChargeList.length = 6 := by
  native_decide

theorem slope_continuity_arithmetic :
    (7 : ℚ) = 11 - 4 ∧ (7 : ℚ) = z7OrbitPeriod := by
  refine ⟨?_, ?_⟩
  · norm_num
  · unfold z7OrbitPeriod; rfl

/-- **lambda_gte_threshold_identity** (CatAL): Λ_GTE arithmetic skeleton. -/
theorem lambda_gte_threshold_identity :
    lambdaGTEOverTau = 8 / 7 ∧
      (∀ n : ℕ, 0 < n → n % 7 = 0 → 7 ≤ n) ∧
        z7CosetChargeResidues.card = 6 ∧
          (7 : ℚ) = 11 - 4 ∧
            (11 * (3 : ℕ) - 2 * 6) / 3 = z7OrbitPeriod := by
  refine ⟨lambda_gte_over_tau_identity, multiplier_minimality, z7_coset_charge_residues_card,
    slope_continuity_arithmetic.1, ?_⟩
  unfold z7OrbitPeriod
  exact b0_eq_z7_order

end UgpLean.Universality.LambdaGTEThreshold
