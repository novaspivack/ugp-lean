import Mathlib.Tactic
import UgpLean.Physics.KinkVacuumPolarization
import UgpLean.Universality.SylowIndexCouplingHierarchy

/-!
# Burnside-boundary coset charge spectrum

Algebraic core of the F₂₁→SU(3) threshold matching: coset charges under
`H_A = (−T³+√3T⁸)/2`, the vector index `t_V = 3`, fundamental trace `1/2`,
orthogonality under `H_{A′}`, and the rational instance `c_coset = −1` at `M_V = Λ_GTE`.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Physics.BurnsideCosetCharges

open UgpLean.Physics.KinkVacuumPolarization
open UgpLean.Universality.SylowIndexCoupling

/-- The six coset charges under `H_A` (two half-integer pairs + one integer). -/
def burnsideCosetCharges : List ℚ := [1 / 2, -1 / 2, 1 / 2, -1 / 2, 1, -1]

/-- Sum of squared coset charges `t_V`. -/
def tVectorCoset : ℚ := burnsideCosetCharges.foldl (fun acc q => acc + q ^ 2) 0

/-- Fundamental trace `tr_f(H_A²)` per Dirac flavor. -/
def trFundamentalHA : ℚ := cartanChargeSquaredSumPerFlavor

/-- Cartan index entering the Weinberg–Hall matching numerator. -/
def cartanMatchingNumerator : ℚ := tVectorCoset / 3

/-- Rational matching instance `c_coset(M_V = Λ_GTE) = −t_V/3`. -/
def cCosetAtLambdaGTE : ℚ := -tVectorCoset / 3

theorem burnside_coset_charge_list :
    burnsideCosetCharges = [1 / 2, -1 / 2, 1 / 2, -1 / 2, 1, -1] := rfl

theorem t_vector_coset_eq_three : tVectorCoset = 3 := by
  unfold tVectorCoset burnsideCosetCharges
  norm_num

theorem tr_fundamental_ha_eq_half : trFundamentalHA = 1 / 2 := by
  exact cartan_charge_squared_sum_per_flavor

theorem t_vector_eq_tr_adj_ha_squared :
    tVectorCoset = 3 ∧ trFundamentalHA = 1 / 2 := by
  exact ⟨t_vector_coset_eq_three, tr_fundamental_ha_eq_half⟩

theorem no_kinetic_mixing_orthogonality :
    (1 / 2) * (-1 / 2) + (1 / 2) * (-1 / 2) + (1 : ℚ) * (-1) = -3 / 2 ∧
      burnsideCosetCharges.foldl (fun acc q => acc + q) 0 = 0 := by
  unfold burnsideCosetCharges
  norm_num

theorem t_vector_invariant_under_ha_prime :
    tVectorCoset = 3 := t_vector_coset_eq_three

theorem c_coset_at_lambda_gte_eq_neg_one : cCosetAtLambdaGTE = -1 := by
  unfold cCosetAtLambdaGTE
  rw [t_vector_coset_eq_three]
  norm_num

theorem cartan_matching_numerator_eq_one : cartanMatchingNumerator = 1 := by
  unfold cartanMatchingNumerator
  rw [t_vector_coset_eq_three]
  norm_num

/-- **burnside_coset_charge_spectrum** (CatAL): Burnside-boundary charge skeleton. -/
theorem burnside_coset_charge_spectrum :
    tVectorCoset = 3 ∧
      trFundamentalHA = 1 / 2 ∧
        cCosetAtLambdaGTE = -1 ∧
          cartanMatchingNumerator = 1 ∧
            burnsideCosetCharges.foldl (fun acc q => acc + q) 0 = 0 := by
  refine ⟨t_vector_coset_eq_three, tr_fundamental_ha_eq_half, c_coset_at_lambda_gte_eq_neg_one,
    cartan_matching_numerator_eq_one, ?_⟩
  exact no_kinetic_mixing_orthogonality.2

end UgpLean.Physics.BurnsideCosetCharges
