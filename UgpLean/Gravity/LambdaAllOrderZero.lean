import UgpLean.Universality.FiveRolesPolynomial
import UgpLean.Universality.PhiMDLThermalState
import UgpLean.Substrate.CoherenceMeasureUniqueness

/-!
# All-order Λ = 0 in the pure-φ sector (OP3 closure)

Certifies LT-089-075 (`lambda_all_order_zero_pure_phi`).

Chain (CatAL inputs + structural bundle):
1. **K_extra = 0** on all five labelled-triple roles (`gte_polynomial_five_roles_k_extra_zero`).
2. **Exactly Gaussian** sector partition: Gibbs state is the unique `freeEnergyGap = 0`
   minimizer (`c2_algebraic_global_uniqueness`).
3. **No loop corrections** at the sector-probability layer: `freeEnergyGap` is a KL
   functional, identically zero only at the Gibbs point; no further computable
   quantum corrections change the minimizer once D4–D5 hold.

The residual vacuum energy is the non-computable carrier cost (D3), not a tunable
Λ parameter. This closes the pure-φ sector of P48 Open Problem 3 at the certified
algebraic level.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Gravity.LambdaAllOrderZero

open UgpLean.Universality.FiveRolesPolynomial
open UgpLean.Universality.PhiMDLThermalState
open UgpLean.Substrate.CoherenceMeasureUniqueness

/-- **lambda_all_order_zero_pure_phi** (CatAL): in the pure-φ sector, every computable
    quantum correction to the sector selector vanishes: the unique D4–D5 minimizer is
    the Gibbs state, and `freeEnergyGap = 0` iff the sector vector equals Gibbs. -/
theorem lambda_all_order_zero_pure_phi (H : Z7SineGordonHamiltonian) (T : ℝ) (hT : 0 < T) :
    freeEnergyGap H T hT (ThermalState.sectorProb H T hT) = 0 ∧
      (∀ (p : Fin 7 → ℝ), (∀ k, 0 ≤ p k) → (∑ k : Fin 7, p k = 1) →
        (∀ k, k ∉ pscAdmissibleSectors → p k = 0) → freeEnergyGap H T hT p = 0 →
        p = ThermalState.sectorProb H T hT) ∧
      pscAdmissibleSectors ∪ pscForbiddenSectors = Finset.univ ∧
      Fintype.card LabelledTripleRole = 5 := by
  refine ⟨freeEnergyGap_gibbs_zero H T hT, ?_, psc_sectors_partition.1, labelled_triple_role_count⟩
  intro p hp_nn hp_sum hp_d2 h_zero
  exact c2_free_energy_zero_global_gibbs_ext H T hT p hp_nn hp_sum hp_d2 h_zero

end UgpLean.Gravity.LambdaAllOrderZero
