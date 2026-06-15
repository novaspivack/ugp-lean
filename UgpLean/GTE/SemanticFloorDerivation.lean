import Mathlib
import UgpLean.Core.SievePredicates
import UgpLean.Core.TripleDefs
import UgpLean.GTE.UpdateMap
import UgpLean.MassRelations.KoideS3DiscreteIdentities

/-!
# UgpLean.GTE.SemanticFloorDerivation — GT-003

The a-values `{1, 5, 9}` in `SemanticFloor` are the a-orbit projection of the
GTE cascade at ridge `n = 10`. They are not independently specified; they are the
output of the cascade formula `a' = m − (n+2−t)` applied to the Lepton Seed.

Derivation chain:
- `a₂ = 9 = oddStepA 20 10 1`  (CatAL: `odd_step_a2`)
- `a₃ = 5 = evenStepA 15 10 2` (CatAL: `even_step_a3`)
- `a₁ = 1`: sum constraint `a₁ + a₂ = n = 10` (CatAL: `lepton_a_sum_eq_ten`) with a₂=9

All three values are consequences of the cascade arithmetic. The set `{1, 5, 9}`
is exactly the orbit a-projection of the Lepton Seed at ridge `n = 10`.

Reference: GT-003, EPIC_091; UpdateMap.lean §4; KoideS3DiscreteIdentities.lean.
-/

namespace UgpLean.GT003

open UgpLean
open UgpLean.MassRelations.KoideS3DiscreteIdentities

-- ════════════════════════════════════════════════════════════════
-- §1 Cascade formula values
-- ════════════════════════════════════════════════════════════════

/-- The odd-step a-update at the Lepton Seed: a' = m₁ − (n+2−1) = 20 − 11 = 9. -/
theorem a2_from_odd_step_formula : oddStepA 20 10 1 = 9 := by native_decide

/-- The even-step a-update at the Lepton Seed: a' = m₂ − (n+2−2) = 15 − 10 = 5. -/
theorem a3_from_even_step_formula : evenStepA 15 10 2 = 5 := by native_decide

/-- The orbit a-projection set is exactly {1, oddStepA 20 10 1, evenStepA 15 10 2}
    = {1, 9, 5} = {1, 5, 9} as a Finset. -/
theorem orbit_a_projection_eq_semantic_floor_set :
    ({1, oddStepA 20 10 1, evenStepA 15 10 2} : Finset ℕ) =
    ({1, 5, 9} : Finset ℕ) := by native_decide

-- ════════════════════════════════════════════════════════════════
-- §2 The SemanticFloor a-set equals the orbit projection
-- ════════════════════════════════════════════════════════════════

/-- The SemanticFloor a-set {1, 5, 9} equals the set of GTE generation a-components. -/
theorem semantic_floor_a_set_eq_gen_components :
    ({1, 5, 9} : Finset ℕ) =
    ({LeptonSeed.a, canonicalGen2.a, canonicalGen3.a} : Finset ℕ) := by
  native_decide

/-- a₁ = 1 is derivable: it is uniquely forced by the sum constraint a₁ + a₂ = n=10
    together with the cascade-derived value a₂ = 9. -/
theorem a1_from_cascade_sum_constraint :
    LeptonSeed.a = 10 - canonicalGen2.a := by
  have h := lepton_a_sum_eq_ten
  omega

-- ════════════════════════════════════════════════════════════════
-- §3 Membership characterisation
-- ════════════════════════════════════════════════════════════════

/-- Membership in the SemanticFloor a-set is equivalent to being one of the three
    orbit a-values produced by the cascade formula at n=10. -/
theorem semantic_floor_a_membership_iff_orbit (a : ℕ) :
    a ∈ ({1, 5, 9} : Finset ℕ) ↔
    a = 1 ∨ a = oddStepA 20 10 1 ∨ a = evenStepA 15 10 2 := by
  -- oddStepA 20 10 1 = 9; evenStepA 15 10 2 = 5 (both by native_decide)
  have h9 : oddStepA 20 10 1 = 9 := by native_decide
  have h5 : evenStepA 15 10 2 = 5 := by native_decide
  rw [h9, h5]
  simp only [Finset.mem_insert, Finset.mem_singleton]
  tauto

/-- Any triple satisfying SemanticFloor has its a-component in the orbit projection
    of the GTE cascade at n=10. -/
theorem semantic_floor_a_in_orbit_projection (t : Triple) (h : SemanticFloor t) :
    t.a = LeptonSeed.a ∨ t.a = canonicalGen2.a ∨ t.a = canonicalGen3.a := by
  obtain ⟨ha, _, _⟩ := h
  simp only [Finset.mem_insert, Finset.mem_singleton] at ha
  have hvals : LeptonSeed.a = 1 ∧ canonicalGen2.a = 9 ∧ canonicalGen3.a = 5 :=
    lepton_a_values
  rcases ha with (h1 | h5 | h9)
  · left; omega
  · right; right; omega
  · right; left; omega

-- ════════════════════════════════════════════════════════════════
-- §4 Main derivation theorem
-- ════════════════════════════════════════════════════════════════

/-- The SemanticFloor a-floor set `{1, 5, 9}` is the orbit a-projection of the
    GTE cascade applied to the Lepton Seed at ridge n=10:

    - `a₂ = canonicalGen2.a = 9 = oddStepA 20 10 1`  (cascade formula, CatAL)
    - `a₃ = canonicalGen3.a = 5 = evenStepA 15 10 2`  (cascade formula, CatAL)
    - `a₁ = LeptonSeed.a = 1 = n − a₂`  (sum constraint, CatAL)

    The set is not postulated; it is the output of the parity-phase formula
    `a' = m − (n+2−t)` at the two orbit steps from the Lepton Seed. -/
theorem semantic_floor_a_condition_from_cascade :
    -- 1. The hardcoded set equals the cascade orbit projection
    ({1, 5, 9} : Finset ℕ) =
    ({1, oddStepA 20 10 1, evenStepA 15 10 2} : Finset ℕ) ∧
    -- 2. The three a-values are the GTE generation a-components
    LeptonSeed.a = 1 ∧ canonicalGen2.a = 9 ∧ canonicalGen3.a = 5 ∧
    -- 3. a₁ is not free: forced by sum constraint a₁ + a₂ = n
    LeptonSeed.a + canonicalGen2.a = 10 ∧
    -- 4. a₃ is the arithmetic mean of a₁ and a₂
    2 * canonicalGen3.a = LeptonSeed.a + canonicalGen2.a := by
  refine ⟨?_, lepton_a_values.1, lepton_a_values.2.1, lepton_a_values.2.2,
          lepton_a_sum_eq_ten, lepton_a_arithmetic_mean⟩
  native_decide

end UgpLean.GT003
