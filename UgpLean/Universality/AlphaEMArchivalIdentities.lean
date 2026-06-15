import Mathlib.Data.Nat.Totient
import UgpLean.Universality.AlphaEMStructuralIdentity

/-!
# Alpha EM archival structural identities (EPIC_092 / 092-A3)

Certifies the dual-route arithmetic connecting b₁ = 73 to |Z₇| = φ(7) = 6 and the
equivalence of the two historical routes to 1/α_em = 137, plus the primorial(7) closure.
-/

namespace UgpLean.Universality.AlphaEMArchivalIdentities

open AlphaEMStructuralIdentity

/-- b₁ = 2^(φ(7)) + N_gen² = 2^6 + 9 = 73. -/
theorem b1_totient7_ngen_identity : (73 : ℕ) = 2 ^ Nat.totient 7 + 3 ^ 2 := by decide

/-- The two historical routes to 1/α_em = 137 agree: 2×b₁ − N_gen² = 2^|Z₇| + N_gen². -/
theorem alpha_inv_routes_equivalent : 2 * 73 - 9 = 2 ^ 7 + 9 := by decide

/-- primorial(7) = b₁ + 1/α_em = 73 + 137 = 210. -/
theorem primorial7_eq_b1_plus_alpha_inv : 2 * 3 * 5 * 7 = (73 : ℕ) + 137 := by decide

/-- Bundle linking the totient identity to the certified current α route. -/
theorem alpha_archival_identities_bundle :
    (73 : ℕ) = 2 ^ Nat.totient 7 + 3 ^ 2 ∧
    2 * 73 - 9 = 2 ^ 7 + 9 ∧
    2 * 3 * 5 * 7 = 73 + 137 ∧
    2 ^ 7 + 3 ^ 2 = 137 := by
  refine ⟨b1_totient7_ngen_identity, alpha_inv_routes_equivalent, primorial7_eq_b1_plus_alpha_inv,
    alpha_em_inverse_structural_identity⟩

end UgpLean.Universality.AlphaEMArchivalIdentities
