import Mathlib
import Mathlib.GroupTheory.SpecificGroups.Alternating
import UgpLean.Polynomial.EisensteinIdentities

/-!
# Eisenstein functor: F₂₁ at split prime 7 and A₄ at inert prime 2

The Eisenstein integer ring `ℤ[ω]` (`ω = e^{2πi/3}`) yields two finite residue
structures tied to the shared unit group `μ₃ ≅ ℤ₃`:

* **Split prime 7:** `F₂₁ ≅ ℤ₇ ⋊ ℤ₃` (`f21_eisenstein_residue_model`, CatAL).
* **Inert prime 2:** `(ℤ[ω]/(2))⁺ ≅ V₄ ≅ (ℤ/2)²` with `μ₃` acting by Frobenius;
  the semidirect product `V₄ ⋊ ℤ₃` has order 12, matching `A₄`.

All theorems: zero sorry, zero custom axioms. Finite checks use `decide` /
`native_decide` where appropriate.

Level framing: Level 1 algebraic certificate (finite group arithmetic over the
GF(4) residue additive group).
-/

namespace UgpLean.Algebra.EisensteinFunctor

open UgpLean.Polynomial.EisensteinIdentities
open Equiv.Perm

/-- Additive group model of `(ℤ[ω]/(2))⁺ ≅ GF(4)⁺ ≅ V₄`. -/
abbrev V4 := ZMod 2 × ZMod 2

def v4OneZero : V4 := (1, 0)
def v4ZeroOne : V4 := (0, 1)
def v4OneOne : V4 := (1, 1)

theorem v4_card : Fintype.card V4 = 4 := by decide

theorem v4_is_abelian (a b : V4) : a + b = b + a := add_comm a b

theorem v4_one_zero_order_two : v4OneZero + v4OneZero = (0 : V4) := by native_decide

theorem v4_elements_order_two (a : V4) : a + a = (0 : V4) := by
  rcases a with ⟨a1, a2⟩
  have ha1 : a1 + a1 = (0 : ZMod 2) := by fin_cases a1 <;> decide
  have ha2 : a2 + a2 = (0 : ZMod 2) := by fin_cases a2 <;> decide
  ext
  · exact ha1
  · exact ha2

/-- Frobenius action of `μ₃` on `V₄`: `(a,b) ↦ (b,a+b)` at generator `1`. -/
def z3_action_on_v4 : ZMod 3 → V4 → V4 := fun n v =>
  if n = 1 then (v.2, v.1 + v.2)
  else if n = 2 then (v.1 + v.2, v.1)
  else v

theorem z3_orbits_nonzero_v4_elements :
    (z3_action_on_v4 1 v4OneZero = v4ZeroOne) ∧
    (z3_action_on_v4 1 v4ZeroOne = v4OneOne) ∧
    (z3_action_on_v4 1 v4OneOne = v4OneZero) := by decide

theorem v4_sdp_z3_order : Fintype.card (V4 × ZMod 3) = 12 := by decide

theorem alternating_group_four_card :
    Fintype.card (alternatingGroup (Fin 4)) = 12 := by native_decide

/-- **eisenstein_a4_from_inert_2** (CatAL):
    At inert prime 2, the Eisenstein residue additive group is order-4 with
    exponent 2, `μ₃` acts by the GF(4) Frobenius on the three non-identity
    elements, and the resulting `V₄ ⋊ ℤ₃` candidate has order 12 = |A₄|. -/
theorem eisenstein_a4_from_inert_2 :
    (Fintype.card V4 = 4) ∧
    (z3_action_on_v4 1 v4OneZero = v4ZeroOne) ∧
    (Fintype.card (V4 × ZMod 3) = 12) ∧
    ((Fintype.card (alternatingGroup (Fin 4)) = 12) ∧
      (v4OneZero + v4OneZero = (0 : V4))) := by
  refine And.intro v4_card <|
    And.intro z3_orbits_nonzero_v4_elements.1 <|
      And.intro v4_sdp_z3_order <|
        And.intro alternating_group_four_card v4_one_zero_order_two

end UgpLean.Algebra.EisensteinFunctor
