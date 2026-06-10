import Mathlib
import UgpLean.Algebra.ChiralDoublet
import UgpLean.Polynomial.EisensteinIdentities

/-!
# AGL(1,7) chiral Z₂ mechanism

`AGL(1,7) = {x ↦ ax+b : a ∈ (ℤ/7ℤ)*, b ∈ ℤ/7ℤ}` has order `42 = 6·7`.
The spatial reflection `s(x) = −x` (`6x` mod `7`) has order `2`, swaps Rule 110 and
Rule 124 on all binary inputs, and commutes with the color action `c(x) = 2x`.

All theorems: zero sorry, zero custom axioms.
-/

namespace UgpLean.Polynomial.AGL17ChiralZ2

open UgpLean.Polynomial.EisensteinIdentities
open ChiralDoublet

/-- Affine map `(a,b)` acting on `ZMod 7`. -/
def agl17Act (a b x : ZMod 7) : ZMod 7 := a * x + b

/-- The spatial reflection `s = (−1, 0)` in `AGL(1,7)`: `s(x) = −x`. -/
def spatialReflection (x : ZMod 7) : ZMod 7 := agl17Act 6 0 x

/-- The standard `Z₃` color action on coordinates: multiplication by `2`. -/
def colorAction (x : ZMod 7) : ZMod 7 := agl17Act 2 0 x

/-- Cardinality of the unit group `(ℤ/7ℤ)*`. -/
theorem zmod7_units_card : Fintype.card (ZMod 7)ˣ = 6 := by
  native_decide

/-- **agl17_order** (CatAL — `decide`): `|AGL(1,7)| = 6 · 7 = 42`. -/
theorem agl17_order :
    Fintype.card (ZMod 7)ˣ * Fintype.card (ZMod 7) = 42 ∧
    6 * 7 = 42 := by
  refine ⟨?_, by decide⟩
  rw [zmod7_units_card]
  native_decide

theorem spatial_reflection_sq (x : ZMod 7) : spatialReflection (spatialReflection x) = x := by
  unfold spatialReflection agl17Act
  fin_cases x <;> decide

/-- **spatial_reflection_order_two** (CatAL): `s² = id` on `ZMod 7`. -/
theorem spatial_reflection_order_two :
    (∀ x : ZMod 7, spatialReflection (spatialReflection x) = x) ∧
    spatialReflection (spatialReflection 0) = 0 := by
  exact ⟨spatial_reflection_sq, by simpa using spatial_reflection_sq 0⟩

theorem rule124_eq_rule110_reflected_all :
    ∀ l c r : Fin 2, rule124 l c r = rule110 r c l :=
  rule124_eq_rule110_reflected

theorem color_commutes_with_spatial_reflection (x : ZMod 7) :
    colorAction (spatialReflection x) = spatialReflection (colorAction x) := by
  unfold colorAction spatialReflection agl17Act
  fin_cases x <;> decide

/-- **agl17_chiral_z2_mechanism** (CatAL — `decide` / existing chiral doublet):
    `|AGL(1,7)| = 42`; spatial reflection has order `2`; Rule 110 ↔ Rule 124 swap;
    color commutes with reflection. -/
theorem agl17_chiral_z2_mechanism :
    (Fintype.card (ZMod 7)ˣ * Fintype.card (ZMod 7) = 42) ∧
    (∀ x : ZMod 7, spatialReflection (spatialReflection x) = x) ∧
    (∀ l c r : Fin 2, rule124 l c r = rule110 r c l) ∧
    (∀ x : ZMod 7, colorAction (spatialReflection x) = spatialReflection (colorAction x)) ∧
    phi6 7 = 43 ∧
    poly_p_zeroFinset.card = 43 := by
  refine ⟨agl17_order.1, spatial_reflection_order_two.1, rule124_eq_rule110_reflected_all,
    color_commutes_with_spatial_reflection, ?_, poly_p_zeroFinset_card⟩
  · unfold phi6; norm_num

end UgpLean.Polynomial.AGL17ChiralZ2
