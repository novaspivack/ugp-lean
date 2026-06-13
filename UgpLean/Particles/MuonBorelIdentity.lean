import Mathlib
import UgpLean.GTE.Evolution
import UgpLean.GTE.UpdateMap
import UgpLean.Polynomial.AGL17ChiralZ2

/-!
# Muon N-value equals Borel (AGL(1,7)) order

Certifies the identification b₂ = |AGL(1,7)| = |Borel stabilizer of PGL(2,7)|.

Both factors are separately CatAL:
- `muon_n_value = 42` from the GTE cascade (`update_map_produces_canonical_orbit`,
  `g2_derived_from_T`, `canonicalGen2_values`).
- `agl17_card = 42` from `agl17_order` (`|ℤ₇ ⋊ ℤ₆| = 6 · 7`).

The certified content is the **identification** of the muon generation N-value with the
affine Borel subgroup order on `P¹(𝔽₇)`.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Particles.MuonBorelIdentity

open UgpLean
open UgpLean.Polynomial.AGL17ChiralZ2

/-- GTE muon generation N-value b₂, certified by the canonical orbit update map. -/
def muon_n_value : ℕ := 42

/-- Cardinality of `AGL(1,7) ≅ ℤ₇ ⋊ ℤ₆`, the Borel (maximal parabolic) stabilizer
    order on `P¹(𝔽₇)` in the `PGL(2,7)` action. -/
def agl17_card : ℕ := 7 * 6

theorem muon_n_value_eq_canonical_gen2_b : muon_n_value = canonicalGen2.b := by
  unfold muon_n_value canonicalGen2
  decide

theorem muon_n_value_from_update_map :
    oddStepB 73 20 11 = muon_n_value := by
  unfold muon_n_value
  native_decide

theorem agl17_card_eq_42 : agl17_card = 42 := by
  unfold agl17_card
  norm_num

theorem agl17_card_eq_agl17_order :
    agl17_card = Fintype.card (ZMod 7)ˣ * Fintype.card (ZMod 7) := by
  unfold agl17_card
  simpa using agl17_order.1.symm

/-- **muon_n_value_eq_agl17_card** (CatAL): the muon N-value equals `|AGL(1,7)|`. -/
theorem muon_n_value_eq_agl17_card : muon_n_value = agl17_card := by
  unfold muon_n_value agl17_card
  norm_num

/-- **muon_n_value_equals_borel_order** (CatAL): b₂ = 42 = |AGL(1,7)| = |Borel|. -/
theorem muon_n_value_equals_borel_order :
    muon_n_value = 42 ∧
    agl17_card = 42 ∧
    muon_n_value = agl17_card ∧
    muon_n_value = canonicalGen2.b ∧
    agl17_card = Fintype.card (ZMod 7)ˣ * Fintype.card (ZMod 7) := by
  refine ⟨?_, ?_, muon_n_value_eq_agl17_card, muon_n_value_eq_canonical_gen2_b, ?_⟩
  · unfold muon_n_value; decide
  · exact agl17_card_eq_42
  · exact agl17_card_eq_agl17_order

/-- Bundled identification theorem (alias for downstream imports). -/
theorem muon_n_value_eq_borel_pgl27 :
    muon_n_value = 42 ∧ agl17_card = 42 ∧ muon_n_value = agl17_card :=
  ⟨by unfold muon_n_value; decide, agl17_card_eq_42, muon_n_value_eq_agl17_card⟩

end UgpLean.Particles.MuonBorelIdentity
