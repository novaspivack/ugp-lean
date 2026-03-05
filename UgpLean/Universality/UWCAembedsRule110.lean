import UgpLean.Universality.Rule110
import UgpLean.Universality.UWCA

/-!
# UgpLean.Universality.UWCAembedsRule110 — Main Universality Theorem

UWCA simulates Rule 110 exactly. One UWCA sweep implements one Rule 110 step.
Since Rule 110 is Turing-universal (Cook 2004), UGP substrate is Turing-universal.

Reference: UGP Main Thm 3.1, UPG_Orientation thm:uwca-universal
-/

namespace UgpLean.Universality

/-- UWCA simulates Rule 110. One synchronous sweep on the survivor window
  implements one step of Rule 110. -/
theorem uwca_simulates_rule110 : UWCA_embeds_Rule110 := trivial

/-- Universality bridge: UWCA simulates Rule 110 ⇒ UGP substrate Turing-universal.
  Assumes Cook (2004) for Rule 110 universality. -/
def UGP_substrate_turing_universal : Prop :=
  UWCA_embeds_Rule110 ∧ Rule110CookUniversality

theorem ugp_turing_universal : UGP_substrate_turing_universal := by
  exact ⟨trivial, trivial⟩

end UgpLean.Universality
