import Mathlib
import UgpLean.Universality.UWCASimulation

/-!
# UgpLean.Universality.UWCAHistoryReversible — Exact reversibility via a history lane

augment the UWCA state with a **history stack** of prior
tape configurations. One forward sweep stores the pre-image in the stack; peeling the
stack recovers the exact previous configuration—no floating-point “MSE” needed.

This is not reversibility of Rule 110 on the visible `C` bits alone; it is structural
invertibility of the **lifted** system on `Tape L × List (Tape L)`.

Reference: companion to ML-9 discussion in `ugp_meta_laws.tex` (`ugp-lean` formal substrate).
-/

namespace UgpLean.Universality

variable {L : ℕ} [NeZero L]

/-- Augmented forward step: apply `uwcaRound` to the current tape and push the pre-image
    onto the history stack. -/
def uwcaAugmentedFwd (cur : Tape L) (hist : List (Tape L)) : Tape L × List (Tape L) :=
  (uwcaRound cur, cur :: hist)

/-- Dummy tape (only needed to make `uwcaAugmentedBwd` total on the empty-history branch;
    `uwca_augmented_left_inverse` never hits this branch). -/
def defaultTape : Tape L :=
  fun _ =>
    { C := false, L := false, R := false, M := fun _ => false, N := false }

/-- Inverse on reachable augmented states: pop the saved pre-image off the history stack.
    The `newTape` argument is ignored (the committed UWCA output is redundant once the
    history lane is present). -/
def uwcaAugmentedBwd (_newTape : Tape L) (hist : List (Tape L)) : Tape L × List (Tape L) :=
  match hist with
  | [] => (defaultTape, [])
  | pre :: hs => (pre, hs)

/-- **Main lemma:** backward ∘ forward = identity on the product tape × history. -/
theorem uwca_augmented_left_inverse (cur : Tape L) (hist : List (Tape L)) :
    uwcaAugmentedBwd (uwcaAugmentedFwd cur hist).1 (uwcaAugmentedFwd cur hist).2 =
      (cur, hist) := by
  simp [uwcaAugmentedFwd, uwcaAugmentedBwd]

/-- Corollary in one-variable form (history starts empty). -/
theorem uwca_history_lane_step_reversible (cur : Tape L) :
    uwcaAugmentedBwd (uwcaAugmentedFwd cur []).1 (uwcaAugmentedFwd cur []).2 = (cur, []) := by
  simpa using uwca_augmented_left_inverse cur []

end UgpLean.Universality
