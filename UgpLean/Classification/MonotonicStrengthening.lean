import UgpLean.Core.SievePredicates
import UgpLean.Classification.Bounds
import UgpLean.Classification.TheoremB
import UgpLean.Compute.DecidablePredicates

/-!
# UgpLean.Classification.MonotonicStrengthening — Predicate Strengthening Cannot Add Survivors

If we strengthen any of the sieve predicates, the residual under stronger predicates
is a SUBSET of the residual under weaker predicates. No new survivors can appear.

Reference: Advisor recommendation §8
-/

namespace UgpLean

/-- Residual under a decidable predicate (Bool version). -/
def ResidualUnder (f : Triple → Bool) : Finset Triple :=
  Candidates.filter (fun t => f t = true)

/-- Monotonicity: If f₁(t)=true → f₂(t)=true, then ResidualUnder f₁ ⊆ ResidualUnder f₂. -/
theorem residual_monotone (f₁ f₂ : Triple → Bool)
    (himp : ∀ t, f₁ t = true → f₂ t = true) :
    ResidualUnder f₁ ⊆ ResidualUnder f₂ := by
  intro t ht
  simp only [ResidualUnder, Finset.mem_filter] at ht ⊢
  exact ⟨ht.1, himp t ht.2⟩

/-- Strengthening decSemanticFloor, decQuarterLockRigid, or decRelationalAnchor
  (by replacing with a stronger decidable predicate) cannot add survivors to Residual. -/
theorem strengthening_cannot_add_survivors
    (fSF fQL fRA : Triple → Bool)
    (hsf : ∀ t, fSF t = true → decSemanticFloor t = true)
    (hql : ∀ t, fQL t = true → decQuarterLockRigid t = true)
    (hra : ∀ t, fRA t = true → decRelationalAnchor t = true) (t : Triple)
    (ht : t ∈ Candidates.filter (fun s => (fSF s && fQL s && fRA s) = true)) :
    t ∈ Residual := by
  simp only [Residual, Finset.mem_filter, Bool.and_eq_true] at *
  obtain ⟨hmem, ⟨⟨h1, h2⟩, h3⟩⟩ := ht
  exact ⟨hmem, (decUnifiedAdmissible_correct t).mpr
    ⟨(decSemanticFloor_correct t).mp (hsf t h1),
     (decQuarterLockRigid_correct t).mp (hql t h2),
     (RelationalAnchorAt_10_iff t).mpr ((decRelationalAnchor_correct t).mp (hra t h3))⟩⟩

end UgpLean
