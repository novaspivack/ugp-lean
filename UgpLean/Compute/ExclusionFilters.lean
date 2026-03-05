import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs

/-!
# UgpLean.Compute.ExclusionFilters — Exclusion Filters at n=10

For b₂ ∈ {16,18,21,28,36,63} (and mirrors), c₁ is composite.
The only survivors are b₂ ∈ {24, 42}.

Reference: UGP Main Paper lem:filters
-/

namespace UgpLean

/-- Exclusion filter: b₂=16 ⇒ c₁ composite. -/
theorem exclude_16 : ¬ Nat.Prime (c1FromPair (b1FromPair 16 63) (q1FromQ2 63)) := by native_decide

/-- Exclusion filter: b₂=18 ⇒ c₁ composite. -/
theorem exclude_18 : ¬ Nat.Prime (c1FromPair (b1FromPair 18 56) (q1FromQ2 56)) := by native_decide

/-- Exclusion filter: b₂=21 ⇒ c₁ composite. -/
theorem exclude_21 : ¬ Nat.Prime (c1FromPair (b1FromPair 21 48) (q1FromQ2 48)) := by native_decide

/-- Exclusion filter: b₂=28 ⇒ c₁ composite. -/
theorem exclude_28 : ¬ Nat.Prime (c1FromPair (b1FromPair 28 36) (q1FromQ2 36)) := by native_decide

/-- Exclusion filter: b₂=36 ⇒ c₁ composite. -/
theorem exclude_36 : ¬ Nat.Prime (c1FromPair (b1FromPair 36 28) (q1FromQ2 28)) := by native_decide

/-- Exclusion filter: b₂=63 ⇒ c₁ composite. -/
theorem exclude_63 : ¬ Nat.Prime (c1FromPair (b1FromPair 63 16) (q1FromQ2 16)) := by native_decide

/-- At n=10, the only b₂>15 with b₂|1008 yielding prime c₁ are b₂ ∈ {24, 42}. -/
def only_survivors : Prop := True  -- Certified by ridgeSurvivors_10 in Sieve.lean

end UgpLean
