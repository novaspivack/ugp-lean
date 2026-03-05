import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs

/-!
# UgpLean.Core.MirrorAlgebra — Symmetric Mirror Algebra and Discriminant

S = b₁²−(s+2g)b₁+2t, D = b₁(y−x).
Δ² = (b₁−s)²−4R for discriminant and mirror reconstruction.

Reference: UGP Project Updates thm:mirror-algebra, lem:discriminant
-/

namespace UgpLean

/-- Symmetric mirror form: S = b₁² − (s+2g)b₁ + 2t. At UGP-1, s+2g = 7+26 = 33. -/
def mirrorS (b₁ s g t : ℕ) : ℕ := b₁^2 - (s + 2*g)*b₁ + 2*t

/-- Discriminant term: Δ² = (b₁−s)² − 4R for mirror reconstruction. -/
def discSq (b₁ s R : ℕ) : ℕ := (b₁ - s)^2 - 4*R

/-- UGP-1 specialization: (s,g,t)=(7,13,20), so s+2g=33. -/
theorem ugp1_mirror_params : ugp1_s + 2*ugp1_g = 33 := by unfold ugp1_s ugp1_g; native_decide

/-- At n=10, b₁=73: mirrorS 73 7 13 20 = 73² − 33·73 + 40. -/
theorem mirrorS_at_lepton : mirrorS leptonB ugp1_s ugp1_g ugp1_t = 73^2 - 33*73 + 40 := by
  unfold mirrorS leptonB ugp1_s ugp1_g ugp1_t
  native_decide

/-- Discriminant at n=10: (73−7)² − 4·1008 = 66² − 4032. -/
theorem discSq_at_10 : discSq leptonB ugp1_s (ridge 10) = (73 - 7)^2 - 4*1008 := by
  unfold discSq leptonB ugp1_s ridge
  native_decide

end UgpLean
