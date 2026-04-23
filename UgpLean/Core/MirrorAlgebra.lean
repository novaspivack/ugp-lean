import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs

/-!
# UgpLean.Core.MirrorAlgebra — Symmetric Mirror Algebra and Discriminant

S = b₁²−(s+2g)b₁+2t, D = b₁(y−x).
Δ² = (b₁−s)²−4R for discriminant and mirror reconstruction.

Also contains the Lepton-level mirror shift and shared-residue identities:
- mirrorC1 - leptonC1 = 18 * leptonB (the "mirror shift" = 1314 = 18·73)
- Both 823 and 2137 are ≡ ugp1_t (mod leptonB), i.e. ≡ 20 (mod 73)

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

-- ════════════════════════════════════════════════════════════════
-- Mirror shift and shared residue at the Lepton level (n=10)
-- ════════════════════════════════════════════════════════════════

/-- **Mirror shift at n=10:** mirrorC1 − leptonC1 = 18 · leptonB = 1314.
 I.e. 2137 − 823 = 18 · 73 = 1314. -/
theorem lepton_mirror_shift : mirrorC1 - leptonC1 = 18 * leptonB := by
  unfold mirrorC1 leptonC1 leptonB; native_decide

/-- **Mirror shift value:** the shift is 1314. -/
theorem lepton_mirror_shift_val : mirrorC1 - leptonC1 = 1314 := by
  unfold mirrorC1 leptonC1; native_decide

/-- **Factored mirror shift:** 1314 = 2 · 3² · 73. -/
theorem mirror_shift_factored : (1314 : ℕ) = 2 * 3^2 * 73 := by native_decide

/-- **Shared residue (leptonC1):** 823 ≡ 20 (mod 73). -/
theorem leptonC1_mod_leptonB : leptonC1 % leptonB = ugp1_t := by
  unfold leptonC1 leptonB ugp1_t; native_decide

/-- **Shared residue (mirrorC1):** 2137 ≡ 20 (mod 73). -/
theorem mirrorC1_mod_leptonB : mirrorC1 % leptonB = ugp1_t := by
  unfold mirrorC1 leptonB ugp1_t; native_decide

/-- **Both Lepton c-values share the same residue mod b₁:**
 leptonC1 % leptonB = mirrorC1 % leptonB = ugp1_t = 20. -/
theorem lepton_shared_residue :
    leptonC1 % leptonB = ugp1_t ∧ mirrorC1 % leptonB = ugp1_t :=
  ⟨leptonC1_mod_leptonB, mirrorC1_mod_leptonB⟩

end UgpLean
