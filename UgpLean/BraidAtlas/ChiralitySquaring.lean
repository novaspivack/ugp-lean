import Mathlib.Tactic.NormNum
import UgpLean.Phase4.GaugeCouplings
import UgpLean.Phase4.PositiveRootTheorem

/-!
# UgpLean.BraidAtlas.ChiralitySquaring — T7: Arithmetic Signature of V−A Structure

**Theorem (Chirality Squaring):** The SU(3) bare coupling numerator is a perfect
square while the SU(2) numerator is not.  This is the arithmetic signature of the
V−A structure of the Standard Model gauge interactions:

  - SU(3) colour is **vector-like**: both T-history (c > 0) and T†-history (c < 0)
    particles carry colour charge; each root-system factor therefore appears from
    both chirality sectors, yielding a squared numerator
    $(13 \cdot 17 \cdot 29)^2$.

  - SU(2) weak is **chiral**: only left-handed (T-history) fermions carry weak
    isospin; the root-system factor appears once, giving an unsquared numerator
    $17 \cdot 137$.

The arithmetic facts (squareness/non-squareness) are Lean-certified below.
The physics bridge (vector-like vs. chiral coupling) is documented in the
Braid Atlas (P17, §6) and follows from the T/T† dual-operator formalism.

Reference: P25 §6, P17 §6, `papers/17_braid_atlas/Braid_Atlas_v2_First_Principles.tex`
-/

namespace UgpLean.BraidAtlas.ChiralitySquaring

open UgpLean.Phase4 UgpLean.Phase4.PositiveRootTheorem

/-! ## Squareness of the SU(3) coupling numerator -/

/-- g₃² numerator = (13×17×29)² is a perfect square.
  This reflects the vector-like nature of SU(3) colour: both chirality histories
  contribute, so each root-system factor appears twice. -/
theorem g3_numerator_is_perfect_square :
    ∃ k : ℤ, (g3Sq_bare.num : ℤ) = k ^ 2 := by
  exact ⟨13 * 17 * 29, by rw [g3_num_val]; norm_num⟩

/-- The explicit square root: g₃² numerator = (13×17×29)². -/
theorem g3_numerator_sqrt : (13 * 17 * 29 : ℤ) ^ 2 = g3Sq_bare.num := by
  rw [g3_num_val]; norm_num

/-! ## Non-squareness of the SU(2) coupling numerator -/

/-- 2329 is not a perfect square. Proved by bounding: 48²=2304 < 2329 < 2401=49². -/
theorem two_three_two_nine_not_nat_sq : ¬ ∃ k : ℕ, k ^ 2 = 2329 := by
  intro ⟨k, hk⟩
  -- k must satisfy k ≤ 48 (else k² ≥ 49² = 2401 > 2329)
  -- and k ≥ 49 is impossible; checking 0..48 by native_decide
  have hbound : k ≤ 48 := by
    by_contra h
    have hge : k ≥ 49 := by omega
    have : k ^ 2 ≥ 49 ^ 2 := Nat.pow_le_pow_left hge 2
    norm_num at this; omega
  -- Now check all k ∈ [0,48]: none satisfy k² = 2329
  have : ∀ j : Fin 49, j.val ^ 2 ≠ 2329 := by native_decide
  exact this ⟨k, by omega⟩ hk

/-- 2329 is not a perfect square (ℤ version). -/
theorem two_three_two_nine_not_square : ¬ ∃ k : ℤ, (2329 : ℤ) = k ^ 2 := by
  intro ⟨k, hk⟩
  apply two_three_two_nine_not_nat_sq
  refine ⟨k.natAbs, ?_⟩
  have h1 : (k.natAbs : ℤ) ^ 2 = k ^ 2 := by
    push_cast [Int.natAbs_pow]
    exact sq_abs k
  exact_mod_cast show (k.natAbs : ℤ) ^ 2 = 2329 from h1.trans hk.symm

/-- g₂² numerator = 17×137 is not a perfect square.
  This reflects the chiral nature of SU(2) weak: only the T-history (left-handed)
  sector contributes, so the root-system factor appears once, not twice. -/
theorem g2_numerator_not_perfect_square :
    ¬ ∃ k : ℤ, (g2Sq_bare.num : ℤ) = k ^ 2 := by
  intro ⟨k, hk⟩
  rw [g2_num_val] at hk
  exact two_three_two_nine_not_square ⟨k, hk⟩

/-! ## The Combined Chirality Theorem (arithmetic statement) -/

/-- **Chirality Theorem (arithmetic):**
  The SU(3) coupling numerator is a perfect square and the SU(2) coupling
  numerator is not.  This is the arithmetic signature of the V−A structure. -/
theorem chirality_arithmetic :
    (∃ k : ℤ, (g3Sq_bare.num : ℤ) = k ^ 2) ∧
    ¬(∃ k : ℤ, (g2Sq_bare.num : ℤ) = k ^ 2) :=
  ⟨g3_numerator_is_perfect_square, g2_numerator_not_perfect_square⟩

end UgpLean.BraidAtlas.ChiralitySquaring
