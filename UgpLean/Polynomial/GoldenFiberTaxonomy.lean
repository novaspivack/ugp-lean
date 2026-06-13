import UgpLean.Universality.Z7InvariantSubsets
import Mathlib.Data.Fintype.Powerset

/-!
# Golden-Fiber Invariant-Subset Taxonomy (q = 7)

Size-2 classifications for `p`-invariant subsets of GF(7).

The GTE polynomial is `p(L,C,R) = C + R − C·R − L·C·R` (`GTE.Z7InvariantSubsets.p_poly`).

All theorems: zero sorry, `native_decide`. CatAL.
-/

namespace UgpLean.Polynomial.GoldenFiberTaxonomy

open GTE.Z7InvariantSubsets

/-- Two-element fiber `{0, x}` over GF(7). -/
def binaryZeroFiber (x : Fin 7) : Finset (Fin 7) := {0, x}

/-- **golden_taxonomy_size2_zero_complete** (CatAL):
    `{0, x}` is `p`-invariant over GF(7) iff `x = 1`. At `q = 7` there is no
    ramified `{0, 2}` second floor (that case occurs only at `q = 5`). -/
theorem golden_taxonomy_size2_zero_complete :
    ∀ x : Fin 7, x ≠ 0 →
      (isInvariantSubsetBool (binaryZeroFiber x) = true ↔ x = 1) := by
  native_decide

/-- **golden_roots_no_two_element_subset** (CatAL):
    No two distinct nonzero elements of GF(7) form a `p`-invariant pair.
    Golden roots live in GF(49); over GF(7) every nonzero pair fails closure. -/
theorem golden_roots_no_two_element_subset :
    ∀ x y : Fin 7, x ≠ 0 → y ≠ 0 → x ≠ y →
      isInvariantSubsetBool ({x, y} : Finset (Fin 7)) = false := by
  native_decide

end UgpLean.Polynomial.GoldenFiberTaxonomy
