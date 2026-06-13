import UgpLean.Universality.Z7InvariantSubsets
import Mathlib.Data.Fintype.Powerset

/-!
# Golden-Fiber Invariant-Subset Taxonomy (q = 7)

Complete classification of `p`-invariant subsets of GF(7).

The GTE polynomial is `p(L,C,R) = C + R − C·R − L·C·R` (`GTE.Z7InvariantSubsets.p_poly`).

At `q = 7` the master quadratic `m(x) = x² + x − 1` is rootless (5 is QNR mod 7), so
golden singletons do not exist in GF(7); they live in GF(49). The only `p`-invariant subsets
are `∅`, `{0}`, `{0,1}`, and GF(7) itself.

All theorems: zero sorry, `native_decide` where finite. CatAL at `q = 7`.
The size-≥3 step for general prime `q ≥ 5` is CatAD analytically (Key Lemma below).
-/

namespace UgpLean.Polynomial.GoldenFiberTaxonomy

open GTE.Z7InvariantSubsets

/-- Two-element fiber `{0, x}` over GF(7). -/
def binaryZeroFiber (x : Fin 7) : Finset (Fin 7) := {0, x}

/-- **golden_taxonomy_size1_complete** (CatAL):
    Singleton `{x}` is `p`-invariant over GF(7) iff `x = 0`. Golden roots require GF(49). -/
theorem golden_taxonomy_size1_complete :
    ∀ x : Fin 7, isInvariantSubsetBool {x} = true ↔ x = 0 := by
  native_decide

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

/-- **golden_fiber_only_trivial_q7** (CatAL):
    The only `p`-invariant subsets of GF(7) are `∅`, `{0}`, `{0,1}`, and GF(7). -/
theorem golden_fiber_only_trivial_q7 :
    ∀ S : Finset (Fin 7), IsInvariantSubset S →
      S = ∅ ∨ S = {0} ∨ S = binarySublayer ∨ S = Finset.univ :=
  p_poly_invariant_subsets

/-- **golden_taxonomy_complete_q7** (CatAL):
    Any proper `p`-invariant subset of GF(7) with cardinality ≥ 3 equals GF(7). -/
theorem golden_taxonomy_complete_q7 :
    ∀ S : Finset (Fin 7), isInvariantSubsetBool S → 3 ≤ S.card → S = Finset.univ := by
  native_decide

theorem golden_taxonomy_complete_q7_prop :
    ∀ S : Finset (Fin 7), IsInvariantSubset S → 3 ≤ S.card → S = Finset.univ := by
  intro S hInv hcard
  exact golden_taxonomy_complete_q7 S hInv hcard

/-- **Key Lemma** (CatAD, general prime `q ≥ 5`):
    For a proper multiplicative subgroup `H` of GF(q)* with `|H| ≥ 2`, the image of
    `φ(h) = 1 − h` cannot lie in `H ∪ {0}`. Proof: summing `t` over `φ(H)` gives
    `d` directly and `−1` via the subgroup sum, forcing `d = q − 1` and hence `H = GF(q)*`.

    At `q = 7` the size-≥3 golden-fiber taxonomy step is machine-certified below.
    Full general-`q` formalization requires Mathlib finite-field subgroup infrastructure. -/
theorem golden_fiber_key_lemma_documented :
    ∀ S : Finset (Fin 7),
      IsInvariantSubset S → 3 ≤ S.card → S = Finset.univ :=
  golden_taxonomy_complete_q7_prop

end UgpLean.Polynomial.GoldenFiberTaxonomy
