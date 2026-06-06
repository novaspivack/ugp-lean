/-
  Z7InvariantSubsets.lean — EPIC_085

  Invariant Subset Uniqueness Theorem for the GTE polynomial p(L,C,R) over GF(7).

  The GTE polynomial p(L,C,R) = C + R - C·R - L·C·R (mod 7) has exactly three
  non-empty subsets S ⊆ Fin 7 that are closed under p (i.e. p(S×S×S) ⊆ S):
    - {0}           (trivial vacuum)
    - {0, 1}        (= Rule 110 binary sublayer — the unique non-trivial invariant sub-CA)
    - Fin 7 itself  (trivially closed)

  All theorems proved by `decide` or `native_decide` (finite enumeration over Fin 7).
  Zero sorry. CatAL.
-/

import UgpLean.Universality.CUP3DUniqueness
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.Fintype.Powerset

namespace GTE.Z7InvariantSubsets

open CUP3D

/-- The binary sublayer {0, 1} ⊂ Z₇. -/
def binarySublayer : Finset (Fin 7) := {0, 1}

/-- The raw GTE polynomial over all of Z₇ (no f_MDL orbit-position filtering). -/
def p_poly (L C R : Fin 7) : Fin 7 :=
  C + R - C * R - L * C * R

/-- All triples in S×S×S as a finset. -/
private def triplesIn (S : Finset (Fin 7)) : Finset (Fin 7 × Fin 7 × Fin 7) :=
  (S : Finset (Fin 7)) ×ˢ ((S : Finset (Fin 7)) ×ˢ (S : Finset (Fin 7)))

/-- Decidable check: S is closed under p_poly on S×S×S. -/
def isInvariantSubsetBool (S : Finset (Fin 7)) : Bool :=
  ((triplesIn S).filter fun t => p_poly t.1 t.2.1 t.2.2 ∉ S).card == 0

/-- A subset S ⊆ Z₇ is invariant under p_poly when p maps S×S×S into S. -/
def IsInvariantSubset (S : Finset (Fin 7)) : Prop :=
  isInvariantSubsetBool S = true

/-- **p_poly agrees with fmdl on the binary sublayer** (CatAL).

    On {0,1}³, the raw polynomial equals fmdl (hence Rule 110).
    At non-binary orbit neighborhoods with fmdl ≠ 0, p_poly and fmdl differ:
    fmdl encodes SM orbit constraints, not the unrestricted polynomial. -/
theorem p_poly_agrees_fmdl_on_binary :
    ∀ L C R : Fin 7, L ∈ binarySublayer → C ∈ binarySublayer → R ∈ binarySublayer →
      p_poly L C R = fmdl L C R := by decide

/-- **p_poly is closed on the binary sublayer** (CatAL).

    On all inputs in {0,1}³, p_poly outputs remain in {0,1}, matching Rule 110. -/
theorem p_poly_binary_restriction_closed :
    ∀ L C R : Fin 7, L ∈ binarySublayer → C ∈ binarySublayer → R ∈ binarySublayer →
      p_poly L C R ∈ binarySublayer := by decide

/-- **Invariant Subset Uniqueness** (CatAL).

    The only subsets S ⊆ Z₇ closed under p_poly are ∅, {0}, {0,1}, and Z₇ itself. -/
theorem p_poly_invariant_subsets_classification :
    ∀ S : Finset (Fin 7), isInvariantSubsetBool S →
      S = ∅ ∨ S = {0} ∨ S = binarySublayer ∨ S = Finset.univ := by
  native_decide

/-- **Invariant Subset Uniqueness** (Prop formulation, CatAL). -/
theorem p_poly_invariant_subsets :
    ∀ S : Finset (Fin 7), IsInvariantSubset S →
      S = ∅ ∨ S = {0} ∨ S = binarySublayer ∨ S = Finset.univ :=
  p_poly_invariant_subsets_classification

/-- **Rule 110 is the unique maximal proper invariant sub-CA** (CatAL).

    Among non-empty proper subsets of Z₇ closed under p_poly, only {0} and {0,1} remain. -/
theorem rule110_unique_proper_invariant_subca :
    ∀ S : Finset (Fin 7), isInvariantSubsetBool S → S ≠ ∅ → S ≠ Finset.univ →
      S = {0} ∨ S = binarySublayer := by
  native_decide

end GTE.Z7InvariantSubsets
