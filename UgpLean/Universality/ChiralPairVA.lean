import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# UgpLean.Universality.ChiralPairVA — V-A Chirality Mismatch Theorem (Rank 133, CatAL)

## Background

The two-layer vertex table (Rule 110 vs Rule 124) over the canonical SM vocabulary
{0=vac, 2=u, 3=W⁺, 4=e⁻, 6=d} ⊂ Z₇ contains exactly **32 mismatches out of 5³ = 125** triples.
All mismatches involve W⁺ (winding=3) as a non-center neighbor.  This is the discrete V-A
chirality structure: the right-moving layer (Rule 110) and left-moving layer (Rule 124) diverge
precisely when the W⁺ gauge field appears in the local neighborhood.

Rule 124 is the spatial mirror of Rule 110: it applies Rule 110 with the left and right
neighbors swapped.  This reversal is the discrete analogue of the V−A parity flip.

## Key theorems (all LEAN-CERTIFIED, native_decide / decide, zero sorry)

- `bit_mismatch_iff`: the exact Fin-2 characterisation — rule110 ≠ rule124 iff l≠r ∧ c=0
- `va_mismatch_count`: exactly 32 of the 125 SM-vocabulary triples are mismatches
- `va_mismatch_involves_wplus`: every mismatch triple has W⁺ (value 3) as left or right neighbor
- `va_no_center_parity_mismatch`: odd-parity center never causes a mismatch (Fin-2 level)
-/

namespace ChiralPairVA

/-! ### Rule 110 and Rule 124 on one bit each -/

/-- Rule 110 lookup table on Fin 2 × Fin 2 × Fin 2 (left, center, right). -/
def rule110 (l c r : Fin 2) : Fin 2 :=
  match l, c, r with
  | 1, 1, 1 => 0
  | 1, 1, 0 => 1
  | 1, 0, 1 => 1
  | 1, 0, 0 => 0
  | 0, 1, 1 => 1
  | 0, 1, 0 => 1
  | 0, 0, 1 => 1
  | 0, 0, 0 => 0

/-- Rule 124 is Rule 110 with left and right neighbors swapped — the parity mirror. -/
def rule124 (l c r : Fin 2) : Fin 2 := rule110 r c l

/-! ### Z₇ parity projection and f_MDL -/

/-- Z₇ parity bit: 0 for even winding, 1 for odd winding. -/
def z7parity (x : Fin 7) : Fin 2 := ⟨x.val % 2, by omega⟩

/-- f_MDL under Rule 110: applies the rule to the parity bits of Z₇ neighbors. -/
def fmdl110 (l c r : Fin 7) : Fin 2 := rule110 (z7parity l) (z7parity c) (z7parity r)

/-- f_MDL under Rule 124: applies the mirror rule to the parity bits of Z₇ neighbors. -/
def fmdl124 (l c r : Fin 7) : Fin 2 := rule124 (z7parity l) (z7parity c) (z7parity r)

/-! ### SM vocabulary -/

/-- The canonical SM vocabulary {vac=0, u=2, W⁺=3, e⁻=4, d=6} as a Finset of Fin 7. -/
def smVocab : Finset (Fin 7) :=
  {⟨0, by norm_num⟩, ⟨2, by norm_num⟩, ⟨3, by norm_num⟩, ⟨4, by norm_num⟩, ⟨6, by norm_num⟩}

/-! ### Core theorems -/

/-- Exact Fin-2 characterisation: rule110 and rule124 disagree if and only if l ≠ r and c = 0.
    Proved by exhaustive decision over all 8 Fin-2 triples. -/
theorem bit_mismatch_iff :
    ∀ l c r : Fin 2, rule110 l c r ≠ rule124 l c r ↔ (l ≠ r ∧ c = 0) := by
  decide

/-- Odd-parity center is never a mismatch site: when c % 2 = 1, rule110 and rule124 agree
    for every choice of l and r (Fin-2 level). -/
theorem va_no_center_parity_mismatch :
    ∀ l r : Fin 2, rule110 l 1 r = rule124 l 1 r := by
  decide

/-- The total number of SM-vocabulary triples (l,c,r) ∈ {0,2,3,4,6}³ where
    Rule 110 and Rule 124 disagree is exactly 32. -/
theorem va_mismatch_count :
    ((smVocab ×ˢ (smVocab ×ˢ smVocab)).filter
      (fun t => fmdl110 t.1 t.2.1 t.2.2 ≠ fmdl124 t.1 t.2.1 t.2.2)).card = 32 := by
  native_decide

/-- Every mismatch triple in the SM vocabulary has W⁺ (winding = 3) as the left or
    right neighbor.  W⁺ as center, or W⁺ absent from the neighborhood, yields no mismatch. -/
theorem va_mismatch_involves_wplus :
    ∀ t ∈ smVocab ×ˢ (smVocab ×ˢ smVocab),
      fmdl110 t.1 t.2.1 t.2.2 ≠ fmdl124 t.1 t.2.1 t.2.2 →
      (t.1.val = 3 ∨ t.2.2.val = 3) := by
  native_decide

end ChiralPairVA
