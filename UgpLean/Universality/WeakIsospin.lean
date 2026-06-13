import Mathlib.Data.Fin.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Finset.Card
import Mathlib.Data.Fintype.Basic

/-!
# UgpLean.Universality.WeakIsospin — Z₇ Winding Origin of Weak Isospin

## Physical content

In GTE, weak isospin is encoded in the Z₇ species winding number W_B, not in a
separate gauge SU(2)_L (which is absent from the Z₇×Z₃ automorphism group).

The SM charged-current vertices conserve W_B modulo 7.  The four SM fermions form two
weak isospin doublets differing by ΔW_B = 4 mod 7, forced by the species formula
W_B = 4k mod 7 at consecutive k values.  The W bosons are composite Z₇ kinks whose
winding numbers are uniquely determined by the CC vertex conservation requirement.

### Species W_B winding numbers (Z₇ ≃ Fin 7)
- vacuum / ν_e  : W_B = 0
- u-quark        : W_B = 2
- W⁺ boson       : W_B = 3
- e⁻ / W⁻        : W_B = 4
- d-quark         : W_B = 6

### Weak isospin doublet partition
- I₃ = +1/2 sector : {ν, u}  with W_B ∈ {0, 2}
- I₃ = −1/2 sector : {e⁻, d} with W_B ∈ {4, 6}

## Key theorems (all CatAL — zero sorry, proved by `decide`)

- `wb_conservation_charged_current`    : W_B conserved at all 4 SM CC vertices
- `weak_isospin_doublet_delta_four`    : ΔW_B = 4 between doublet partners
- `species_formula_forces_delta_four`  : species formula W_B = 4k mod 7 forces ΔW_B = 4
- `wb_wplus_uniquely_determined`       : W_B(W⁺) = 3 is the unique CC solution
- `wb_wminus_uniquely_determined`      : W_B(W⁻) = 4 is the unique CC solution
- `weak_isospin_identification`        : combined certification theorem
-/

namespace WeakIsospin

-- ════════════════════════════════════════════════════════════════
-- §1  SM species Z₇ winding numbers (W_B)
-- ════════════════════════════════════════════════════════════════

/-- Z₇ species winding number W_B for the SM neutral fermion / vacuum sector: W_B = 0. -/
def wb_vacuum : Fin 7 := 0

/-- Z₇ species winding number W_B for the up-type quark: W_B = 2. -/
def wb_u : Fin 7 := 2

/-- Z₇ species winding number W_B for the W⁺ boson: W_B = 3. -/
def wb_wplus : Fin 7 := 3

/-- Z₇ species winding number W_B for the electron: W_B = 4. -/
def wb_eminus : Fin 7 := 4

/-- Z₇ species winding number W_B for the down-type quark: W_B = 6. -/
def wb_d : Fin 7 := 6

/-- W_B(W⁻) = W_B(e⁻) = 4: the W⁻ boson shares the electron winding number.
    Both sit at W_B = 4 in the Z₇ spectrum — the W⁻ is a composite kink with
    the same topological winding as the electron, mediating opposite-direction
    charged-current transitions. -/
def wb_wminus : Fin 7 := wb_eminus

/-- All five distinct nonzero SM winding values are pairwise distinct (except
    the W⁻ = e⁻ identification). -/
theorem wb_labels_distinct :
    wb_vacuum ≠ wb_u ∧ wb_vacuum ≠ wb_wplus ∧ wb_vacuum ≠ wb_eminus ∧
    wb_vacuum ≠ wb_d ∧ wb_u ≠ wb_wplus ∧ wb_u ≠ wb_eminus ∧
    wb_u ≠ wb_d ∧ wb_wplus ≠ wb_eminus ∧ wb_wplus ≠ wb_d ∧
    wb_eminus ≠ wb_d := by decide

-- ════════════════════════════════════════════════════════════════
-- §2  Weak isospin doublet structure
-- ════════════════════════════════════════════════════════════════

/-- I₃ = +1/2 (upper doublet) SM fermion W_B winding set: {ν, u} = {0, 2}. -/
def upperDoubletWB : Finset (Fin 7) := {wb_vacuum, wb_u}

/-- I₃ = −1/2 (lower doublet) SM fermion W_B winding set: {e⁻, d} = {4, 6}. -/
def lowerDoubletWB : Finset (Fin 7) := {wb_eminus, wb_d}

/-- The two weak isospin doublet sectors are disjoint subsets of Z₇. -/
theorem doublet_sectors_disjoint :
    Disjoint upperDoubletWB lowerDoubletWB := by decide

/-- Each weak isospin doublet sector has exactly 2 elements. -/
theorem doublet_sector_card :
    upperDoubletWB.card = 2 ∧ lowerDoubletWB.card = 2 := by decide

/-- The union of both doublet sectors contains all four SM fermion W_B values. -/
theorem doublet_union_card :
    (upperDoubletWB ∪ lowerDoubletWB).card = 4 := by decide

-- ════════════════════════════════════════════════════════════════
-- §3  ΔW_B = 4 between doublet partners (species formula)
-- ════════════════════════════════════════════════════════════════

/-- Lepton doublet: W_B(e⁻) = W_B(ν) + 4 mod 7. -/
theorem wb_lepton_doublet_delta_four :
    (wb_vacuum + 4 : Fin 7) = wb_eminus := by decide

/-- Quark doublet: W_B(d) = W_B(u) + 4 mod 7. -/
theorem wb_quark_doublet_delta_four :
    (wb_u + 4 : Fin 7) = wb_d := by decide

/-- **ΔW_B = 4 theorem (CatAL)**: both SM fermion doublet pairs differ by ΔW_B = 4 mod 7.

    This is forced by the species formula W_B = 4k mod 7 at consecutive k values:
    - Lepton doublet: k = 0 (ν, W_B = 0) and k = 1 (e⁻, W_B = 4)
    - Quark doublet:  k = 4 (u, W_B = 2) and k = 5 (d,  W_B = 6)
    In both cases Δk = 1 implies ΔW_B = 4 mod 7. -/
theorem weak_isospin_doublet_delta_four :
    (wb_vacuum + 4 : Fin 7) = wb_eminus ∧
    (wb_u + 4 : Fin 7) = wb_d := by decide

/-- **Species formula certification (CatAL)**: the SM fermion W_B values are given by
    W_B = 4k mod 7 at specific k values.  Consecutive k values (Δk = 1) give
    ΔW_B = 4 mod 7 within each doublet.

    - ν:  k = 0 → W_B = 0  (vacuum / neutrino sector)
    - e⁻: k = 1 → W_B = 4  (electron sector)
    - u:  k = 4 → W_B = 2  (up-type quark sector)
    - d:  k = 5 → W_B = 6  (down-type quark sector)

    The four GTE fermion species occupy a Z₇ arithmetic progression with step 4. -/
theorem species_formula_forces_delta_four :
    (4 * (0 : Fin 7) : Fin 7) = wb_vacuum ∧
    (4 * (1 : Fin 7) : Fin 7) = wb_eminus ∧
    (4 * (4 : Fin 7) : Fin 7) = wb_u ∧
    (4 * (5 : Fin 7) : Fin 7) = wb_d := by decide

/-- The Δk = 1 step in the species formula produces ΔW_B = 4 universally in Z₇:
    for any k, (4 · (k+1)) mod 7 = (4 · k + 4) mod 7. -/
theorem species_delta_universally_four :
    ∀ k : Fin 7, 4 * (k + 1) = 4 * k + 4 := by decide

-- ════════════════════════════════════════════════════════════════
-- §4  W_B conservation at SM charged-current vertices (CatAL)
-- ════════════════════════════════════════════════════════════════

/-!
### CC vertex conservation: W_B(initial) = W_B(product₁) + W_B(product₂) mod 7

The four SM charged-current vertices and their W_B accounting:
- u(2) → d(6) + W⁺(3):  2 = (6 + 3) mod 7 = 9 mod 7 = 2 ✓
- ν(0) → e⁻(4) + W⁺(3): 0 = (4 + 3) mod 7 = 7 mod 7 = 0 ✓
- d(6) → u(2) + W⁻(4):  6 = (2 + 4) mod 7 = 6 ✓
- e⁻(4) → ν(0) + W⁻(4): 4 = (0 + 4) mod 7 = 4 ✓
-/

/-- CC vertex u → d + W⁺: W_B(u) = W_B(d) + W_B(W⁺) mod 7.
    2 = (6 + 3) mod 7. -/
theorem wb_conservation_u_to_d_wplus :
    wb_u = wb_d + wb_wplus := by decide

/-- CC vertex ν → e⁻ + W⁺: W_B(ν) = W_B(e⁻) + W_B(W⁺) mod 7.
    0 = (4 + 3) mod 7. -/
theorem wb_conservation_nu_to_eminus_wplus :
    wb_vacuum = wb_eminus + wb_wplus := by decide

/-- CC vertex d → u + W⁻: W_B(d) = W_B(u) + W_B(W⁻) mod 7.
    6 = (2 + 4) mod 7. -/
theorem wb_conservation_d_to_u_wminus :
    wb_d = wb_u + wb_wminus := by decide

/-- CC vertex e⁻ → ν + W⁻: W_B(e⁻) = W_B(ν) + W_B(W⁻) mod 7.
    4 = (0 + 4) mod 7. -/
theorem wb_conservation_eminus_to_nu_wminus :
    wb_eminus = wb_vacuum + wb_wminus := by decide

/-- **W_B conservation theorem (CatAL)**: W_B is conserved at all four SM
    charged-current vertices.  All weak charged-current interactions preserve
    the Z₇ species winding number modulo 7. -/
theorem wb_conservation_charged_current :
    wb_u = wb_d + wb_wplus ∧
    wb_vacuum = wb_eminus + wb_wplus ∧
    wb_d = wb_u + wb_wminus ∧
    wb_eminus = wb_vacuum + wb_wminus := by decide

-- ════════════════════════════════════════════════════════════════
-- §5  W-boson winding uniquely determined by CC conservation (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- **W⁺ uniqueness (CatAL)**: W_B(W⁺) = 3 is the unique w ∈ Z₇ satisfying both
    CC conservation constraints simultaneously:
      W_B(d) + w = W_B(u) mod 7   (quark CC vertex)
      W_B(e⁻) + w = W_B(ν) mod 7  (lepton CC vertex)
    The Z₇ winding of the W⁺ composite kink is uniquely forced by CC conservation. -/
theorem wb_wplus_uniquely_determined :
    ∀ w : Fin 7,
      (wb_d + w = wb_u ∧ wb_eminus + w = wb_vacuum) ↔ w = wb_wplus := by decide

/-- **W⁻ uniqueness (CatAL)**: W_B(W⁻) = 4 is the unique w ∈ Z₇ satisfying both
    CC conservation constraints for the reverse transitions:
      W_B(u) + w = W_B(d) mod 7   (quark CC vertex)
      W_B(ν) + w = W_B(e⁻) mod 7  (lepton CC vertex)
    The W⁻ kink winding equals the electron winding: both sit at W_B = 4. -/
theorem wb_wminus_uniquely_determined :
    ∀ w : Fin 7,
      (wb_u + w = wb_d ∧ wb_vacuum + w = wb_eminus) ↔ w = wb_wminus := by decide

-- ════════════════════════════════════════════════════════════════
-- §6  W-boson kink structure (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- W⁺ and W⁻ are Z₇ conjugates: W_B(W⁺) + W_B(W⁻) = 0 mod 7.
    They form a charge-conjugate pair in the Z₇ winding spectrum. -/
theorem w_bosons_z7_conjugate :
    wb_wplus + wb_wminus = 0 := by decide

/-- W⁺ is the ΔW_B = 3 kink: adding W_B(W⁺) = 3 to either lower-doublet
    species recovers the corresponding upper-doublet partner mod 7.
    - d(6) + 3 = 9 mod 7 = 2 = u ✓
    - e⁻(4) + 3 = 7 mod 7 = 0 = ν ✓ -/
theorem w_plus_is_delta_three_kink :
    (wb_d + wb_wplus : Fin 7) = wb_u ∧
    (wb_eminus + wb_wplus : Fin 7) = wb_vacuum := by decide

/-- W⁻ is the ΔW_B = 4 kink: adding 4 to either upper-doublet species
    recovers the corresponding lower-doublet partner mod 7.
    - u(2) + 4 = 6 = d ✓
    - ν(0) + 4 = 4 = e⁻ ✓ -/
theorem w_minus_is_delta_four_kink :
    (wb_u + wb_wminus : Fin 7) = wb_d ∧
    (wb_vacuum + wb_wminus : Fin 7) = wb_eminus := by decide

/-- The W-boson winding numbers W_B(W⁺) = 3 and W_B(W⁻) = 4 are numerically
    confirmed as the unique pair satisfying the dual CC constraint. -/
theorem w_boson_winding_values :
    wb_wplus = 3 ∧ wb_wminus = 4 := by decide

-- ════════════════════════════════════════════════════════════════
-- §7  Combined weak isospin identification theorem (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- **Weak isospin identification theorem (CatAL)**:

    The GTE Z₇ species winding number W_B encodes weak isospin.  Formally:

    (1) **Doublet partition**: SM fermion W_B values partition into two disjoint
        doublet sectors of size 2:
        I₃ = +1/2: {ν, u} with W_B ∈ {0, 2}
        I₃ = −1/2: {e⁻, d} with W_B ∈ {4, 6}

    (2) **ΔW_B = 4 rule**: doublet partners satisfy W_B(lower) = W_B(upper) + 4 mod 7,
        forced by the species formula W_B = 4k mod 7 with Δk = +1.

    (3) **CC conservation**: all four SM charged-current vertices conserve W_B mod 7.

    (4) **W-boson uniqueness**: the W-boson winding numbers W_B(W⁺) = 3 and
        W_B(W⁻) = 4 are uniquely determined by the CC vertex conservation
        conditions — no other Z₇ element satisfies both constraints simultaneously.

    This identifies weak isospin as Z₇ winding arithmetic.  No gauge SU(2)_L field
    appears: the doublet structure is a consequence of the species formula and orbit
    structure of the GTE-Möbius substrate. -/
theorem weak_isospin_identification :
    -- (1) Doublet partition (disjoint sectors of size 2)
    Disjoint upperDoubletWB lowerDoubletWB ∧
    upperDoubletWB.card = 2 ∧ lowerDoubletWB.card = 2 ∧
    -- (2) ΔW_B = 4 between doublet partners
    (wb_vacuum + 4 : Fin 7) = wb_eminus ∧
    (wb_u + 4 : Fin 7) = wb_d ∧
    -- (3) CC conservation at all four vertices
    wb_u = wb_d + wb_wplus ∧
    wb_vacuum = wb_eminus + wb_wplus ∧
    wb_d = wb_u + wb_wminus ∧
    wb_eminus = wb_vacuum + wb_wminus ∧
    -- (4) W-boson winding values confirmed
    wb_wplus = 3 ∧ wb_wminus = 4 := by decide

-- ════════════════════════════════════════════════════════════════
-- §8  SM vocabulary incomplete under chirality Z₂ (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- Standard Model species winding vocabulary `S = {0,2,3,4,6} ⊂ Z₇`. -/
def smVocabularyWB : Finset (Fin 7) := {wb_vacuum, wb_u, wb_wplus, wb_eminus, wb_d}

/-- Chirality reflection on `Fin 7`: `s(x) = −x mod 7`. -/
def chiralityReflection (x : Fin 7) : Fin 7 := -x

theorem sm_vocabulary_card : smVocabularyWB.card = 5 := by decide

/-- **va_sm_vocab_z2_incomplete** (CatAL — decide):
    `S = {0,2,3,4,6}` is not closed under chirality reflection `s(x) = −x mod 7`:
    `s(u) = 5 ∉ S` and `s(d) = 1 ∉ S`, so right-handed quark windings are absent. -/
theorem va_sm_vocab_z2_incomplete :
    chiralityReflection wb_u = 5 ∧
    chiralityReflection wb_d = 1 ∧
    (5 : Fin 7) ∉ smVocabularyWB ∧
    (1 : Fin 7) ∉ smVocabularyWB ∧
    ∃ x ∈ smVocabularyWB, chiralityReflection x ∉ smVocabularyWB := by
  decide

end WeakIsospin
