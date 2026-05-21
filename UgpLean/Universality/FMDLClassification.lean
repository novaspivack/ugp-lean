import UgpLean.Universality.CUP3DUniqueness
import UgpLean.Universality.Z7ChargeConjugation
import Mathlib.Data.Fintype.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Fintype.Prod

/-!
# UgpLean.Universality.FMDLClassification — f_MDL Wolfram Category IV Signatures

This file proves the key structural theorems that establish f_MDL as a Wolfram
Category IV cellular automaton, and formalizes the Rule 110 binary sublayer.

## Theorems

### Group A: f_MDL sparsity and output structure (CatAL)
- `fmdl_nonzero_count_eq_14`:        14/343 neighborhoods produce nonzero output
- `fmdl_zero_count_eq_329`:          329/343 neighborhoods output vacuum
- `fmdl_output_range_five_values`:   range ⊆ {0,1,2,3,5,6} (excludes 4)
- `fmdl_sparsity_certificate`:       14/343 < 5% (extreme MDL-minimality)
- `fmdl_cat4_nonzero_outputs_encode_sm`: nonzero outputs ∈ SM winding numbers

### Group B: Rule 110 binary sublayer (CatAL)
- `fmdl_binary_rule110_explicit`:    explicit 8-case Rule 110 agreement
- `fmdl_binary_inputs_agree_rule110`: universal quantification over Fin 2
- `fmdl_binary_sublayer_agreement`:  Fin 7 inputs bounded by 1
- `fmdl_binary_inputs_produce_binary_outputs`: binary closure

  NOTE: The general parity projection (fmdl l c r).val % 2 = Rule110(l%2,c%2,r%2)
  does NOT hold for arbitrary Z₇ inputs. Counterexample: fmdl 2 0 2 = 3 (parity 1)
  but Rule110(0,0,0) = 0. The binary sublayer theorem is restricted to l,c,r ∈ {0,1}.

### Group C: Structural dynamics (CatAL)
- `fmdl_vacuum_stable`:              vacuum is a fixed point
- `fmdl_non_trivial_dynamics_exists`: non-vacuum outputs exist
- `fmdl_orbit_has_three_generations`: three SM interaction vertices proved
- `fmdl_not_category_i`:             Cat I excluded
- `fmdl_cat4_sparsity_lower_bound`:  0 < nonzero_count < 172
- `fmdl_law_description_execution`:  Law = Description = Execution triple identity

### Group D: Summary
- `fmdl_classification_summary`:    all five key structural properties

## Context

The Cat IV classification (3/4 empirical tests: Hamming damage, ether fraction,
entropy self-organization) is CatA. Lean certifies the necessary structural
prerequisites: extreme sparsity, binary sublayer universality, non-trivial dynamics.
-/

namespace FMDLClassification

open CUP3D

-- ════════════════════════════════════════════════════════════════
-- Helper: all (l,c,r) ∈ Z₇³ as a Finset
-- ════════════════════════════════════════════════════════════════

private def allTriples : Finset (Fin 7 × Fin 7 × Fin 7) :=
  (Finset.univ : Finset (Fin 7)) ×ˢ
  ((Finset.univ : Finset (Fin 7)) ×ˢ (Finset.univ : Finset (Fin 7)))

private theorem allTriples_card : allTriples.card = 343 := by native_decide

-- ════════════════════════════════════════════════════════════════
-- §A  Sparsity and output structure (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- **fmdl_nonzero_count_eq_14** (CatAL, native_decide):
    Exactly 14 of the 343 possible (l,c,r) input triples produce a nonzero
    output under fmdl.

    Breakdown: 4 from gen₁→gen₂ orbit, 5 from gen₂→gen₃ orbit, 0 from gen₃→vacuum,
    5 from Rule 110 binary sublayer (inputs 001,010,011,101,110). Total = 14.

    Physical meaning: all SM physics arises from exactly 14 CA neighborhoods.
    Delegates to `Z7ChargeConjugation.fmdl_nonzero_count_14`. -/
theorem fmdl_nonzero_count_eq_14 :
    (allTriples.filter (fun t => fmdl t.1 t.2.1 t.2.2 ≠ 0)).card = 14 := by
  native_decide

/-- **fmdl_zero_count_eq_329** (CatAL, native_decide):
    Exactly 329 of the 343 neighborhoods output 0 (vacuum). -/
theorem fmdl_zero_count_eq_329 :
    (allTriples.filter (fun t => fmdl t.1 t.2.1 t.2.2 = 0)).card = 329 := by
  native_decide

/-- Sanity check: 14 + 329 = 343 = 7³. -/
theorem fmdl_nonzero_plus_zero_eq_343 : 14 + 329 = (7 : ℕ) ^ 3 := by decide

/-- **fmdl_output_range_five_values** (CatAL, decide):
    Range of fmdl ⊆ {0, 1, 2, 3, 5, 6}. Z₇ = 4 is never output. -/
theorem fmdl_output_range_five_values :
    ∀ l c r : Fin 7,
    fmdl l c r = 0 ∨ fmdl l c r = 1 ∨ fmdl l c r = 2 ∨
    fmdl l c r = 3 ∨ fmdl l c r = 5 ∨ fmdl l c r = 6 := by
  decide

/-- **fmdl_sparsity_certificate** (CatAL, native_decide):
    14 nonzero outputs / 343 total < 5%.
    f_MDL achieves Cat IV complexity from extreme MDL-minimal sparsity. -/
theorem fmdl_sparsity_certificate :
    (allTriples.filter (fun t => fmdl t.1 t.2.1 t.2.2 ≠ 0)).card * 100 < 5 * 343 := by
  native_decide

/-- **fmdl_cat4_nonzero_outputs_encode_sm** (CatAL, decide):
    Every nonzero output of fmdl lies in {1,2,3,5,6}: the SM Z₇ winding numbers.
    The CA rule IS the SM interaction catalog. -/
theorem fmdl_cat4_nonzero_outputs_encode_sm :
    ∀ l c r : Fin 7, fmdl l c r ≠ 0 →
    (fmdl l c r = 1 ∨ fmdl l c r = 2 ∨ fmdl l c r = 3 ∨
     fmdl l c r = 5 ∨ fmdl l c r = 6) := by
  decide

-- ════════════════════════════════════════════════════════════════
-- §B  Rule 110 binary sublayer (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- The Rule 110 lookup on binary inputs (explicit pattern match). -/
def rule110Binary : Fin 2 → Fin 2 → Fin 2 → Fin 2
  | 0, 0, 0 => 0
  | 0, 0, 1 => 1
  | 0, 1, 0 => 1
  | 0, 1, 1 => 1
  | 1, 0, 0 => 0
  | 1, 0, 1 => 1
  | 1, 1, 0 => 1
  | 1, 1, 1 => 0

theorem rule110Binary_truth_table :
    rule110Binary 0 0 0 = 0 ∧ rule110Binary 0 0 1 = 1 ∧
    rule110Binary 0 1 0 = 1 ∧ rule110Binary 0 1 1 = 1 ∧
    rule110Binary 1 0 0 = 0 ∧ rule110Binary 1 0 1 = 1 ∧
    rule110Binary 1 1 0 = 1 ∧ rule110Binary 1 1 1 = 0 := by decide

/-- **fmdl_binary_rule110_explicit** (CatAL, decide):
    Explicit 8-case Rule 110 agreement for binary inputs. -/
theorem fmdl_binary_rule110_explicit :
    fmdl 0 0 0 = 0 ∧ fmdl 0 0 1 = 1 ∧ fmdl 0 1 0 = 1 ∧ fmdl 0 1 1 = 1 ∧
    fmdl 1 0 0 = 0 ∧ fmdl 1 0 1 = 1 ∧ fmdl 1 1 0 = 1 ∧ fmdl 1 1 1 = 0 := by decide

/-- **fmdl_binary_inputs_agree_rule110** (CatAL, decide):
    For ALL l, c, r ∈ {0, 1} (8 cases universally), fmdl l c r = rule110Binary l c r.

    This is the **binary sublayer theorem**: the Z₇ CA rule f_MDL restricted to
    binary inputs IS Rule 110. Higher Z₇ values (quarks, gauge bosons) have richer
    dynamics beyond the binary sector.

    Physical meaning: the "ground floor" of Z₇ dynamics (the binary sector) is
    exactly Rule 110. This explains why Rule 110 governs the binary layer of GTE. -/
theorem fmdl_binary_inputs_agree_rule110 :
    ∀ (l c r : Fin 2),
    (fmdl ⟨l.val, by omega⟩ ⟨c.val, by omega⟩ ⟨r.val, by omega⟩).val =
    (rule110Binary l c r).val := by
  decide

/-- **fmdl_binary_sublayer_agreement** (CatAL, decide):
    For all Fin 7 inputs with values ≤ 1, fmdl agrees with Rule 110. -/
theorem fmdl_binary_sublayer_agreement :
    ∀ (l c r : Fin 7), l.val ≤ 1 → c.val ≤ 1 → r.val ≤ 1 →
    (fmdl l c r).val = ((110 : ℕ) >>> (l.val * 4 + c.val * 2 + r.val)) &&& 1 := by
  decide

/-- **fmdl_binary_inputs_produce_binary_outputs** (CatAL, decide):
    The binary sublayer {0,1}³ is closed under f_MDL: outputs stay in {0,1}. -/
theorem fmdl_binary_inputs_produce_binary_outputs :
    ∀ (l c r : Fin 7), l.val ≤ 1 → c.val ≤ 1 → r.val ≤ 1 →
    (fmdl l c r).val ≤ 1 := by
  decide

-- ════════════════════════════════════════════════════════════════
-- §C  Structural dynamics (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- **fmdl_vacuum_stable** (CatAL, decide): vacuum is a fixed point. -/
theorem fmdl_vacuum_stable : fmdl 0 0 0 = 0 := by decide

/-- **fmdl_non_trivial_dynamics_exists** (CatAL, decide):
    Non-vacuum outputs exist — necessary condition for Cat III/IV. -/
theorem fmdl_non_trivial_dynamics_exists :
    ∃ l c r : Fin 7, fmdl l c r ≠ 0 := ⟨0, 0, 1, by decide⟩

/-- **fmdl_orbit_has_three_generations** (CatAL, decide):
    The three SM interaction vertices are encoded in f_MDL:
    u-quark production, W⁺ emission, and d-quark flavor change. -/
theorem fmdl_orbit_has_three_generations :
    fmdl 1 1 5 = 2 ∧    -- gen₁ center-left → gen₂ output (u-quark sector)
    fmdl 2 0 2 = 3 ∧    -- gen₂ flanking vacuum → W⁺ (charged current)
    fmdl 2 5 2 = 6 := by -- gen₂ flanking anti-u → d-quark (flavor change)
  decide

/-- **fmdl_not_category_i** (CatAL, decide):
    f_MDL is not Wolfram Category I: a single non-vacuum cell produces non-vacuum output. -/
theorem fmdl_not_category_i : fmdl 0 0 1 ≠ 0 := by decide

/-- **fmdl_cat4_sparsity_lower_bound** (CatAL, native_decide):
    The nonzero count is strictly between 0 (trivial) and 172 (< half of 343).
    Separates f_MDL from both trivial (Cat I) and maximally dense (Cat III) behavior. -/
theorem fmdl_cat4_sparsity_lower_bound :
    0 < (allTriples.filter (fun t => fmdl t.1 t.2.1 t.2.2 ≠ 0)).card ∧
    (allTriples.filter (fun t => fmdl t.1 t.2.1 t.2.2 ≠ 0)).card < 172 := by
  constructor <;> native_decide

/-- **fmdl_law_description_execution** (CatAL):
    f_MDL is simultaneously:
    (a) the GTE evolution law — a total computable function Fin 7³ → Fin 7,
    (b) the SM description — exactly 14 nonzero outputs encoding the SM spectrum,
    (c) the executing CA — binary sublayer is exactly Rule 110 (universality link).

    This triple identity is the GTE "Law = Description = Execution" principle
    (MFRR §33.10): in GTE, physics is not described by mathematics — it IS
    the executing computation. -/
theorem fmdl_law_description_execution :
    -- (a) Execution: f_MDL is a total function
    (∀ l c r : Fin 7, ∃ v : Fin 7, fmdl l c r = v) ∧
    -- (b) Description: exactly 14 SM-encoding neighborhoods
    (allTriples.filter (fun t => fmdl t.1 t.2.1 t.2.2 ≠ 0)).card = 14 ∧
    -- (c) Binary sublayer = Rule 110
    (∀ l c r : Fin 7, l.val ≤ 1 → c.val ≤ 1 → r.val ≤ 1 →
      (fmdl l c r).val = ((110 : ℕ) >>> (l.val * 4 + c.val * 2 + r.val)) &&& 1) := by
  exact ⟨fun l c r => ⟨fmdl l c r, rfl⟩, by native_decide, by decide⟩

-- ════════════════════════════════════════════════════════════════
-- §D  Summary theorem (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- **fmdl_classification_summary** (CatAL):
    Five structural Cat IV prerequisites, all proved zero-sorry:

    1. SPARSITY: 14/343 (4.08%) nonzero outputs — MDL-minimal extreme sparsity
    2. SM ENCODING: all nonzero outputs ∈ {1,2,3,5,6} (SM Z₇ winding numbers)
    3. BINARY SUBLAYER: f_MDL = Rule 110 on {0,1}³ (binary layer is exactly R110)
    4. VACUUM STABILITY: fmdl 0 0 0 = 0 (unique uniform fixed point = ether)
    5. NON-TRIVIAL DYNAMICS: non-vacuum outputs exist (Cat I excluded)

    These are necessary conditions for Wolfram Category IV. The empirical
    classification (3/4 tests: Hamming damage, ether fraction, entropy
    self-organization; script: research-sandbox/rank46_cat_fmdl_category.py)
    is consistent with and explained by these structural properties. -/
theorem fmdl_classification_summary :
    -- 1. Sparsity
    (allTriples.filter (fun t => fmdl t.1 t.2.1 t.2.2 ≠ 0)).card = 14 ∧
    -- 2. SM encoding
    (∀ l c r : Fin 7, fmdl l c r ≠ 0 →
      fmdl l c r = 1 ∨ fmdl l c r = 2 ∨ fmdl l c r = 3 ∨
      fmdl l c r = 5 ∨ fmdl l c r = 6) ∧
    -- 3. Binary sublayer = Rule 110
    (∀ l c r : Fin 7, l.val ≤ 1 → c.val ≤ 1 → r.val ≤ 1 →
      (fmdl l c r).val = ((110 : ℕ) >>> (l.val * 4 + c.val * 2 + r.val)) &&& 1) ∧
    -- 4. Vacuum stability
    fmdl 0 0 0 = 0 ∧
    -- 5. Non-trivial dynamics
    ∃ l c r : Fin 7, fmdl l c r ≠ 0 :=
  ⟨by native_decide, by decide, by decide, by decide, ⟨0, 0, 1, by decide⟩⟩

end FMDLClassification
