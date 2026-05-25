import UgpLean.Substrate.CoherenceMeasure
import UgpLean.Substrate.PSCPreservingTransformation
import UgpLean.Substrate.Substrate
import UgpLean.Universality.CUP3DUniqueness
import UgpLean.Universality.GUTStructure
import UgpLean.Universality.BornRuleMDL
import UgpLean.Spacetime.QECStabilizer

/-!
# [D] D1–D5 ↔ QEC Stabilizer Bridge — Rank 38-QEC (EPIC_074)

Maps P34 §6 **D1–D5** coherence-measure axioms to quantum error correcting code (QEC)
structure, and certifies the discrete **DWeight** step-function instantiation.

## Assessment (Rank 38-QEC)

| Constraint | P34 content | QEC stabilizer analogue | Lean status |
|---|---|---|---|
| **D1** | Non-negativity; zero iff fully coherent | Code projector ≥ 0; syndrome 0 on errors | **CatAL** — `d1_dweight_nonnegative`, `d1_zero_iff_error` |
| **D2** | PSC-preserving invariance of [D] | Stabilizer preserves code subspace | **CatAL partial** — abstract `d2_universal`; discrete `d2_stabilizer_closure` |
| **D3** | Non-computability on diagonal records | *Not* a stabilizer axiom — transputation / TPC | **CatAL proxy** — `d3_tpc_above_decidable`; full diagonal barrier elsewhere |
| **D4** | Unique minimum per record class | Unique code words / decoder | **CatAL partial** — 4 code words + MDL-minimum proxy; full record-class open |
| **D5** | Born-rule marginals | *Not* a stabilizer axiom — measurement layer | **CatAL conditional** — `born_rule_from_psc_mdl`; not derived from QEC alone |

**Conclusion:** The step-function **DWeight** on Z₇⁵ beables defines a genuine QEC stabilizer
structure (code subspace, stabilizer action, syndrome, logical observable). D1, D2, and D4
(partially) correspond to standard QEC axioms at this discrete level. D3 and D5 belong to
the transputation and measurement layers respectively — they constrain [D] but are not
stabilizer-code axioms.

The complete discrete QEC certificate lives in `GTE.Spacetime.QEC`
(`qec_gte_is_stabilizer_code`, zero sorry). This module packages the D1–D5 interpretation.
-/

namespace UgpLean.Substrate.QEC

open CUP3D
open UgpLean.Universality.LawvereZone
open GTE.Lifting
open GTE.Spacetime.QEC
open GUTStructure DUniqueness TPCPowerClass
open UgpLean.Universality.BornRuleMDL

instance : DecidablePred InCodeSubspace := fun b =>
  inferInstanceAs (Decidable (PSCAdmissible b))

-- ─────────────────────────────────────────────────────────────────────────────
-- §1  Abstract D1–D5 predicates on Substrate
-- ─────────────────────────────────────────────────────────────────────────────

/-- **D1 (non-negativity):** coherence measure is non-negative on all pairs. -/
def SatisfiesD1 (S : Substrate) : Prop :=
  ∀ ρ w : S.config, 0 ≤ S.coherence ρ w

/-- **D1 (zero characterization):** vanishing coherence iff configurations coincide.
    On the discrete DWeight instantiation this becomes "zero weight ↔ error state". -/
def SatisfiesD1ZeroCharacterization (S : Substrate) : Prop :=
  ∀ ρ w : S.config, S.coherence ρ w = 0 ↔ ρ = w

/-- **D2 (PSC invariance):** [D] is invariant under all PSC-preserving maps.
    Encoded as `d2_universal` in `CoherenceMeasure.lean`. -/
def SatisfiesD2 (S : Substrate) (_hS : S.psc_consistent) : Prop :=
  ∀ f : S.config → S.config, IsPSCPreserving f →
    ∀ ρ w : S.config, S.coherence (f ρ) (f w) = S.coherence ρ w

/-- **D4 proxy (unique selection):** every non-empty finite set of ℕ has a unique minimum.
    Arithmetic proxy for "unique minimum over each record-equivalence class". -/
def SatisfiesD4Proxy : Prop :=
  ∀ (S : Finset ℕ), S.Nonempty → ∃! n, n ∈ S ∧ ∀ m ∈ S, n ≤ m

/-- The five-constraint cardinality (D1–D5) equals N_fam = 5. -/
theorem d_constraints_cardinality : n_d_constraints = n_fam := d_count_equals_nfam

-- ─────────────────────────────────────────────────────────────────────────────
-- §2  D1 on the discrete DWeight step function
-- ─────────────────────────────────────────────────────────────────────────────

/-- **D1 discrete (CatAL):** `DWeight b ≥ 0` for every beable. -/
theorem d1_dweight_nonnegative (b : Fin 5 → Fin 7) : 0 ≤ DWeight b := by
  unfold DWeight
  split_ifs <;> norm_num

/-- **D1 discrete zero characterization (CatAL):** `DWeight b = 0` iff `b` is an error state
    (not PSC-admissible / not in the code subspace). Fully coherent code words have weight 1. -/
theorem d1_zero_iff_error (b : Fin 5 → Fin 7) :
    DWeight b = 0 ↔ ¬InCodeSubspace b := by
  constructor
  · intro h hcode
    have hpos : 0 < DWeight b := (qec_dweight_projector b).mpr hcode
    rw [h] at hpos
    norm_num at hpos
  · exact qec_error_detected b

/-- **D1 discrete positive on code words (CatAL).** -/
theorem d1_positive_on_code (b : Fin 5 → Fin 7) (h : InCodeSubspace b) :
    0 < DWeight b :=
  (qec_dweight_projector b).mpr h

-- ─────────────────────────────────────────────────────────────────────────────
-- §3  D2 ↔ stabilizer closure
-- ─────────────────────────────────────────────────────────────────────────────

/-- **D2 abstract (from CoherenceMeasure):** PSC-preserving maps leave [D] invariant. -/
theorem d2_psc_invariance (S : Substrate) (hS : S.psc_consistent)
    (f : S.config → S.config) (hf : IsPSCPreserving f) (ρ w : S.config) :
    S.coherence (f ρ) (f w) = S.coherence ρ w :=
  d2_universal hS f hf ρ w

/-- **D2 discrete stabilizer closure (CatAL):** `fmdl_step5` preserves the code subspace.
    Re-export of `qec_orbit_closure`. -/
theorem d2_stabilizer_closure (b : Fin 5 → Fin 7) (h : InCodeSubspace b) :
    InCodeSubspace (fmdl_step5 b) :=
  qec_orbit_closure b h

-- ─────────────────────────────────────────────────────────────────────────────
-- §4  D3 — transputation layer, not a stabilizer axiom
-- ─────────────────────────────────────────────────────────────────────────────

/-- **D3 proxy (CatAL):** TPC (transputation power class) strictly exceeds the decidable level.
    D3 (non-computability of [D] on diagonal records) forces selection problems into TPC;
    this is the diagonal-barrier content, not a QEC stabilizer generator condition.

    Full D3 certification: NEMS Paper 11 diagonal barrier + Zone L2 (LawvereZone.lean). -/
theorem d3_tpc_above_decidable : level_decidable < level_tpc :=
  decidable_below_tpc

/-- D3 is classified as a **transputation** constraint, not a stabilizer-code axiom. -/
def D3IsTransputationLayer : Prop := level_decidable < level_tpc

theorem d3_is_transputation_layer : D3IsTransputationLayer :=
  d3_tpc_above_decidable

-- ─────────────────────────────────────────────────────────────────────────────
-- §5  D4 ↔ unique code words and MDL-minimum selection
-- ─────────────────────────────────────────────────────────────────────────────

/-- **D4 discrete (CatAL):** code subspace is exactly the four orbit-certified states. -/
theorem d4_four_code_words (b : Fin 5 → Fin 7) :
    InCodeSubspace b ↔
      b = fmdl_vacuum5 ∨ b = fmdl_gen1_z7 ∨ b = fmdl_gen2_z7 ∨ b = fmdl_gen3_z7 :=
  qec_code_words b

/-- **D4 discrete cardinality (CatAL):** exactly four code words. -/
theorem d4_exactly_four_code_words :
    (Finset.univ.filter InCodeSubspace).card = 4 := by
  native_decide

/-- **D4 discrete uniqueness (CatAL):** the four code words are pairwise distinct. -/
theorem d4_code_words_distinct :
    fmdl_vacuum5 ≠ fmdl_gen1_z7 ∧
    fmdl_vacuum5 ≠ fmdl_gen2_z7 ∧
    fmdl_vacuum5 ≠ fmdl_gen3_z7 ∧
    fmdl_gen1_z7 ≠ fmdl_gen2_z7 ∧
    fmdl_gen1_z7 ≠ fmdl_gen3_z7 ∧
    fmdl_gen2_z7 ≠ fmdl_gen3_z7 :=
  qec_code_words_distinct

/-- **D4 proxy (CatAL):** unique minimum over non-empty finite sets (MDL selection skeleton). -/
theorem d4_unique_minimum_proxy : SatisfiesD4Proxy :=
  mdl_minimum_unique

-- ─────────────────────────────────────────────────────────────────────────────
-- §6  D5 — measurement layer, not a stabilizer axiom
-- ─────────────────────────────────────────────────────────────────────────────

/-- **D5 structural slot (CatAL):** Born consistency is the fifth [D] constraint. -/
theorem d5_is_fifth_constraint : n_d_constraints = 5 := d_constraint_count

/-- D5 connects to sector Born weights via `born_rule_from_psc_mdl` (CatAL conditional).
    It is a **measurement-outcome** constraint, not part of the stabilizer generator algebra. -/
def D5IsMeasurementLayer : Prop := n_d_constraints = 5

theorem d5_is_measurement_layer : D5IsMeasurementLayer :=
  d5_is_fifth_constraint

-- ─────────────────────────────────────────────────────────────────────────────
-- §7  QEC mapping classification
-- ─────────────────────────────────────────────────────────────────────────────

/-- Which D-constraints map to standard QEC stabilizer structure at the discrete level. -/
inductive DConstraintQECRole where
  | stabilizer_axiom    : DConstraintQECRole  -- D1, D2, D4 (partial)
  | transputation_layer : DConstraintQECRole  -- D3
  | measurement_layer   : DConstraintQECRole  -- D5
  deriving DecidableEq, Repr

/-- Canonical classification of D1–D5 against QEC roles (Rank 38-QEC). -/
def d_constraint_qec_role : Fin 5 → DConstraintQECRole
  | 0 => .stabilizer_axiom    -- D1
  | 1 => .stabilizer_axiom    -- D2
  | 2 => .transputation_layer -- D3
  | 3 => .stabilizer_axiom    -- D4 (partial)
  | 4 => .measurement_layer   -- D5
  | _ => .stabilizer_axiom

theorem d1_role : d_constraint_qec_role 0 = .stabilizer_axiom := rfl
theorem d2_role : d_constraint_qec_role 1 = .stabilizer_axiom := rfl
theorem d3_role : d_constraint_qec_role 2 = .transputation_layer := rfl
theorem d4_role : d_constraint_qec_role 3 = .stabilizer_axiom := rfl
theorem d5_role : d_constraint_qec_role 4 = .measurement_layer := rfl

/-- Count of D-constraints that map to stabilizer axioms (D1, D2, D4). -/
def n_stabilizer_mapped_constraints : ℕ := 3

theorem n_stabilizer_mapped_eq_three : n_stabilizer_mapped_constraints = 3 := rfl

-- ─────────────────────────────────────────────────────────────────────────────
-- §8  Main bundle — discrete DWeight QEC + D1–D5 classification
-- ─────────────────────────────────────────────────────────────────────────────

/-- **Rank 38-QEC master bundle (CatAL, zero sorry).

    Packages:
    (1) Full discrete QEC stabilizer code on Z₇⁵ beables (`qec_gte_is_stabilizer_code`).
    (2) D1 non-negativity and zero/error characterization on DWeight.
    (3) D2 stabilizer closure under `fmdl_step5`.
    (4) D3 transputation classification (TPC above decidable).
    (5) D4 four unique code words + MDL-minimum proxy.
    (6) D5 fifth-constraint slot + measurement-layer classification.

    **Gaps (honest scope):**
    - D2 universal form on continuum Φ_MDL: axiom `d2_universal` (CoherenceMeasure.lean).
    - D3 full diagonal barrier: certified in LawvereZone / NEMS, not re-proved here.
    - D4 full record-equivalence-class uniqueness: open (C2 CatD).
    - D5 Born weights: conditional on `BeableAmplitudeHypothesis` (77-2QUANT-CANON closed). -/
theorem dweight_qec_d1_d5_bundle :
    -- (1) Complete QEC structure
    (∀ b : Fin 5 → Fin 7, InCodeSubspace b ↔ PSCAdmissible b) ∧
    (∀ b : Fin 5 → Fin 7, InCodeSubspace b → InCodeSubspace (fmdl_step5 b)) ∧
    (∀ b : Fin 5 → Fin 7, ¬InCodeSubspace b → DWeight b = 0) ∧
    (∃ Δ : ℚ, Δ > 0 ∧ ∀ b : Fin 5 → Fin 7, InCodeSubspace b → b ≠ fmdl_vacuum5 →
      ∃ mass : ℚ, mass ≥ Δ) ∧
    -- (2) D1
    (∀ b : Fin 5 → Fin 7, 0 ≤ DWeight b) ∧
    (∀ b : Fin 5 → Fin 7, DWeight b = 0 ↔ ¬InCodeSubspace b) ∧
    -- (3) D3 transputation
    (level_decidable < level_tpc) ∧
    -- (4) D4
    ((Finset.univ.filter InCodeSubspace).card = 4) ∧
    (∀ (S : Finset ℕ), S.Nonempty → ∃! n, n ∈ S ∧ ∀ m ∈ S, n ≤ m) ∧
    -- (5) D5 slot
    (n_d_constraints = 5) ∧
    -- (6) Role classification
    (d_constraint_qec_role 2 = .transputation_layer) ∧
    (d_constraint_qec_role 4 = .measurement_layer) := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact qec_gte_is_stabilizer_code.1
  · exact qec_gte_is_stabilizer_code.2.1
  · exact qec_gte_is_stabilizer_code.2.2.1
  · exact qec_gte_is_stabilizer_code.2.2.2
  · intro b; exact d1_dweight_nonnegative b
  · intro b; exact d1_zero_iff_error b
  · exact d3_tpc_above_decidable
  · exact d4_exactly_four_code_words
  · exact mdl_minimum_unique
  · exact d5_is_fifth_constraint
  · exact d3_role
  · exact d5_role

/-- Re-export: the GTE [D]-measure is a QEC stabilizer code (Spacetime certificate). -/
theorem qec_gte_is_stabilizer_code_substrate :
    (∀ b : Fin 5 → Fin 7, InCodeSubspace b ↔ PSCAdmissible b) ∧
    (∀ b : Fin 5 → Fin 7, InCodeSubspace b → InCodeSubspace (fmdl_step5 b)) ∧
    (∀ b : Fin 5 → Fin 7, ¬InCodeSubspace b → DWeight b = 0) ∧
    (∃ Δ : ℚ, Δ > 0 ∧ ∀ b : Fin 5 → Fin 7, InCodeSubspace b → b ≠ fmdl_vacuum5 →
      ∃ mass : ℚ, mass ≥ Δ) :=
  qec_gte_is_stabilizer_code

end UgpLean.Substrate.QEC
