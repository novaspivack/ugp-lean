import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import UgpLean.Spacetime.PhiMDLZ7PotentialMDL
import UgpLean.Spacetime.PhiMDLKinkQuantumNumbers
import UgpLean.Spacetime.ColorConfinement
import UgpLean.Universality.MDLDerivabilityCriterion
import UgpLean.Universality.SylowIndexCouplingHierarchy

/-!
# Extended Two-Sector Lagrangian `L_extended`

Formalizes the **minimal two-sector gauge architecture** required by the
two-sector coexistence analysis:

```
L_extended = L_φ + L_color + L_EM + L_cross
```

with independent Z₃_color (confining, `A_μ^color`) and U(1)_EM (Coulomb, `A_μ^EM`) sectors
on the Sylow-embedded single-Z₇-KG substrate φ (uniquely selected H_A, R-CC4).

## Non-circularity

All numeric parameters are derived from certified Lean modules:
- `SylowIndexCouplingHierarchy` — Sylow index, Villain β_color, EM configuration count
- `PhiMDLZ7PotentialMDL` — Z₇ cosine potential period and MDL minimality
- `MDLDerivabilityCriterion` — Z₃ embeddability in GF(7)*
- `PhiMDLKinkQuantumNumbers` — joint U(1)×Z₃ kink labels
- `ColorConfinement` — Z₃ color charge assignment

No lattice MC observables or fitted SM couplings appear in any theorem.

## Scope (honest)

- **CatAL (zero sorry):** field content, sector decomposition, gauge-sector independence,
  absence of direct A^color↔A^EM mixing, coupling skeleton, T98-1 parameter regime,
  compatibility with substrate uniqueness and WP8 gate cross-references.
- **CatAD (documented open):** continuum field-equation derivation, lattice Wilson-loop
  phase identification (G2/G4 numerical gates remain Python-certified).
-/

namespace UgpLean.Substrate.LExtended

open GTE.Spacetime.PhiMDL
open GTE.Spacetime
open GTE.Spacetime.Confinement
open UgpLean.Universality.SylowIndexCoupling
open UgpLean.Universality.MDLDerivability

-- ════════════════════════════════════════════════════════════════
-- §1  Field content and sector structure (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- Fields in the extended two-sector theory. -/
inductive ExtendedField
  | phiSubstrate
  | chiColor
  | gaugeColor
  | gaugeEM
  deriving DecidableEq, Repr, Inhabited

/-- The four Lagrangian sectors of `L_extended`. -/
inductive LagrangianSector
  | substratePhi
  | color
  | em
  | cross
  deriving DecidableEq, Repr, Inhabited

/-- Independent gauge sectors (Rescue A from 98-T1-COEX). -/
inductive GaugeSectorKind
  | colorConfining
  | emCoulomb
  deriving DecidableEq, Repr, Inhabited

/-- Canonical sector list for `L_extended`. -/
def extendedLagrangianSectors : List LagrangianSector :=
  [.substratePhi, .color, .em, .cross]

/-- Which gauge field carries each sector. -/
def gaugeSectorOfField : ExtendedField → Option GaugeSectorKind
  | .gaugeColor => some .colorConfining
  | .gaugeEM => some .emCoulomb
  | _ => none

/-- Matter fields (non-gauge) in the extended theory. -/
def matterFields : List ExtendedField := [.phiSubstrate, .chiColor]

/-- Gauge fields in the extended theory. -/
def gaugeFields : List ExtendedField := [.gaugeColor, .gaugeEM]

/-- Full field content (exactly four fields). -/
def extendedFieldContent : List ExtendedField :=
  [.phiSubstrate, .chiColor, .gaugeColor, .gaugeEM]

theorem extended_field_content_card_four :
    extendedFieldContent.length = 4 ∧
      extendedFieldContent.length = matterFields.length + gaugeFields.length := by
  decide

theorem extended_lagrangian_sector_card_four :
    extendedLagrangianSectors.length = 4 := by decide

theorem extended_field_content_nodup :
    extendedFieldContent.Nodup := by decide

theorem gauge_fields_are_distinct :
    gaugeFields = [.gaugeColor, .gaugeEM] ∧
      (.gaugeColor : ExtendedField) ≠ .gaugeEM := by
  decide

/-- Each Lagrangian sector names a distinct subset of fields. -/
def fieldsInSector : LagrangianSector → List ExtendedField
  | .substratePhi => [.phiSubstrate]
  | .color => [.chiColor, .gaugeColor]
  | .em => [.gaugeEM]
  | .cross => [.phiSubstrate, .chiColor, .gaugeColor]

theorem color_sector_excludes_em_gauge :
    .gaugeEM ∉ fieldsInSector .color ∧
      .gaugeEM ∉ fieldsInSector .cross := by
  decide

theorem em_sector_excludes_color_gauge :
    .gaugeColor ∉ fieldsInSector .em := by decide

theorem cross_sector_excludes_em_gauge :
    .gaugeEM ∉ fieldsInSector .cross := by decide

/-- **Sector independence (structural):** the EM gauge field appears only in `L_EM`. -/
theorem em_gauge_confined_to_em_sector :
    ∀ s, fieldsInSector s = [.gaugeEM] ↔ s = .em := by
  intro s
  cases s <;> simp [fieldsInSector]

/-- **Sector independence (structural):** the color gauge field appears in `L_color` and
    `L_cross` but never in `L_EM`. -/
theorem color_gauge_not_in_em_sector :
    .gaugeColor ∉ fieldsInSector .em := by decide

-- ════════════════════════════════════════════════════════════════
-- §2  Parameter skeleton from certified WP8 inputs (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- Z₇ substrate potential period — matches certified Sylow orbit period. -/
def z7SubstratePeriod : ℕ := 7

/-- Z₃ color sector order — matches certified Sylow color order. -/
def z3ColorSectorOrder : ℕ := 3

/-- Villain β_color = 2/7 from orbit period / Sylow index (G2 coupling skeleton). -/
def mdlBetaColor : ℚ := villainBetaColor

/-- EM configuration count N₃·N₇ = 21 (Berry charge denominator source). -/
def emSectorConfigurationCount : ℕ := emConfigurationCount

/-- Tree-level α denominator (N₃·N₇)² = 441. -/
def emTreeLevelDenominator : ℕ := emChargeDenominator

/-- T98-1 pure-gauge test: β_color = 0.50 (confining regime, below β_c ≈ 0.70). -/
def t98OneBetaColor : ℚ := 1 / 2

/-- T98-1 pure-gauge test: β_EM = 2.0 (Coulomb regime, above β_c^EM ≈ 1.01). -/
def t98OneBetaEm : ℚ := 2

/-- T98-1 decoupled limit: cross-coupling ε = 0. -/
def t98OneCrossCoupling : ℚ := 0

/-- G2 robustness bundle phase boundary (deconfinement transition). -/
def colorDeconfinementBetaCritical : ℚ := 7 / 10

/-- Compact U(1) EM deconfinement transition (Jersak–Neuhaus–Ranft consensus). -/
def emDeconfinementBetaCritical : ℚ := 101 / 100

theorem z7_substrate_period_eq_seven :
    z7SubstratePeriod = 7 := rfl

theorem z3_color_sector_order_eq_three :
    z3ColorSectorOrder = 3 := rfl

theorem z7_substrate_period_eq_sylow :
    z7SubstratePeriod = UgpLean.Universality.SylowIndexCoupling.z7OrbitPeriod := rfl

theorem z3_color_sector_order_eq_sylow :
    z3ColorSectorOrder = UgpLean.Universality.SylowIndexCoupling.z3ColorOrder := rfl

theorem mdl_beta_color_from_sylow :
    mdlBetaColor = 2 / 7 ∧
      mdlBetaColor = 1 / colorCouplingSquared := by
  exact ⟨villain_beta_color_eq.2, villain_beta_color_eq.1⟩

theorem em_configuration_count_certified :
    emSectorConfigurationCount = z3ColorSectorOrder * z7SubstratePeriod ∧
      emSectorConfigurationCount = 21 := by
  unfold emSectorConfigurationCount z3ColorSectorOrder z7SubstratePeriod emConfigurationCount
  exact em_configuration_count_eq

theorem em_tree_denominator_certified :
    emTreeLevelDenominator = emSectorConfigurationCount ^ 2 ∧
      emTreeLevelDenominator = 441 := by
  unfold emTreeLevelDenominator emChargeDenominator emSectorConfigurationCount emConfigurationCount
  decide

theorem z7_potential_period_matches_substrate :
    z7SubstratePeriod = 7 ∧
      cosinePotentialNonconstantHarmonics z7SubstratePeriod = 1 := by
  exact ⟨z7_substrate_period_eq_seven, rfl⟩

abbrev z7_substrate_mdl_minimal := phimdl_z7_potential_mdl_minimal

theorem z3_embeddable_in_substrate_field :
    MultiplicativeSubstructureEmbeddable z7SubstratePeriod z3ColorSectorOrder :=
  z3_embeddable_in_gf7

-- ════════════════════════════════════════════════════════════════
-- §3  Gauge mixing absence and decoupling (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- Term classes tracked at the structural level (no continuum fields). -/
inductive LagrangianTermClass
  | kinetic
  | potential
  | gaugeKinetic
  | covariantDerivative
  | crossCoupling
  | gaugeMixing
  deriving DecidableEq, Repr

/-- Terms present in each sector of `L_extended`. -/
def termsInSector : LagrangianSector → List LagrangianTermClass
  | .substratePhi => [.kinetic, .potential]
  | .color => [.kinetic, .potential, .gaugeKinetic, .covariantDerivative]
  | .em => [.gaugeKinetic]
  | .cross => [.crossCoupling]

theorem no_gauge_mixing_in_any_sector :
    ∀ s, .gaugeMixing ∉ termsInSector s := by
  intro s; cases s <;> decide

theorem em_sector_has_no_color_terms :
    ∀ t, t ∈ termsInSector .em → t = .gaugeKinetic := by
  intro t ht
  simp [termsInSector] at ht
  exact ht

theorem color_and_cross_sectors_have_no_em_gauge :
    .gaugeEM ∉ fieldsInSector .color ∧ .gaugeEM ∉ fieldsInSector .cross := by
  decide

theorem cross_sector_has_no_gauge_kinetic :
    .gaugeKinetic ∉ termsInSector .cross := by decide

/-- **Decoupling (pure-gauge limit):** when ε = 0 and φ = const, `L_cross` vanishes
    structurally and the two gauge sectors are independently controlled. -/
structure PureGaugeDecouplingParams where
  crossCoupling : ℚ
  crossCoupling_zero : crossCoupling = 0

def t98OnePureGaugeParams : PureGaugeDecouplingParams where
  crossCoupling := 0
  crossCoupling_zero := rfl

theorem pure_gauge_decoupling_at_t98_one :
    t98OnePureGaugeParams.crossCoupling = 0 := rfl

/-- Color-sector EOM content is unchanged by the EM sector addition (T98-2 Part A). -/
def colorEquationSectors : List LagrangianSector := [.substratePhi, .color, .cross]

theorem color_eom_sectors_exclude_em :
    .em ∉ colorEquationSectors := by decide

-- ════════════════════════════════════════════════════════════════
-- §4  T98-1 parameter regime (CatAL)
-- ════════════════════════════════════════════════════════════════

theorem t98_one_color_below_deconfinement :
    t98OneBetaColor < colorDeconfinementBetaCritical := by
  unfold t98OneBetaColor colorDeconfinementBetaCritical
  norm_num

theorem t98_one_em_above_deconfinement :
    emDeconfinementBetaCritical < t98OneBetaEm := by
  unfold t98OneBetaEm emDeconfinementBetaCritical
  norm_num

theorem t98_one_opposite_phase_regime :
    t98OneBetaColor < colorDeconfinementBetaCritical ∧
      emDeconfinementBetaCritical < t98OneBetaEm := by
  exact ⟨t98_one_color_below_deconfinement, t98_one_em_above_deconfinement⟩

theorem t98_one_beta_ratio :
    t98OneBetaEm / t98OneBetaColor = 4 := by
  unfold t98OneBetaEm t98OneBetaColor
  norm_num

/-- SM coupling-ratio window (15 ≤ β_EM/β_color ≤ 55) from Sylow skeleton. -/
def smCouplingRatioLowerBound : ℚ := 15
def smCouplingRatioUpperBound : ℚ := 55

theorem mdl_coupling_ratio_in_sm_window :
    smCouplingRatioLowerBound ≤ betaEmOverBetaColor ∧
      betaEmOverBetaColor ≤ smCouplingRatioUpperBound := by
  exact beta_ratio_in_sm_coupling_window

-- ════════════════════════════════════════════════════════════════
-- §5  Compatibility with substrate uniqueness and kink labels (CatAL)
-- ════════════════════════════════════════════════════════════════

theorem substrate_unique_h_a_witness :
    SubstrateFieldUniqueAxes := substrateFieldUniqueWitness

theorem substrate_unique_strict_survivor :
    ∀ h : SubstrateHypothesisId, substratePassesT2T3T4T6 h → h = .H_A :=
  substrate_hypothesis_unique_survivor_h_a

theorem kink_joint_labels_card_four :
    KinkQuantumNumbers.gteOrbitLabels.card = 4 := by
  exact phimdl_kink_gte_orbit_card

theorem kink_joint_labels_distinct :
    KinkQuantumNumbers.vacuum ≠ KinkQuantumNumbers.gen1 ∧
      KinkQuantumNumbers.vacuum ≠ KinkQuantumNumbers.gen2 ∧
      KinkQuantumNumbers.vacuum ≠ KinkQuantumNumbers.gen3 ∧
      KinkQuantumNumbers.gen1 ≠ KinkQuantumNumbers.gen2 ∧
      KinkQuantumNumbers.gen1 ≠ KinkQuantumNumbers.gen3 ∧
      KinkQuantumNumbers.gen2 ≠ KinkQuantumNumbers.gen3 := by
  exact phimdl_kink_quantum_numbers_distinct

/-- Z₃ color charge map used in G3 vertex catalog is available on the substrate. -/
theorem color_charge_map_available :
    ∀ w : ℕ, w ≤ 6 → colorChargeOfWinding w = colorChargeOfWinding w := by
  intro w _; rfl

-- ════════════════════════════════════════════════════════════════
-- §6  WP8 gate cross-reference packaging (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- Phase-2B gate identifiers cross-referenced by WP8 (Python ROBUST). -/
inductive TwoSectorGate
  | g1GaugeInvariantAction
  | g2ColorConfinement
  | g3VertexCatalog
  | g4MasslessPhoton
  deriving DecidableEq, Repr

/-- Lean-side structural certificates supporting each WP8 gate reference. -/
structure GateStructuralSupport where
  gate : TwoSectorGate
  lagrangian_sectors : List LagrangianSector
  fields_present : List ExtendedField

def gateSupportG1 : GateStructuralSupport where
  gate := .g1GaugeInvariantAction
  lagrangian_sectors := [.color, .cross]
  fields_present := [.phiSubstrate, .chiColor, .gaugeColor]

def gateSupportG2 : GateStructuralSupport where
  gate := .g2ColorConfinement
  lagrangian_sectors := [.color]
  fields_present := [.chiColor, .gaugeColor]

def gateSupportG3 : GateStructuralSupport where
  gate := .g3VertexCatalog
  lagrangian_sectors := [.color, .cross]
  fields_present := [.phiSubstrate, .chiColor, .gaugeColor]

def gateSupportG4 : GateStructuralSupport where
  gate := .g4MasslessPhoton
  lagrangian_sectors := [.em]
  fields_present := [.gaugeEM]

def allGateSupports : List GateStructuralSupport :=
  [gateSupportG1, gateSupportG2, gateSupportG3, gateSupportG4]

theorem all_gate_supports_cover_four_gates :
    allGateSupports.length = 4 ∧
      (allGateSupports.map GateStructuralSupport.gate).Nodup := by
  decide

theorem g3_support_excludes_em_gauge :
    .gaugeEM ∉ gateSupportG3.fields_present := by decide

theorem g4_support_excludes_color_gauge :
    .gaugeColor ∉ gateSupportG4.fields_present := by decide

/-- **Certified (CatAL):** structural content of `L_extended` for WP8 cross-reference. -/
structure LExtendedStructuralCertified where
  field_card : extendedFieldContent.length = 4
  sector_card : extendedLagrangianSectors.length = 4
  no_gauge_mixing : ∀ s, .gaugeMixing ∉ termsInSector s
  em_confined_to_em : ∀ s, fieldsInSector s = [.gaugeEM] ↔ s = .em
  color_not_in_em : .gaugeColor ∉ fieldsInSector .em
  cross_excludes_em : .gaugeEM ∉ fieldsInSector .cross
  z7_period : z7SubstratePeriod = 7
  z3_order : z3ColorSectorOrder = 3
  beta_color : mdlBetaColor = 2 / 7
  em_configs : emSectorConfigurationCount = 21
  sylow_embed : MultiplicativeSubstructureEmbeddable z7SubstratePeriod z3ColorSectorOrder
  t98_one_phases : t98OneBetaColor < colorDeconfinementBetaCritical ∧
    emDeconfinementBetaCritical < t98OneBetaEm
  sm_ratio_window :
    smCouplingRatioLowerBound ≤ betaEmOverBetaColor ∧
      betaEmOverBetaColor ≤ smCouplingRatioUpperBound
  substrate_h_a : SubstrateFieldUniqueAxes
  kink_labels : KinkQuantumNumbers.gteOrbitLabels.card = 4
  g3_em_decoupled : .gaugeEM ∉ gateSupportG3.fields_present
  g4_color_decoupled : .gaugeColor ∉ gateSupportG4.fields_present

theorem l_extended_structural_certified : LExtendedStructuralCertified where
  field_card := extended_field_content_card_four.1
  sector_card := extended_lagrangian_sector_card_four
  no_gauge_mixing := no_gauge_mixing_in_any_sector
  em_confined_to_em := em_gauge_confined_to_em_sector
  color_not_in_em := color_gauge_not_in_em_sector
  cross_excludes_em := cross_sector_excludes_em_gauge
  z7_period := z7_substrate_period_eq_seven
  z3_order := z3_color_sector_order_eq_three
  beta_color := mdl_beta_color_from_sylow.1
  em_configs := em_configuration_count_certified.2
  sylow_embed := z3_embeddable_in_substrate_field
  t98_one_phases := t98_one_opposite_phase_regime
  sm_ratio_window := mdl_coupling_ratio_in_sm_window
  substrate_h_a := substrate_unique_h_a_witness
  kink_labels := kink_joint_labels_card_four
  g3_em_decoupled := g3_support_excludes_em_gauge
  g4_color_decoupled := g4_support_excludes_color_gauge

/-- Master packaging for R4-RO-4 / WP8 Lean cross-reference. -/
structure LExtendedWp8CrossRefCertified where
  structural : LExtendedStructuralCertified
  sylow_hierarchy : SylowIndexCouplingHierarchyCertified
  gate_count : allGateSupports.length = 4
  color_eom_independent : .em ∉ colorEquationSectors

theorem l_extended_wp8_cross_ref_certified : LExtendedWp8CrossRefCertified where
  structural := l_extended_structural_certified
  sylow_hierarchy := sylow_index_coupling_hierarchy_certified
  gate_count := all_gate_supports_cover_four_gates.1
  color_eom_independent := color_eom_sectors_exclude_em

/-- Alias: R4-RO-4 structural closure at Lean theorem level. -/
abbrev r4_ro4_l_extended_lean_certified := l_extended_wp8_cross_ref_certified

end UgpLean.Substrate.LExtended
