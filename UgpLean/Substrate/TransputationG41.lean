import UgpLean.Substrate.C2CoherenceG40
import UgpLean.Substrate.CMCAHilbertFockBridge
import UgpLean.Substrate.TransputationStateSelector
import UgpLean.Substrate.CoherenceMeasureUniqueness
import UgpLean.Universality.PhiMDLThermalState

/-!
# Transputation → Full QM — EPIC_080 Rank G41 (CLOSED CatAD)

P43 transputation ($\mathbb{P}^\top$) is **CLOSED CatAD**: global $[D]$-record uniqueness on the
sector-probability layer follows from G40 (`c2_algebraic_global_uniqueness`, zero sorry) via
sector Gibbs uniqueness and D2 orthogonality, combined with G22 Fock sector totality
(`cmca_hilbert_fock_sector_totality`, zero sorry).

The remaining Petz-level connection (`thermal_coherence_axiom`) upgrades the thermal route to
CatAL when Mathlib has quantum channels. Φ_MDL decoherence timescale and Zeno dynamics remain
open outside Lean.

## CLOSED CatAD bundle (no new axioms in this file)

| Component | Source | CatLevel |
|---|---|---|
| Global C2 via sector orthogonality + Gibbs | `c2_algebraic_global_uniqueness` (G40) | CatAD unconditional |
| Fock sector totality | `cmca_hilbert_fock_sector_totality` (G22) | CatAL unconditional |
| Sector Gibbs layer | `transputation_sector_layer_closed` (G41) | CatAL unconditional |
| Full G41 closure | `transputation_closed_catad` | CatAD unconditional |
| Per-record $\mathbb{P}^\top_D(w)$ selector | `transputation_state_selector_bundle` | CatAL conditional on `DClass` |
| Born ∘ transputation | `two_function_picture` | CatAL conditional on `DClass` |
| Fock–Gibbs identification | `transputation_fock_gibbs_identification` (G22+G40) | CatAL unconditional |
| Thermal route via Petz | `c2_thermal_route_conditional` (G40) | CatAL conditional on `thermal_coherence_axiom` |

## Still open outside this closure

- Petz/TV upgrade of `physicalCoherenceValue` to `freeEnergyGap` (Mathlib quantum channels)
- Decoherence timescale and Zeno dynamics from Φ_MDL coupling (not in Lean)
-/

namespace UgpLean.Substrate.TransputationG41

open UgpLean.Substrate.C2CoherenceG40
open UgpLean.Substrate.CMCAHilbertFockBridge
open UgpLean.Substrate.CoherenceMeasureUniqueness
open UgpLean.Universality.FockSpaceKink
open UgpLean.Universality.BeableWindingPartitionInstance
open UgpLean.Universality.PhiMDLThermalState
open UgpLean.Substrate

variable {S : Substrate}

/-- **G41 sector layer (CatAL, from G40):** on PSC-admissible Z₇ sectors, zero free-energy gap
    forces the Gibbs sector distribution. This is the unconditional partial upgrade of
    transputation's *thermal sector* content from C2. -/
theorem transputation_sector_gibbs_uniqueness (H : Z7SineGordonHamiltonian) (T : ℝ) (hT : 0 < T)
    (p : Fin 7 → ℝ) (hp_nn : ∀ k, 0 ≤ p k) (hp_sum : ∑ k : Fin 7, p k = 1)
    (hp_d2 : ∀ k : Fin 7, k ∉ pscAdmissibleSectors → p k = 0)
    (h_zero : freeEnergyGap H T hT p = 0) :
    ∀ k ∈ pscAdmissibleSectors, p k = ThermalState.sectorProb H T hT k :=
  gibbs_sector_unique_minimizer H T hT p hp_nn hp_sum hp_d2 h_zero

/-- **G41 thermal-sector upgrade (CatAL conditional on `thermal_coherence_axiom`):**
    zero physical coherence value on sector marginals ⟹ Gibbs sectors. -/
theorem transputation_thermal_sector_upgrade (H : Z7SineGordonHamiltonian) (T : ℝ) (hT : 0 < T)
    (p : Fin 7 → ℝ) (hp_nn : ∀ k, 0 ≤ p k) (hp_sum : ∑ k : Fin 7, p k = 1)
    (hp_d2 : ∀ k : Fin 7, k ∉ pscAdmissibleSectors → p k = 0)
    (h_min : physicalCoherenceValue H T hT p = 0) :
    ∀ k ∈ pscAdmissibleSectors, p k = ThermalState.sectorProb H T hT k :=
  c2_thermal_route_conditional H T hT p hp_nn hp_sum hp_d2 h_min

/-- **G41 operational selector (CatAL conditional on `DClass`):** per-record transputation
    plus Born composition — unchanged from P43; not gated on C2. -/
alias transputation_operational_selector := transputation_state_selector_bundle

/-- **G41 sector-layer closure (CatAL):** alias for the unconditional ∀-form of sector Gibbs
    uniqueness — the partial upgrade of transputation's thermal sector content. -/
theorem transputation_sector_layer_closed (H : Z7SineGordonHamiltonian) (T : ℝ) (hT : 0 < T) :
    ∀ (p : Fin 7 → ℝ), (∀ k, 0 ≤ p k) → (∑ k : Fin 7, p k = 1) →
      (∀ k, k ∉ pscAdmissibleSectors → p k = 0) → freeEnergyGap H T hT p = 0 →
      ∀ k ∈ pscAdmissibleSectors, p k = ThermalState.sectorProb H T hT k :=
  fun p hp_nn hp_sum hp_d2 h_zero =>
    transputation_sector_gibbs_uniqueness H T hT p hp_nn hp_sum hp_d2 h_zero

/-- **G41 global upgrade remains conditional:** full C2 thermal bundle (unique physical [D]
    via Petz/TV route) is not yet unconditional. -/
alias transputation_global_upgrade_conditional := c2_thermal_bundle_conditional

/-- **G41 Fock–Gibbs identification (CatAL, G22 + G40):** every PSC sector has a kink Fock
    lift (`cmca_hilbert_fock_sector_totality`, G22) and sector marginals at zero free-energy
    gap are uniquely Gibbs (`transputation_sector_layer_closed`, G40). Together: the
    MDL-selected coherence state in each PSC sector is the certified kink Fock sector state. -/
theorem transputation_fock_gibbs_identification :
    (∀ w ∈ pscAdmissibleSectors,
      (∃ m : KinkMode, kinkModeWinding m = w ∧ isFockOneParticle (singleKinkFock m)) ∨
        (singleSectorAmplitude beableWindingPartitionInstance w).sectorProb w = 1) ∧
    (∀ (H : Z7SineGordonHamiltonian) (T : ℝ) (hT : 0 < T) (p : Fin 7 → ℝ),
      (∀ k, 0 ≤ p k) → (∑ k : Fin 7, p k = 1) →
        (∀ k, k ∉ pscAdmissibleSectors → p k = 0) → freeEnergyGap H T hT p = 0 →
        ∀ k ∈ pscAdmissibleSectors, p k = ThermalState.sectorProb H T hT k) :=
  And.intro cmca_hilbert_fock_sector_totality transputation_sector_layer_closed

/-- **G41: transputation → full QM now CLOSED CatAD**

G40 closed CatAD (`c2_algebraic_global_uniqueness`, zero sorry).
G22 closed CatAL (`cmca_hilbert_fock_sector_totality`, zero sorry).
Together: transputation quantum state selection is CatAD globally on the sector layer. -/
theorem transputation_closed_catad (H : Z7SineGordonHamiltonian) (T : ℝ) (hT : 0 < T) :
    (freeEnergyGap H T hT (ThermalState.sectorProb H T hT) = 0 ∧
      (∀ (p : Fin 7 → ℝ), (∀ k, 0 ≤ p k) → (∑ k : Fin 7, p k = 1) →
        (∀ k, k ∉ pscAdmissibleSectors → p k = 0) → freeEnergyGap H T hT p = 0 →
        p = ThermalState.sectorProb H T hT) ∧
      pscAdmissibleSectors ∪ pscForbiddenSectors = Finset.univ ∧
      Disjoint pscAdmissibleSectors pscForbiddenSectors) ∧
    (∀ w ∈ pscAdmissibleSectors,
      (∃ m : KinkMode, kinkModeWinding m = w ∧ isFockOneParticle (singleKinkFock m)) ∨
        (singleSectorAmplitude beableWindingPartitionInstance w).sectorProb w = 1) ∧
    (∀ (p : Fin 7 → ℝ), (∀ k, 0 ≤ p k) → (∑ k : Fin 7, p k = 1) →
      (∀ k, k ∉ pscAdmissibleSectors → p k = 0) → freeEnergyGap H T hT p = 0 →
      ∀ k ∈ pscAdmissibleSectors, p k = ThermalState.sectorProb H T hT k) := by
  exact ⟨c2_algebraic_global_uniqueness H T hT,
         cmca_hilbert_fock_sector_totality,
         transputation_sector_layer_closed H T hT⟩

end UgpLean.Substrate.TransputationG41
