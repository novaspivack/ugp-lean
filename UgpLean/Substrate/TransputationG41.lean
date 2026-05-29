import UgpLean.Substrate.C2CoherenceG40
import UgpLean.Substrate.CMCAHilbertFockBridge
import UgpLean.Substrate.TransputationStateSelector
import UgpLean.Substrate.CoherenceMeasureUniqueness
import UgpLean.Universality.PhiMDLThermalState

/-!
# Transputation → Full QM — EPIC_080 Rank G41 (Partial CatAL)

P43 transputation ($\mathbb{P}^\top$) is **CatAD** globally because Conjecture C2 (unique
physical $D \in [D]$) remains open. G40 closed the **sector-level** thermal route unconditionally:

`freeEnergyGap = 0` on PSC-admissible Z₇ sectors ⟹ Gibbs sector distribution.

This module records the **partial G41 upgrade**: transputation's *sector probability layer*
is CatAL at the Gibbs minimum; global $[D]$-class uniqueness and Φ_MDL decoherence dynamics
remain open (full QM pass criterion).

## CatAL today (no new axioms in this file)

| Component | Source | CatLevel |
|---|---|---|
| Per-record $\mathbb{P}^\top_D(w)$ selector | `transputation_state_selector_bundle` | CatAL conditional on `DClass` |
| Born ∘ transputation | `two_function_picture` | CatAL conditional on `DClass` |
| Z₇ sector Gibbs uniqueness | `gibbs_sector_unique_minimizer` (G40) | CatAL unconditional |
| Sector Gibbs under thermal route | `c2_thermal_route_conditional` (G40) | CatAL conditional on `thermal_coherence_axiom` |
| Fock–Gibbs identification | `transputation_fock_gibbs_identification` (G22+G40) | CatAL unconditional |

## Still CatAD / open for full G41

- Unique physical $D \in [D]$ (global C2; Petz/Mathlib or architectural route)
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
open GTE.Spacetime KinkQuantumNumbers

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

end UgpLean.Substrate.TransputationG41
