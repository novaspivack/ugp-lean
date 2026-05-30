import UgpLean.Substrate.CoherenceMeasureUniqueness
import UgpLean.Substrate.CMCAHilbertFockBridge
import UgpLean.Substrate.PSCStructureLorentzPreserved
import UgpLean.Universality.Z7ChargeConjugation

/-!
# C2 Coherence Uniqueness — EPIC_080 Rank G40

Thin re-export layer documenting what is certified today for P43 C2 / P34 Conjecture C2.

Full proofs live in `CoherenceMeasureUniqueness.lean` (zero sorry, 2 physics axioms)
and `GUTStructure.DUniqueness` (MDL finite-minimum scaffold).

## G40 status: CLOSED CatAD (2026-05-29)

**Algebraic global route (zero sorry, no Petz):**
- `gibbs_sector_unique_minimizer` — sector-level KL = 0 ⟹ Gibbs (CatAL)
- `c2_free_energy_zero_global_gibbs` — lifts to full `Fin 7` vector equality (CatAL)
- `c2_global_from_sector_uniqueness` — bundles G22 sector totality + PSC partition + global Gibbs

**Full CatAL via Petz/TV:** `thermal_coherence_axiom` bridges `physicalCoherenceValue` to
`freeEnergyGap`; remains conditional pending Mathlib Petz recovery (CatD residual).
-/

namespace UgpLean.Substrate.C2CoherenceG40

open Z7ChargeConjugation
open CUP3D
open UgpLean.Universality.PhiMDLThermalState
open PSCStructureLorentzPreserved
open UgpLean.Substrate (DClass)
open UgpLean.Substrate.CMCAHilbertFockBridge
open UgpLean.Substrate.CoherenceMeasureUniqueness
open UgpLean.Universality.FockSpaceKink
open UgpLean.Universality.BeableWindingPartitionInstance

/-- **G40 (CatAL):** MDL + five [D]-constraint arithmetic scaffold for C2. -/
alias c2_coherence_mdl_scaffold := GUTStructure.DUniqueness.d_uniqueness_master

/-- **G40 (CatAL):** Lorentz and CPT equivariance of [D] follow from D2 on Φ_MDL. -/
alias c2_coherence_lorentz_cpt_from_d2 := CoherenceMeasureUniqueness.lorentz_cpt_implicit_in_d2

/-- **G40 (CatAL):** six abstract [D] candidates are pairwise distinguishable (existence). -/
theorem c2_coherence_distinguishability :
    ∃ c1 c2 : CoherenceMeasureUniqueness.C2Candidate, c1 ≠ c2 ∧
      ∃ k : Fin 7, CoherenceMeasureUniqueness.c2SectorMarginal c1 k ≠
        CoherenceMeasureUniqueness.c2SectorMarginal c2 k :=
  CoherenceMeasureUniqueness.c2_distinguishability.1

/-- **G40 Z₇ MDL (CatAL):** unique MDL-minimal orbit-admissible `f_MDL` on `Fin 7³`. -/
theorem mdl_fmdl_unique_minimizer_z7
    (f : Fin 7 → Fin 7 → Fin 7 → Fin 7)
    (h_fixed : ∀ l c r : Fin 7, isFixedNeighborhood l c r → f l c r = fmdl l c r)
    (h_free : ∀ l c r : Fin 7, ¬isFixedNeighborhood l c r → f l c r = 0) :
    f = fmdl :=
  fmdl_mdl_uniqueness f h_fixed h_free

/-- **G40 sector Gibbs (CatAL):** unique `freeEnergyGap = 0` minimizer = Gibbs sectors. -/
theorem gibbs_sector_unique_minimizer (H : Z7SineGordonHamiltonian) (T : ℝ) (hT : 0 < T)
    (p : Fin 7 → ℝ) (hp_nn : ∀ k, 0 ≤ p k) (hp_sum : ∑ k : Fin 7, p k = 1)
    (hp_d2 : ∀ k : Fin 7, k ∉ pscAdmissibleSectors → p k = 0)
    (h_zero : CoherenceMeasureUniqueness.freeEnergyGap H T hT p = 0) :
    ∀ k ∈ pscAdmissibleSectors, p k = ThermalState.sectorProb H T hT k :=
  CoherenceMeasureUniqueness.freeEnergyGap_zero_iff_gibbs H T hT p hp_nn hp_sum hp_d2 h_zero

/-- **G40 global Gibbs (CatAL, algebraic — no Petz):** zero free-energy gap determines the
    full D2-admissible sector probability vector uniquely. -/
theorem c2_free_energy_zero_global_gibbs (H : Z7SineGordonHamiltonian) (T : ℝ) (hT : 0 < T)
    (p : Fin 7 → ℝ) (hp_nn : ∀ k, 0 ≤ p k) (hp_sum : ∑ k : Fin 7, p k = 1)
    (hp_d2 : ∀ k : Fin 7, k ∉ pscAdmissibleSectors → p k = 0)
    (h_zero : CoherenceMeasureUniqueness.freeEnergyGap H T hT p = 0) :
    p = ThermalState.sectorProb H T hT :=
  CoherenceMeasureUniqueness.c2_free_energy_zero_global_gibbs_ext H T hT p hp_nn hp_sum hp_d2 h_zero

/-- **G40 algebraic global C2 (CatAD):** on the Z₇ sector-probability layer, the Gibbs state
    is the unique zero of `freeEnergyGap`. D2 partitions `{0,2,3,4,6}` vs `{1,5}`; sector
    KL uniqueness lifts to global vector equality without Petz recovery. -/
theorem c2_algebraic_global_uniqueness (H : Z7SineGordonHamiltonian) (T : ℝ) (hT : 0 < T) :
    freeEnergyGap H T hT (ThermalState.sectorProb H T hT) = 0 ∧
    (∀ (p : Fin 7 → ℝ), (∀ k, 0 ≤ p k) → (∑ k : Fin 7, p k = 1) →
      (∀ k, k ∉ pscAdmissibleSectors → p k = 0) → freeEnergyGap H T hT p = 0 →
      p = ThermalState.sectorProb H T hT) ∧
    pscAdmissibleSectors ∪ pscForbiddenSectors = Finset.univ ∧
    Disjoint pscAdmissibleSectors pscForbiddenSectors := by
  refine ⟨freeEnergyGap_gibbs_zero H T hT, ?_, psc_sectors_partition.1, psc_sectors_partition.2⟩
  intro p hp_nn hp_sum hp_d2 h_zero
  exact c2_free_energy_zero_global_gibbs H T hT p hp_nn hp_sum hp_d2 h_zero

/-- **G40 global from sector orthogonality (CatAD):** G22 Fock sector totality + PSC sector
    partition + global Gibbs uniqueness. Born marginals on orthogonal PSC sectors fix the
    sector probability vector; `freeEnergyGap = 0` selects Gibbs uniquely. No Petz. -/
theorem c2_global_from_sector_uniqueness (H : Z7SineGordonHamiltonian) (T : ℝ) (hT : 0 < T) :
    (∀ w (hw : w ∈ pscAdmissibleSectors),
      (∃ m : KinkMode, kinkModeWinding m = w ∧ isFockOneParticle (singleKinkFock m)) ∨
        (singleSectorAmplitude beableWindingPartitionInstance w).sectorProb w = 1) ∧
    (∀ (p : Fin 7 → ℝ), (∀ k, 0 ≤ p k) → (∑ k : Fin 7, p k = 1) →
      (∀ k, k ∉ pscAdmissibleSectors → p k = 0) → freeEnergyGap H T hT p = 0 →
      ∀ k ∈ pscAdmissibleSectors, p k = ThermalState.sectorProb H T hT k) ∧
    (∀ (p : Fin 7 → ℝ), (∀ k, 0 ≤ p k) → (∑ k : Fin 7, p k = 1) →
      (∀ k, k ∉ pscAdmissibleSectors → p k = 0) → freeEnergyGap H T hT p = 0 →
      p = ThermalState.sectorProb H T hT) ∧
    pscAdmissibleSectors ∪ pscForbiddenSectors = Finset.univ ∧
    Disjoint pscAdmissibleSectors pscForbiddenSectors := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · intro w hw; exact cmca_hilbert_fock_sector_totality w hw
  · intro p hp_nn hp_sum hp_d2 h_zero k hk
    exact gibbs_sector_unique_minimizer H T hT p hp_nn hp_sum hp_d2 h_zero k hk
  · intro p hp_nn hp_sum hp_d2 h_zero
    exact c2_free_energy_zero_global_gibbs H T hT p hp_nn hp_sum hp_d2 h_zero
  · exact psc_sectors_partition.1
  · exact psc_sectors_partition.2

/-- **G40 thermal route (CatAL conditional on `thermal_coherence_axiom`). -/
theorem c2_thermal_route_conditional (H : Z7SineGordonHamiltonian) (T : ℝ) (hT : 0 < T)
    (p : Fin 7 → ℝ) (hp_nn : ∀ k, 0 ≤ p k) (hp_sum : ∑ k : Fin 7, p k = 1)
    (hp_d2 : ∀ k : Fin 7, k ∉ pscAdmissibleSectors → p k = 0)
    (h_min : CoherenceMeasureUniqueness.physicalCoherenceValue H T hT p = 0) :
    ∀ k ∈ pscAdmissibleSectors, p k = ThermalState.sectorProb H T hT k :=
  CoherenceMeasureUniqueness.c2_gibbs_unique_minimum H T hT p hp_nn hp_sum hp_d2 h_min

/-- **G40 thermal route global (CatAL conditional on `thermal_coherence_axiom`). -/
theorem c2_thermal_route_global_conditional (H : Z7SineGordonHamiltonian) (T : ℝ) (hT : 0 < T)
    (p : Fin 7 → ℝ) (hp_nn : ∀ k, 0 ≤ p k) (hp_sum : ∑ k : Fin 7, p k = 1)
    (hp_d2 : ∀ k : Fin 7, k ∉ pscAdmissibleSectors → p k = 0)
    (h_min : CoherenceMeasureUniqueness.physicalCoherenceValue H T hT p = 0) :
    p = ThermalState.sectorProb H T hT := by
  have h_fe : freeEnergyGap H T hT p = 0 := by
    rw [← thermal_coherence_axiom H T hT p hp_nn hp_sum hp_d2]; exact h_min
  exact c2_free_energy_zero_global_gibbs H T hT p hp_nn hp_sum hp_d2 h_fe

/-- **G40 architectural route (CatAL conditional on `architectural_restriction`). -/
alias c2_architectural_route_conditional :=
  CoherenceMeasureUniqueness.c2_uniqueness_structural_bundle

/-- **G40 thermal bundle (CatAL conditional on `thermal_coherence_axiom`). -/
alias c2_thermal_bundle_conditional := CoherenceMeasureUniqueness.c2_thermal_closure_bundle

end UgpLean.Substrate.C2CoherenceG40
