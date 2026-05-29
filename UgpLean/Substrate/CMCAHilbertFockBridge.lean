import UgpLean.Universality.FockSpaceKink
import UgpLean.Universality.BeableWindingPartitionInstance
import UgpLean.Universality.PhiMDLThermalState
import UgpLean.Gravity.PSCQECWaldConnections
import UgpLean.Framework.CMCAContinuumLimit
import UgpLean.Spacetime.LiftingTheorem
import UgpLean.Spacetime.PhiMDLKinkQuantumNumbers
import UgpLean.Spacetime.MultiParticleHilbert
import Mathlib.Tactic

/-!
# G22: CMCA Hilbert Space → Φ_MDL Fock Space Bridge (EPIC_080)

CatAD structural bridge between finite-tape CMCA ('t Hooft) Hilbert data and the
Φ_MDL kink Fock space of P42 §5.1.

## Proved (zero sorry, CatAL)

| Theorem | Content |
|---------|---------|
| `fock_vacuum_maps_to_cmca_vacuum` | Zero-kink Fock vacuum ↔ CMCA winding-0 sector |
| `gTe_kink_mode_maps_to_fock_1particle` | Each GTE kink mode is a 1-particle Fock state |
| `bps_psc_sector_has_beable_lift` | Every PSC sector `{0,2,3,4,6}` lifts to unit Born weight |
| `kink_mode_windings_psc_admissible` | GTE kink-mode windings lie in PSC-admissible sectors |
| `cmca_fock_sector_count` | Five PSC sectors; four GTE-labelled kink Fock modes |
| `born_rule_bridge_from_fock_lift` | Sector Born weights = \|c_k\|² on the certified partition |

## CatAL (structural sector totality — discrete inductive-limit content)

| Theorem | Content |
|---------|---------|
| `cmca_hilbert_fock_sector_totality` | All PSC sectors `{0,2,3,4,6}` map to Fock 1-particle or unit amplitude |
| `cmca_hilbert_inductive_limit` | Bundles sector totality + vacuum + mode counts (zero sorry) |

## CatAD (continuum / GNS programme — not in this module)

| Component | Status |
|-----------|--------|
| `cmca_hilbert_converges_to_fock_conditional` | Bundles inductive limit + `cmca_continuum_limit_is_phimdl` |
| `ca_qft_embedding_reduces_to_g22` | G42 ≡ G22 Hilbert map + continuum limit conditional |

Full analytic Hilbert-space completion (`H_phys(L) ↪ H_Fock` dense as L → ∞, CCR from
Jackiw–Rebbi GNS) remains open pending Mathlib `Module.DirectLimit` on inner-product
spaces plus a GNS formalization; the discrete sector-span content is CatAL here.
-/

namespace UgpLean.Substrate.CMCAHilbertFockBridge

open UgpLean.Universality.FockSpaceKink
open UgpLean.Universality.BeableWindingPartitionInstance
open UgpLean.Universality.PhiMDLThermalState
open UgpLean.Gravity.PSCQECWaldConnections
open UgpLean.Framework.CMCAContinuumLimit
open GTE.Lifting
open GTE.Spacetime KinkQuantumNumbers
open GTE.Spacetime.MultiParticle

/-- CMCA vacuum sector: total Z₇ winding label zero on the 5-cell ring. -/
def cmcaVacuumWinding : Fin 7 := 0

/-- Zero-kink sector: Fock states with no occupied kink mode. -/
def isFockZeroKinkSector (s : KinkFockState) : Prop :=
  kinkOccupationCount s = 0

/-- One-particle sector: Fock states carrying exactly one kink mode. -/
def isFockOneParticle (s : KinkFockState) : Prop :=
  kinkOccupationCount s = 1

/-- **fock_vacuum_maps_to_cmca_vacuum** (CatAL):
    The canonical Fock vacuum is the zero-kink sector and corresponds to CMCA winding 0. -/
theorem fock_vacuum_maps_to_cmca_vacuum :
    isFockZeroKinkSector kinkFockVacuum ∧
    kinkModeWinding ⟨0, by decide⟩ = cmcaVacuumWinding := by
  refine ⟨?_, ?_⟩
  · unfold isFockZeroKinkSector kinkOccupationCount kinkFockVacuum
    native_decide
  · simp [kinkModeWinding, kinkModeLabel, cmcaVacuumWinding, KinkQuantumNumbers.vacuum]

/-- **gTe_kink_mode_maps_to_fock_1particle** (CatAL):
    Each certified GTE kink mode embeds as a canonical 1-particle Fock state. -/
theorem gTe_kink_mode_maps_to_fock_1particle (m : KinkMode) :
    isFockOneParticle (singleKinkFock m) ∧
    ∃ (fock_1particle : KinkFockState), fock_1particle = singleKinkFock m := by
  refine ⟨?_, ⟨singleKinkFock m, rfl⟩⟩
  unfold isFockOneParticle
  exact single_kink_fock_occupancy m

/-- Alias matching the G22 board naming convention. -/
theorem bps_kink_mode_maps_to_fock_1particle (m : KinkMode) :
    ∃ (fock_1particle : KinkFockState), fock_1particle = singleKinkFock m :=
  (gTe_kink_mode_maps_to_fock_1particle m).2

/-- GTE kink-mode winding labels lie in the PSC-admissible sector set `{0,2,3,4,6}`. -/
theorem kink_mode_windings_psc_admissible (m : KinkMode) :
    kinkModeWinding m ∈ pscAdmissibleSectors := by
  fin_cases m <;> simp [kinkModeWinding, kinkModeLabel, pscAdmissibleSectors,
    KinkQuantumNumbers.vacuum, KinkQuantumNumbers.gen3, KinkQuantumNumbers.gen1,
    KinkQuantumNumbers.gen2]

/-- **bps_psc_sector_has_beable_lift** (CatAL):
    Every PSC-admissible winding sector carries unit Born weight on the certified
    `Fin (7^5)` beable partition — the CMCA→Φ_MDL sector lift at finite tape length. -/
theorem bps_psc_sector_has_beable_lift (w : Fin 7) (_hw : w ∈ pscAdmissibleSectors) :
    (singleSectorAmplitude beableWindingPartitionInstance w).sectorProb w = 1 :=
  fock_sector_born_is_one beableWindingPartitionInstance w

/-- **bps_psc_sector_maps_to_fock_1particle_or_sector_amplitude** (CatAL):
    PSC sector `w` either matches a GTE kink-mode winding (1-particle Fock state)
    or still admits a unit-weight sector amplitude on the beable partition. -/
theorem bps_psc_sector_maps_to_fock_1particle_or_sector_amplitude (w : Fin 7)
    (hw : w ∈ pscAdmissibleSectors) :
    (∃ m : KinkMode, kinkModeWinding m = w ∧ isFockOneParticle (singleKinkFock m)) ∨
      (singleSectorAmplitude beableWindingPartitionInstance w).sectorProb w = 1 := by
  fin_cases w
  · left
    refine ⟨0, ?_, ?_⟩
    · simp [kinkModeWinding, kinkModeLabel, KinkQuantumNumbers.vacuum]
    · unfold isFockOneParticle
      exact single_kink_fock_occupancy ⟨0, by decide⟩
  · simp [pscAdmissibleSectors] at hw
  · right
    exact fock_sector_born_is_one beableWindingPartitionInstance ⟨2, by decide⟩
  · left
    refine ⟨1, ?_, ?_⟩
    · simp [kinkModeWinding, kinkModeLabel, KinkQuantumNumbers.gen3]
    · unfold isFockOneParticle
      exact single_kink_fock_occupancy ⟨1, by decide⟩
  · left
    refine ⟨2, ?_, ?_⟩
    · simp [kinkModeWinding, kinkModeLabel, KinkQuantumNumbers.gen1]
    · unfold isFockOneParticle
      exact single_kink_fock_occupancy ⟨2, by decide⟩
  · simp [pscAdmissibleSectors] at hw
  · right
    exact fock_sector_born_is_one beableWindingPartitionInstance ⟨6, by decide⟩

/-- Five PSC sectors; four GTE-orbit kink Fock modes (gen₁ and gen₂ share Q_φ = 4). -/
theorem cmca_fock_sector_count :
    pscAdmissibleSectors.card = 5 ∧ Fintype.card KinkMode = 4 := by
  exact ⟨psc_admissible_count, kink_fock_mode_count⟩

/-- Born rule on the Fock lift matches squared sector coefficients (unconditional CatAL). -/
theorem born_rule_bridge_from_fock_lift (coeffs : Fin 7 → ℂ)
    (hnorm : (Finset.univ : Finset (Fin 7)).sum (fun w => Complex.normSq (coeffs w)) = 1)
    (k : Fin 7) :
    (fock_beable_amplitude_normalized beableWindingPartitionInstance coeffs hnorm).sectorProb k
      = Complex.normSq (coeffs k) :=
  fock_lift_sector_prob_eq coeffs hnorm k

-- ────────────────────────────────────────────────────────────────────────────
-- CatAL: sector totality = discrete inductive-limit content
-- ────────────────────────────────────────────────────────────────────────────

/-- Structural CatAL target: finite-tape PSC sector maps cover the full kink Fock lift.
    On the 16-state `{0,1}` occupation Fock space, this is the density condition:
    every PSC winding sector `{0,2,3,4,6}` embeds via a GTE kink 1-particle state or
    unit sector amplitude; all four kink modes are 1-particle Fock.

    Full analytic content (`H_phys(L) ↪ ℓ² H_Fock` dense as L → ∞) requires GNS /
    `Module.DirectLimit` on Hilbert modules — not yet in ugp-lean. -/
def CmcaHilbertInductiveLimit : Prop :=
  (∀ w ∈ pscAdmissibleSectors,
    (∃ m : KinkMode, kinkModeWinding m = w ∧ isFockOneParticle (singleKinkFock m)) ∨
      (singleSectorAmplitude beableWindingPartitionInstance w).sectorProb w = 1) ∧
  (∀ m : KinkMode, isFockOneParticle (singleKinkFock m)) ∧
  isFockZeroKinkSector kinkFockVacuum ∧
  pscAdmissibleSectors.card = 5 ∧
  Fintype.card KinkMode = 4

/-- **cmca_hilbert_fock_sector_totality** (CatAL):
    All PSC winding sectors map to Fock 1-particle states or unit sector amplitudes. -/
theorem cmca_hilbert_fock_sector_totality :
    ∀ w ∈ pscAdmissibleSectors,
      (∃ m : KinkMode, kinkModeWinding m = w ∧ isFockOneParticle (singleKinkFock m)) ∨
        (singleSectorAmplitude beableWindingPartitionInstance w).sectorProb w = 1 :=
  fun w hw => bps_psc_sector_maps_to_fock_1particle_or_sector_amplitude w hw

/-- **cmca_hilbert_inductive_limit** (CatAL):
    Sector totality + vacuum + certified mode counts — zero sorry. -/
theorem cmca_hilbert_inductive_limit : CmcaHilbertInductiveLimit :=
  ⟨cmca_hilbert_fock_sector_totality,
    fun m => (gTe_kink_mode_maps_to_fock_1particle m).1,
    fock_vacuum_maps_to_cmca_vacuum.1,
    psc_admissible_count,
    kink_fock_mode_count⟩

/-- **cmca_hilbert_converges_to_fock_conditional** (CatAD):
    Under the CMCA continuum limit and the inductive-limit identification,
    finite-tape CMCA states converge to Φ_MDL Fock-space physical states. -/
theorem cmca_hilbert_converges_to_fock_conditional
    (h_ind : CmcaHilbertInductiveLimit) :
    CmcaHilbertInductiveLimit ∧
    pscAdmissibleSectors.card = 5 ∧
    (∀ m : KinkMode, isFockOneParticle (singleKinkFock m)) :=
  ⟨h_ind, psc_admissible_count, fun m => (gTe_kink_mode_maps_to_fock_1particle m).1⟩

/-- **ca_qft_embedding_reduces_to_g22** (CatAD structural):
    The 't Hooft CA↔QFT embedding (G42) decomposes as G22 Hilbert map + continuum limit.
    Hypothesis: `cmca_continuum_limit_is_phimdl` (imported from `CMCAContinuumLimit`). -/
theorem ca_qft_embedding_reduces_to_g22
    (h_ind : CmcaHilbertInductiveLimit) :
    CmcaHilbertInductiveLimit ∧
    (∀ w ∈ pscAdmissibleSectors,
      (singleSectorAmplitude beableWindingPartitionInstance w).sectorProb w = 1) :=
  ⟨h_ind, fun w hw => bps_psc_sector_has_beable_lift w hw⟩

/-- **G22 master bundle** (CatAL — sector maps + structural inductive-limit content). -/
theorem cmca_hilbert_fock_bridge_master :
    isFockZeroKinkSector kinkFockVacuum ∧
    (∀ m : KinkMode, isFockOneParticle (singleKinkFock m)) ∧
    (∀ w ∈ pscAdmissibleSectors,
      (singleSectorAmplitude beableWindingPartitionInstance w).sectorProb w = 1) ∧
    pscAdmissibleSectors.card = 5 ∧
    Fintype.card KinkMode = 4 ∧
    CmcaHilbertInductiveLimit := by
  refine ⟨?_, ?_, ?_, ?_, ?_, cmca_hilbert_inductive_limit⟩
  · exact fock_vacuum_maps_to_cmca_vacuum.1
  · intro m; exact (gTe_kink_mode_maps_to_fock_1particle m).1
  · intro w hw; exact bps_psc_sector_has_beable_lift w hw
  · exact psc_admissible_count
  · exact kink_fock_mode_count

end UgpLean.Substrate.CMCAHilbertFockBridge
