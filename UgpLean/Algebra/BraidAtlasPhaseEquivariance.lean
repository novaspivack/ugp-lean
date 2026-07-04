import Mathlib.Data.ZMod.Basic
import UgpLean.Gravity.FermionicStatistics
import UgpLean.Spacetime.PhiMDLKinkQuantumNumbers
import UgpLean.Algebra.KinkSectorTrialityAction

set_option maxRecDepth 10000

/-!
# BraidAtlasPhaseEquivariance: S₃ non-equivariance of triple-exchange phases

Machine certificate replaying `triple_exchange_s3_equivariance.py`. All statements are finite
and close with `decide` / `native_decide`.

**Physical content:** The certified uniform-triple exchange phase
`P(g) = BraidAtlasPhase(Q_φ(g))` from `gte_triple_kink_exchange_statistics` is **not**
equivariant under the Spin(8) triality S₃ action on `{gen₁, gen₂, gen₃}`. The sector
permutation σ acts as ℤ₇ charge conjugation on windings (`Q_φ(gen₃) = 3 = −4 mod 7`),
mapping the fermionic charged-lepton sector (`Q_φ = 4`, phase −1) to the bosonic W⁺
sector (`Q_φ = 3`, phase +1). The exchange-statistics structure carries a ℤ₂ symmetry
`{e, σρ²}` (gen₁ ↔ gen₂, both `Q_φ = 4`) but no larger proper subgroup of S₃.

This is a Level 0–1 algebraic certificate obstructing the triple-exchange configuration
space as a Level 3 triality carrier for C3″.

Level framing: Level 0–1 (`Q_φ` from `PhiMDLKinkQuantumNumbers`; `BraidAtlasPhase` from
`FermionicStatistics`; S₃ action from `KinkSectorTrialityAction`).
-/

namespace UgpLean.Algebra.BraidAtlasPhaseEquivariance

open GTE.Spacetime
open GTE.Spacetime.KinkQuantumNumbers (gen1 gen2 gen3)
open GTE.FermionicStatistics (BraidAtlasPhase)
open UgpLean.Algebra.KinkSectorTrialityAction

abbrev KinkSector := KinkQuantumNumbers

/-- Winding charge as an element of `ℤ₇` for Braid Atlas lookup. -/
def qPhiZMod (k : KinkSector) : ZMod 7 := k.qPhi

/-- Uniform-triple exchange phase `P(g,g,g) = BraidAtlasPhase(Q_φ(g))`. -/
def uniformTripleBraidPhase (k : KinkSector) : ℤ :=
  BraidAtlasPhase (qPhiZMod k)

def generationSectorList : List KinkSector := [gen1, gen2, gen3]

def sigmaRho2SectorPerm : SectorPerm :=
  composeSectorPerm sigmaSectorPerm (transformSector rhoSectorPerm 2)

def phasePreservedAtIndex (p : SectorPerm) (i : Fin 3) : Bool :=
  uniformTripleBraidPhase (sectorFromIndex i) ==
    uniformTripleBraidPhase (sectorFromIndex (applySectorPerm p i))

def permIsPhaseEquivariant (p : SectorPerm) : Bool :=
  phasePreservedAtIndex p 0 && phasePreservedAtIndex p 1 && phasePreservedAtIndex p 2

def subgroupIsPhaseEquivariant (elems : List SectorPerm) : Bool :=
  elems.all permIsPhaseEquivariant

/-- **gen2_gen3_braid_phase_differ:** gen₂ and gen₃ carry opposite certified exchange phases. -/
theorem gen2_gen3_braid_phase_differ :
    uniformTripleBraidPhase gen2 ≠ uniformTripleBraidPhase gen3 := by
  native_decide

/-- **gen3_q_phi_is_z7_inverse_of_gen2:** σ swaps gen₂ ↔ gen₃ and exchanges ℤ₇ windings. -/
theorem gen3_q_phi_is_z7_inverse_of_gen2 :
    (gen3.qPhi.val + gen2.qPhi.val) % 7 = 0 ∧
    gen3.qPhi = ⟨(7 - gen2.qPhi.val) % 7, by omega⟩ := by
  native_decide

/-- gen₃ winding is also the ℤ₇ additive inverse of gen₁ (both share the gen₂ inverse). -/
theorem gen3_q_phi_is_z7_inverse_of_gen1 :
    (gen3.qPhi.val + gen1.qPhi.val) % 7 = 0 := by
  native_decide

theorem gen1_gen2_same_braid_phase :
    uniformTripleBraidPhase gen1 = uniformTripleBraidPhase gen2 := by
  native_decide

theorem gen1_fermionic_gen3_bosonic :
    uniformTripleBraidPhase gen1 = -1 ∧
    uniformTripleBraidPhase gen2 = -1 ∧
    uniformTripleBraidPhase gen3 = 1 := by
  native_decide

/-- **sigma_not_equivariant_with_braid_phase:** σ maps gen₂ (phase −1) to gen₃ (phase +1). -/
theorem sigma_not_equivariant_with_braid_phase :
    sectorFromIndex (applySectorPerm sigmaSectorPerm 1) = gen3 ∧
    uniformTripleBraidPhase gen2 ≠ uniformTripleBraidPhase gen3 := by
  exact ⟨sigma_sector_action.2.1, gen2_gen3_braid_phase_differ⟩

theorem sigma_rho2_swaps_gen1_gen2 :
    sectorFromIndex (applySectorPerm sigmaRho2SectorPerm 0) = gen2 ∧
    sectorFromIndex (applySectorPerm sigmaRho2SectorPerm 1) = gen1 ∧
    sectorFromIndex (applySectorPerm sigmaRho2SectorPerm 2) = gen3 := by
  native_decide

theorem sigma_rho2_is_phase_equivariant : permIsPhaseEquivariant sigmaRho2SectorPerm := by
  native_decide

theorem identity_is_phase_equivariant : permIsPhaseEquivariant identitySectorPerm := by
  native_decide

theorem sigma_is_not_phase_equivariant :
    permIsPhaseEquivariant sigmaSectorPerm = false := by
  native_decide

theorem rho_is_not_phase_equivariant : permIsPhaseEquivariant rhoSectorPerm = false := by
  native_decide

theorem rho2_is_not_phase_equivariant :
    permIsPhaseEquivariant (transformSector rhoSectorPerm 2) = false := by
  native_decide

theorem sigma_rho_is_not_phase_equivariant :
    permIsPhaseEquivariant (composeSectorPerm sigmaSectorPerm rhoSectorPerm) = false := by
  native_decide

theorem z3_subgroup_not_phase_equivariant :
    subgroupIsPhaseEquivariant [identitySectorPerm, rhoSectorPerm,
      transformSector rhoSectorPerm 2] = false := by
  native_decide

theorem z2_sigma_subgroup_not_phase_equivariant :
    subgroupIsPhaseEquivariant [identitySectorPerm, sigmaSectorPerm] = false := by
  native_decide

theorem z2_sigma_rho_subgroup_not_phase_equivariant :
    subgroupIsPhaseEquivariant [identitySectorPerm,
      composeSectorPerm sigmaSectorPerm rhoSectorPerm] = false := by
  native_decide

theorem full_s3_not_phase_equivariant :
    subgroupIsPhaseEquivariant (s3SectorElements.map Prod.fst) = false := by
  native_decide

theorem z2_sigma_rho2_subgroup_is_phase_equivariant :
    subgroupIsPhaseEquivariant [identitySectorPerm, sigmaRho2SectorPerm] = true := by
  native_decide

/-- **equivariant_z2_subgroup:** `{e, σρ²}` is the unique nontrivial proper S₃ subgroup
    preserving the uniform-triple braid phase. -/
theorem equivariant_z2_subgroup :
    subgroupIsPhaseEquivariant [identitySectorPerm, sigmaRho2SectorPerm] = true ∧
    subgroupIsPhaseEquivariant [identitySectorPerm, sigmaSectorPerm] = false ∧
    subgroupIsPhaseEquivariant [identitySectorPerm,
      composeSectorPerm sigmaSectorPerm rhoSectorPerm] = false ∧
    subgroupIsPhaseEquivariant [identitySectorPerm, rhoSectorPerm,
      transformSector rhoSectorPerm 2] = false ∧
    subgroupIsPhaseEquivariant (s3SectorElements.map Prod.fst) = false ∧
    sectorFromIndex (applySectorPerm sigmaRho2SectorPerm 0) = gen2 ∧
    sectorFromIndex (applySectorPerm sigmaRho2SectorPerm 1) = gen1 ∧
    sectorFromIndex (applySectorPerm sigmaRho2SectorPerm 2) = gen3 := by
  native_decide

/-- **braid_phase_equivariance_certificate:** bundles the S₃ non-equivariance and ℤ₂
    equivariance structure for the certified triple-exchange phase assignment. -/
theorem braid_phase_equivariance_certificate :
    uniformTripleBraidPhase gen2 ≠ uniformTripleBraidPhase gen3 ∧
    (gen3.qPhi.val + gen2.qPhi.val) % 7 = 0 ∧
    sectorFromIndex (applySectorPerm sigmaSectorPerm 1) = gen3 ∧
    subgroupIsPhaseEquivariant [identitySectorPerm, sigmaRho2SectorPerm] = true ∧
    subgroupIsPhaseEquivariant [identitySectorPerm, sigmaSectorPerm] = false ∧
    uniformTripleBraidPhase gen1 = -1 ∧
    uniformTripleBraidPhase gen2 = -1 ∧
    uniformTripleBraidPhase gen3 = 1 := by
  native_decide

end UgpLean.Algebra.BraidAtlasPhaseEquivariance
