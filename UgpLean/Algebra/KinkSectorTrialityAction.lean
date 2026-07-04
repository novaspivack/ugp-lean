import Mathlib.Data.List.Basic
import UgpLean.Algebra.TrialityInterface
import UgpLean.Spacetime.PhiMDLKinkQuantumNumbers

set_option maxRecDepth 10000

/-!
# KinkSectorTrialityAction: faithful S₃ on Φ_MDL kink sectors

Machine certificate replaying `yukawa_dirac_index_kink.py` (Task 3). All statements are
finite and close with `decide` / `native_decide`.

**Physical content:** The Spin(8) triality group S₃ = ⟨ρ, σ⟩ acts faithfully on the
three-element set of generation kink species `{gen₁, gen₂, gen₃}`, identified with the
triality slots `{V, S⁺, S⁻}` under the Eisenstein pinning gen₁ ↔ V. The carrier is the
discrete label set — a permutation representation of degree three — not JR zero-mode
vector spaces.

Level framing: Level 0–1 algebraic certificate (kink sector labels from
`PhiMDLKinkQuantumNumbers`; triality dictionary from `TrialityInterface` G4).
-/

namespace UgpLean.Algebra.KinkSectorTrialityAction

open GTE.Spacetime
open GTE.Spacetime.KinkQuantumNumbers (vacuum gen1 gen2 gen3)
open UgpLean.Algebra.TrialityInterface

abbrev KinkSector := KinkQuantumNumbers

/-- The three generation kink sectors (vacuum excluded). -/
def generationSectors : List KinkSector := [gen1, gen2, gen3]

/-- Index map for `{gen₁, gen₂, gen₃}` under the Python mirror ordering. -/
def sectorIndex : KinkSector → Option (Fin 3)
  | k =>
    if k = gen1 then some 0
    else if k = gen2 then some 1
    else if k = gen3 then some 2
    else none

def sectorFromIndex : Fin 3 → KinkSector
  | 0 => gen1
  | 1 => gen2
  | 2 => gen3

abbrev SectorPerm := Fin 3 → Fin 3

/-- Cyclic triality move: gen₁ → gen₂ → gen₃ → gen₁ (Python `rho`). -/
def rhoSectorPerm : SectorPerm := ![1, 2, 0]

/-- Spinor-slot swap: gen₁ fixed, gen₂ ↔ gen₃ (Python `sigma`). -/
def sigmaSectorPerm : SectorPerm := ![0, 2, 1]

def applySectorPerm (p : SectorPerm) (i : Fin 3) : Fin 3 := p i

def transformSector (p : SectorPerm) (n : Nat) (i : Fin 3) : Fin 3 :=
  (List.range n).foldl (fun s _ => applySectorPerm p s) i

def composeSectorPerm (p q : SectorPerm) : SectorPerm :=
  fun i => applySectorPerm p (applySectorPerm q i)

def rhoInvSectorPerm : SectorPerm := ![2, 0, 1]

def sectorPermEq (p q : SectorPerm) : Bool :=
  p 0 == q 0 && p 1 == q 1 && p 2 == q 2

def permActionTriple (p : SectorPerm) : List (Fin 3) :=
  [p 0, p 1, p 2]

def identitySectorPerm : SectorPerm := ![0, 1, 2]

def s3SectorElements : List (SectorPerm × String) :=
  [ (identitySectorPerm, "e")
  , (rhoSectorPerm, "rho")
  , (transformSector rhoSectorPerm 2, "rho^2")
  , (sigmaSectorPerm, "sigma")
  , (composeSectorPerm sigmaSectorPerm rhoSectorPerm, "sigma*rho")
  , (composeSectorPerm sigmaSectorPerm (transformSector rhoSectorPerm 2), "sigma*rho^2") ]

def distinctSectorPermCount : Nat :=
  (s3SectorElements.map fun p => permActionTriple p.1).eraseDups.length

/-- gen₁ ↔ V (vector slot), gen₂ ↔ S⁺, gen₃ ↔ S⁻ under the adopted Eisenstein pinning. -/
def sectorToTrialitySlot : Fin 3 → Fin 3
  | 0 => 0
  | 1 => 1
  | 2 => 2

theorem generation_sectors_length : generationSectors.length = 3 := by native_decide

theorem sector_index_roundtrip :
    sectorIndex gen1 = some 0 ∧
    sectorIndex gen2 = some 1 ∧
    sectorIndex gen3 = some 2 ∧
    sectorFromIndex 0 = gen1 ∧
    sectorFromIndex 1 = gen2 ∧
    sectorFromIndex 2 = gen3 := by
  native_decide

theorem rho_sector_action :
    sectorFromIndex (applySectorPerm rhoSectorPerm 0) = gen2 ∧
    sectorFromIndex (applySectorPerm rhoSectorPerm 1) = gen3 ∧
    sectorFromIndex (applySectorPerm rhoSectorPerm 2) = gen1 := by
  native_decide

theorem sigma_sector_action :
    sectorFromIndex (applySectorPerm sigmaSectorPerm 0) = gen1 ∧
    sectorFromIndex (applySectorPerm sigmaSectorPerm 1) = gen3 ∧
    sectorFromIndex (applySectorPerm sigmaSectorPerm 2) = gen2 := by
  native_decide

theorem rho_sector_order_three :
    transformSector rhoSectorPerm 3 0 = 0 ∧
    transformSector rhoSectorPerm 3 1 = 1 ∧
    transformSector rhoSectorPerm 3 2 = 2 := by
  native_decide

theorem sigma_sector_order_two :
    transformSector sigmaSectorPerm 2 0 = 0 ∧
    transformSector sigmaSectorPerm 2 1 = 1 ∧
    transformSector sigmaSectorPerm 2 2 = 2 := by
  native_decide

theorem sigma_conjugates_rho :
    ∀ i : Fin 3,
      applySectorPerm sigmaSectorPerm
        (applySectorPerm rhoSectorPerm (applySectorPerm sigmaSectorPerm i)) =
        applySectorPerm rhoInvSectorPerm i := by
  intro i
  fin_cases i <;> native_decide

theorem s3_sector_six_distinct_permutations :
    distinctSectorPermCount = 6 := by
  native_decide

theorem s3_sector_elements_are_valid :
    s3SectorElements.all fun p => sectorPermEq p.1 identitySectorPerm ||
      sectorPermEq p.1 rhoSectorPerm ||
      sectorPermEq p.1 (transformSector rhoSectorPerm 2) ||
      sectorPermEq p.1 sigmaSectorPerm ||
      sectorPermEq p.1 (composeSectorPerm sigmaSectorPerm rhoSectorPerm) ||
      sectorPermEq p.1 (composeSectorPerm sigmaSectorPerm (transformSector rhoSectorPerm 2)) := by
  native_decide

/-- Sector ρ matches the G4 triality ρ on slot indices under gen₁↔V. -/
theorem rho_matches_triality_slot_cycle :
    applySectorPerm rhoSectorPerm 0 = 1 ∧
    applySectorPerm rhoSectorPerm 1 = 2 ∧
    applySectorPerm rhoSectorPerm 2 = 0 ∧
    applySlotPerm trialityRhoPerm kleinCenter1 = kleinCenter3 ∧
    applySlotPerm trialityRhoPerm kleinCenter3 = kleinCenter2 ∧
    applySlotPerm trialityRhoPerm kleinCenter2 = kleinCenter1 := by
  exact ⟨by native_decide, ⟨by native_decide, ⟨by native_decide,
    G4_equivariant_dictionary.1, ⟨G4_equivariant_dictionary.2.1,
      G4_equivariant_dictionary.2.2.1⟩⟩⟩⟩

/-- Sector σ matches the G4 spinor swap on slot indices under gen₁↔V. -/
theorem sigma_matches_triality_spinor_swap :
    applySectorPerm sigmaSectorPerm 0 = 0 ∧
    applySectorPerm sigmaSectorPerm 1 = 2 ∧
    applySectorPerm sigmaSectorPerm 2 = 1 ∧
    applySlotPerm spinorSwapPerm kleinCenter1 = kleinCenter1 ∧
    applySlotPerm spinorSwapPerm kleinCenter2 = kleinCenter3 ∧
    applySlotPerm spinorSwapPerm kleinCenter3 = kleinCenter2 := by
  exact ⟨by native_decide, ⟨by native_decide, ⟨by native_decide,
    G4_equivariant_dictionary.2.2.2.1, ⟨G4_equivariant_dictionary.2.2.2.2.1,
      G4_equivariant_dictionary.2.2.2.2.2⟩⟩⟩⟩

/-- **triality_acts_faithfully_on_kink_sectors** (CatAL): S₃ = ⟨ρ, σ⟩ satisfies
    ρ³ = id, σ² = id, σρσ = ρ⁻¹ on `{gen₁, gen₂, gen₃}`, and the six group elements
    induce six distinct permutations. The action is the standard Spin(8) triality action
    on `{V, S⁺, S⁻}` with gen₁ ↔ V. -/
theorem triality_acts_faithfully_on_kink_sectors :
    generationSectors.length = 3 ∧
    (transformSector rhoSectorPerm 3 0 = 0 ∧
      transformSector rhoSectorPerm 3 1 = 1 ∧
      transformSector rhoSectorPerm 3 2 = 2) ∧
    (transformSector sigmaSectorPerm 2 0 = 0 ∧
      transformSector sigmaSectorPerm 2 1 = 1 ∧
      transformSector sigmaSectorPerm 2 2 = 2) ∧
    (∀ i : Fin 3,
      applySectorPerm sigmaSectorPerm
        (applySectorPerm rhoSectorPerm (applySectorPerm sigmaSectorPerm i)) =
        applySectorPerm rhoInvSectorPerm i) ∧
    distinctSectorPermCount = 6 ∧
    sectorFromIndex (applySectorPerm rhoSectorPerm 0) = gen2 ∧
    sectorFromIndex (applySectorPerm sigmaSectorPerm 1) = gen3 := by
  refine ⟨generation_sectors_length, ?_⟩
  refine ⟨rho_sector_order_three, ?_⟩
  refine ⟨sigma_sector_order_two, ?_⟩
  exact ⟨sigma_conjugates_rho, ⟨s3_sector_six_distinct_permutations,
    ⟨rho_sector_action.1, sigma_sector_action.2.1⟩⟩⟩

end UgpLean.Algebra.KinkSectorTrialityAction
