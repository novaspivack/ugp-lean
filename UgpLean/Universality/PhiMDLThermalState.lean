import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Data.Real.Basic
import Mathlib.Tactic
import UgpLean.Universality.FockSpaceKink
import UgpLean.Universality.GUTStructure

/-!
# Φ_MDL Hamiltonian Thermal State — Rank 76-L3-LEAN (EPIC_074)

Formalizes the L3-corrected state-selection content: the physical Φ_MDL quantum state on
the PSC-admissible-truncated Z₇ sine-Gordon kink Hilbert space is the canonical thermal
ensemble `ρ_T ∝ exp(-β H)` with sector marginals `P(k) = exp(-M_k/T)/Z_T` on admissible
sectors and zero weight on dark-mirror sectors `{1,5}`.

## Physical content (CatAL conditional)

- BPS kink mass `M_k = 8m/49` for every non-vacuum sector (Z₇ symmetry of the cosine potential).
- Vacuum sector mass `M_0 = 0`.
- PSC-admissible winding sectors `{0,2,3,4,6}`; forbidden `{1,5}` (P29 dark-mirror / GUT leptoquark).
- Thermal Boltzmann weights on the admissible truncation; vacuum-dominant at `T ≪ M_k`.

## Axioms

Zero custom physics axioms. Inherits only prior CatAL arithmetic from `GUTStructure` gauge-sector
identification and the BPS mass scale `8/N₇² = 8/49`.

## Status

CatAL conditional — zero sorry target for the structural thermal-state layer.
-/

namespace UgpLean.Universality.PhiMDLThermalState

open Real
open FockSpaceKink
open scoped BigOperators

/-- Z₇ sine-Gordon Hamiltonian data: natural coupling `m > 0`. -/
structure Z7SineGordonHamiltonian where
  m : ℝ
  m_pos : 0 < m

namespace Z7SineGordonHamiltonian

variable (H : Z7SineGordonHamiltonian)

/-- BPS kink mass on sector `k`: vacuum `0`, all non-zero sectors `8m/49`. -/
noncomputable def kinkMass (k : Fin 7) : ℝ :=
  if k = 0 then 0 else 8 * H.m / 49

/-- Common positive kink mass `8m/49` for every non-vacuum sector. -/
noncomputable def positiveKinkMass : ℝ := 8 * H.m / 49

theorem positive_kink_mass_eq (k : Fin 7) (hk : k ≠ 0) :
    H.kinkMass k = H.positiveKinkMass := by
  unfold kinkMass positiveKinkMass
  simp [hk]

theorem positive_kink_mass_pos : 0 < H.positiveKinkMass := by
  unfold positiveKinkMass
  exact div_pos (by linarith [H.m_pos]) (by norm_num)

end Z7SineGordonHamiltonian

/-- PSC-admissible Z₇ winding sectors (SM + vacuum): `{0,2,3,4,6}`. -/
def pscAdmissibleSectors : Finset (Fin 7) := {0, 2, 3, 4, 6}

/-- PSC-forbidden dark-mirror / GUT leptoquark sectors: `{1,5}`. -/
def pscForbiddenSectors : Finset (Fin 7) := {1, 5}

def pscAdmissibleSector (k : Fin 7) : Prop := k ∈ pscAdmissibleSectors

def pscForbiddenSector (k : Fin 7) : Prop := k ∈ pscForbiddenSectors

instance (k : Fin 7) : Decidable (pscAdmissibleSector k) := inferInstanceAs (Decidable (k ∈ pscAdmissibleSectors))

instance (k : Fin 7) : Decidable (pscForbiddenSector k) := inferInstanceAs (Decidable (k ∈ pscForbiddenSectors))

theorem psc_admissible_card : pscAdmissibleSectors.card = 5 := by decide

theorem psc_forbidden_card : pscForbiddenSectors.card = 2 := by decide

theorem psc_sectors_partition :
    pscAdmissibleSectors ∪ pscForbiddenSectors = Finset.univ ∧
    Disjoint pscAdmissibleSectors pscForbiddenSectors := by
  decide

/-- **phimdl_vacuum_mass_zero**: the vacuum winding sector has zero kink mass. -/
theorem phimdl_vacuum_mass_zero (H : Z7SineGordonHamiltonian) :
    H.kinkMass 0 = 0 := by
  unfold Z7SineGordonHamiltonian.kinkMass
  simp

/-- **phimdl_kink_masses_equal**: every non-vacuum Z₇ sector carries the same BPS mass. -/
theorem phimdl_kink_masses_equal (H : Z7SineGordonHamiltonian) {k₁ k₂ : Fin 7}
    (h₁ : k₁ ≠ 0) (h₂ : k₂ ≠ 0) :
    H.kinkMass k₁ = H.kinkMass k₂ :=
  (H.positive_kink_mass_eq k₁ h₁).trans (H.positive_kink_mass_eq k₂ h₂).symm

/-- **psc_admissible_sectors**: admissible sectors are exactly `{0,2,3,4,6}`; `{1,5}` forbidden. -/
theorem psc_admissible_sectors :
    pscAdmissibleSectors = {0, 2, 3, 4, 6} ∧
    pscForbiddenSectors = {1, 5} ∧
    pscAdmissibleSectors.card = 5 ∧
    pscForbiddenSectors = Finset.univ \ pscAdmissibleSectors := by
  refine ⟨rfl, rfl, psc_admissible_card, ?_⟩
  ext k
  simp only [pscForbiddenSectors, pscAdmissibleSectors, Finset.mem_sdiff, Finset.mem_univ,
    true_and, Finset.mem_insert, Finset.mem_singleton, not_or]
  fin_cases k <;> decide

/-- Compatibility with `GUTStructure` SM / leptoquark sector arithmetic. -/
theorem psc_admissible_matches_gut_structure :
    pscAdmissibleSectors.card = ({0, 2, 3, 4, 6} : Finset (ZMod 7)).card ∧
    pscForbiddenSectors.card = ({1, 5} : Finset (ZMod 7)).card :=
  ⟨by rw [psc_admissible_card]; decide, by rw [psc_forbidden_card]; decide⟩

theorem psc_forbidden_iff_not_admissible (k : Fin 7) :
    pscForbiddenSector k ↔ k ∉ pscAdmissibleSectors := by
  fin_cases k <;> simp [pscForbiddenSector, pscAdmissibleSectors, pscForbiddenSectors]

namespace ThermalState

variable (H : Z7SineGordonHamiltonian)

/-- Inverse temperature parameter `β = 1/T`; requires `T > 0`. -/
noncomputable def beta (T : ℝ) : ℝ := 1 / T

/-- Boltzmann weight `exp(-M_k/T)` on PSC-admissible sectors; zero on `{1,5}`. -/
noncomputable def boltzmannWeight (T : ℝ) (k : Fin 7) : ℝ :=
  if k ∈ pscAdmissibleSectors then Real.exp (-H.kinkMass k / T) else 0

/-- Canonical thermal partition function `Z_T` over PSC-admissible sectors. -/
noncomputable def partitionFunction (T : ℝ) : ℝ :=
  pscAdmissibleSectors.sum (boltzmannWeight H T)

/-- Thermal sector probability `P(k) = exp(-M_k/T)/Z_T` on admissible sectors. -/
noncomputable def sectorProb (T : ℝ) (_hT : 0 < T) (k : Fin 7) : ℝ :=
  boltzmannWeight H T k / partitionFunction H T

theorem boltzmann_weight_admissible (T : ℝ) (k : Fin 7) (hadm : pscAdmissibleSector k) :
    boltzmannWeight H T k = Real.exp (-H.kinkMass k / T) := by
  dsimp [boltzmannWeight, pscAdmissibleSector] at *
  rw [if_pos hadm]

theorem boltzmann_weight_forbidden (T : ℝ) (k : Fin 7) (hforb : pscForbiddenSector k) :
    boltzmannWeight H T k = 0 := by
  have hnot := (psc_forbidden_iff_not_admissible k).1 hforb
  simp [boltzmannWeight, hnot]

theorem vacuum_boltzmann_weight (T : ℝ) (_hT : 0 < T) :
    boltzmannWeight H T 0 = 1 := by
  have hadm : pscAdmissibleSector (0 : Fin 7) := by
    simp [pscAdmissibleSector, pscAdmissibleSectors]
  rw [boltzmann_weight_admissible H T 0 hadm, phimdl_vacuum_mass_zero H]
  simp

theorem partitionFunction_pos (T : ℝ) (hT : 0 < T) : 0 < partitionFunction H T := by
  unfold partitionFunction
  have hvac : 0 ∈ pscAdmissibleSectors := by simp [pscAdmissibleSectors]
  have hlt : boltzmannWeight H T 0 ≤ pscAdmissibleSectors.sum (boltzmannWeight H T) :=
    Finset.single_le_sum (fun k _ => by
      by_cases h : k ∈ pscAdmissibleSectors
      · simp [boltzmannWeight, h]
        exact le_of_lt (Real.exp_pos _)
      · simp [boltzmannWeight, h]) hvac
  have hpos : 0 < boltzmannWeight H T 0 := by
    rw [vacuum_boltzmann_weight H T hT]
    norm_num
  exact lt_of_lt_of_le hpos hlt

theorem sectorProb_nonneg (T : ℝ) (hT : 0 < T) (k : Fin 7) : 0 ≤ sectorProb H T hT k := by
  unfold sectorProb
  have hden : 0 < partitionFunction H T := partitionFunction_pos H T hT
  by_cases hadm : pscAdmissibleSector k
  · rw [boltzmann_weight_admissible H T k hadm]
    exact div_nonneg (le_of_lt (Real.exp_pos _)) (le_of_lt hden)
  · have hforb : pscForbiddenSector k := (psc_forbidden_iff_not_admissible k).2 hadm
    rw [boltzmann_weight_forbidden H T k hforb]
    simp

theorem sectorProb_forbidden (T : ℝ) (hT : 0 < T) (k : Fin 7) (hforb : pscForbiddenSector k) :
    sectorProb H T hT k = 0 := by
  unfold sectorProb
  rw [boltzmann_weight_forbidden H T k hforb, zero_div]

/-- **thermal_state_sector_prob**: on PSC-admissible sectors, `P(k) = exp(-M_k/T)/Z_T`. -/
theorem thermal_state_sector_prob (T : ℝ) (hT : 0 < T) (k : Fin 7) (hadm : pscAdmissibleSector k) :
    sectorProb H T hT k = Real.exp (-H.kinkMass k / T) / partitionFunction H T := by
  unfold sectorProb
  rw [boltzmann_weight_admissible H T k hadm]

theorem sectorProb_admissible_sum (T : ℝ) (hT : 0 < T) :
    pscAdmissibleSectors.sum (sectorProb H T hT) = 1 := by
  unfold sectorProb partitionFunction
  have hden : pscAdmissibleSectors.sum (boltzmannWeight H T) ≠ 0 :=
    ne_of_gt (partitionFunction_pos H T hT)
  rw [← Finset.sum_div]
  field_simp [hden]

theorem vacuum_particle_prob_ratio (T : ℝ) (hT : 0 < T) {k : Fin 7}
    (hk : k ≠ 0) (hadm : pscAdmissibleSector k) :
    sectorProb H T hT 0 / sectorProb H T hT k = Real.exp (H.positiveKinkMass / T) := by
  have hM : H.kinkMass k = H.positiveKinkMass := H.positive_kink_mass_eq k hk
  have hnum : sectorProb H T hT 0 = 1 / partitionFunction H T := by
    rw [thermal_state_sector_prob H T hT 0 (by simp [pscAdmissibleSector, pscAdmissibleSectors])]
    simp [phimdl_vacuum_mass_zero H, Real.exp_zero]
  have hden : sectorProb H T hT k =
      Real.exp (-H.positiveKinkMass / T) / partitionFunction H T := by
    rw [thermal_state_sector_prob H T hT k hadm, hM]
  rw [hnum, hden, div_div]
  field_simp [ne_of_gt (partitionFunction_pos H T hT), Real.exp_ne_zero]
  rw [Real.exp_neg, inv_mul_cancel₀ (Real.exp_ne_zero _)]

private lemma ten_pow_thirty_pos : (0 : ℝ) < (10 : ℝ) ^ 30 := by norm_num

private lemma one_lt_ten_pow_thirty : (1 : ℝ) < (10 : ℝ) ^ 30 := by norm_num

/-- **thermal_state_vacuum_dominant**: at sufficiently low temperature, vacuum dominates by `> 10^30`. -/
theorem thermal_state_vacuum_dominant (T : ℝ) (hT : 0 < T)
    (hcold : H.positiveKinkMass / T > Real.log ((10 : ℝ) ^ 30)) :
    sectorProb H T hT 0 / sectorProb H T hT ⟨2, by decide⟩ > (10 : ℝ) ^ 30 := by
  have hadm : pscAdmissibleSector ⟨2, by decide⟩ := by
    simp [pscAdmissibleSector, pscAdmissibleSectors]
  have hk : (⟨2, by decide⟩ : Fin 7) ≠ 0 := by decide
  rw [vacuum_particle_prob_ratio H T hT hk hadm]
  have hmono : Real.exp (H.positiveKinkMass / T) > Real.exp (Real.log ((10 : ℝ) ^ 30)) :=
    Real.exp_lt_exp.mpr hcold
  rwa [Real.exp_log ten_pow_thirty_pos] at hmono

/-- Observed cosmic temperatures satisfy the cold limit when `T < M_k / ln(10^30)`. -/
theorem thermal_state_cosmic_cold_hypothesis (T : ℝ) (hT : 0 < T)
    (hT_cold : T < H.positiveKinkMass / Real.log ((10 : ℝ) ^ 30)) :
    H.positiveKinkMass / T > Real.log ((10 : ℝ) ^ 30) := by
  have hlog_pos : 0 < Real.log ((10 : ℝ) ^ 30) := Real.log_pos one_lt_ten_pow_thirty
  have hprod : Real.log ((10 : ℝ) ^ 30) * T < H.positiveKinkMass := by
    rw [mul_comm]
    exact (lt_div_iff₀ hlog_pos).1 hT_cold
  exact (lt_div_iff₀ hT).2 hprod

/-- Cosmic-vacuum dominance at any temperature colder than `M_k / ln(10^30)`. -/
theorem thermal_state_vacuum_dominant_cold (T : ℝ) (hT : 0 < T)
    (hT_cold : T < H.positiveKinkMass / Real.log ((10 : ℝ) ^ 30)) :
    sectorProb H T hT 0 / sectorProb H T hT ⟨2, by decide⟩ > (10 : ℝ) ^ 30 :=
  thermal_state_vacuum_dominant H T hT (thermal_state_cosmic_cold_hypothesis H T hT hT_cold)

end ThermalState

/-- **phimdl_thermal_state_master**: bundled L3-corrected thermal-state certificate. -/
theorem phimdl_thermal_state_master (H : Z7SineGordonHamiltonian) (T : ℝ) (hT : 0 < T)
    (hcold : H.positiveKinkMass / T > Real.log ((10 : ℝ) ^ 30)) :
    H.kinkMass 0 = 0 ∧
    (∀ {k₁ k₂ : Fin 7}, k₁ ≠ 0 → k₂ ≠ 0 → H.kinkMass k₁ = H.kinkMass k₂) ∧
    pscAdmissibleSectors = {0, 2, 3, 4, 6} ∧
    pscForbiddenSectors = {1, 5} ∧
    (∀ k : Fin 7, pscAdmissibleSector k →
      ThermalState.sectorProb H T hT k =
        Real.exp (-H.kinkMass k / T) / ThermalState.partitionFunction H T) ∧
    (∀ k : Fin 7, pscForbiddenSector k → ThermalState.sectorProb H T hT k = 0) ∧
    ThermalState.sectorProb H T hT 0 / ThermalState.sectorProb H T hT ⟨2, by decide⟩ >
      (10 : ℝ) ^ 30 := by
  have h0 := phimdl_vacuum_mass_zero H
  have h1 : ∀ {k₁ k₂ : Fin 7}, k₁ ≠ 0 → k₂ ≠ 0 → H.kinkMass k₁ = H.kinkMass k₂ :=
    fun {k₁ k₂} h₁ h₂ => phimdl_kink_masses_equal H h₁ h₂
  have h2 := psc_admissible_sectors.1
  have h3 := psc_admissible_sectors.2.1
  have h4 : ∀ k : Fin 7, pscAdmissibleSector k →
      ThermalState.sectorProb H T hT k =
        Real.exp (-H.kinkMass k / T) / ThermalState.partitionFunction H T :=
    fun k hadm => ThermalState.thermal_state_sector_prob H T hT k hadm
  have h5 : ∀ k : Fin 7, pscForbiddenSector k → ThermalState.sectorProb H T hT k = 0 :=
    fun k hforb => ThermalState.sectorProb_forbidden H T hT k hforb
  have h6 := ThermalState.thermal_state_vacuum_dominant H T hT hcold
  exact ⟨h0, ⟨h1, ⟨h2, ⟨h3, ⟨h4, ⟨h5, h6⟩⟩⟩⟩⟩⟩

end UgpLean.Universality.PhiMDLThermalState
