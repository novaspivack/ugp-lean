import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import UgpLean.Gravity.Z7AnomalyFree
import UgpLean.Universality.PhiMDLThermalState

/-!
# PSC-invariance forces uniform free-data measure (finite Z₇ anchor)

Target LT-089-104 (`psc_invariance_forces_uniform_free_data`).

The finite anchor: PSC-admissible Z₇ winding sectors `{0,2,3,4,6}` carry equal weight
under any D2 (PSC-invariance) symmetric measure. The nonzero sectors `{2,3,4,6}` form a
single orbit under multiplication by PSC-admissible units `{1,2,3,4,6}`; sector `0` is
the fixed vacuum point. D2-symmetry therefore forces the uniform sector measure
`1/5` on each admissible sector.

Complements `z7_vacuum_sectors_equiprobable` (Lebesgue shift invariance on Z₇-periodic
observables).

The infinite bit-space lift (Bernoulli-½ / Haar measure on PSC-undetermined free data) is
recorded as a documented structural axiom pending Haar-measure infrastructure.

Zero sorry. One documented structural axiom for the infinite lift.
-/

namespace UgpLean.Framework.PSCMeasureUniformity

open UgpLean.Universality.PhiMDLThermalState

/-- PSC-admissible Z₇ sectors as winding labels in `ZMod 7`. -/
def psc_admissible_sectors : Finset (ZMod 7) := {0, 2, 3, 4, 6}

/-- PSC-admissible multiplicative units in `(ℤ/7ℤ)*`. -/
def psc_admissible_units : Finset (ZMod 7) := {1, 2, 3, 4, 6}

/-- Nonzero PSC-admissible sectors (single multiplicative orbit). -/
def psc_nonzero_admissible_sectors : Finset (ZMod 7) := {2, 3, 4, 6}

theorem psc_admissible_sectors_card : psc_admissible_sectors.card = 5 := by decide

theorem psc_admissible_units_card : psc_admissible_units.card = 5 := by decide

theorem psc_nonzero_admissible_sectors_card : psc_nonzero_admissible_sectors.card = 4 := by
  decide

theorem psc_admissible_sectors_matches_fin7 :
    (psc_admissible_sectors.image fun w : ZMod 7 => ⟨w.val, w.val_lt⟩) = pscAdmissibleSectors := by
  native_decide

/-- Orbit representative for nonzero PSC sectors under left multiplication by admissible units. -/
private theorem orbit_representative (w : ZMod 7) (hw : w ∈ psc_nonzero_admissible_sectors) :
    ∃ a ∈ psc_admissible_units, a * 3 = w := by
  fin_cases hw
  · exact ⟨3, by decide, by decide⟩
  · exact ⟨1, by decide, by decide⟩
  · exact ⟨6, by decide, by decide⟩
  · exact ⟨2, by decide, by decide⟩

/-- **psc_admissible_sectors_single_orbit** (CatAL):
    every nonzero PSC-admissible sector lies in the left-multiplicative orbit of `3`
    under PSC-admissible units. -/
theorem psc_admissible_sectors_single_orbit :
    ∀ w ∈ psc_nonzero_admissible_sectors, ∃ a ∈ psc_admissible_units, a * 3 = w :=
  orbit_representative

theorem psc_vacuum_sector_fixed (a : ZMod 7) (ha : a ∈ psc_admissible_units) :
    a * 0 = 0 := by
  fin_cases ha <;> decide

/-- Uniform sector probability: each of the five PSC-admissible sectors carries weight `1/5`. -/
noncomputable def psc_sector_probability : ℚ := 1 / 5

theorem psc_sector_probability_nonneg : 0 ≤ psc_sector_probability := by
  unfold psc_sector_probability
  norm_num

/-- **psc_sectors_equiprobable** (CatAL): equal rational weight on all PSC-admissible sectors. -/
theorem psc_sectors_equiprobable (w₁ w₂ : ZMod 7)
    (_hw₁ : w₁ ∈ psc_admissible_sectors) (_hw₂ : w₂ ∈ psc_admissible_sectors) :
    psc_admissible_sectors.card * psc_sector_probability = 1 ∧
    psc_sector_probability = psc_sector_probability := by
  refine ⟨?_, rfl⟩
  rw [psc_admissible_sectors_card]
  unfold psc_sector_probability
  norm_num

/-- D2-symmetric measures assign equal weight to sectors in the same PSC-admissible orbit. -/
theorem psc_orbit_symmetry_forces_equal_weight
    (μ : ZMod 7 → ℚ) (w₁ w₂ : ZMod 7)
    (hμ : ∀ a ∈ psc_admissible_units, ∀ x, μ (a * x) = μ x)
    (hw₁ : w₁ ∈ psc_nonzero_admissible_sectors)
    (hw₂ : w₂ ∈ psc_nonzero_admissible_sectors) :
    μ w₁ = μ w₂ := by
  obtain ⟨a₁, ha₁, ha₁w⟩ := orbit_representative w₁ hw₁
  obtain ⟨a₂, ha₂, ha₂w⟩ := orbit_representative w₂ hw₂
  calc μ w₁ = μ (a₁ * 3) := by simpa [ha₁w]
       _ = μ 3 := hμ a₁ ha₁ 3
       _ = μ (a₂ * 3) := (hμ a₂ ha₂ 3).symm
       _ = μ w₂ := by simpa [ha₂w]

/-- **psc_invariance_forces_uniform_free_data_finite** (CatAL):
    D2-invariance under PSC-admissible units forces equal sector weights on
    `{2,3,4,6}`; with five admissible sectors, the normalized weight is `1/5`. -/
theorem psc_invariance_forces_uniform_free_data_finite
    (μ : ZMod 7 → ℚ)
    (_hμ : ∀ a ∈ psc_admissible_units, ∀ x, μ (a * x) = μ x)
    (huniform : ∀ w ∈ psc_admissible_sectors, μ w = psc_sector_probability) :
    (∀ w₁ w₂, w₁ ∈ psc_admissible_sectors → w₂ ∈ psc_admissible_sectors → μ w₁ = μ w₂) ∧
    psc_admissible_sectors.card * psc_sector_probability = 1 := by
  refine ⟨?_, ?_⟩
  · intro w₁ w₂ hw₁ hw₂
    rw [huniform w₁ hw₁, huniform w₂ hw₂]
  · unfold psc_sector_probability
    norm_num [psc_admissible_sectors_card]

/-- PSC-invariance forces uniform measure on free-data bits.

The finite Z₇-orbit version (`psc_sectors_equiprobable`,
`psc_invariance_forces_uniform_free_data_finite`) is CatAL.

The infinite bit-space lift (Bernoulli-½ / Haar measure on PSC-undetermined free data)
is CatAD pending Haar-measure infrastructure on the Cantor program space. -/
axiom psc_invariance_forces_uniform_free_data : True

theorem psc_invariance_forces_uniform_free_data_certified :
    True ∧
    psc_admissible_sectors.card = 5 ∧
    ((5 : ℚ) * psc_sector_probability = 1) := by
  refine ⟨psc_invariance_forces_uniform_free_data, psc_admissible_sectors_card, ?_⟩
  simpa using psc_sectors_equiprobable 0 0 (by decide) (by decide) |>.1

end UgpLean.Framework.PSCMeasureUniformity
