import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import UgpLean.Universality.BornRuleMDL
import UgpLean.Spacetime.PhiMDLKinkQuantumNumbers
import UgpLean.Framework.GTEOptimalityInstance

/-!
# Second Quantization of Φ_MDL Kinks — Rank 77-2QUANT (EPIC_073)

Algebraic Fock-space layer over the four GTE-orbit Φ_MDL kink modes, connecting
normalized kink-mode amplitudes to `BornRuleMDL.BeableAmplitudeHypothesis`.

## Proved (zero sorry, CatAL structural layer)

- Four kink Fock modes with certified `qPhi` winding labels.
- Creation / annihilation on `{0,1}` occupations per mode.
- Uniform sector lift over a certified `BeableWindingPartition`.
- `fock_beable_amplitude_normalized` ⇒ `BeableAmplitudeHypothesis`.
- `fock_sector_born_is_one` — single-sector coefficient ⇒ Born weight 1.
- `born_rule_from_fock_lift` — Fock lift + PSC-MDL Born partition.

## Open (Genius Team / continuum)

- Canonical Z₇-KG kink soliton quantization (Jackiw–Rebbi / Rajaraman).
- MDL weight `P(k) ∝ 1/K_k` identified with continuum `|φ_k|²`.
-/

namespace UgpLean.Universality.FockSpaceKink

open BornRuleMDL
open GTE.Spacetime KinkQuantumNumbers
open CUP3D GUTStructure DUniqueness
open UgpLean.Framework.GTE
open scoped BigOperators

abbrev KinkMode := Fin 4

def kinkModeLabel (m : KinkMode) : KinkQuantumNumbers :=
  match m with
  | 0 => vacuum
  | 1 => gen3
  | 2 => gen1
  | 3 => gen2

theorem kink_fock_mode_count : Fintype.card KinkMode = 4 :=
  Fintype.card_fin 4

def kinkModeWinding (m : KinkMode) : Fin 7 :=
  (kinkModeLabel m).qPhi

theorem kink_mode_winding_certified (m : KinkMode) :
    kinkModeWinding m = (kinkModeLabel m).qPhi := rfl

theorem kink_gen1_gen2_same_winding :
    kinkModeWinding ⟨2, by decide⟩ = kinkModeWinding ⟨3, by decide⟩ ∧
    (kinkModeLabel ⟨2, by decide⟩).qChi ≠ (kinkModeLabel ⟨3, by decide⟩).qChi :=
  phimdl_kink_same_winding_distinct_color

abbrev KinkOccupation := Fin 2
abbrev KinkFockState := KinkMode → KinkOccupation

def kinkFockVacuum : KinkFockState := fun _ => 0

def kinkOccupationCount (s : KinkFockState) : ℕ :=
  (Finset.univ.filter (fun m => s m = 1)).card

theorem kink_fock_state_count : Fintype.card KinkFockState = 16 := by
  simp [KinkFockState, KinkMode, KinkOccupation, pow_succ, pow_zero]

def kinkCreation (m : KinkMode) (s : KinkFockState) : KinkFockState :=
  fun i => if i = m then 1 else s i

def kinkAnnihilation (m : KinkMode) (s : KinkFockState) : KinkFockState :=
  fun i => if i = m then 0 else s i

theorem kink_creation_from_vacuum (m : KinkMode) :
    kinkCreation m kinkFockVacuum = fun i => if i = m then (1 : KinkOccupation) else 0 := by
  funext i; simp [kinkCreation, kinkFockVacuum]

theorem kink_annihilation_after_creation (m : KinkMode) (s : KinkFockState) :
    kinkAnnihilation m (kinkCreation m s) = fun i => if i = m then (0 : KinkOccupation) else s i := by
  funext i; by_cases hi : i = m <;> simp [kinkAnnihilation, kinkCreation, hi]

def singleKinkFock (m : KinkMode) : KinkFockState :=
  kinkCreation m kinkFockVacuum

theorem single_kink_fock_occupancy (m : KinkMode) :
    kinkOccupationCount (singleKinkFock m) = 1 := by
  unfold kinkOccupationCount singleKinkFock kinkCreation kinkFockVacuum
  have hfilter :
      (Finset.univ.filter (fun i : KinkMode => (if i = m then (1 : Fin 2) else 0) = 1)) = {m} := by
    ext i
    simp only [Finset.mem_filter, Finset.mem_univ, Finset.mem_singleton]
    by_cases hi : i = m <;> simp [hi]
  rw [hfilter, Finset.card_singleton]

def beablesPerWindingSector : ℕ := 2401

theorem beables_per_sector_eq_z7_four : beablesPerWindingSector = 7 ^ 4 := rfl

theorem beables_per_sector_times_seven :
    7 * beablesPerWindingSector = 7 ^ 5 := by
  rw [beables_per_sector_eq_z7_four]
  exact z7_sector_sizes

structure BeableWindingPartition where
  winding : BeableIndex → Fin 7
  card_each :
    ∀ w : Fin 7,
      (Finset.univ.filter (fun i : BeableIndex => winding i = w)).card = beablesPerWindingSector

noncomputable def sectorSpreadNorm : ℝ :=
  1 / Real.sqrt (beablesPerWindingSector : ℝ)

noncomputable def toBeableAmplitude (P : BeableWindingPartition) (coeffs : Fin 7 → ℂ)
    (i : BeableIndex) : ℂ :=
  coeffs (P.winding i) * (sectorSpreadNorm : ℂ)

theorem sector_spread_norm_sq :
    sectorSpreadNorm * sectorSpreadNorm = (1 : ℝ) / beablesPerWindingSector := by
  unfold sectorSpreadNorm
  have hpos : (0 : ℝ) ≤ (beablesPerWindingSector : ℝ) := by norm_num
  have hsq : (Real.sqrt (beablesPerWindingSector : ℝ)) ^ 2 = beablesPerWindingSector := Real.sq_sqrt hpos
  field_simp [beablesPerWindingSector]
  nlinarith

theorem spread_normSq (c : ℂ) :
    Complex.normSq (c * (sectorSpreadNorm : ℂ)) =
      Complex.normSq c / beablesPerWindingSector := by
  rw [Complex.normSq_mul, Complex.normSq_ofReal, sector_spread_norm_sq]
  ring_nf

noncomputable def fock_beable_amplitude_normalized (P : BeableWindingPartition)
    (coeffs : Fin 7 → ℂ)
    (hnorm : (Finset.univ : Finset (Fin 7)).sum (fun w => Complex.normSq (coeffs w)) = 1) :
    BeableAmplitudeHypothesis where
  α := toBeableAmplitude P coeffs
  winding := P.winding
  normalized := by
    have hm : ∀ i ∈ (Finset.univ : Finset BeableIndex), P.winding i ∈ (Finset.univ : Finset (Fin 7)) :=
      fun i _ => Finset.mem_univ _
    have hfiber :
        (Finset.univ : Finset BeableIndex).sum (fun i => Complex.normSq (toBeableAmplitude P coeffs i)) =
          (Finset.univ : Finset (Fin 7)).sum (fun w =>
            (Finset.univ.filter (fun i : BeableIndex => P.winding i = w)).sum
              (fun i => Complex.normSq (toBeableAmplitude P coeffs i))) := by
      rw [← Finset.sum_fiberwise_of_maps_to hm (f := fun i => Complex.normSq (toBeableAmplitude P coeffs i))]
    rw [hfiber]
    have hinner :
        ∀ w : Fin 7,
          (Finset.univ.filter (fun i : BeableIndex => P.winding i = w)).sum
            (fun i => Complex.normSq (toBeableAmplitude P coeffs i)) =
            Complex.normSq (coeffs w) := by
      intro w
      have hconst :
          ∀ i ∈ Finset.univ.filter (fun i : BeableIndex => P.winding i = w),
            Complex.normSq (toBeableAmplitude P coeffs i) = Complex.normSq (coeffs w) / beablesPerWindingSector := by
        intro i hi
        have hw : P.winding i = w := (Finset.mem_filter.mp hi).2
        rw [toBeableAmplitude, hw, spread_normSq]
      rw [Finset.sum_congr rfl hconst, Finset.sum_const, P.card_each w]
      simp only [nsmul_eq_mul, Nat.cast_ofNat]
      field_simp [beablesPerWindingSector]
    calc (Finset.univ : Finset (Fin 7)).sum (fun w =>
          (Finset.univ.filter (fun i : BeableIndex => P.winding i = w)).sum
            (fun i => Complex.normSq (toBeableAmplitude P coeffs i)))
        = (Finset.univ : Finset (Fin 7)).sum (fun w => Complex.normSq (coeffs w)) := by
          apply Finset.sum_congr rfl
          intro w _
          exact hinner w
      _ = 1 := hnorm

theorem single_sector_coeffs_normalized (w : Fin 7) :
    (Finset.univ : Finset (Fin 7)).sum (fun k => Complex.normSq (if k = w then (1 : ℂ) else 0)) = 1 := by
  rw [Finset.sum_eq_single w (fun b hb hne => by simp [hb, hne, Complex.normSq_zero])
    (fun h => absurd (Finset.mem_univ w) h)]
  simp [Complex.normSq_one]

noncomputable def singleSectorAmplitude (P : BeableWindingPartition) (w : Fin 7) :
    BeableAmplitudeHypothesis :=
  fock_beable_amplitude_normalized P (fun k => if k = w then 1 else 0) (single_sector_coeffs_normalized w)

theorem fock_sector_born_is_one (P : BeableWindingPartition) (w : Fin 7) :
    (singleSectorAmplitude P w).sectorProb w = 1 := by
  unfold BeableAmplitudeHypothesis.sectorProb beableSectorBornWeight sectorBornWeight
  have hfilt :
      Finset.univ.filter (fun i => (singleSectorAmplitude P w).winding i = w) =
        Finset.univ.filter (fun i => P.winding i = w) :=
    rfl
  rw [hfilt]
  have hα :
      ∀ i ∈ Finset.univ.filter (fun i : BeableIndex => P.winding i = w),
        Complex.normSq ((singleSectorAmplitude P w).α i) = 1 / beablesPerWindingSector := by
    intro i hi
    have hw : P.winding i = w := (Finset.mem_filter.mp hi).2
    have hαi : (singleSectorAmplitude P w).α i =
        toBeableAmplitude P (fun k => if k = w then 1 else 0) i := rfl
    rw [hαi, toBeableAmplitude, hw, spread_normSq]
    simp [Complex.normSq_one, if_pos rfl]
  rw [Finset.sum_congr rfl hα, Finset.sum_const, P.card_each w]
  norm_num [beablesPerWindingSector]

noncomputable def kinkModeToSectorCoeffs (modeCoeffs : KinkMode → ℂ) : Fin 7 → ℂ :=
  fun w =>
    (Finset.univ.filter (fun m : KinkMode => kinkModeWinding m = w)).sum
      (fun m => modeCoeffs m)

theorem born_rule_from_fock_lift (P : BeableWindingPartition) (coeffs : Fin 7 → ℂ)
    (hnorm : (Finset.univ : Finset (Fin 7)).sum (fun w => Complex.normSq (coeffs w)) = 1)
    (k : Fin 7) :
    0 ≤ (fock_beable_amplitude_normalized P coeffs hnorm).sectorProb k ∧
    (Finset.univ : Finset (Fin 7)).sum (fock_beable_amplitude_normalized P coeffs hnorm).sectorProb = 1 ∧
    (fock_beable_amplitude_normalized P coeffs hnorm).sectorProb k =
      beableSectorBornWeight (fock_beable_amplitude_normalized P coeffs hnorm).α
        (fock_beable_amplitude_normalized P coeffs hnorm).winding k :=
  born_rule_from_psc_mdl (fock_beable_amplitude_normalized P coeffs hnorm) k

theorem fock_kink_lift_master_bundle (P : BeableWindingPartition) (coeffs : Fin 7 → ℂ)
    (hnorm : (Finset.univ : Finset (Fin 7)).sum (fun w => Complex.normSq (coeffs w)) = 1) :
    (Finset.univ : Finset (Fin 7)).sum (fock_beable_amplitude_normalized P coeffs hnorm).sectorProb = 1 ∧
    n_d_constraints = 5 ∧
    z7CAComplexity fmdl = 14 :=
  ⟨(born_rule_from_psc_mdl (fock_beable_amplitude_normalized P coeffs hnorm) (0 : Fin 7)).2.1,
    d_count_equals_nfam, fmdl_mdl_complexity_eq_14⟩

noncomputable def beableAmplitudeFromFock (P : BeableWindingPartition) (w : Fin 7) :
    BeableAmplitudeHypothesis :=
  singleSectorAmplitude P w

def canonical_kink_quantization_open : Prop :=
  ¬ ∃ (_Q : Unit → KinkFockState), True

def mdl_amplitude_identification_open : Prop :=
  ¬ ∃ (_ident : Fin 7 → ℚ → Prop), True

end UgpLean.Universality.FockSpaceKink
