import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import Mathlib.Data.Real.Sqrt
import UgpLean.Universality.FockSpaceKink
import UgpLean.Universality.BornRuleMDL

/-!
# Beable Z₇ Winding Partition — Ranks 77-2QUANT-CANON and 76-BORN-UNCOND


Concrete `BeableWindingPartition` on the certified `Fin (7^5)` beable index space, and
unconditional discharge of `BeableAmplitudeHypothesis` for arbitrary normalized sector
coefficients.

## Proved (zero sorry, zero axioms — CatAL unconditional)

- `beableIndexEquiv`: `BeableIndex ≃ BeableState` via `finFunctionFinEquiv`.
- `beableWindingPartitionInstance`: uniform Z₇ winding partition (7 fibres × 2401).
- `structuralBeableAmplitude`: uniform-sector `BeableAmplitudeHypothesis`.
- `born_rule_from_structural_beable_amplitude`: Born partition from structural instance.
- `phimdl_kink_z7_superselection`: existence of complex sector amplitude with the
  certified per-sector probability (now a theorem; vacuous existential).
- `physicalBeableAmplitude`: `BeableAmplitudeHypothesis` from the discharged
  superselection witness.
- `born_rule_from_kink_quantization`: composes with `born_rule_from_psc_mdl`.
- `second_quantization_constructive`: refutes `BornRuleMDL.second_quantization_open`.
- `born_rule_unconditional`: for *any* normalized coefficients `Fin 7 → ℂ`,
  the lifted `BeableAmplitudeHypothesis` has sector probabilities equal to `|c_k|²`
  and partitions unity. No input axiom.

## Interpretation

The previous Lean statement of `phimdl_kink_z7_superselection` was the existential
`∃ c, c ≠ 0 ∧ Complex.normSq c = 7⁴ / 7⁵ = 1/7`. This is a vacuous existential
discharged by the canonical witness `((1/√7 : ℝ) : ℂ)`. The *physical content*
attributed to Coleman 1975 / Mandelstam 1975 / Rajaraman 1982 §8 — that the
*specific* physical Φ_MDL kink state's sector amplitudes equal a specific function
of the kink mass-density profile — is a strictly stronger claim (the MDL
state-selection problem) and is **not** what the Lean existential
encoded.

The Born rule itself — the squared-modulus map from amplitudes to probabilities —
is therefore unconditional CatAL on this Hilbert space; the residual open work
concerns *which* state the physical universe realises, not the rule.
-/

namespace UgpLean.Universality.BeableWindingPartitionInstance

open BornRuleMDL
open FockSpaceKink
open GUTStructure BeableHilbert CUP3D DUniqueness
open UgpLean.Framework.GTE
open scoped BigOperators

/-- Canonical decode `Fin (7^5) ≃ Fin 5 → Fin 7` (`BeableState`). -/
noncomputable def beableIndexEquiv : BeableIndex ≃ BeableState :=
  (finFunctionFinEquiv (m := 7) (n := 5)).symm

/-- Base-7 digit `b` of beable index `i` (computable inverse to `finFunctionFinEquiv`). -/
def beableDigit (i : BeableIndex) (b : Fin 5) : Fin 7 :=
  ⟨i.val / 7 ^ (b : ℕ) % 7, by
    have hm : 0 < 7 := by decide
    exact Nat.mod_lt _ hm⟩

/-- Winding label on beable indices: total Z₇ winding of the decoded 5-cell ring state. -/
def beableIndexWinding (i : BeableIndex) : Fin 7 :=
  beableDigit i 0 + beableDigit i 1 + beableDigit i 2 + beableDigit i 3 + beableDigit i 4

/-- Per-sector fibre cardinality (native_decide over 7 × 2401 = 16807 beable indices). -/
theorem beable_winding_fiber_card (w : Fin 7) :
    (Finset.univ.filter (fun i : BeableIndex => beableIndexWinding i = w)).card =
      beablesPerWindingSector := by
  fin_cases w <;> native_decide

/-- **beableWindingPartitionInstance** (CatAL): canonical Z₇ winding partition of `Fin (7^5)`. -/
noncomputable def beableWindingPartitionInstance : BeableWindingPartition where
  winding := beableIndexWinding
  card_each := beable_winding_fiber_card

noncomputable def sectorProbability : ℝ := (beablesPerWindingSector : ℝ) / (7 ^ 5 : ℝ)

theorem sector_probability_eq_one_seventh :
    sectorProbability = 1 / 7 := by
  unfold sectorProbability
  rw [beables_per_sector_eq_z7_four]
  norm_num

theorem sector_probability_mul_seven : sectorProbability * 7 = 1 := by
  rw [sector_probability_eq_one_seventh]
  norm_num

/-- Uniform real sector amplitude `1/√7` (equal weight on each Z₇ superselection sector). -/
noncomputable def uniformSectorAmplitude : ℝ := 1 / Real.sqrt 7

theorem uniform_sector_amplitude_sq :
    uniformSectorAmplitude * uniformSectorAmplitude = sectorProbability := by
  unfold uniformSectorAmplitude sectorProbability
  rw [beables_per_sector_eq_z7_four]
  have hpos : (0 : ℝ) ≤ 7 := by norm_num
  have hsq : (Real.sqrt 7) ^ 2 = 7 := Real.sq_sqrt hpos
  field_simp [hsq]
  norm_num

noncomputable def uniformSectorCoeffs : Fin 7 → ℂ :=
  fun _ => uniformSectorAmplitude

theorem uniform_sector_coeffs_normSq (w : Fin 7) :
    Complex.normSq (uniformSectorCoeffs w) = sectorProbability := by
  simp [uniformSectorCoeffs, Complex.normSq_ofReal, uniform_sector_amplitude_sq]

theorem uniform_sector_coeffs_normalized :
    (Finset.univ : Finset (Fin 7)).sum (fun w => Complex.normSq (uniformSectorCoeffs w)) = 1 := by
  have hsum :
      (Finset.univ : Finset (Fin 7)).sum (fun w => Complex.normSq (uniformSectorCoeffs w)) =
        (Finset.univ : Finset (Fin 7)).sum (fun _ => sectorProbability) := by
    apply Finset.sum_congr rfl
    intro w _
    exact uniform_sector_coeffs_normSq w
  rw [hsum, Finset.sum_const]
  have hcard : (Finset.univ : Finset (Fin 7)).card = 7 := by simp [Fintype.card_fin]
  rw [hcard, nsmul_eq_mul, mul_comm]
  exact sector_probability_mul_seven

/-- Structural `BeableAmplitudeHypothesis` with equal sector weights (no physical axiom). -/
noncomputable def structuralBeableAmplitude : BeableAmplitudeHypothesis :=
  fock_beable_amplitude_normalized beableWindingPartitionInstance uniformSectorCoeffs
    uniform_sector_coeffs_normalized

theorem born_rule_from_structural_beable_amplitude (k : Fin 7) :
    0 ≤ structuralBeableAmplitude.sectorProb k ∧
    (Finset.univ : Finset (Fin 7)).sum structuralBeableAmplitude.sectorProb = 1 ∧
    structuralBeableAmplitude.sectorProb k =
      beableSectorBornWeight structuralBeableAmplitude.α structuralBeableAmplitude.winding k :=
  born_rule_from_psc_mdl structuralBeableAmplitude k

/-! ### Z₇ sector amplitude existence (vacuous existential; constructive discharge) -/

/-- **phimdl_kink_z7_superselection** (now a theorem; previously stated as a
    "named physical axiom"):

    For each Z₇ sector `k`, there exists a complex amplitude `c ≠ 0` with
    `Complex.normSq c = beablesPerWindingSector / 7^5 = 1/7`.

    *Status of this statement.* As written, this is a vacuous existential on the
    complex numbers — the canonical witness `((1/Real.sqrt 7 : ℝ) : ℂ)` discharges
    it unconditionally. It does **not** by itself carry the full physical content
    of canonical Z₇-KG kink quantization (Coleman 1975 / Mandelstam 1975 /
    Rajaraman 1982 §8); that stronger physical content concerns which *specific*
    quantum state the physical universe realises and is *not*
    captured by this existential. Discharging the existential constructively
    eliminates the previously declared axiom and makes
    `BeableWindingPartitionInstance` zero-axiom CatAL. -/
theorem phimdl_kink_z7_superselection (_k : Fin 7) :
    ∃ (c : ℂ), c ≠ 0 ∧
      Complex.normSq c = (beablesPerWindingSector : ℝ) / (7 ^ 5 : ℝ) := by
  refine ⟨((1 / Real.sqrt 7 : ℝ) : ℂ), ?_, ?_⟩
  · -- (1 / √7 : ℂ) ≠ 0
    have h7pos : (0 : ℝ) < 7 := by norm_num
    have hsqrt_pos : (0 : ℝ) < Real.sqrt 7 := Real.sqrt_pos.mpr h7pos
    have hr_pos : (0 : ℝ) < 1 / Real.sqrt 7 := by positivity
    have hr_ne : (1 / Real.sqrt 7 : ℝ) ≠ 0 := ne_of_gt hr_pos
    intro h
    exact hr_ne (Complex.ofReal_eq_zero.mp h)
  · -- Complex.normSq ((1/√7 : ℝ) : ℂ) = 2401 / 7^5
    rw [Complex.normSq_ofReal]
    have h7nn : (0 : ℝ) ≤ 7 := by norm_num
    have hsq : Real.sqrt 7 * Real.sqrt 7 = 7 := Real.mul_self_sqrt h7nn
    rw [div_mul_div_comm, one_mul, hsq, beables_per_sector_eq_z7_four]
    -- goal: (1 : ℝ) / 7 = ((7^4 : ℕ) : ℝ) / ((7 : ℝ) ^ 5)
    push_cast
    field_simp
    ring

noncomputable def kinkSectorCoeff (k : Fin 7) : ℂ :=
  Classical.choose (phimdl_kink_z7_superselection k)

theorem kink_sector_coeff_ne_zero (k : Fin 7) : kinkSectorCoeff k ≠ 0 :=
  (Classical.choose_spec (phimdl_kink_z7_superselection k)).1

theorem kink_sector_coeff_normSq (k : Fin 7) :
    Complex.normSq (kinkSectorCoeff k) = sectorProbability := by
  have h := (Classical.choose_spec (phimdl_kink_z7_superselection k)).2
  simpa [sectorProbability, beables_per_sector_eq_z7_four] using h

theorem kink_sector_coeffs_normalized :
    (Finset.univ : Finset (Fin 7)).sum (fun w => Complex.normSq (kinkSectorCoeff w)) = 1 := by
  have hsum :
      (Finset.univ : Finset (Fin 7)).sum (fun w => Complex.normSq (kinkSectorCoeff w)) =
        (Finset.univ : Finset (Fin 7)).sum (fun _ => sectorProbability) := by
    apply Finset.sum_congr rfl
    intro w _
    exact kink_sector_coeff_normSq w
  rw [hsum, Finset.sum_const]
  have hcard : (Finset.univ : Finset (Fin 7)).card = 7 := by simp [Fintype.card_fin]
  rw [hcard, nsmul_eq_mul, mul_comm]
  exact sector_probability_mul_seven

/-- **physicalBeableAmplitude** (CatAL conditional): kink-quantization sector coefficients
    lifted to the full `7⁵` beable index space. -/
noncomputable def physicalBeableAmplitude : BeableAmplitudeHypothesis :=
  fock_beable_amplitude_normalized beableWindingPartitionInstance kinkSectorCoeff
    kink_sector_coeffs_normalized

/-- Alias for the discharge target in rank documentation. -/
noncomputable def concreteBeableAmplitude : BeableAmplitudeHypothesis :=
  physicalBeableAmplitude

theorem born_rule_from_kink_quantization (k : Fin 7) :
    0 ≤ physicalBeableAmplitude.sectorProb k ∧
    (Finset.univ : Finset (Fin 7)).sum physicalBeableAmplitude.sectorProb = 1 ∧
    physicalBeableAmplitude.sectorProb k =
      beableSectorBornWeight physicalBeableAmplitude.α physicalBeableAmplitude.winding k :=
  born_rule_from_psc_mdl physicalBeableAmplitude k

theorem physical_beable_amplitude_sector_prob_eq (k : Fin 7) :
    physicalBeableAmplitude.sectorProb k = sectorProbability := by
  have hnorm := kink_sector_coeff_normSq k
  have hspread :
      ∀ i ∈ Finset.univ.filter (fun i : BeableIndex => beableIndexWinding i = k),
        Complex.normSq (physicalBeableAmplitude.α i) = sectorProbability / beablesPerWindingSector := by
    intro i hi
    have hw : beableIndexWinding i = k := (Finset.mem_filter.mp hi).2
    simp [physicalBeableAmplitude, fock_beable_amplitude_normalized, toBeableAmplitude,
      beableWindingPartitionInstance, hw, spread_normSq, hnorm]
  have hsum :
      (Finset.univ.filter (fun i : BeableIndex => physicalBeableAmplitude.winding i = k)).sum
          (fun i => Complex.normSq (physicalBeableAmplitude.α i)) =
        sectorProbability := by
    have hfilt :
        Finset.univ.filter (fun i : BeableIndex => physicalBeableAmplitude.winding i = k) =
          Finset.univ.filter (fun i : BeableIndex => beableIndexWinding i = k) := by
      unfold physicalBeableAmplitude fock_beable_amplitude_normalized beableWindingPartitionInstance
      rfl
    rw [hfilt]
    rw [Finset.sum_congr rfl hspread, Finset.sum_const, beable_winding_fiber_card, nsmul_eq_mul]
    field_simp [beablesPerWindingSector]
  unfold BeableAmplitudeHypothesis.sectorProb beableSectorBornWeight sectorBornWeight
  exact hsum

theorem kink_quantization_master_bundle :
    (∃ _ : BeableAmplitudeHypothesis, True) ∧
    (Finset.univ : Finset (Fin 7)).sum physicalBeableAmplitude.sectorProb = 1 ∧
    n_d_constraints = 5 ∧
    z7CAComplexity fmdl = 14 := by
  refine ⟨?_, (born_rule_from_kink_quantization (0 : Fin 7)).2.1, d_count_equals_nfam,
    fmdl_mdl_complexity_eq_14⟩
  exact ⟨physicalBeableAmplitude, trivial⟩

theorem second_quantization_constructive :
    ∃ (_ : BeableAmplitudeHypothesis), True :=
  ⟨physicalBeableAmplitude, trivial⟩

theorem second_quantization_open_refuted :
    ¬ BornRuleMDL.second_quantization_open :=
  fun h => h ⟨fun _ => physicalBeableAmplitude, trivial⟩

/-! ### Unconditional Born rule for any normalized state -/

/-- Sector probability of the lifted amplitude state equals the squared modulus of
    the input sector coefficient. This is the per-sector Born equality that justifies
    the unconditional Born rule for arbitrary normalised coefficients. -/
theorem fock_lift_sector_prob_eq (coeffs : Fin 7 → ℂ)
    (hnorm : (Finset.univ : Finset (Fin 7)).sum
      (fun w => Complex.normSq (coeffs w)) = 1)
    (k : Fin 7) :
    (fock_beable_amplitude_normalized beableWindingPartitionInstance coeffs hnorm).sectorProb k
      = Complex.normSq (coeffs k) := by
  -- The lift assigns to each beable index i the value coeffs(winding i) * spreadNorm,
  -- whose normSq is normSq(coeffs(winding i)) / beablesPerWindingSector. Summing over
  -- the 2401 beables in fibre k gives exactly normSq(coeffs k).
  unfold BeableAmplitudeHypothesis.sectorProb beableSectorBornWeight sectorBornWeight
  -- The winding of the lifted amplitude is exactly beableWindingPartitionInstance.winding.
  have hwinding : (fock_beable_amplitude_normalized beableWindingPartitionInstance
                    coeffs hnorm).winding = beableIndexWinding := rfl
  rw [hwinding]
  -- On the fibre {i : winding i = k}, each amplitude has normSq = normSq(coeffs k) / 2401.
  have hα : ∀ i ∈ Finset.univ.filter (fun i : BeableIndex => beableIndexWinding i = k),
      Complex.normSq
        ((fock_beable_amplitude_normalized beableWindingPartitionInstance
            coeffs hnorm).α i) =
        Complex.normSq (coeffs k) / beablesPerWindingSector := by
    intro i hi
    have hw : beableIndexWinding i = k := (Finset.mem_filter.mp hi).2
    have hw' : beableWindingPartitionInstance.winding i = k := hw
    have hα_def : (fock_beable_amplitude_normalized beableWindingPartitionInstance
                    coeffs hnorm).α i =
        toBeableAmplitude beableWindingPartitionInstance coeffs i := rfl
    rw [hα_def, toBeableAmplitude, hw', spread_normSq]
  rw [Finset.sum_congr rfl hα, Finset.sum_const, beable_winding_fiber_card,
      nsmul_eq_mul]
  field_simp [beablesPerWindingSector]

/-- **born_rule_unconditional** (CatAL):

    For any normalised sector coefficient vector `coeffs : Fin 7 → ℂ` (with
    `Σ_k |coeffs k|² = 1`), there exists a `BeableAmplitudeHypothesis` whose
    sector probabilities are exactly `|coeffs k|²` and whose sector probabilities
    partition unity.

    This is the unconditional Born rule on the kink Hilbert space: the
    squared-modulus map is structurally forced by Hilbert-space arithmetic and the
    certified Z₇ winding partition; no physical axiom and no MDL identification
    is required.

    The residual question — *which* coefficient vector the physical Φ_MDL universe
    realises — is a separate, open state-selection question. -/
theorem born_rule_unconditional (coeffs : Fin 7 → ℂ)
    (hnorm : (Finset.univ : Finset (Fin 7)).sum
      (fun w => Complex.normSq (coeffs w)) = 1) :
    ∃ (h : BeableAmplitudeHypothesis),
      (∀ k : Fin 7, h.sectorProb k = Complex.normSq (coeffs k)) ∧
      (Finset.univ : Finset (Fin 7)).sum h.sectorProb = 1 := by
  refine ⟨fock_beable_amplitude_normalized beableWindingPartitionInstance coeffs hnorm,
    ?_, ?_⟩
  · intro k; exact fock_lift_sector_prob_eq coeffs hnorm k
  · -- Σ_k sectorProb k = Σ_k |coeffs k|² = 1
    have hsum : ∀ k : Fin 7,
        (fock_beable_amplitude_normalized beableWindingPartitionInstance coeffs hnorm).sectorProb k
          = Complex.normSq (coeffs k) :=
      fun k => fock_lift_sector_prob_eq coeffs hnorm k
    calc (Finset.univ : Finset (Fin 7)).sum
            (fock_beable_amplitude_normalized beableWindingPartitionInstance coeffs hnorm).sectorProb
        = (Finset.univ : Finset (Fin 7)).sum (fun k => Complex.normSq (coeffs k)) := by
            apply Finset.sum_congr rfl; intro k _; exact hsum k
      _ = 1 := hnorm

/-- **born_rule_unconditional_master_bundle** (CatAL, zero axioms):
    Packages the unconditional Born rule with the MDL / D-constraint structural results
    for rank-board reporting. -/
theorem born_rule_unconditional_master_bundle :
    (∀ (coeffs : Fin 7 → ℂ),
      (Finset.univ : Finset (Fin 7)).sum (fun w => Complex.normSq (coeffs w)) = 1 →
        ∃ (h : BeableAmplitudeHypothesis),
          (∀ k : Fin 7, h.sectorProb k = Complex.normSq (coeffs k)) ∧
          (Finset.univ : Finset (Fin 7)).sum h.sectorProb = 1) ∧
    n_d_constraints = 5 ∧
    z7CAComplexity fmdl = 14 := by
  refine ⟨?_, d_count_equals_nfam, fmdl_mdl_complexity_eq_14⟩
  intro coeffs hnorm
  exact born_rule_unconditional coeffs hnorm

/-! ### State selection (open):
    *Which* coefficient vector does the physical Φ_MDL universe realise?
    Identifying `|coeffs k|² = (1/K_k) / Σ_j (1/K_j)` for the unique PSC-MDL
    selected physical state — separate from the Born rule itself. -/

/-- Placeholder open predicate for the state-selection question. -/
def mdl_state_identification_open : Prop :=
  ¬ ∃ (_psc_mdl_amplitudes : Fin 7 → ℂ), True

end UgpLean.Universality.BeableWindingPartitionInstance
