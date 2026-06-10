import Mathlib.Tactic
import Mathlib.Data.Real.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Analysis.Calculus.Deriv.Mul
import Mathlib.Analysis.Calculus.Deriv.Pow
import Mathlib.Analysis.Calculus.Deriv.Add
import Mathlib.Analysis.Calculus.MeanValue
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Data.Nat.Cast.Order.Basic
import UgpLean.Universality.GaugeInvariance
import UgpLean.Universality.SylowIndexCouplingHierarchy

/-!
# Z₇ vacuum-sector selection certificates

Certifies the coupling shift-breaking, χ-kinetic inequivalence, wall-bias minimum,
Z₃-orbit transversal, BPS-window exclusion for periodic competitors, compact-completion
minimum, scalar CW step inequality, and S¹ seam discontinuity.

Complements `z7_vacuum_sectors_equiprobable` (Z₇-periodic observables only) and
`phimdl_coupling_gauge_invariant` (Z₃ gauge invariance, not Z₇ shift invariance).

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Physics.ZSevenVacuumSelection

open Real
open UgpLean.Universality.GaugeInvariance
open UgpLean.Universality.SylowIndexCoupling

noncomputable section

/-- Canonical GTE coupling ε = N₇/N₃² = 7/9. -/
def gteEpsilon : ℝ := (7 : ℝ) / 9

theorem gteEpsilon_eq : gteEpsilon = (7 : ℝ) / 9 := rfl

theorem gteEpsilon_pos : 0 < gteEpsilon := by
  unfold gteEpsilon
  norm_num

/-- Vacuum label φ_k = 2πk/7 on the real axis. -/
def vacuumAngle (k : Fin 7) : ℝ := 2 * π * (k : ℝ) / 7

/-- The Φ_MDL coupling density V_coupling = ε|φ|²(D_μχ)² at a given φ and squared
    covariant derivative X = (D_μχ)². -/
def vcouplingDensity (epsilon phi X : ℝ) : ℝ := epsilon * phi ^ 2 * X

/-- χ-sector kinetic normalization Z_k = 1 + 2εφ_k² at the canonical ε = 7/9. -/
def chiKineticNorm (k : Fin 7) : ℝ :=
  1 + 2 * gteEpsilon * (vacuumAngle k) ^ 2

/-- Wall-bias coupling weight εφ_k²X used in the inward-channel vacuum selection. -/
def wallBiasWeight (epsilon X : ℝ) (k : Fin 7) : ℝ :=
  epsilon * (vacuumAngle k) ^ 2 * X

/-- Minimal compact completion profile 2(1 − cos φ) evaluated at φ_k. -/
def compactCompletion (k : Fin 7) : ℝ := 2 * (1 - cos (vacuumAngle k))

/-- Effective near-vacuum quadratic coupling for the literal φ² profile. -/
def phiSqEffectiveCoupling : ℚ := gteCouplingEpsilon * 1

/-- Effective near-vacuum quadratic coupling for the Z₇-periodic profile (1 − cos 7φ)
    at natural normalization: ε · f''(0)/2 with f''(0) = 49. -/
def periodicProfileEffectiveCoupling : ℚ := gteCouplingEpsilon * (49 / 2)

/-- Scalar-channel Coleman–Weinberg step function between adjacent vacua. -/
def scalarCwStep (r : ℝ) : ℝ := 3 / 2 - (2 * log r + 3 / 2) / r ^ 2

/-- Literal φ² coupling on the seam φ = 0⁺ vs φ = 2π⁻: ratio Z(2π)/Z(0). -/
def couplingSeamRatio : ℝ := 1 + 2 * gteEpsilon * (2 * π) ^ 2

-- ─────────────────────────────────────────────────────────────────────────
-- V_coupling breaks the Z₇ shift
-- ─────────────────────────────────────────────────────────────────────────

theorem two_pi_over_seven_ne_zero : (2 : ℝ) * π / 7 ≠ 0 := by
  have hπ : (0 : ℝ) < π := Real.pi_pos
  intro h
  have h2 : (2 : ℝ) * π = 0 := by linarith [h]
  linarith [mul_pos (by norm_num : (0 : ℝ) < 2) hπ]

theorem vacuum_angle_shift (k : Fin 7) :
    vacuumAngle k + 2 * π / 7 = 2 * π * ((k : ℕ) + 1 : ℝ) / 7 := by
  unfold vacuumAngle
  ring

theorem vacuum_angle_sq_shift_ne (k : Fin 7) :
    (vacuumAngle k + 2 * π / 7) ^ 2 ≠ vacuumAngle k ^ 2 := by
  rw [vacuum_angle_shift]
  fin_cases k <;> simp [vacuumAngle] <;> norm_num <;>
    nlinarith [Real.pi_pos, Real.pi_gt_d6, Real.pi_lt_d6]

/-- The canonical coupling density εφ²X is not invariant under the Z₇ shift φ ↦ φ + 2π/7
    at any vacuum φ_k when ε > 0 and X ≠ 0. Complements `phimdl_coupling_gauge_invariant`. -/
theorem vcoupling_breaks_z7_shift
    (k : Fin 7) (epsilon X : ℝ) (heps : 0 < epsilon) (hX : X ≠ 0) :
    vcouplingDensity epsilon (vacuumAngle k + 2 * π / 7) X ≠
      vcouplingDensity epsilon (vacuumAngle k) X := by
  unfold vcouplingDensity
  intro h
  have hφne := vacuum_angle_sq_shift_ne k
  have hepsX : epsilon * X ≠ 0 := mul_ne_zero (ne_of_gt heps) hX
  have hdiff : epsilon * X *
      ((vacuumAngle k + 2 * π / 7) ^ 2 - vacuumAngle k ^ 2) = 0 := by
    linear_combination h - epsilon * vacuumAngle k ^ 2 * X
  have hφdiff : (vacuumAngle k + 2 * π / 7) ^ 2 - vacuumAngle k ^ 2 ≠ 0 :=
    sub_ne_zero.mpr hφne
  rcases mul_eq_zero.mp hdiff with hZX | hφzero
  · exact absurd hZX hepsX
  · exact hφdiff hφzero

-- ─────────────────────────────────────────────────────────────────────────
-- χ-kinetic inequivalence across Z₇ vacua
-- ─────────────────────────────────────────────────────────────────────────

theorem chiKineticNorm_zero : chiKineticNorm ⟨0, by decide⟩ = 1 := by
  unfold chiKineticNorm vacuumAngle gteEpsilon
  simp

theorem chiKineticNorm_eq_one {k : Fin 7} (hk : k.val = 0) : chiKineticNorm k = 1 := by
  match k with
  | ⟨0, _⟩ => exact chiKineticNorm_zero
  | ⟨n + 1, hn⟩ => simp at hk

theorem vacuum_angle_sq_mono {k₁ k₂ : Fin 7} (h : k₁ < k₂) :
    vacuumAngle k₁ ^ 2 < vacuumAngle k₂ ^ 2 := by
  unfold vacuumAngle
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hk : (k₁ : ℝ) < (k₂ : ℝ) := by exact_mod_cast h
  have hangle : 2 * π * (k₁ : ℝ) / 7 < 2 * π * (k₂ : ℝ) / 7 := by
    nlinarith [hπ, hk]
  have hnonneg₁ : 0 ≤ 2 * π * (k₁ : ℝ) / 7 := by positivity
  have hnonneg₂ : 0 ≤ 2 * π * (k₂ : ℝ) / 7 := by positivity
  have hsq : (2 * π * (k₁ : ℝ) / 7) ^ 2 < (2 * π * (k₂ : ℝ) / 7) ^ 2 := by
    nlinarith [hnonneg₁, hnonneg₂, hangle]
  simpa using hsq

theorem chiKineticNorm_strictMono {k₁ k₂ : Fin 7} (h : k₁ < k₂) :
    chiKineticNorm k₁ < chiKineticNorm k₂ := by
  unfold chiKineticNorm
  have hε : 0 < 2 * gteEpsilon := by
    unfold gteEpsilon
    norm_num
  have hsq := vacuum_angle_sq_mono h
  nlinarith [hε, gteEpsilon_pos]

theorem chiKineticNorm_mono {k₁ k₂ : Fin 7} (h : k₁ ≤ k₂) :
    chiKineticNorm k₁ ≤ chiKineticNorm k₂ := by
  rcases eq_or_lt_of_le h with rfl | hlt
  · rfl
  · exact le_of_lt (chiKineticNorm_strictMono hlt)

theorem chiKineticNorm_six_gt_46 : (46 : ℝ) < chiKineticNorm ⟨6, by decide⟩ := by
  unfold chiKineticNorm vacuumAngle gteEpsilon
  have hπ_lo := Real.pi_gt_d6
  have hπ_sq_lo : (9.869588 : ℝ) < π ^ 2 := by nlinarith [sq_pos_of_ne_zero Real.pi_ne_zero, hπ_lo]
  have hcore : (45 : ℝ) < 32 * π ^ 2 / 7 := by nlinarith [hπ_sq_lo]
  norm_num [div_eq_mul_inv]
  linarith

/-- The seven vacua are pairwise inequivalent in the full Lagrangian via Z_k = 1 + 2εφ_k²
    at ε = 7/9; Z₆/Z₀ > 46. -/
theorem z7_vacua_chi_kinetic_inequivalent :
    (∀ k₁ k₂ : Fin 7, k₁ < k₂ → chiKineticNorm k₁ < chiKineticNorm k₂) ∧
    (46 : ℝ) < chiKineticNorm ⟨6, by decide⟩ / chiKineticNorm ⟨0, by decide⟩ := by
  refine ⟨fun k₁ k₂ h => chiKineticNorm_strictMono h, ?_⟩
  have hden := chiKineticNorm_eq_one (k := ⟨0, by decide⟩) rfl
  rw [hden, div_one]
  exact chiKineticNorm_six_gt_46

-- ─────────────────────────────────────────────────────────────────────────
-- wall-bias minimum unique at k = 0
-- ─────────────────────────────────────────────────────────────────────────

theorem vacuum_angle_sq_pos {k : Fin 7} (hk : k ≠ ⟨0, by decide⟩) :
    0 < vacuumAngle k ^ 2 := by
  unfold vacuumAngle
  fin_cases k <;> simp at hk ⊢ <;> try contradiction
  all_goals nlinarith [Real.pi_pos, Real.pi_gt_d6]

theorem wall_bias_weight_pos {k : Fin 7} (epsilon X : ℝ) (heps : 0 < epsilon) (hX : 0 < X)
    (hk : k ≠ ⟨0, by decide⟩) :
    0 < wallBiasWeight epsilon X k := by
  unfold wallBiasWeight
  exact mul_pos (mul_pos heps (vacuum_angle_sq_pos hk)) hX

theorem wall_bias_weight_zero (epsilon X : ℝ) :
    wallBiasWeight epsilon X ⟨0, by decide⟩ = 0 := by
  unfold wallBiasWeight vacuumAngle
  simp

theorem wall_bias_minimum_unique (epsilon X : ℝ) (heps : 0 < epsilon) (hX : 0 < X) :
    (∀ k : Fin 7, wallBiasWeight epsilon X ⟨0, by decide⟩ ≤ wallBiasWeight epsilon X k) ∧
    (∀ k : Fin 7, k ≠ ⟨0, by decide⟩ →
      wallBiasWeight epsilon X ⟨0, by decide⟩ < wallBiasWeight epsilon X k) := by
  refine ⟨fun k => ?_, fun k hk => ?_⟩
  · rw [wall_bias_weight_zero]
    by_cases h : k = ⟨0, by decide⟩
    · rw [h, wall_bias_weight_zero]
    · exact le_of_lt (wall_bias_weight_pos epsilon X heps hX h)
  · rw [wall_bias_weight_zero]
    exact wall_bias_weight_pos epsilon X heps hX hk

-- ─────────────────────────────────────────────────────────────────────────
-- {0,1,5} is a ⟨×2⟩ orbit transversal in Z₇
-- ─────────────────────────────────────────────────────────────────────────

/-- ⟨×2⟩ orbit of a winding label in Z₇. -/
def z3Orbit (k : ZMod 7) : Finset (ZMod 7) :=
  {k, 2 * k, 4 * k}

theorem z3_orbit_zero : z3Orbit 0 = {0} := by decide

theorem z3_orbit_one : z3Orbit 1 = {1, 2, 4} := by decide

theorem z3_orbit_three : z3Orbit 3 = {3, 5, 6} := by decide

def groundStateTransversal : Finset (ZMod 7) := {0, 1, 5}

theorem gs_set_is_z3_orbit_transversal :
    groundStateTransversal ∩ z3Orbit 0 = {0} ∧
    groundStateTransversal ∩ z3Orbit 1 = {1} ∧
    groundStateTransversal ∩ z3Orbit 3 = {5} := by
  decide

-- ─────────────────────────────────────────────────────────────────────────
-- periodic profile fails the BPS window; φ² profile passes
-- ─────────────────────────────────────────────────────────────────────────

theorem periodic_profile_effective_coupling_val :
    periodicProfileEffectiveCoupling = 343 / 18 := by
  unfold periodicProfileEffectiveCoupling gteCouplingEpsilon
    f21CommutatorNormSq f21IrrepNormSq z7OrbitPeriod z3ColorOrder
  norm_num

theorem phiSqEffectiveCoupling_eq : phiSqEffectiveCoupling = gteCouplingEpsilon := by
  unfold phiSqEffectiveCoupling
  ring

theorem phi_sq_effective_coupling_val :
    phiSqEffectiveCoupling = 7 / 9 := by
  rw [phiSqEffectiveCoupling_eq]
  exact epsilon_coupling_f21.1

theorem periodic_profile_outside_bps_window :
    ¬ (bpsCouplingLower < periodicProfileEffectiveCoupling ∧
      periodicProfileEffectiveCoupling < bpsCouplingUpper) := by
  rw [periodic_profile_effective_coupling_val]
  unfold bpsCouplingLower bpsCouplingUpper
  norm_num

theorem phi_sq_inside_bps_window :
    bpsCouplingLower < phiSqEffectiveCoupling ∧
      phiSqEffectiveCoupling < bpsCouplingUpper := by
  rw [phiSqEffectiveCoupling_eq]
  exact epsilon_in_bps_range

/-- The Z₇-periodic competitor profile (1 − cos 7φ) is BPS-incompatible at ε = 7/9,
    while the literal φ² profile lies in the certified window [4/9, 4/5]. -/
theorem vcoup_periodic_profile_fails_bps_window :
    ¬ (bpsCouplingLower < periodicProfileEffectiveCoupling ∧
      periodicProfileEffectiveCoupling < bpsCouplingUpper) ∧
    bpsCouplingLower < phiSqEffectiveCoupling ∧
      phiSqEffectiveCoupling < bpsCouplingUpper := by
  exact ⟨periodic_profile_outside_bps_window, phi_sq_inside_bps_window⟩

-- ─────────────────────────────────────────────────────────────────────────
-- compact completion minimum at k = 0
-- ─────────────────────────────────────────────────────────────────────────

theorem compact_completion_nonneg (k : Fin 7) : 0 ≤ compactCompletion k := by
  unfold compactCompletion
  have := Real.cos_le_one (vacuumAngle k)
  linarith

theorem vacuum_angle_lt_two_pi (k : Fin 7) (hk : k ≠ ⟨0, by decide⟩) :
    2 * π * (k : ℝ) / 7 < 2 * π := by
  fin_cases k <;> simp at hk ⊢ <;> nlinarith [Real.pi_pos, Real.pi_gt_d6]

theorem vacuum_angle_pos (k : Fin 7) (hk : k ≠ ⟨0, by decide⟩) :
    0 < 2 * π * (k : ℝ) / 7 := by
  fin_cases k <;> simp at hk ⊢ <;> nlinarith [Real.pi_pos, Real.pi_gt_d6]

theorem compact_completion_eq_zero_iff (k : Fin 7) :
    compactCompletion k = 0 ↔ k = ⟨0, by decide⟩ := by
  unfold compactCompletion vacuumAngle
  constructor
  · intro h
    have hcos : cos (2 * π * (k : ℝ) / 7) = 1 := by linarith
    by_cases hk : k = ⟨0, by decide⟩
    · exact hk
    · exfalso
      have hneg : -(2 * π) < 2 * π * (k : ℝ) / 7 :=
        lt_trans (neg_lt_zero.mpr (mul_pos (by norm_num) Real.pi_pos)) (vacuum_angle_pos k hk)
      have hpos : 2 * π * (k : ℝ) / 7 < 2 * π := vacuum_angle_lt_two_pi k hk
      have hangle : 2 * π * (k : ℝ) / 7 = 0 :=
        (Real.cos_eq_one_iff_of_lt_of_lt hneg hpos).mp hcos
      exact ne_of_gt (vacuum_angle_pos k hk) hangle
  · rintro rfl
    simp [vacuumAngle]

theorem compact_completion_zero :
    compactCompletion ⟨0, by decide⟩ = 0 := by
  simp [compactCompletion, vacuumAngle]

theorem compact_completion_pos {k : Fin 7} (hk : k ≠ ⟨0, by decide⟩) :
    0 < compactCompletion k := by
  unfold compactCompletion vacuumAngle
  have hcosne : cos (2 * π * (k : ℝ) / 7) ≠ 1 := by
    intro hcos
    have hneg : -(2 * π) < 2 * π * (k : ℝ) / 7 :=
      lt_trans (neg_lt_zero.mpr (mul_pos (by norm_num) Real.pi_pos)) (vacuum_angle_pos k hk)
    have hpos : 2 * π * (k : ℝ) / 7 < 2 * π := vacuum_angle_lt_two_pi k hk
    have hangle : 2 * π * (k : ℝ) / 7 = 0 :=
      (Real.cos_eq_one_iff_of_lt_of_lt hneg hpos).mp hcos
    exact ne_of_gt (vacuum_angle_pos k hk) hangle
  have hcos : cos (2 * π * (k : ℝ) / 7) < 1 :=
    lt_of_le_of_ne (Real.cos_le_one _) hcosne
  linarith

/-- The compact completion 2(1 − cos(2πk/7)) is nonnegative with unique zero at k = 0. -/
theorem compact_completion_minimum_at_k0 :
    (∀ k : Fin 7, 0 ≤ compactCompletion k) ∧
    (∀ k : Fin 7, compactCompletion k = 0 ↔ k = ⟨0, by decide⟩) ∧
    (∀ k : Fin 7, k ≠ ⟨0, by decide⟩ → 0 < compactCompletion k) := by
  refine ⟨compact_completion_nonneg, ?_, fun k hk => compact_completion_pos hk⟩
  exact compact_completion_eq_zero_iff

-- ─────────────────────────────────────────────────────────────────────────
-- scalar CW step inward
-- ─────────────────────────────────────────────────────────────────────────

theorem scalarCwStep_one : scalarCwStep 1 = 0 := by
  unfold scalarCwStep
  simp [log_one]

/-- Numerator of `scalarCwStep` after clearing the denominator r². -/
def scalarCwNumerator (r : ℝ) : ℝ := (3 / 2) * r ^ 2 - 2 * log r - 3 / 2

theorem scalarCwNumerator_one : scalarCwNumerator 1 = 0 := by
  unfold scalarCwNumerator
  simp [log_one]

theorem scalarCwStep_eq_div (r : ℝ) (hr : r ≠ 0) :
    scalarCwStep r = scalarCwNumerator r / r ^ 2 := by
  unfold scalarCwStep scalarCwNumerator
  field_simp [hr, pow_two]
  ring

theorem hasDerivAt_scalarCwNumerator (r : ℝ) (hr : r ≠ 0) :
    HasDerivAt scalarCwNumerator (3 * r - 2 / r) r := by
  unfold scalarCwNumerator
  have hquad := HasDerivAt.const_mul (3 / 2 : ℝ) (hasDerivAt_pow 2 r)
  have hlog := HasDerivAt.const_mul (2 : ℝ) (HasDerivAt.log (hasDerivAt_id r) hr)
  have hinner := HasDerivAt.sub hquad hlog
  have h := (hasDerivAt_sub_const_iff (3 / 2 : ℝ)).mpr hinner
  have hderiv : (3 / 2 : ℝ) * (2 * r ^ (1 : ℕ)) - (2 : ℝ) * (1 / id r) = 3 * r - 2 / r := by
    simp only [pow_one, id, one_div]
    field_simp [hr]
  exact h.congr_deriv hderiv

theorem scalarCwNumerator_deriv_eq (r : ℝ) (hr : r ≠ 0) :
    deriv scalarCwNumerator r = 3 * r - 2 / r :=
  (hasDerivAt_scalarCwNumerator r hr).deriv

theorem scalarCwNumerator_deriv_pos (r : ℝ) (hr : 1 ≤ r) :
    0 < deriv scalarCwNumerator r := by
  have hr0 : 0 < r := by nlinarith [hr]
  rw [scalarCwNumerator_deriv_eq r (ne_of_gt hr0)]
  have hnum : (2 : ℝ) < 3 * r ^ 2 := by nlinarith [hr]
  have hlt : 2 / r < 3 * r := by
    rw [div_lt_iff₀ hr0]
    nlinarith [hnum]
  linarith

theorem scalarCwNumerator_contOn (r : ℝ) (_hr : 1 < r) :
    ContinuousOn scalarCwNumerator (Set.Icc 1 r) := by
  unfold scalarCwNumerator
  have hsubset : Set.Icc 1 r ⊆ ({0} : Set ℝ)ᶜ :=
    fun x hx => ne_of_gt (zero_lt_one.trans_le hx.1)
  refine ContinuousOn.sub
    (ContinuousOn.sub ((continuousOn_pow 2).const_mul (3 / 2 : ℝ))
      ((Real.continuousOn_log.mono hsubset).const_mul (2 : ℝ)))
    continuousOn_const

theorem scalarCwNumerator_diffOn (r : ℝ) (_hr : 1 < r) :
    DifferentiableOn ℝ scalarCwNumerator (Set.Ioo 1 r) := by
  intro x hx
  exact (hasDerivAt_scalarCwNumerator x (ne_of_gt (lt_trans zero_lt_one hx.1))).differentiableAt.differentiableWithinAt

theorem scalarCwNumerator_pos (r : ℝ) (hr : 1 < r) : 0 < scalarCwNumerator r := by
  obtain ⟨c, hc, hEq⟩ :=
    exists_deriv_eq_slope scalarCwNumerator hr
      (scalarCwNumerator_contOn r hr) (scalarCwNumerator_diffOn r hr)
  have hc1 : 1 < c := hc.1
  have hderivc : 0 < deriv scalarCwNumerator c := scalarCwNumerator_deriv_pos c (le_of_lt hc1)
  have hr1 : 0 < r - 1 := sub_pos.mpr hr
  have hEq' : deriv scalarCwNumerator c * (r - 1) = scalarCwNumerator r - scalarCwNumerator 1 := by
    have := congrArg (fun t => t * (r - 1)) hEq
    field_simp [hr1.ne'] at this
    linarith
  have hpos : 0 < deriv scalarCwNumerator c * (r - 1) := mul_pos hderivc hr1
  rw [hEq', scalarCwNumerator_one] at hpos
  linarith

theorem scalarCwStep_pos (r : ℝ) (hr : 1 < r) : 0 < scalarCwStep r := by
  have hr0 : 0 < r := lt_trans zero_lt_one hr
  rw [scalarCwStep_eq_div r (ne_of_gt hr0)]
  apply div_pos (scalarCwNumerator_pos r hr)
  exact pow_pos hr0 2

/-- The scalar-channel Coleman–Weinberg step G(r) is strictly positive for r > 1. -/
theorem scalar_cw_step_inward (r : ℝ) (hr : 1 < r) : 0 < scalarCwStep r :=
  scalarCwStep_pos r hr

-- ─────────────────────────────────────────────────────────────────────────
-- seam discontinuity
-- ─────────────────────────────────────────────────────────────────────────

theorem coupling_seam_ratio_gt_56 : (56 : ℝ) < couplingSeamRatio := by
  unfold couplingSeamRatio gteEpsilon
  have hπ_lo := Real.pi_gt_d6
  have hπ_sq_lo : (9.869588 : ℝ) < π ^ 2 := by
    nlinarith [sq_pos_of_ne_zero (show π ≠ 0 from Real.pi_ne_zero), hπ_lo]
  norm_num
  nlinarith [hπ_sq_lo]

theorem couplingSeamRatio_eq_alt :
    couplingSeamRatio = 1 + 8 * π ^ 2 * gteEpsilon := by
  unfold couplingSeamRatio gteEpsilon
  ring

/-- The literal φ² coupling is not single-valued under φ ~ φ + 2π: the seam ratio exceeds 56. -/
theorem z7_coupling_seam_discontinuity :
    (56 : ℝ) < 1 + 8 * π ^ 2 * gteEpsilon ∧
    couplingSeamRatio = 1 + 8 * π ^ 2 * gteEpsilon := by
  refine ⟨?_, couplingSeamRatio_eq_alt⟩
  rw [← couplingSeamRatio_eq_alt]
  exact coupling_seam_ratio_gt_56

-- ─────────────────────────────────────────────────────────────────────────
-- boundary-sensitivity coefficient positive
-- ─────────────────────────────────────────────────────────────────────────

/-- Villain color coupling `e² = 7/2` from the Sylow hierarchy. -/
def colorESquared : ℝ := (7 : ℝ) / 2

/-- χ-sector mass parameter at the SCC identification `g = m_τ` (GeV). -/
def chiMassGeV : ℝ := (1776860000 : ℝ) / 1000000000

/-- Kinetic normalization at vacuum label `k = 1`. -/
def z1KineticNorm : ℝ := chiKineticNorm ⟨1, by decide⟩

/-- Boundary-sensitivity coefficient `3e⁴(Z₁²−1) + g⁴(Z₁⁻²−1)`. -/
def boundarySensitivityCoeff : ℝ :=
  3 * colorESquared ^ 2 * (z1KineticNorm ^ 2 - 1) +
    chiMassGeV ^ 4 * ((z1KineticNorm ^ 2)⁻¹ - 1)

theorem z1_kinetic_norm_gt_one : (1 : ℝ) < z1KineticNorm := by
  unfold z1KineticNorm chiKineticNorm vacuumAngle gteEpsilon
  have hπ : (0 : ℝ) < π := Real.pi_pos
  have hangle : 0 < 2 * π / 7 := by nlinarith [hπ, Real.pi_gt_d6]
  nlinarith [gteEpsilon_pos, hangle, Real.pi_gt_d6]

theorem z1_kinetic_norm_gt_two : (2 : ℝ) < z1KineticNorm := by
  unfold z1KineticNorm chiKineticNorm vacuumAngle gteEpsilon
  have hπ_lo := Real.pi_gt_d6
  have hπ_hi := Real.pi_lt_d6
  nlinarith [gteEpsilon_pos, hπ_lo, hπ_hi]

theorem z1_kinetic_norm_lt_three : z1KineticNorm < (3 : ℝ) := by
  unfold z1KineticNorm chiKineticNorm vacuumAngle gteEpsilon
  have hπ_hi := Real.pi_lt_d6
  have hπ_lo := Real.pi_gt_d6
  nlinarith [sq_pos_of_ne_zero Real.pi_ne_zero, hπ_hi, hπ_lo]

theorem z1_kinetic_norm_pos : 0 < z1KineticNorm := by
  linarith [z1_kinetic_norm_gt_one]

theorem z1_sq_minus_one_pos : 0 < z1KineticNorm ^ 2 - 1 := by
  nlinarith [z1_kinetic_norm_gt_one]

theorem z1_inv_sq_lt_one : (z1KineticNorm ^ 2)⁻¹ < 1 := by
  have hz2 : 1 < z1KineticNorm ^ 2 := by nlinarith [z1_kinetic_norm_gt_one]
  exact inv_lt_one_of_one_lt₀ hz2

theorem z1_inv_sq_minus_one_neg : (z1KineticNorm ^ 2)⁻¹ - 1 < 0 := by
  linarith [z1_inv_sq_lt_one]

theorem color_e_fourth_pos : 0 < colorESquared ^ 4 := by
  unfold colorESquared
  positivity

theorem chi_mass_fourth_pos : 0 < chiMassGeV ^ 4 := by
  unfold chiMassGeV
  positivity

theorem chi_mass_fourth_gt_nine : (9 : ℝ) < chiMassGeV ^ 4 := by
  unfold chiMassGeV
  norm_num

theorem chi_mass_fourth_lt_ten : chiMassGeV ^ 4 < (10 : ℝ) := by
  unfold chiMassGeV
  norm_num

theorem z1_inv_sq_pos : 0 < (z1KineticNorm ^ 2)⁻¹ := by
  positivity [z1_kinetic_norm_pos]

theorem z1_inv_sq_minus_one_gt_neg_one : (-1 : ℝ) < (z1KineticNorm ^ 2)⁻¹ - 1 := by
  linarith [z1_inv_sq_pos]

theorem color_term_lower_bound :
    (40 : ℝ) < 3 * colorESquared ^ 2 * (z1KineticNorm ^ 2 - 1) := by
  unfold colorESquared
  have hz : (3 : ℝ) < z1KineticNorm ^ 2 - 1 := by nlinarith [z1_kinetic_norm_gt_two]
  nlinarith [hz]

theorem chi_term_lower_bound :
    (-10 : ℝ) < chiMassGeV ^ 4 * ((z1KineticNorm ^ 2)⁻¹ - 1) := by
  have hfac := z1_inv_sq_minus_one_gt_neg_one
  have hneg := z1_inv_sq_minus_one_neg
  nlinarith [chi_mass_fourth_lt_ten, hfac, hneg]

/-- **boundary_sensitivity_coefficient_positive** (CatAL):
    `3e⁴(Z₁²−1) + g⁴(Z₁⁻²−1) > 0` at `e² = 7/2`, `g = m_τ`, `Z₁ = 1 + 2(7/9)(2π/7)²`. -/
theorem boundary_sensitivity_coefficient_positive :
    0 < boundarySensitivityCoeff := by
  unfold boundarySensitivityCoeff
  linarith [color_term_lower_bound, chi_term_lower_bound]

end

end UgpLean.Physics.ZSevenVacuumSelection
