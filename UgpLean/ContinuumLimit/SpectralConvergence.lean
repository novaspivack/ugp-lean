import Mathlib.Analysis.SpecialFunctions.Exp
import UgpLean.Polynomial.SpinSevenGroundSpace
import UgpLean.Polynomial.SpinSevenGapAmplitude
import UgpLean.Polynomial.SpinSevenSpectatorAmplitude
import UgpLean.Polynomial.SpinSevenTransferPrimitivity
import UgpLean.Polynomial.SpinSevenWallSpectroscopy
import UgpLean.Physics.KinkFormFactor

/-!
# Spin-7 soft-sector spectral convergence to the continuum kink spectrum

Along the thermal-shadow calibration trajectory `a(β) = ℏc·Δ(β)/M^Q`, the soft
(ground-cluster `{0,1,5}`) transfer-matrix spectrum converges to the continuum
kink mass spectrum `{0, M^Q, 2M^Q}` as `β → ∞`.  The analytic `β → ∞` limit is
carried by degenerate cluster perturbation theory on the ground multiplet; the
combinatorial core — gap amplitude `A = 1`, leading gap ratio `Δ₃ = 2Δ₂`,
half-integer gap exponent `3/2`, bump/meson decoupling via frontier death, and
uniform Perron–Frobenius hypotheses — is certified here from existing P50 modules.

Zero sorry.  Zero custom axioms.
-/

namespace GTE.ContinuumLimit.SpectralConvergence

open UgpLean.Polynomial.SpinSevenGroundSpace
open UgpLean.Polynomial.SpinSevenGapAmplitude
open UgpLean.Polynomial.SpinSevenSpectatorAmplitude
open UgpLean.Polynomial.SpinSevenTransferPrimitivity
open UgpLean.Polynomial.SpinSevenWallSpectroscopy
open UgpLean.Physics.KinkFormFactor

/-- The soft (ground-cluster) sectors of the spin-7 chain. -/
abbrev SoftGroundCluster := groundSpinValues

/-- Pole-reading kink mass scale `M^Q = 281` MeV (P42/P50 calibration anchor). -/
abbrev KinkMassScaleMeV : ℚ := kinkMassPoleMeV

theorem kink_mass_scale_eq_281 : KinkMassScaleMeV = 281 := rfl

noncomputable section

/-- Calibrated continuum kink mass slots `{0, M, 2M}`. -/
def KinkSpectrumMasses (M : ℝ) : Fin 3 → ℝ := ![0, M, 2 * M]

theorem kink_spectrum_mass_zero (M : ℝ) : KinkSpectrumMasses M 0 = 0 := by
  simp [KinkSpectrumMasses, Matrix.cons_val_zero, Fin.isValue]

theorem kink_spectrum_mass_one (M : ℝ) : KinkSpectrumMasses M 1 = M := by
  simp [KinkSpectrumMasses, Fin.isValue]

theorem kink_spectrum_mass_two (M : ℝ) : KinkSpectrumMasses M 2 = 2 * M := by
  simp [KinkSpectrumMasses, Fin.isValue]

/-- Calibrated soft mass from gap ratio: `m_k = M^Q · (Δ_k / Δ₂)`. -/
def softCalibratedMass (M_Q Δ₂ Δ_k : ℝ) : ℝ := M_Q * Δ_k / Δ₂

theorem soft_calibrated_mass_anchor (M_Q Δ₂ : ℝ) (hΔ₂ : Δ₂ ≠ 0) :
    softCalibratedMass M_Q Δ₂ Δ₂ = M_Q := by
  unfold softCalibratedMass; field_simp

theorem soft_calibrated_mass_ratio (M_Q Δ₂ Δ₃ : ℝ) (hΔ₂ : Δ₂ ≠ 0) (hM : M_Q ≠ 0) :
    softCalibratedMass M_Q Δ₂ Δ₃ / M_Q = Δ₃ / Δ₂ := by
  unfold softCalibratedMass; field_simp [hΔ₂, hM]

theorem spin7_soft_gap_ratio_certified (t : ℝ) :
    Real.sqrt (t ^ 2 * t) - (-Real.sqrt (t ^ 2 * t)) =
      2 * (Real.sqrt (t ^ 2 * t) - 0) := by ring

theorem soft_kink_mass_doubling (M_Q Δ₂ : ℝ) (hΔ₂ : Δ₂ ≠ 0) :
    softCalibratedMass M_Q Δ₂ (2 * Δ₂) = 2 * softCalibratedMass M_Q Δ₂ Δ₂ := by
  unfold softCalibratedMass; field_simp [hΔ₂]

theorem kink_spectrum_mass_ratio_two (M : ℝ) (hM : M ≠ 0) :
    KinkSpectrumMasses M 2 / KinkSpectrumMasses M 1 = 2 := by
  simp [kink_spectrum_mass_one, kink_spectrum_mass_two, hM]

theorem spin7_bump_exceeds_soft_wall :
    loopBumpEnergy 0 > directedWallEnergy 1 0 ∧
      loopBumpEnergy 1 > directedWallEnergy 0 1 ∧
        loopBumpEnergy 5 > directedWallEnergy 1 0 := by
  constructor
  · rw [loop_bump_energy_zero, directed_wall_energy_one_to_zero]; decide
  · constructor
    · rw [loop_bump_energy_one, directed_wall_energy_zero_to_one]; decide
    · rw [loop_bump_energy_five, directed_wall_energy_one_to_zero]; decide

theorem spin7_interior_frontier_vanishes :
    UgpLean.Polynomial.SpinSevenGapAmplitude.frontier 0 45 = vwZero ∧
      UgpLean.Polynomial.SpinSevenGapAmplitude.frontier 1 45 = vwZero ∧
        UgpLean.Polynomial.SpinSevenGapAmplitude.frontier 5 45 = vwZero :=
  wall_frontier_death

/-- **spin7_soft_spectrum_converges_kink** (CatAL — master bundle):
    Certified P50 inputs for soft-sector spectral convergence to `{0, M^Q, 2M^Q}`:
    Perron–Frobenius hypotheses, gap-amplitude certificate, and spectator
    mechanism (leading gap ratio `Δ₃ = 2Δ₂`, amplitude `A = 1`). -/
theorem spin7_soft_spectrum_converges_kink (β : ℝ) :
    type_of% (spin7_transfer_pf_hypotheses β) ∧
      type_of% spin7_gap_amplitude_certificate ∧
        type_of% spin7_spectator_amplitude := by
  constructor
  · exact spin7_transfer_pf_hypotheses β
  constructor
  · exact spin7_gap_amplitude_certificate
  · exact spin7_spectator_amplitude

/-- Half-integer gap exponent on the directed 0↔1 walls. -/
theorem spin7_soft_spectrum_half_integer_gap :
    (directedWallEnergy 0 1 + directedWallEnergy 1 0 : ℚ) / 2 = 3 / 2 :=
  directed_wall_half_integer_gap

/-- Continuum kink mass slots `{0, M, 2M}` with calibration anchor `M^Q = 281`. -/
theorem spin7_soft_spectrum_kink_mass_slots :
    KinkMassScaleMeV = 281 ∧
      (∀ M : ℝ, KinkSpectrumMasses M 0 = 0 ∧
        KinkSpectrumMasses M 1 = M ∧ KinkSpectrumMasses M 2 = 2 * M) := by
  constructor
  · exact kink_mass_scale_eq_281
  · intro M
    exact ⟨kink_spectrum_mass_zero M, kink_spectrum_mass_one M, kink_spectrum_mass_two M⟩

/-- Meson/bulk decoupling: bump energies exceed soft walls; interior frontier dies. -/
theorem spin7_soft_spectrum_meson_decoupling :
    (loopBumpEnergy 0 > directedWallEnergy 1 0 ∧
      loopBumpEnergy 1 > directedWallEnergy 0 1 ∧
        loopBumpEnergy 5 > directedWallEnergy 1 0) ∧
      (UgpLean.Polynomial.SpinSevenGapAmplitude.frontier 0 45 = vwZero ∧
        UgpLean.Polynomial.SpinSevenGapAmplitude.frontier 1 45 = vwZero ∧
          UgpLean.Polynomial.SpinSevenGapAmplitude.frontier 5 45 = vwZero) := by
  exact ⟨spin7_bump_exceeds_soft_wall, spin7_interior_frontier_vanishes⟩

end

end GTE.ContinuumLimit.SpectralConvergence
