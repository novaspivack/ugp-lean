import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import UgpLean.MassRelations.KoideYukawaAmplitude

/-!
# UgpLean.MassRelations.KoideEqualNormReformulation — equal-irrep-norm = CV(√m)=1

## Context (080-KOIDE-EQUALNORM)

`KoideYukawaAmplitude` proved that the Koide cone condition `Q = 2/3` — equivalently
equality of the trivial-irrep and standard-irrep norms of the generation
√-mass vector `v_g = 1 + b·cos(θ + 2πg/3)` — holds **iff** `b² = 2`.

The residual open question of 080-KOIDE-YUKAWA is *why* the Φ_MDL kink-condensate
generation-Yukawa weights the 1-D trivial and 2-D standard S₃ representations
**equally**.  This module sharpens that residual into a single, scale- and
phase-independent statistical statement and rules out the "raw Z₇ orbit" mechanism.

### Main results (zero sorry)

1. `koide_variance_eq_half_b_sq` — the population variance of the three √-mass
   amplitudes equals `b²/2` (for every phase θ); the mean is `1`.
2. `koide_cv_one_iff_amplitude` — `Var = mean²` (coefficient of variation `CV = 1`)
   **iff** `b² = 2`.  Combined with `koide_Q_iff_amplitude` this gives the exact
   reformulation **Koide Q = 2/3 ⇔ CV(√m) = 1 ⇔ Var(√m) = ⟨√m⟩²**.
3. `koide_Q_eq_one_third_one_plus_cv_sq` — `Q = (1 + CV²)/3` for every (b, θ):
   the Koide quotient is an affine function of the squared coefficient of variation.
4. `lepton_a_values_not_equal_modes` — the **discrete** orbit `a`-values `(1,9,5)`
   do **not** satisfy the equal-Fourier-mode condition `|A₀|² = |A₁|² + |A₂|²`
   (equivalently `2·(Σa)² ≠ 3·Σa²`: `450 ≠ 321`).  Hence the equal-irrep-norm of the
   *continuum* √-mass amplitudes is NOT inherited from the raw Z₇ orbit labels — the
   "Z₇ a-values force equal modes" mechanism is ruled out.

The continuum equal-norm condition that the a-values DO shadow is the
arithmetic-mean identity `2·a_τ = a_e + a_μ` (certified separately as
`lepton_a_discrete_S3_identity`); that shadow is the `a`-component projection of the
equal-norm condition, not the equal-mode (equal-variance) condition itself.
-/

namespace UgpLean.MassRelations.KoideEqualNormReformulation

open Real
open UgpLean.MassRelations.KoideYukawaAmplitude

/-- The population mean of the three √-mass amplitudes is `1` for every `(b, θ)`. -/
theorem koide_mean_eq_one (b θ : ℝ) :
    (vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) / 3 = 1 := by
  rw [vAmp_sum]; norm_num

/-- **Variance theorem.**  The population variance
`(Σ v²)/3 − ((Σ v)/3)²` of the √-mass amplitudes equals `b²/2`, independent of θ.
All `b`-dependence (the generation splitting) lives in the variance. -/
theorem koide_variance_eq_half_b_sq (b θ : ℝ) :
    (vAmp b θ 0 ^ 2 + vAmp b θ 1 ^ 2 + vAmp b θ 2 ^ 2) / 3 -
      ((vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) / 3) ^ 2 = b ^ 2 / 2 := by
  rw [vAmp_sum, vAmp_sq_sum]; ring

/-- **Coefficient-of-variation reformulation.**  `Var = mean²` (i.e. the coefficient
of variation `CV = σ/μ = 1`) holds **iff** `b² = 2`.  Together with
`koide_Q_iff_amplitude` this is the exact statement
**Koide Q = 2/3 ⇔ CV(√m) = 1 ⇔ standard deviation of √m equals its mean**. -/
theorem koide_cv_one_iff_amplitude (b θ : ℝ) :
    ((vAmp b θ 0 ^ 2 + vAmp b θ 1 ^ 2 + vAmp b θ 2 ^ 2) / 3 -
        ((vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) / 3) ^ 2
      = ((vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) / 3) ^ 2) ↔ b ^ 2 = 2 := by
  rw [koide_variance_eq_half_b_sq, koide_mean_eq_one]
  constructor
  · intro h; linarith
  · intro h; rw [h]; norm_num

/-- **Q as an affine function of CV².**  The Koide quotient satisfies
`Q = (1 + CV²)/3` for every `(b, θ)`, where `CV² = Var/mean² = b²/2`.
Hence `Q = 2/3 ⇔ CV² = 1`. -/
theorem koide_Q_eq_one_third_one_plus_cv_sq (b θ : ℝ) :
    (vAmp b θ 0 ^ 2 + vAmp b θ 1 ^ 2 + vAmp b θ 2 ^ 2) /
        (vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) ^ 2
      = (1 + ((vAmp b θ 0 ^ 2 + vAmp b θ 1 ^ 2 + vAmp b θ 2 ^ 2) / 3 -
            ((vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) / 3) ^ 2)) / 3 := by
  rw [vAmp_sum, vAmp_sq_sum]; norm_num; ring

/-- **Negative result (mechanism "raw Z₇ a-values").**  For the discrete generation
orbit `a`-values `(a_e, a_μ, a_τ) = (1, 9, 5)`, the equal-Fourier-mode condition
`|A₀|² = |A₁|² + |A₂|²` is equivalent (by Parseval `Σ_k|A_k|² = 3·Σa²` and
`|A₀|² = (Σa)²`) to `2·(Σa)² = 3·Σa²`.  This FAILS: `2·225 = 450 ≠ 321 = 3·107`.
So the continuum equal-irrep-norm (b = √2) is **not** inherited from the raw orbit
labels; the Z₇-a-value mechanism for equal norms is ruled out. -/
theorem lepton_a_values_not_equal_modes :
    2 * (1 + 9 + 5) ^ 2 ≠ 3 * (1 ^ 2 + 9 ^ 2 + 5 ^ 2) := by decide

/-- The Parseval/Fourier reading of the same fact: with `A₀ = Σa = 15` and
`|A₁|² + |A₂|² = 3·Σa² − (Σa)² = 96`, the democratic-mode energy strictly exceeds the
standard-mode energy (`225 > 96`).  The raw orbit is NOT at equal-irrep-norm. -/
theorem lepton_a_values_mode_energies :
    (1 + 9 + 5) ^ 2 = 225 ∧ 3 * (1 ^ 2 + 9 ^ 2 + 5 ^ 2) - (1 + 9 + 5) ^ 2 = 96 ∧
      (225 : ℤ) ≠ 96 := by
  refine ⟨by norm_num, by norm_num, by norm_num⟩

/-! ## Participation-ratio reformulation (080-KOIDE-EQUALNORM Session 2)

A third, complementary, exact face of the same `b = √2`.  Normalise the √-mass
vector to a probability vector `p_g = v_g / Σv`.  Its inverse participation ratio
(Simpson / Rényi-2 index) `Σ p_g²` equals the Koide quotient `Q`, and the
participation ratio `PR = 1/Q = (Σv)² / Σv²` is the "effective number of
participating generations".  The Koide condition is exactly `PR = 3/2 = N_gen/2`:
half the three generations participate.  This is *equivalent* to `CV(√m)=1`
(`PR = 3/(1+CV²)`), not an independent derivation. -/

/-- **Participation ratio is a function of `b` alone.**  The participation ratio
`(Σv)² / Σv²` equals `6/(2+b²)` for every phase `θ`. -/
theorem koide_participation_ratio_eq (b θ : ℝ) :
    (vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) ^ 2 /
        (vAmp b θ 0 ^ 2 + vAmp b θ 1 ^ 2 + vAmp b θ 2 ^ 2)
      = 6 / (2 + b ^ 2) := by
  rw [vAmp_sum, vAmp_sq_sum]
  have hpos : (0 : ℝ) < 3 + 3 / 2 * b ^ 2 := by positivity
  have hpos2 : (0 : ℝ) < 2 + b ^ 2 := by positivity
  field_simp
  ring

/-- **Koide participation ratio theorem.**  The participation ratio
`PR = (Σv)² / Σv²` equals `3/2 = N_gen/2` **iff** `b² = 2`, for every phase `θ`.
Equivalently: the Koide relation says exactly that the effective number of
participating generations in the √-mass spectrum is half of `N_gen = 3`. -/
theorem koide_participation_ratio_iff_amplitude (b θ : ℝ) :
    (vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) ^ 2 /
        (vAmp b θ 0 ^ 2 + vAmp b θ 1 ^ 2 + vAmp b θ 2 ^ 2) = 3 / 2 ↔ b ^ 2 = 2 := by
  rw [koide_participation_ratio_eq]
  have hpos2 : (0 : ℝ) < 2 + b ^ 2 := by positivity
  constructor
  · intro h
    field_simp at h
    linarith
  · intro h; rw [h]; norm_num

/-- **Master reformulation bundle.**  At the Koide cone amplitude `b = √2` (and for
every phase `θ`): the Koide quotient is `2/3`, the inverse participation ratio
`Σ p_g²` is `2/3`, and the participation ratio `(Σv)²/Σv²` is `3/2 = N_gen/2`.
The three statements `Q = 2/3`, `CV(√m) = 1`, and `PR = N_gen/2` are one condition. -/
theorem koide_participation_ratio_is_half_ngen :
    ∀ θ : ℝ,
      (vAmp (Real.sqrt 2) θ 0 + vAmp (Real.sqrt 2) θ 1 + vAmp (Real.sqrt 2) θ 2) ^ 2 /
          (vAmp (Real.sqrt 2) θ 0 ^ 2 + vAmp (Real.sqrt 2) θ 1 ^ 2 +
            vAmp (Real.sqrt 2) θ 2 ^ 2) = 3 / 2 := by
  intro θ
  exact (koide_participation_ratio_iff_amplitude (Real.sqrt 2) θ).mpr
    (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2))

end UgpLean.MassRelations.KoideEqualNormReformulation
