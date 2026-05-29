import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import UgpLean.MassRelations.KoideAngle

/-!
# UgpLean.MassRelations.KoideYukawaAmplitude — The cone amplitude √2 is forced

## Context (080-KOIDE-YUKAWA)

The charged-lepton generation Yukawa couplings are the three Z₃-orbit images of a
single kink-condensate amplitude on the period-3 generation orbit.  Z₃ covariance
forces the generic real Fourier form

    √m_g = A · (1 + b · cos(θ + 2πg/3)),   g = 0,1,2,

i.e. a democratic (trivial, 1-D) component plus one standard-rep (2-D) Fourier mode.

The phase θ = 2/9 is the QCD colour-rank value (`koide_angle_from_N_c_pure`, CatAL).
This module pins the *amplitude*: it proves that the Koide cone condition
Q = 2/3 — equivalently, equality of the trivial-irrep and standard-irrep norms —
holds **iff** b² = 2, hence (for b ≥ 0) **iff** b = √2.

Thus the full Koide cone parametrisation is structurally pinned:
* amplitude  b = √2  ⇔  equal trivial/standard S₃-irrep norm  (= Koide Q = 2/3);
* phase      θ = 2/9 (CatAL, from N_c = 3).

The residual open item of 080-KOIDE-YUKAWA is exactly the equal-irrep-norm
condition itself: why the Φ_MDL kink-condensate Yukawa weights the 1-D trivial and
2-D standard representations equally.  This module makes that residual precise — it
is the single number b = √2.

## Theorems (zero sorry, zero hypotheses beyond positivity where stated)

1. `vAmp_sum`              — Σ v_g = 3 for every (b, θ)
2. `vAmp_sq_sum`           — Σ v_g² = 3 + (3/2)·b² for every (b, θ)
3. `koide_Q_iff_amplitude` — Q = 2/3 ⇔ b² = 2 (any θ)
4. `equal_norm_iff_amplitude` — |v_triv|² = |v_std|² ⇔ b² = 2 (any θ)
5. `cone_amplitude_eq_sqrt2`  — equal-norm + b ≥ 0 ⇒ b = √2
6. `koide_cone_pinned`        — master: at b = √2, θ = 2/9, Q = 2/3 and equal-norm hold
-/

namespace UgpLean.MassRelations.KoideYukawaAmplitude

open Real
open UgpLean.MassRelations.KoideAngle

/-- Generation Yukawa √mass amplitude with a *general* cone coefficient `b`:
`v_g = 1 + b·cos(θ + 2πg/3)`, `g = 0,1,2`.  The Koide family is the special
case `b = √2`. -/
noncomputable def vAmp (b θ : ℝ) : ℕ → ℝ
  | 0 => 1 + b * Real.cos θ
  | 1 => 1 + b * Real.cos (θ + 2 * Real.pi / 3)
  | 2 => 1 + b * Real.cos (θ + 4 * Real.pi / 3)
  | _ => 0

/-- The democratic (trivial-irrep) sum is `3` for every amplitude and phase. -/
theorem vAmp_sum (b θ : ℝ) : vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2 = 3 := by
  simp only [vAmp]
  have h := cos_sum_three_120 θ
  linear_combination b * h

/-- The sum of squares is `3 + (3/2)·b²` for every amplitude and phase.
The `b`-dependence is entirely in the standard-irrep contribution `(3/2)·b²`. -/
theorem vAmp_sq_sum (b θ : ℝ) :
    vAmp b θ 0 ^ 2 + vAmp b θ 1 ^ 2 + vAmp b θ 2 ^ 2 = 3 + (3 / 2) * b ^ 2 := by
  simp only [vAmp]
  have hsum := cos_sum_three_120 θ
  have hsq := cos_sq_sum_three_120 θ
  linear_combination (2 * b) * hsum + (b ^ 2) * hsq

/-- **Koide cone amplitude theorem.**  For the general Z₃-Fourier amplitude
`v_g = 1 + b·cos(θ + 2πg/3)`, the Koide quotient
`Q = (Σ v_g²)/(Σ v_g)²` equals `2/3` **iff** `b² = 2`, for *every* phase θ.
So the cone amplitude is independent of θ: θ selects the point on the cone,
`b = √2` selects the cone. -/
theorem koide_Q_iff_amplitude (b θ : ℝ) :
    (vAmp b θ 0 ^ 2 + vAmp b θ 1 ^ 2 + vAmp b θ 2 ^ 2) /
      (vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) ^ 2 = 2 / 3 ↔ b ^ 2 = 2 := by
  simp only [vAmp_sum, vAmp_sq_sum]
  rw [show ((3:ℝ)) ^ 2 = 9 by norm_num]
  constructor
  · intro h
    have key : 3 + 3 / 2 * b ^ 2 = 6 := by linear_combination 9 * h
    linarith
  · intro h
    rw [h]; norm_num

/-- **Equal-irrep-norm theorem.**  The trivial-irrep norm² `(Σv)²/3` equals the
standard-irrep norm² `Σv² − (Σv)²/3` **iff** `b² = 2`.  This is the S₃ "45° cone"
condition expressed directly on the amplitude. -/
theorem equal_norm_iff_amplitude (b θ : ℝ) :
    (vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) ^ 2 / 3 =
      (vAmp b θ 0 ^ 2 + vAmp b θ 1 ^ 2 + vAmp b θ 2 ^ 2) -
        (vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) ^ 2 / 3 ↔ b ^ 2 = 2 := by
  simp only [vAmp_sum, vAmp_sq_sum]
  rw [show ((3:ℝ)) ^ 2 / 3 = 3 by norm_num]
  constructor
  · intro h; linarith
  · intro h; rw [h]; norm_num

/-- For a non-negative amplitude, the equal-norm / Koide condition forces `b = √2`. -/
theorem cone_amplitude_eq_sqrt2 (b θ : ℝ) (hb : 0 ≤ b)
    (hcone : (vAmp b θ 0 ^ 2 + vAmp b θ 1 ^ 2 + vAmp b θ 2 ^ 2) /
      (vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) ^ 2 = 2 / 3) :
    b = Real.sqrt 2 := by
  have hb2 : b ^ 2 = 2 := (koide_Q_iff_amplitude b θ).mp hcone
  have : b = Real.sqrt (b ^ 2) := by
    rw [Real.sqrt_sq hb]
  rw [this, hb2]

/-- **Master pinning theorem.**  The Koide cone parametrisation is fully fixed by
two structural facts:
* the amplitude `b = √2` is the unique non-negative cone amplitude (equal-irrep-norm);
* the phase `θ = 2/9 = (N_c²−1)/(4N_c²)` is the QCD colour-rank value.
At this `(b, θ)` the Koide relation `Q = 2/3` and the S₃ equal-norm condition hold. -/
theorem koide_cone_pinned :
    ((Real.sqrt 2) ^ 2 = 2) ∧
    (koideThetaUGP = (3 ^ 2 - 1 : ℝ) / (4 * 3 ^ 2)) ∧
    (∀ θ : ℝ,
      (vAmp (Real.sqrt 2) θ 0 ^ 2 + vAmp (Real.sqrt 2) θ 1 ^ 2 + vAmp (Real.sqrt 2) θ 2 ^ 2) /
        (vAmp (Real.sqrt 2) θ 0 + vAmp (Real.sqrt 2) θ 1 + vAmp (Real.sqrt 2) θ 2) ^ 2 = 2 / 3) := by
  refine ⟨Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2), koide_angle_from_N_c_pure, ?_⟩
  intro θ
  exact (koide_Q_iff_amplitude (Real.sqrt 2) θ).mpr (Real.sq_sqrt (by norm_num : (0:ℝ) ≤ 2))

end UgpLean.MassRelations.KoideYukawaAmplitude
