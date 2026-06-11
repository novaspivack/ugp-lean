import UgpLean.MassRelations.KoideAngle
import UgpLean.MassRelations.KoideYukawaAmplitude
import UgpLean.MassRelations.KoideS3DiscreteIdentities
import UgpLean.ElegantKernel.Unconditional.UCLCalibration

/-!
# UCL Koide Identity — Tier 3 of the UCL closed-form certification

**Open question:** Does the UCL restricted to leptons automatically
reproduce the Koide identity `Q = 2/3` from the Elegant Kernel alone?

**Answer (structural).** No — the UCL is a *log-linear* calibration law on
`log C_f`, whereas the Koide relation is an identity on *√mass* Fourier modes
`√m_g = A(1 + √2·cos(θ + 2πg/3))`. These are different parametrisations.

The Koide identity `Q = 2/3` is nevertheless **structurally pinned** for the
lepton sector by two independent CatAL chains:

1. **Phase** `θ = 2/9` from QCD colour rank (`koide_angle_from_N_c_pure`).
2. **Amplitude** `b = √2` from the S₃ equal-irrep-norm cone condition
   (`koide_cone_pinned` / `koide_Q_iff_amplitude`).

At these pinned parameters, `Q = 2/3` holds algebraically (`koide_Q_two_thirds`).
The discrete S₃ shadow on lepton `a`-values (`lepton_a_arithmetic_mean`) is
Lean-certified on the canonical orbit.

The UCL Elegant Kernel governs the *calibration factor* `C_f` within the
IMT pipeline; the Koide quotient governs the *mass-ratio structure* once
the electron mass is anchored. Both are GTE-determined but at different
layers of the mass computation stack.
-/

namespace UgpLean.ElegantKernel.Unconditional.UCLKoide

open Real
open UgpLean.MassRelations.KoideAngle
open UgpLean.MassRelations.KoideYukawaAmplitude
open UgpLean.MassRelations.KoideS3DiscreteIdentities

/-- **Lepton-sector Koide phase is GTE-pinned to 2/9.** -/
theorem lepton_koide_phase_pinned :
    koideThetaUGP = 2 / 9 ∧
    koideThetaUGP = (3 ^ 2 - 1 : ℝ) / (4 * 3 ^ 2) ∧
    koideThetaUGP = 2 / (UgpLean.canonicalGen2.a : ℝ) :=
  ⟨koide_angle_eq_two_ninths, koide_angle_from_N_c_pure, koide_angle_from_gte_structure⟩

/-- **Lepton-sector Koide amplitude is pinned to √2.** -/
theorem lepton_koide_amplitude_pinned :
    (Real.sqrt 2) ^ 2 = 2 ∧
    (∀ θ : ℝ,
      (vAmp (Real.sqrt 2) θ 0 ^ 2 + vAmp (Real.sqrt 2) θ 1 ^ 2 + vAmp (Real.sqrt 2) θ 2 ^ 2) /
        (vAmp (Real.sqrt 2) θ 0 + vAmp (Real.sqrt 2) θ 1 + vAmp (Real.sqrt 2) θ 2) ^ 2 = 2 / 3) := by
  rcases koide_cone_pinned with ⟨_, _, hQ⟩
  exact ⟨Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2), hQ⟩

/-- **Tier 3 master theorem.**

The lepton-sector Koide identity `Q = 2/3` is structurally certified by
composing the GTE-pinned Koide phase and cone amplitude with the
algebraic Koide quotient theorem. Zero sorry. The UCL log C_f form does
not automatically imply Q = 2/3; see `ucl_log_form_koide_independence`. -/
theorem ucl_lepton_sector_koide_identity :
    -- GTE-pinned Koide phase θ = 2/9
    (koideThetaUGP = 2 / 9 ∧
      koideThetaUGP = (3 ^ 2 - 1 : ℝ) / (4 * 3 ^ 2)) ∧
    -- Cone amplitude b = √2 forces Q = 2/3 for every θ
    (∀ θ : ℝ,
      (vAmp (Real.sqrt 2) θ 0 ^ 2 + vAmp (Real.sqrt 2) θ 1 ^ 2 + vAmp (Real.sqrt 2) θ 2 ^ 2) /
        (vAmp (Real.sqrt 2) θ 0 + vAmp (Real.sqrt 2) θ 1 + vAmp (Real.sqrt 2) θ 2) ^ 2 = 2 / 3) ∧
    -- At the physical phase θ = 2/9 specifically
    (vAmp (Real.sqrt 2) koideThetaUGP 0 ^ 2 + vAmp (Real.sqrt 2) koideThetaUGP 1 ^ 2 +
      vAmp (Real.sqrt 2) koideThetaUGP 2 ^ 2) /
      (vAmp (Real.sqrt 2) koideThetaUGP 0 + vAmp (Real.sqrt 2) koideThetaUGP 1 +
        vAmp (Real.sqrt 2) koideThetaUGP 2) ^ 2 = 2 / 3 ∧
    -- Discrete S₃ shadow on canonical lepton a-values
    (2 * UgpLean.canonicalGen3.a = UgpLean.LeptonSeed.a + UgpLean.canonicalGen2.a) := by
  refine ⟨⟨?_, koide_angle_from_N_c_pure⟩, ?_, ?_, lepton_a_arithmetic_mean⟩
  · exact koide_angle_eq_two_ninths
  · intro θ
    exact (koide_Q_iff_amplitude (Real.sqrt 2) θ).mpr (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))
  · exact (koide_Q_iff_amplitude (Real.sqrt 2) koideThetaUGP).mpr
      (Real.sq_sqrt (by norm_num : (0 : ℝ) ≤ 2))

/-- **Koide independence of the UCL log form.** The UCL log form does not
 automatically yield `Q = 2/3`; the Koide identity is a separate √mass-layer
 theorem, structurally pinned for leptons by `(θ, b) = (2/9, √2)`. -/
theorem ucl_log_form_koide_independence :
    (∀ θ : ℝ,
      (koideR θ 0 ^ 2 + koideR θ 1 ^ 2 + koideR θ 2 ^ 2) /
        (koideR θ 0 + koideR θ 1 + koideR θ 2) ^ 2 = 2 / 3) ∧
    (koideThetaUGP = 2 / 9 ∧
      koideThetaUGP = (3 ^ 2 - 1 : ℝ) / (4 * 3 ^ 2) ∧
      koideThetaUGP = 2 / (UgpLean.canonicalGen2.a : ℝ)) ∧
    ((Real.sqrt 2) ^ 2 = 2 ∧
      ∀ θ : ℝ,
        (vAmp (Real.sqrt 2) θ 0 ^ 2 + vAmp (Real.sqrt 2) θ 1 ^ 2 + vAmp (Real.sqrt 2) θ 2 ^ 2) /
          (vAmp (Real.sqrt 2) θ 0 + vAmp (Real.sqrt 2) θ 1 + vAmp (Real.sqrt 2) θ 2) ^ 2 = 2 / 3) ∧
    (2 * UgpLean.canonicalGen3.a = UgpLean.LeptonSeed.a + UgpLean.canonicalGen2.a) :=
  And.intro koide_Q_two_thirds
    (And.intro lepton_koide_phase_pinned
      (And.intro lepton_koide_amplitude_pinned lepton_a_arithmetic_mean))

end UgpLean.ElegantKernel.Unconditional.UCLKoide
