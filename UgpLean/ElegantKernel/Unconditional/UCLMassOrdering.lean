import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Exp
import UgpLean.ElegantKernel.Unconditional.UCLCalibration
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingDelta

/-!
# UCL Mass Ordering — Tier 2 of 083C-UCL-FORM

**Claim.** For each SM fermion sector (lepton, up-type, down-type), the
generation-scaled UCL mass proxy

  m̃_g = 4^(g−1) · exp(log C_f)

increases strictly with generation `g = 1 < 2 < 3` on the canonical GTE triples
with CatAL Elegant Kernel coefficients.

**Proof status.** The structural bridge from log-space inequalities to
`uclGenerationScaledMass` is in `UCLMassOrderingBounds`; coupled-corner
delta bounds (`S_g1 - S_g2 < R < log 4`) are in `UCLMassOrderingSBounds`.
Zero sorry.
-/

namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrdering

open Real
open UgpLean.ElegantKernel.Unconditional.UCLCalibration
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingDelta

/-! ## Per-sector ordering -/

/-- Proposition: lepton sector generation-scaled mass ordering. -/
def leptonUclMassOrderingProp : Prop :=
  uclGenerationScaledMass 1 (-1) (-1) (Real.log 73 - Real.log 823) 1 <
    uclGenerationScaledMass 0 (-1) (-1) (Real.log 42 - Real.log 1023) 2 ∧
  uclGenerationScaledMass 0 (-1) (-1) (Real.log 42 - Real.log 1023) 2 <
    uclGenerationScaledMass (-1) 0 1 (Real.log 275 - Real.log 65535) 3

/-- Proposition: up-quark sector generation-scaled mass ordering. -/
def upUclMassOrderingProp : Prop :=
  uclGenerationScaledMass (-1) 0 0 (Real.log 9 - Real.log 275) 1 <
    uclGenerationScaledMass (-1) 0 1 (Real.log 275 - Real.log 65535) 2 ∧
  uclGenerationScaledMass (-1) 0 1 (Real.log 275 - Real.log 65535) 2 <
    uclGenerationScaledMass 0 0 1 (Real.log 337920 - Real.log 1) 3

/-- Proposition: down-quark sector generation-scaled mass ordering. -/
def downUclMassOrderingProp : Prop :=
  uclGenerationScaledMass 0 (-1) (-1) (Real.log 5 - Real.log 42) 1 <
    uclGenerationScaledMass 0 (-1) (-1) (Real.log 186 - Real.log 1023) 2 ∧
  uclGenerationScaledMass 0 (-1) (-1) (Real.log 186 - Real.log 1023) 2 <
    uclGenerationScaledMass (-1) (-1) 1 (Real.log 8191 - Real.log 65535) 3

/-- **Lepton sector:** m̃₁ < m̃₂ < m̃₃ for `(1,73,823)`, `(9,42,1023)`, `(5,275,65535)`.

Numerically: m̃ ≈ (1.10, 3.74, 4.33). Equivalent to
`S₁ < log 4 + S₂` and `S₂ < log 4 + S₃` with S_g = `uclLogCalibration` on each triple. -/
theorem lepton_ucl_mass_ordering_holds : leptonUclMassOrderingProp := by
  constructor
  · exact ucl_mass_lt_gen12_diff (S₁ := _) (S₂ := _) rfl rfl lepton_log_delta12
  · exact ucl_mass_lt_gen23_diff (S₂ := _) (S₃ := _) rfl rfl lepton_log_delta23

/-- **Up-quark sector:** m̃₁ < m̃₂ < m̃₃ for `(5,9,275)`, `(5,275,65535)`, `(76,337920,1)`.

Numerically: m̃ ≈ (1.72, 13.27, 42.79). -/
theorem up_ucl_mass_ordering_holds : upUclMassOrderingProp := by
  constructor
  · exact ucl_mass_lt_gen12_diff (S₁ := _) (S₂ := _) rfl rfl up_log_delta12
  · exact ucl_mass_lt_gen23_diff (S₂ := _) (S₃ := _) rfl rfl up_log_delta23

/-- **Down-quark sector:** m̃₁ < m̃₂ < m̃₃ for `(9,5,42)`, `(9,186,1023)`, `(5,8191,65535)`.

Numerically: m̃ ≈ (2.15, 3.49, 6.53). -/
theorem down_ucl_mass_ordering_holds : downUclMassOrderingProp := by
  constructor
  · exact ucl_mass_lt_gen12_diff (S₁ := _) (S₂ := _) rfl rfl down_log_delta12
  · exact ucl_mass_lt_gen23_diff (S₂ := _) (S₃ := _) rfl rfl down_log_delta23

/-- **Tier 2 master theorem (083C-UCL-FORM).**

For each SM fermion sector, the generation-scaled UCL mass proxy increases
strictly with generation under the CatAL Elegant Kernel coefficients.

**Note:** `C_f` alone decreases with generation for leptons; ordering requires
the IMT generation phase factor `4^(g−1)`. -/
theorem ucl_fermion_mass_ordering :
    leptonUclMassOrderingProp ∧
    upUclMassOrderingProp ∧
    downUclMassOrderingProp :=
  And.intro lepton_ucl_mass_ordering_holds
    (And.intro up_ucl_mass_ordering_holds down_ucl_mass_ordering_holds)

end UgpLean.ElegantKernel.Unconditional.UCLMassOrdering
