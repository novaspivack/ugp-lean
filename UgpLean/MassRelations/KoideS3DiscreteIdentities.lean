import UgpLean.GTE.Evolution
import UgpLean.Core.TripleDefs

/-!
# UgpLean.MassRelations.KoideS3DiscreteIdentities

## Overview

A discrete arithmetic identity on the lepton GTE a-values, the integer
shadow of the S₃ equal-norm condition that underwrites the Koide
parametrisation `Q = 2/3` (see `UgpLean.MassRelations.KoideAngle`).

The canonical lepton GTE orbit produces three triples whose a-components
are
  a_e = `LeptonSeed.a` = 1
  a_μ = `canonicalGen2.a` = 9
  a_τ = `canonicalGen3.a` = 5

These satisfy the clean arithmetic-mean identity
  2 · a_τ = a_e + a_μ ,    i.e.   2 · 5 = 1 + 9 = 10.

This is a Lean-decidable structural fact about the canonical orbit,
independent of N_c, of the Koide angle θ = 2/9, and of any choice of
absolute normalisation. It is the discrete shadow of the S₃ equal-norm
condition `|v₁|² = |v₂|² = 3` projected onto the a-component only:
where the continuous S₃ identity holds for every θ in the Koide family
(see `koide_equal_norm` in `KoideAngle.lean`), the discrete identity
holds for the actual Lean-certified canonical orbit a-values.

## Theorems proved (zero sorry, zero hypotheses)

1. `lepton_a_arithmetic_mean` — `2 * canonicalGen3.a = LeptonSeed.a + canonicalGen2.a`
2. `lepton_a_tau_is_average` — equivalent form `canonicalGen3.a * 2 = LeptonSeed.a + canonicalGen2.a`
3. `lepton_a_values` — `LeptonSeed.a = 1 ∧ canonicalGen2.a = 9 ∧ canonicalGen3.a = 5`
4. `lepton_a_sum_eq_ten` — `LeptonSeed.a + canonicalGen2.a = 10`
5. `lepton_a_arithmetic_mean_explicit` — `2 * 5 = 1 + 9`

## Status

The discrete arithmetic-mean identity
on the canonical lepton orbit. The remaining refined targets (PDG-θ
alignment to 7.4×10⁻⁶ rad, Koide-cone near-attractor of UCL within
6×10⁻⁴) involve PDG real-valued masses and continuous geometric
arguments and are tracked separately.
-/

namespace UgpLean.MassRelations.KoideS3DiscreteIdentities

open UgpLean

/-! ## §1. The discrete arithmetic-mean identity -/

/-- **Discrete S₃ arithmetic-mean identity on lepton a-values.**

The tau a-value is the arithmetic mean of the electron and muon
a-values:

  2 · a_τ = a_e + a_μ ,    i.e.   2 · 5 = 1 + 9 = 10.

This is the discrete shadow of the S₃ equal-norm condition
`|v₁|² = |v₂|² = 3` (see `koide_equal_norm` in
`UgpLean.MassRelations.KoideAngle`) for the a-component alone.
It is independent of N_c, of the Koide angle θ = 2/9, and of the
absolute normalisation of the parametrisation, and depends only on
the canonical orbit a-component sequence (1, 9, 5).

Proof: by `decide` after unfolding the canonical GTE triples. -/
theorem lepton_a_arithmetic_mean :
    2 * canonicalGen3.a = LeptonSeed.a + canonicalGen2.a := by
  unfold LeptonSeed canonicalGen2 canonicalGen3
  decide

/-- Equivalent form: the tau a-value times 2 equals the sum of
electron and muon a-values. -/
theorem lepton_a_tau_is_average :
    canonicalGen3.a * 2 = LeptonSeed.a + canonicalGen2.a := by
  rw [Nat.mul_comm]
  exact lepton_a_arithmetic_mean

/-- The Lean-certified canonical lepton a-values:
`a_e = 1`, `a_μ = 9`, `a_τ = 5`. -/
theorem lepton_a_values :
    LeptonSeed.a = 1 ∧ canonicalGen2.a = 9 ∧ canonicalGen3.a = 5 := by
  unfold LeptonSeed canonicalGen2 canonicalGen3
  exact ⟨rfl, rfl, rfl⟩

/-- The electron and muon a-values sum to 10. -/
theorem lepton_a_sum_eq_ten :
    LeptonSeed.a + canonicalGen2.a = 10 := by
  unfold LeptonSeed canonicalGen2
  decide

/-- Twice the tau a-value equals 10. -/
theorem two_tau_a_eq_ten :
    2 * canonicalGen3.a = 10 := by
  unfold canonicalGen3
  decide

/-- Fully explicit numerical form of the identity: `2 · 5 = 1 + 9`. -/
theorem lepton_a_arithmetic_mean_explicit : 2 * 5 = 1 + 9 := by decide

/-! ## §2. Conjunction certificate -/

/-- **The discrete S₃ arithmetic-mean structural certificate.**

Combines the three facts:
* the canonical lepton a-values are exactly `(1, 9, 5)`;
* their electron-plus-muon sum equals `10`;
* the arithmetic-mean identity `2 · a_τ = a_e + a_μ` holds. -/
theorem lepton_a_discrete_S3_identity :
    (LeptonSeed.a = 1 ∧ canonicalGen2.a = 9 ∧ canonicalGen3.a = 5) ∧
    LeptonSeed.a + canonicalGen2.a = 10 ∧
    2 * canonicalGen3.a = LeptonSeed.a + canonicalGen2.a :=
  ⟨lepton_a_values, lepton_a_sum_eq_ten, lepton_a_arithmetic_mean⟩

/-! ## §3. Refined open question (target for future closure of OP(vii))

Conjecture (informal, not yet formalised): the Universal Calibration
Law applied to the canonical lepton orbit produces a sqrt-mass triple
in the `koideR θ` parametrisation family for some absolute scale `c`
and phase `θ`. Combined with `koide_angle_from_N_c_pure` (proving
`θ = 2/9` from `N_c = 3`, see `UgpLean.MassRelations.KoideAngle`),
this would close OP(vii) entirely.

The discrete identity `lepton_a_arithmetic_mean` proved above is the
arithmetic shadow that makes the conjecture plausible: even without
calibration, the bare a-component sequence (1, 9, 5) of the canonical
orbit already exhibits the equal-mean balance characteristic of the
S₃ Koide parametrisation. -/

end UgpLean.MassRelations.KoideS3DiscreteIdentities
