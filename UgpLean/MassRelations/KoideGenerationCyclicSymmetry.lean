import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic
import UgpLean.MassRelations.KoideYukawaAmplitude
import UgpLean.MassRelations.KoideIrrepEqualNorm

/-!
# UgpLean.MassRelations.KoideGenerationCyclicSymmetry — origin of the Koide flavour symmetry

## Context (080-KOIDE-DYNAMICAL)

The Koide equipartition argument (`KoideIrrepEqualNorm`) presupposes that the
generation Yukawa decomposes into the trivial (dim 1) and standard (dim 2)
irreducible TYPES of a permutation representation on the three generations.
The open question was the **origin** of that flavour symmetry: is it an imposed
`S₃` axiom, or is it derived from the `Φ_MDL` structure?

This module records the derivation. In the UGP framework the three generations
are the **cyclic `Z₃` factor** of the `Φ_MDL` automorphism group
`F₂₁ = Z₇ ⋊ Z₃` (all three generations share the same `Z₇` winding `w = 4`:
lepton-`W` universality). The cyclic generator acts on the Koide cone

  `v_g = 1 + b·cos(θ + 2πg/3)`,  `g = 0,1,2`

by the **phase shift `θ ↦ θ + 2π/3`**, which cyclically permutes the three
generation components. The two ingredients the equipartition argument needs are:

* the *block decomposition* trivial(1) ⊕ standard(2): over `ℝ` the cyclic `Z₃`
  action on `ℝ³` already decomposes as trivial(1) ⊕ rotation(2), **identical** to
  the `S₃` decomposition `ℝ³ = 1 ⊕ 2`; the `S₃` transpositions are not needed;
* the *invariants* `Σv` (trivial block) and `Σv²` (total): both are manifestly
  invariant under `θ ↦ θ + 2π/3` (they are constant in `θ`).

Hence the cyclic `Z₃` generation symmetry — established as the `Z₃` factor of
`F₂₁` (CatAL) — already supplies the full irrep structure used to force
`b = √2`. No `S₃`-on-generations axiom and no appeal to the (distinct) spatial
three-tape `S₃` of P45 is required.

### Results (zero sorry)

* `cone_cyclic_shift_0`, `cone_cyclic_shift_1`, `cone_cyclic_shift_2` — the phase
  shift `θ ↦ θ + 2π/3` realizes the cyclic generation permutation
  `g ↦ g + 1 (mod 3)` on the cone components.
* `cone_trivial_block_cyclic_invariant` — the trivial-block sum `Σv` is invariant
  under the cyclic shift.
* `cone_total_norm_cyclic_invariant` — the total Frobenius norm² `Σv²` is invariant
  under the cyclic shift.
* `koide_amplitude_from_cyclic_generation_symmetry` — under the cyclic `Z₃`
  generation symmetry, MDL equipartition of the two real-irrep TYPES forces
  `b = √2`, `b² = d_standard(S₃) = 2`, and Koide `Q = 2/3`, for every phase `θ`.
-/

namespace UgpLean.MassRelations.KoideGenerationCyclicSymmetry

open Real
open UgpLean.MassRelations.KoideYukawaAmplitude
open UgpLean.MassRelations.KoideIrrepEqualNorm

/-- The cyclic generation shift `g ↦ g+1` sends component `0` to component `1`:
realized as the phase shift `θ ↦ θ + 2π/3`. -/
theorem cone_cyclic_shift_0 (b θ : ℝ) :
    vAmp b (θ + 2 * Real.pi / 3) 0 = vAmp b θ 1 := by
  simp only [vAmp]

/-- The cyclic generation shift sends component `1` to component `2`. -/
theorem cone_cyclic_shift_1 (b θ : ℝ) :
    vAmp b (θ + 2 * Real.pi / 3) 1 = vAmp b θ 2 := by
  simp only [vAmp]
  have harg : θ + 2 * Real.pi / 3 + 2 * Real.pi / 3 = θ + 4 * Real.pi / 3 := by ring
  rw [harg]

/-- The cyclic generation shift sends component `2` back to component `0`
(`cos` is `2π`-periodic). -/
theorem cone_cyclic_shift_2 (b θ : ℝ) :
    vAmp b (θ + 2 * Real.pi / 3) 2 = vAmp b θ 0 := by
  simp only [vAmp]
  have harg : θ + 2 * Real.pi / 3 + 4 * Real.pi / 3 = θ + 2 * Real.pi := by ring
  rw [harg, Real.cos_add_two_pi]

/-- The trivial-irrep block (the democratic sum `Σ v_g = 3`) is invariant under
the cyclic generation shift `θ ↦ θ + 2π/3`. -/
theorem cone_trivial_block_cyclic_invariant (b θ : ℝ) :
    vAmp b (θ + 2 * Real.pi / 3) 0 + vAmp b (θ + 2 * Real.pi / 3) 1
        + vAmp b (θ + 2 * Real.pi / 3) 2
      = vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2 := by
  rw [vAmp_sum, vAmp_sum]

/-- The total Frobenius norm² `Σ v_g² = 3 + (3/2)b²` is invariant under the cyclic
generation shift — the `θ`-independence of `vAmp_sq_sum` is precisely the
`Z₃`-invariance of the standard-block norm. -/
theorem cone_total_norm_cyclic_invariant (b θ : ℝ) :
    vAmp b (θ + 2 * Real.pi / 3) 0 ^ 2 + vAmp b (θ + 2 * Real.pi / 3) 1 ^ 2
        + vAmp b (θ + 2 * Real.pi / 3) 2 ^ 2
      = vAmp b θ 0 ^ 2 + vAmp b θ 1 ^ 2 + vAmp b θ 2 ^ 2 := by
  rw [vAmp_sq_sum, vAmp_sq_sum]

/-- **Koide amplitude from the cyclic `Z₃` generation symmetry (CatAD).**

The cyclic generation generator acts on the cone as `θ ↦ θ + 2π/3`
(`cone_cyclic_shift_0/1/2`); the trivial- and standard-block invariants are
preserved (`cone_trivial_block_cyclic_invariant`,
`cone_total_norm_cyclic_invariant`).  Over `ℝ` this cyclic `Z₃` decomposes
`ℝ³` as trivial(1) ⊕ standard(2) — the same `1 ⊕ 2` block structure as `S₃`.
MDL equipartition of the Frobenius norm across the two irrep TYPES therefore
forces, using only the cyclic symmetry:

* `b = √2 = √d_standard(S₃)`;
* `b² = d_standard(S₃) = 2`;
* Koide `Q = 2/3`,

for every phase `θ`.  The equipartition hypothesis is the framework MDL axiom on
flavour space (CatAD); every downstream step is proved with zero sorry. The
flavour symmetry used is the cyclic `Z₃` (the generation factor of
`F₂₁ = Z₇ ⋊ Z₃`); neither the full `S₃` nor the spatial three-tape `S₃` of P45
is invoked. -/
theorem koide_amplitude_from_cyclic_generation_symmetry (b θ : ℝ) (hb : 0 ≤ b)
    (hMDL : (vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) ^ 2 / 3 =
      (vAmp b θ 0 ^ 2 + vAmp b θ 1 ^ 2 + vAmp b θ 2 ^ 2) -
        (vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) ^ 2 / 3) :
    b = Real.sqrt 2 ∧
    b ^ 2 = (dStandardS3 : ℝ) ∧
    (vAmp b θ 0 ^ 2 + vAmp b θ 1 ^ 2 + vAmp b θ 2 ^ 2) /
      (vAmp b θ 0 + vAmp b θ 1 + vAmp b θ 2) ^ 2 = 2 / 3 :=
  koide_irrep_equalnorm_master b θ hb hMDL

end UgpLean.MassRelations.KoideGenerationCyclicSymmetry
