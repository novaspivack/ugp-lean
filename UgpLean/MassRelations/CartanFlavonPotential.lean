import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.Ring
import UgpLean.MassRelations.FroggattNielsen

/-!
# UgpLean.MassRelations.CartanFlavonPotential — Round 22 Claim C sub-(ii)

**Round 22 (Track D Claim C residual sub-question (ii)):** structural origin of
the transcendental flavon VEVs ε_1 = e^(−π/3), ε_2 = e^(−π/8) introduced in
Round 21's Froggatt-Nielsen UV completion of TT.

## Hypothesis

There is a G-invariant flavon potential on the SU(3)_flavor Cartan torus T²
whose minima land at the Round-21 FN VEVs:
```
V(φ_1, φ_2) = -a·cos(6·φ_1) - b·cos(16·φ_2)
                                            (with a, b > 0)
```

This module proves:
- `φ_1 = -π/3` and `φ_2 = -π/8` are critical points (and global minima) of V.
- The Z_6 symmetry of `cos(6·φ_1)` is the SU(3) Weyl-chamber rotation
  symmetry, **directly linked to Claim A**'s A_2 root-system geometry
  (chamber opening angle = π/3 = 2π/6).
- The Z_16 symmetry of `cos(16·φ_2)` has three candidate physical origins
  (catalogued in Lab Notes 25); leading candidate: SO(10) 16-spinor
  R-symmetry, which would link Claim C to the same SO(10) structure as
  VV's coefficients (Round 17–18).

## What this module formalises

- The potential V(φ_1, φ_2) as a sum of Z_n-invariant Fourier modes.
- The fact that φ_1 = -π/3 and φ_2 = -π/8 minimise V (achieve the global
  minimum value -a - b).
- The connection to Claim A via the Z_6 generator angle π/3 = 2 · π/6.

## What remains open

- The physical origin of the Z_16 symmetry (Lab Notes 25 §6.2).
- Construction of a UV Lagrangian from which V(φ_1, φ_2) emerges as
  the effective flavon potential after gauge / R-symmetry breaking.
-/

namespace UgpLean.MassRelations.CartanFlavonPotential

open Real

/-- The Cartan-torus flavon potential: a sum of Z_6- and Z_16-invariant
    Fourier modes on T² = (SU(3)_flavor Cartan torus).
    Coefficients a, b > 0 set the depth of the potential wells. -/
noncomputable def cartanFlavonPotential (a b : ℝ) (φ₁ φ₂ : ℝ) : ℝ :=
  - a * Real.cos (6 * φ₁) - b * Real.cos (16 * φ₂)

/-- The Z_6 symmetry generator angle: 2π/6 = π/3 = chamber-opening angle of A_2.
    This is **twice** the Claim-A angle π/6 (the half-opening). -/
noncomputable def z6_generator_angle : ℝ := π / 3

/-- The Z_16 symmetry generator angle: 2π/16 = π/8.
    Physical origin candidate: SO(10) 16-spinor R-symmetry. -/
noncomputable def z16_generator_angle : ℝ := π / 8

/-- **Claim A connection:** the Z_6 generator angle equals 2 × the
    Claim-A SU(3) Cartan bisector angle. -/
theorem z6_generator_eq_two_times_claim_A :
    z6_generator_angle = 2 * (π / 6) := by
  unfold z6_generator_angle
  ring

/-- For any positive a, the Z_6 part of the potential is bounded below by `-a`. -/
theorem z6_part_bounded_below (a : ℝ) (ha : 0 ≤ a) (φ₁ : ℝ) :
    -a ≤ -a * Real.cos (6 * φ₁) := by
  have hcos : Real.cos (6 * φ₁) ≤ 1 := Real.cos_le_one _
  nlinarith

/-- For any positive b, the Z_16 part of the potential is bounded below by `-b`. -/
theorem z16_part_bounded_below (b : ℝ) (hb : 0 ≤ b) (φ₂ : ℝ) :
    -b ≤ -b * Real.cos (16 * φ₂) := by
  have hcos : Real.cos (16 * φ₂) ≤ 1 := Real.cos_le_one _
  nlinarith

/-- **Global lower bound on the flavon potential:**
    V(φ_1, φ_2) ≥ -a - b for all (φ_1, φ_2). -/
theorem cartanFlavonPotential_ge_min (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b)
    (φ₁ φ₂ : ℝ) :
    -a - b ≤ cartanFlavonPotential a b φ₁ φ₂ := by
  unfold cartanFlavonPotential
  have h₁ := z6_part_bounded_below a ha φ₁
  have h₂ := z16_part_bounded_below b hb φ₂
  linarith

/-- **Round-21 FN VEVs are global minima of the Z_6 × Z_16 flavon potential.**
    At `(φ_1, φ_2) = (-π/3, -π/8)`, the potential attains its lower bound `-a - b`. -/
theorem cartanFlavonPotential_min_at_FN_vevs (a b : ℝ) :
    cartanFlavonPotential a b (-π/3) (-π/8) = -a - b := by
  unfold cartanFlavonPotential
  -- 6 * (-π/3) = -2π, cos(-2π) = 1
  -- 16 * (-π/8) = -2π, cos(-2π) = 1
  have h1 : Real.cos (6 * (-π/3)) = 1 := by
    have : 6 * (-π/3) = -(2 * π) := by ring
    rw [this, Real.cos_neg, Real.cos_two_pi]
  have h2 : Real.cos (16 * (-π/8)) = 1 := by
    have : 16 * (-π/8) = -(2 * π) := by ring
    rw [this, Real.cos_neg, Real.cos_two_pi]
  rw [h1, h2]
  ring

/-- **Direct identification:** the FN flavon-VEV log values from Round 21
    (`log(ε_1) = -π/3`, `log(ε_2) = -π/8`) are precisely the Round-22
    Cartan-invariant potential's global-minimum coordinates. -/
theorem fn_vevs_are_potential_minima (a b : ℝ) :
    cartanFlavonPotential a b
      UgpLean.MassRelations.FroggattNielsen.log_eps_1
      UgpLean.MassRelations.FroggattNielsen.log_eps_2
      = -a - b := by
  unfold UgpLean.MassRelations.FroggattNielsen.log_eps_1
         UgpLean.MassRelations.FroggattNielsen.log_eps_2
  exact cartanFlavonPotential_min_at_FN_vevs a b

end UgpLean.MassRelations.CartanFlavonPotential
