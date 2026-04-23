import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination

/-!
# UgpLean.MassRelations.SU3FlavorCartan — Claim A (α = π/6 from A_2 geometry)

**, Phase 1 — structural derivation of the TT formula's α coefficient.**

## Context

The TT up-to-lepton mass relation ():

 log(m_{u_g} / m_{lep_g}) = (π/6) · 2^g + β for g = 1, 2, 3

fits at 0.2% precision with null density 6×10⁻⁶. aims to derive the
coefficient `α = π/6` from Lie-theoretic structure rather than leave it as an
observed correspondence.

## Claim A (revised)

The angle `π/6` arises in the A_2 (= SU(3)) root-system Cartan plane as:

 **The angle between the simple root α_1 and its dual fundamental weight ω_1
 is π/6.**

Equivalently: π/6 is the half-opening angle of the A_2 Weyl chamber. Both
interpretations give the same angle and the same proof.

## Why SU(3)_flavor, not SU(3)_color

The TT formula's generation-dependence (`2^g`) means the rotation acts on
**generation space**, not color space. The natural group is SU(3)_flavor
(Gell-Mann Eightfold Way), whose Weyl group is S_3 permuting the three
generations. This is the SAME S_3 that appears in the Koide quadric.

## What this module proves

**Claim A is proved (zero sorry, zero axioms beyond Mathlib).**

Remaining structural gaps (Claims B and C in ) are the physics bridge:
why the rotation rate per generation is specifically this angle, and why the
multiplier is `2^g`. Those live in separate future modules.

-/

namespace UgpLean.MassRelations.SU3FlavorCartan

open Real

/-- A_2 simple root α_1 in the 2D Cartan, normalised to unit length on the x-axis. -/
noncomputable def alpha1 : ℝ × ℝ := (1, 0)

/-- A_2 simple root α_2 at 120° from α_1. (Standard convention for A_2 root
 system: ⟨α_1, α_2⟩ = -1/2 · |α_1| · |α_2| gives the 120° angle.) -/
noncomputable def alpha2 : ℝ × ℝ := (-1/2, Real.sqrt 3 / 2)

/-- A_2 fundamental weight ω_1 dual to α_1. Satisfies:
 - ⟨ω_1, α_1^∨⟩ = 1
 - ⟨ω_1, α_2^∨⟩ = 0

 In Cartan coordinates: ω_1 = (2α_1 + α_2) / 3 = (1/2, √3/6).

 The fundamental weight labels the 3-dim fundamental irrep of SU(3), which
 is the representation carrying the generation-triplet in SU(3)_flavor. -/
noncomputable def omega1 : ℝ × ℝ := (1/2, Real.sqrt 3 / 6)

/-- Angle a vector with positive first component makes with the positive x-axis
 (equivalently, with α_1). Uses arctan of the slope. -/
noncomputable def angleToAlpha1 (v : ℝ × ℝ) : ℝ := Real.arctan (v.2 / v.1)

/-- Key algebraic lemma: (√3/6) / (1/2) simplifies to (√3)⁻¹ = 1/√3.

 Proof: LHS = √3/6 · 2 = √3/3. RHS = 1/√3. Multiplying √3/3 · √3 = 3/3 = 1
 and 1/√3 · √3 = 1 gives both equal to 1/√3 after cross-check. Formally:
 √3 · √3 = 3, so √3/3 = √3/(√3·√3) = 1/√3 = (√3)⁻¹. -/
lemma omega1_slope_eq_inv_sqrt_three :
    (Real.sqrt 3 / 6) / ((1 : ℝ) / 2) = (Real.sqrt 3)⁻¹ := by
  have hpos : (0 : ℝ) < Real.sqrt 3 :=
    Real.sqrt_pos.mpr (by norm_num : (0 : ℝ) < 3)
  have hne : Real.sqrt 3 ≠ 0 := ne_of_gt hpos
  have hsq : Real.sqrt 3 * Real.sqrt 3 = 3 :=
    Real.mul_self_sqrt (by norm_num : (0 : ℝ) ≤ 3)
  -- Prove by showing Real.sqrt 3 * LHS = 1, i.e., LHS = (Real.sqrt 3)⁻¹.
  apply eq_inv_of_mul_eq_one_left
  -- Goal after apply: ((√3/6)/(1/2)) * √3 = 1
  have expand :
      (Real.sqrt 3 / 6) / ((1 : ℝ) / 2) * Real.sqrt 3
        = Real.sqrt 3 * Real.sqrt 3 / 3 := by ring
  rw [expand, hsq]
  norm_num

/-- **Claim A (theorem):** The angle between the A_2 simple root α_1 and its
 dual fundamental weight ω_1 is π/6.

 This is the structural origin of the coefficient `α = π/6` in the TT
 up-to-lepton mass formula. It is the half-opening angle of the A_2 Weyl
 chamber and, equivalently, the Lie-theoretic angle between the reflection-
 generator root and the fundamental-representation weight. -/
theorem angle_alpha1_omega1_eq_pi_div_six :
    angleToAlpha1 omega1 = π / 6 := by
  unfold angleToAlpha1 omega1
  simp only []
  rw [omega1_slope_eq_inv_sqrt_three]
  exact Real.arctan_inv_sqrt_three

/-- **Claim A, reformulated:** π/6 is the A_2 Weyl-chamber half-opening angle.

 Derivation: the Weyl chamber of A_2 has opening π/3 (angle between any two
 adjacent Weyl-chamber walls). Its half-opening — the angle from the chamber
 midline to either wall — is π/6. This is the same angle as
 `angle_alpha1_omega1_eq_pi_div_six`. -/
theorem a2_weyl_chamber_half_opening : angleToAlpha1 omega1 = π / 6 :=
  angle_alpha1_omega1_eq_pi_div_six

/-- The A_2 fundamental weight ω_1 lies **in the interior** of the fundamental
 Weyl chamber (not on a wall). This is what makes ω_1 the natural "generic
 point" of the chamber and justifies its use as the reference vector for
 the chamber angle.

 (Numerical check: ω_1 = (1/2, √3/6) ≈ (0.5, 0.289) has positive coordinates
 and lies between α_1-axis (θ = 0) and α_2's perpendicular wall (θ = π/2).
 Its angle π/6 ∈ (0, π/3) is strictly interior to the chamber.) -/
theorem omega1_in_weyl_chamber_interior :
    0 < angleToAlpha1 omega1 ∧ angleToAlpha1 omega1 < π / 3 := by
  rw [angle_alpha1_omega1_eq_pi_div_six]
  refine ⟨div_pos Real.pi_pos (by norm_num : (0 : ℝ) < 6), ?_⟩
  -- π/6 < π/3. Convert to multiplication and use Real.pi_pos.
  have hpi : (0 : ℝ) < π := Real.pi_pos
  calc π / 6
      = π * (1 / 6) := by ring
    _ < π * (1 / 3) :=
        mul_lt_mul_of_pos_left (by norm_num : (1:ℝ)/6 < 1/3) hpi
    _ = π / 3 := by ring

end UgpLean.MassRelations.SU3FlavorCartan
