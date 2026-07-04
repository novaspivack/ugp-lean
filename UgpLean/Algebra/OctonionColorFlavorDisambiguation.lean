import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import UgpLean.Algebra.F21SU3Embedding
import UgpLean.MassRelations.KoideGenerationCyclicSymmetry

/-!
# OctonionColorFlavorDisambiguation: two distinct `ℤ₃` actions of `F₂₁`

The abstract `ℤ₃` subgroup of `F₂₁ = ℤ₇ ⋊ ℤ₃` appears in the UGP corpus in two
**different representations** on **different carrier spaces**:

* **Color rotation** (`z3Mul = ×2` on `ZMod 7`): certified in
  `F21SU3Embedding` / `OctonionShadowInterface`. This is an inner automorphism
  of `G₂`: it cycles the QR(7) pencil on the Fano point set without permuting
  Spin(8) triality slots.

* **Flavor cycling** (phase shift `θ ↦ θ + 2π/3` on the Koide cone parameter):
  certified in `KoideGenerationCyclicSymmetry`. This is an outer Spin(8) triality
  action: it permutes the three generation components / triality slots.

These modules do **not** import each other; there is no formal identification
between `z3Mul` and the Koide phase shift. The inner/outer split of Theorem G3
(TrialityInterface) is exactly this representation distinction.

Level framing: Level 1 algebraic certificate (finite/discrete action facts).
-/

namespace UgpLean.Algebra.OctonionColorFlavorDisambiguation

open Real
open UgpLean.MassRelations.KoideYukawaAmplitude (vAmp)
open UgpLean.Algebra.F21SU3Embedding (z3Mul z3_order_three)
open UgpLean.MassRelations.KoideGenerationCyclicSymmetry

/-- The `ℤ₃` generator acting on the Fano point set / weight labels (`ZMod 7`).
    Certified as `z3Mul` in `F21SU3Embedding`. -/
def z3_color_action_on_fano_points (x : ZMod 7) : ZMod 7 := z3Mul x

/-- The `ℤ₃` generator acting on the Koide cone phase `θ ∈ ℝ`.
    Realized as `θ ↦ θ + 2π/3` in `KoideGenerationCyclicSymmetry`. -/
noncomputable def z3_flavor_action_on_koide_phase (θ : ℝ) : ℝ := θ + 2 * Real.pi / 3

/-- The `ℤ₃` generator acting on generation labels (`Fin 3`).
    Matches the cyclic permutation realized by the Koide phase shift. -/
def z3_flavor_action_on_generation (g : Fin 3) : Fin 3 := g + 1

theorem z3_color_fixed_point_at_zero :
    z3_color_action_on_fano_points 0 = 0 := by
  simp [z3_color_action_on_fano_points, z3Mul]

theorem z3_flavor_no_phase_fixed_point (θ : ℝ) :
    z3_flavor_action_on_koide_phase θ ≠ θ := by
  intro h
  have h' : θ + 2 * Real.pi / 3 = θ := by simpa [z3_flavor_action_on_koide_phase] using h
  have hpos : 0 < 2 * Real.pi / 3 := by
    apply div_pos (mul_pos (by norm_num) Real.pi_pos)
    norm_num
  have : (2 : ℝ) * Real.pi / 3 = 0 := by linarith
  exact ne_of_gt hpos this

theorem z3_flavor_no_generation_fixed_point (g : Fin 3) :
    z3_flavor_action_on_generation g ≠ g := by
  fin_cases g <;> decide

theorem z3_color_cubed_is_identity (x : ZMod 7) :
    z3_color_action_on_fano_points (z3_color_action_on_fano_points (z3_color_action_on_fano_points x)) = x := by
  native_decide +revert

theorem z3_flavor_generation_cubed (g : Fin 3) :
    z3_flavor_action_on_generation (z3_flavor_action_on_generation (z3_flavor_action_on_generation g)) = g := by
  fin_cases g <;> decide

theorem cone_phase_shift_matches_generation (b θ : ℝ) :
    vAmp b (θ + 2 * Real.pi / 3) 0 = vAmp b θ 1 ∧
    vAmp b (θ + 2 * Real.pi / 3) 1 = vAmp b θ 2 ∧
    vAmp b (θ + 2 * Real.pi / 3) 2 = vAmp b θ 0 := by
  exact ⟨cone_cyclic_shift_0 b θ, cone_cyclic_shift_1 b θ, cone_cyclic_shift_2 b θ⟩

/-- **color_flavor_actions_distinct**: no map `ZMod 7 → Fin 3` intertwines the two
    `ℤ₃` actions. The color action fixes `0`; the flavor action on generations
    has no fixed points. -/
theorem color_flavor_actions_distinct :
    ¬∃ f : ZMod 7 → Fin 3,
      ∀ x, f (z3_color_action_on_fano_points x) = z3_flavor_action_on_generation (f x) := by
  intro ⟨f, hf⟩
  have h0 := hf 0
  simp [z3_color_fixed_point_at_zero] at h0
  exact z3_flavor_no_generation_fixed_point (f 0) h0.symm

theorem z3_color_generates_z3 :
    z3Mul (z3Mul (z3Mul 1)) = 1 ∧ (2 : ZMod 7) ^ 3 = 1 := by
  refine ⟨?_, z3_order_three⟩
  native_decide

theorem z3_flavor_generates_z3 (g : Fin 3) :
    z3_flavor_action_on_generation (z3_flavor_action_on_generation (z3_flavor_action_on_generation g)) = g :=
  z3_flavor_generation_cubed g

/-- Master bundle: two order-3 actions on distinct carriers, with incompatible
    fixed-point structure, witnessing the same abstract `ℤ₃` in different
    representations (inner color vs outer flavor triality). -/
theorem z3_color_flavor_disambiguation :
    z3_color_action_on_fano_points 0 = 0 ∧
    (∀ θ : ℝ, z3_flavor_action_on_koide_phase θ ≠ θ) ∧
    (¬∃ f : ZMod 7 → Fin 3,
      ∀ x, f (z3_color_action_on_fano_points x) = z3_flavor_action_on_generation (f x)) ∧
    (z3Mul (z3Mul (z3Mul 1)) = 1 ∧ (2 : ZMod 7) ^ 3 = 1) ∧
    (∀ g : Fin 3,
      z3_flavor_action_on_generation (z3_flavor_action_on_generation (z3_flavor_action_on_generation g)) = g) := by
  exact ⟨z3_color_fixed_point_at_zero,
    ⟨fun θ => z3_flavor_no_phase_fixed_point θ,
      ⟨color_flavor_actions_distinct,
        ⟨z3_color_generates_z3, fun g => z3_flavor_generates_z3 g⟩⟩⟩⟩

end UgpLean.Algebra.OctonionColorFlavorDisambiguation
