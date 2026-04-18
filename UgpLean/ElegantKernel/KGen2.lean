import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.FieldSimp
import UgpLean.ElegantKernel
import UgpLean.GTE.StructuralTheorems
import UgpLean.LModelDerivation

/-!
# UgpLean.ElegantKernel.KGen2 — k_gen² = −φ/2 from D₅ Pentagonal Symmetry

## Theorem target: THM-UCL-1

The generation curvature coefficient of the UCL equals −φ/2 via the D₅
pentagonal symmetry of the renormalization group flow on the Fisher-isotropic
(L, g) plane.

## Structural chain

  L_model = log₂(2⁴ · 5³ / 3)   [Lean-certified: `L_model_from_gauge_structure`]
     ↓  5³ = rank-3 geometry over Q(√5)
  Q(√5) = Z[φ] = real subfield of Q(ζ₅), ζ₅ = e^{2πi/5}
     ↓  Q(ζ₅) carries D₅ dihedral symmetry
  UCL Fisher-isotropic Hessian on (L, g) inherits D₅ structure
     ↓  D₅ rotation by 4π/5 ≡ 2·(2π/5)
  k_gen² = cos(4π/5)
     ↓  standard trig identity (cos(π−x) = −cos(x))
  cos(4π/5) = −cos(π/5) = −(1+√5)/4   [Mathlib: `Real.cos_pi_div_five`]
     ↓  definition of golden ratio
  cos(4π/5) = −φ/2                    [Mathlib: `Real.goldenRatio`]

## Phase A (this file): the trigonometric core

This module establishes the trigonometric/algebraic portion of the chain,
independently of any UGP-specific structural claims.  Phase B formalizes the
D₅ symmetry argument and shows k_gen² = cos(4π/5) from the Fisher metric.

## Defensibility

See `docs/DEFENSIBILITY_THM_UCL_1.md` for the full Phase 1.5 analysis.
-/

namespace UgpLean.ElegantKernel

open Real

/-! ## Phase A: the core trig/algebraic identity -/

/-- Standard trig identity cos(π − x) = −cos(x), specialized at x = π/5. -/
theorem cos_4pi_div_five_eq_neg_cos_pi_div_five :
    cos (4 * π / 5) = -cos (π / 5) := by
  have h : 4 * π / 5 = π - π / 5 := by ring
  rw [h, cos_pi_sub]

/-- Mathlib already knows `cos(π/5) = (1 + √5)/4`; we record the direct form. -/
theorem cos_pi_div_five_eq : cos (π / 5) = (1 + √5) / 4 :=
  Real.cos_pi_div_five

/-- Therefore cos(4π/5) = −(1+√5)/4. -/
theorem cos_4pi_div_five_eq : cos (4 * π / 5) = -((1 + √5) / 4) := by
  rw [cos_4pi_div_five_eq_neg_cos_pi_div_five, cos_pi_div_five_eq]

/-- (1+√5)/4 = φ/2 by definition of the golden ratio. -/
theorem one_plus_sqrt5_div_4_eq_phi_div_2 :
    (1 + √5) / 4 = Real.goldenRatio / 2 := by
  unfold Real.goldenRatio
  ring

/-- **Core trigonometric identity:** `cos(4π/5) = −φ/2`.
This is the Phase A centerpiece of THM-UCL-1; the algebraic chain from
`cos(4π/5)` (a specific 5th-root-of-unity real part) to `−φ/2` (half-negative
golden ratio) is entirely standard mathematics.  What remains for Phase B is
to establish that the UCL `k_gen²` coefficient equals `cos(4π/5)` via the
D₅ Hessian argument. -/
theorem cos_4pi_div_five_eq_neg_phi_half :
    cos (4 * π / 5) = -(Real.goldenRatio / 2) := by
  rw [cos_4pi_div_five_eq, one_plus_sqrt5_div_4_eq_phi_div_2]

/-! ## Phase B skeleton: the D₅ Hessian axiom + its consequence

The structural claim we aim to Lean-certify in Phase B is:

  Under the D₅ rotation of the Fisher-isotropic (L, g) frame induced by the
  Q(√5) structure embedded in L_model (via the 5³ wedge factor), the UCL
  Hessian's generation-direction coefficient equals cos(4π/5).

Formally, this requires:

(i)   Defining the UCL Fisher-isotropic Hessian as an element of a specific
      2×2 real matrix space.
(ii)  Defining the D₅ action on this space via Q(ζ₅)/Q Galois conjugation.
(iii) Showing the action takes the L-direction to a specific vector whose
      L-component is cos(4π/5).

In Phase B1 (simpler), we state this as a named hypothesis and prove the
conclusion `k_gen² = −φ/2`.

In Phase B2 (deeper), we derive the hypothesis from `L_model` = log₂(2⁴·5³/3)
by formalizing the Q(√5)→D₅ connection.
-/

/-- The UCL generation-squared coefficient as a real number.
    Currently we define it as `-Real.goldenRatio / 2` directly; Phase B proves
    that this matches the value derived from the D₅ Hessian structure. -/
noncomputable def k_gen2 : ℝ := -(Real.goldenRatio / 2)

/-- The UCL k_gen² value equals cos(4π/5) by the trigonometric identity above. -/
theorem k_gen2_eq_cos_4pi_div_5 : k_gen2 = cos (4 * π / 5) := by
  unfold k_gen2
  rw [cos_4pi_div_five_eq_neg_phi_half]

/-- **THM-UCL-1 (Phase A form):** k_gen² equals −φ/2 by trigonometric identity. -/
theorem k_gen2_eq_neg_phi_half : k_gen2 = -(Real.goldenRatio / 2) := rfl

/-! ## Pentagon-golden-ratio identities (support lemmas for Phase B) -/

/-- Double-angle formula cos(2x) = 2 cos²(x) − 1 applied at x = π/5, together
with `cos_pi_div_five`, gives `cos(2π/5) = (√5 − 1)/4`.

(Mathlib doesn't have a direct `cos_two_pi_div_five` in the version pinned
here, so we derive it from the double-angle formula.) -/
theorem cos_2pi_div_five_eq : cos (2 * π / 5) = (√5 - 1) / 4 := by
  have h2x : (2 * π / 5 : ℝ) = 2 * (π / 5) := by ring
  rw [h2x, cos_two_mul, cos_pi_div_five]
  have hsq : (√5 : ℝ)^2 = 5 := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
  -- Goal after rewrite: 2 * ((1 + √5) / 4)^2 - 1 = (√5 - 1) / 4
  -- Expand (1+√5)² = 1 + 2√5 + √5², substitute √5² = 5, simplify
  have expand : ((1 + √5) / 4) ^ 2 = (1 + 2 * √5 + (√5)^2) / 16 := by ring
  rw [expand, hsq]
  ring

/-- cos(2π/5) = (φ − 1)/2 (equivalent form via golden ratio). -/
theorem cos_2pi_div_five_eq_phi_minus_one_div_2 :
    cos (2 * π / 5) = (Real.goldenRatio - 1) / 2 := by
  rw [cos_2pi_div_five_eq]
  unfold Real.goldenRatio
  ring

/-- cos(π/5) − cos(2π/5) = 1/2 (classical pentagon difference identity). -/
theorem cos_pi_div_5_sub_cos_2pi_div_5 :
    cos (π / 5) - cos (2 * π / 5) = 1 / 2 := by
  rw [cos_pi_div_five_eq, cos_2pi_div_five_eq]
  ring

/-- cos(π/5) · cos(2π/5) = 1/4 (product identity).
    Proof: ((1+√5)/4) · ((√5−1)/4) = (√5² − 1²)/16 = 4/16 = 1/4. -/
theorem cos_pi_div_5_mul_cos_2pi_div_5 :
    cos (π / 5) * cos (2 * π / 5) = 1 / 4 := by
  rw [cos_pi_div_five_eq, cos_2pi_div_five_eq]
  have hsq : (√5 : ℝ)^2 = 5 := Real.sq_sqrt (by norm_num : (5:ℝ) ≥ 0)
  have expand : ((1 + √5) / 4) * ((√5 - 1) / 4) = ((√5)^2 - 1) / 16 := by ring
  rw [expand, hsq]
  ring

end UgpLean.ElegantKernel
