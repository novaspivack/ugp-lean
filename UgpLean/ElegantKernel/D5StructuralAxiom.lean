import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Algebra.Field.Basic
import UgpLean.ElegantKernel.KGen2
import UgpLean.LModelDerivation

/-!
# UgpLean.ElegantKernel.D5StructuralAxiom — Phase B1 of THM-UCL-1

## Structural framing

In Phase A (`UgpLean.ElegantKernel.KGen2`), we Lean-certified the trigonometric
core:

    cos(4π/5) = −φ/2                (zero sorry)

The target theorem THM-UCL-1 is `k_gen² = −φ/2`.  The gap between Phase A and
the target is the **structural claim** that k_gen² equals `cos(4π/5)` — i.e.,
the real part of a primitive 5th root of unity squared.

This module formalizes that structural claim as a **named hypothesis**
(`D5PentagonHessian`) and proves the target conditionally.  Phase B2 will
derive the hypothesis from `L_model`'s Lean-certified Q(√5) structure.

## Why the claim is structurally sound (Phase B2 preview)

The hypothesis is not ad hoc:

1. `L_model = log₂(2⁴ · 5³ / 3)` is Lean-certified (see
   `UgpLean.LModelDerivation.L_model_from_gauge_structure`).

2. The 5³ factor is documented in ugp-lean as *"continuous wedge factor 5³
   from rank-3 geometry over Q(√5)"*.  The UGP framework's continuous sector
   therefore embeds over the quadratic field Q(√5).

3. Q(√5) = ℤ[φ], the integer ring of the golden field, is the real subfield
   of the 5th cyclotomic field Q(ζ₅) where ζ₅ = e^{2πi/5}.

4. The natural D₅ dihedral symmetry of Q(ζ₅) acts on the UCL's continuous
   (L, g) sector.  The five primitive real parts are
       cos(0), cos(2π/5), cos(4π/5), cos(6π/5), cos(8π/5)
   = {1, (√5−1)/4, −(1+√5)/4, −(1+√5)/4, (√5−1)/4}
   = {1, (φ−1)/2, −φ/2, −φ/2, (φ−1)/2}.

5. The UCL generation coefficient `k_gen²` is identified with the **second
   non-trivial real root**, −φ/2 = cos(4π/5), corresponding to ζ₅² (the
   square of the primitive generator).

Phase B2 will make step 5 rigorous by constructing the Fisher-isotropic
Hessian of the GTE-linearized UCL and showing its g-eigenvalue matches this
specific D₅ cyclotomic root.

## Phase B1 (this module)

We package the D₅ claim as a `Prop`-valued hypothesis and prove the target
under it.  Concretely, we state:

    D5PentagonHessian : Prop  -- the axiom k_gen² = cos(4π/5)

and derive `k_gen² = −φ/2` conditional on `D5PentagonHessian`.

Because Phase A already established `k_gen₂ = −φ/2 = cos(4π/5)` by
definition, `D5PentagonHessian` holds for the packaged `k_gen2`; we provide
a theorem witnessing this.  Phase B2 replaces the trivial witness with a
genuine derivation from L_model structure.
-/

namespace UgpLean.ElegantKernel.D5

open Real UgpLean.ElegantKernel

/-! ## The D₅ pentagonal Hessian axiom -/

/-- **The D₅ Hessian axiom.**  In the Fisher-isotropic frame of the UCL on the
(L, g) plane, the generation-squared coefficient `k_gen²` equals
`cos(4π/5)`, which is the real part of ζ₅² (the square of the primitive 5th
root of unity).

This axiom encodes the structural claim that the UCL continuous sector
inherits the D₅ dihedral symmetry from its embedding in Q(√5) (the real
subfield of Q(ζ₅)), which is in turn forced by the `5³` wedge factor in
`L_model = log₂(2⁴ · 5³ / 3)` (Lean-certified in
`UgpLean.LModelDerivation.L_model_from_gauge_structure`).

Phase B2 derives this axiom from that upstream structure; Phase B1 (this
file) takes it as a named hypothesis. -/
def D5PentagonHessian : Prop :=
  k_gen2 = cos (4 * π / 5)

/-- The axiom is satisfied in the Phase A setting, where `k_gen₂` is defined
as `-(goldenRatio / 2)` and equals `cos(4π/5)` by `k_gen2_eq_cos_4pi_div_5`.
This provides an existence witness for the D₅ axiom; Phase B2 replaces this
trivial witness with a structural derivation from the L_model Q(√5) chain. -/
theorem d5_pentagon_hessian_holds : D5PentagonHessian :=
  k_gen2_eq_cos_4pi_div_5

/-! ## The conditional theorem -/

/-- **THM-UCL-1 (Phase B1 form).**  Under the D₅ Hessian axiom, the UCL
generation-squared coefficient equals −φ/2 (negative half the golden ratio). -/
theorem k_gen2_eq_neg_phi_half_from_D5
    (hD5 : D5PentagonHessian) : k_gen2 = -(goldenRatio / 2) := by
  unfold D5PentagonHessian at hD5
  rw [hD5]
  exact cos_4pi_div_five_eq_neg_phi_half

/-- **THM-UCL-1 (Phase B1 combined).**  Combining the D₅ axiom (trivially
witnessed for the packaged definition) with the conditional theorem:
`k_gen² = −φ/2`. -/
theorem k_gen2_eq_neg_phi_half : k_gen2 = -(goldenRatio / 2) :=
  k_gen2_eq_neg_phi_half_from_D5 d5_pentagon_hessian_holds

/-! ## Support theorems: characterisation of the D₅ pentagon roots -/

/-- The five real parts of `{ζ₅^k : k = 0, …, 4}`.  These are the roots of
the Chebyshev identity / 5th-roots-of-unity real-part equation.  The set is
`{1, cos(2π/5), cos(4π/5), cos(6π/5), cos(8π/5)} =
{1, (φ−1)/2, −φ/2, −φ/2, (φ−1)/2}`.

We need only the k=2 case for THM-UCL-1, but record all five for context. -/

theorem pentagon_root_0 : cos (0 : ℝ) = 1 := cos_zero

theorem pentagon_root_1 : cos (2 * π / 5) = (goldenRatio - 1) / 2 :=
  cos_2pi_div_five_eq_phi_minus_one_div_2

/-- **The D₅ root selected by the UCL**: cos(4π/5) = −φ/2. -/
theorem pentagon_root_2 : cos (4 * π / 5) = -(goldenRatio / 2) :=
  cos_4pi_div_five_eq_neg_phi_half

/-- cos(6π/5) = cos(2π − 6π/5) = cos(4π/5) = −φ/2 by periodicity + evenness. -/
theorem pentagon_root_3 : cos (6 * π / 5) = -(goldenRatio / 2) := by
  have h : (6 * π / 5 : ℝ) = -(4 * π / 5) + 2 * π := by ring
  rw [h, cos_add_two_pi, cos_neg]
  exact pentagon_root_2

/-- cos(8π/5) = cos(2π − 8π/5) = cos(2π/5) = (φ−1)/2. -/
theorem pentagon_root_4 : cos (8 * π / 5) = (goldenRatio - 1) / 2 := by
  have h : (8 * π / 5 : ℝ) = -(2 * π / 5) + 2 * π := by ring
  rw [h, cos_add_two_pi, cos_neg]
  exact pentagon_root_1

/-- The D₅ real pentagon has **exactly three distinct real-part values**.
We record the pairwise distinctness: `(φ−1)/2 ≠ −φ/2` (one positive, one
negative) is the key asymmetry that makes `k_gen² = −φ/2` a sharp selection
rather than one of two equivalent options. -/
theorem phi_minus_one_half_ne_neg_phi_half :
    (goldenRatio - 1) / 2 ≠ -(goldenRatio / 2) := by
  intro h
  -- (φ - 1)/2 = -φ/2  ⇒  φ - 1 = -φ  ⇒  2φ = 1  ⇒  φ = 1/2
  have h1 : goldenRatio - 1 = -goldenRatio := by linarith
  have h2 : 2 * goldenRatio = 1 := by linarith
  -- But goldenRatio > 1 since (1 + √5)/2 > 1 because √5 > 1 (since 5 > 1).
  have : goldenRatio > 1 := by
    unfold Real.goldenRatio
    have hsqrt_gt : √(5 : ℝ) > 1 := by
      have h1 : (1 : ℝ) = √1 := (Real.sqrt_one).symm
      rw [h1]
      exact Real.sqrt_lt_sqrt (by norm_num) (by norm_num)
    linarith
  linarith

end UgpLean.ElegantKernel.D5
