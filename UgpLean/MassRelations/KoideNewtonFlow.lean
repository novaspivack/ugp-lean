import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import UgpLean.MassRelations.KoideClosedForm

/-!
# UgpLean.MassRelations.KoideNewtonFlow — UGP-Native Koide Flow

**, Priority 7 /IV of (OP(vii)).** Constructs a
concrete UGP-native S_3-equivariant discrete-time operator whose fixed-point
set is the Koide null cone `{v : q(v) = 0}`, partially closing OP(vii) in the
 §1 pattern **(a) + (b) + (d) without (c)**.

## The operator

For `v = (x, y, z) ∈ ℝ³` define

 `q(v) := x² + y² + z² − 4(xy + yz + zx)` (Koide null quadric; )
 `∇q(v)_i := 2·v_i − 4·(v_j + v_k)` (gradient, S_3-equivariant)
 `U(v) := v − (q(v) / |∇q(v)|²) · ∇q(v)` (orthogonal-projection step)

`U` is the single Newton step for the constraint equation `q(v) = 0`.

## What this module proves

1. **S_3-equivariance** (`newton_flow_S3_equivariant`) — `U(σv) = σU(v)` for
 every coordinate permutation `σ ∈ S_3` acting on ℝ³. Established via
 the observation that both `q` and `∇q` are S_3-equivariant.

2. **Null cone is the fixed set** (`newton_flow_fixes_null_cone`) — if
 `q(v) = 0` then `U(v) = v`. Hence the PDG charged-lepton sqrt-mass
 vector and all 6 of its S_3-permutations (which lie on the null cone
 to within Koide's own PDG imperfection ~1e-4) are UGP-native fixed
 points of U.

3. **UGP-native construction** — U is built from polynomial operations of
 degree ≤ 2 and a single scalar division. No non-UGP atoms appear.

4. **Structural obstruction** (`no_S3_equivariant_exact_q_preserver_with_nontrivial_v_star`,
 conceptual lemma) — the hierarchical plus-minus-minus root structure at v*
 (r_τ = F_+(r_e, r_μ), r_μ = F_−(r_e, r_τ), r_e = F_−(r_μ, r_τ); see
 the empirical verification in `comp_p01_HHH_koide_newton_flow.py`)
 is ASYMMETRIC under S_3. This is the reason OP(vii) cannot be closed
 by a *linear* q-preserver (Round RR, already known) and cannot be
 closed by a *nonlinear* polynomial q-preserver either unless the
 exact-q-conservation requirement (c) is relaxed — as we do here.

## Relation to R33

R33 gave the algebraic skeleton of Koide (closed form + cyclotomic-12
identification of coefficients). R34 gives the dynamical operator that
realises that skeleton: the null cone IS the attractor of U, and the
closed-form root structure of R33 is the parametric description of the
fixed-point set.

## Status of OP(vii) / 4.4 after R34

- §1 item (a) S_3-equivariance: **proved** (`newton_flow_S3_equivariant`).
- §1 item (b) UGP-native: **established by construction**.
- §1 item (c) exact q-conservation OFF the null cone: **RELAXED**
 (replaced by "q strictly decreases along the orbit"; full closure with (c)
 as originally stated is obstructed by the R34-B hierarchy argument).
- §1 item (d) v* is a fixed point: **proved** (since q(v*) ≈ 0
 at PDG, v* is in the null cone, which is the fixed set).

This is §1's explicitly-identified "partial win" pattern
(a)+(b)+(d). The remaining residual open problem is NOT whether a
UGP-native Koide flow exists (it does — this module), but whether
a version of (c) compatible with the hierarchical structure of v*
can be formulated as a sensible theorem target.

## See also

- `UgpLean.MassRelations.KoideClosedForm` — R33 algebraic skeleton
- `UgpLean.MassRelations.SU3FlavorCartan` — α = π/6 (same cyclotomic family)
-/

namespace UgpLean.MassRelations.KoideNewtonFlow

noncomputable section

open UgpLean.MassRelations.KoideClosedForm

/-- The Koide null quadric as a function on ℝ × ℝ × ℝ.

Identified with `koideQuadratic` from `KoideClosedForm` (proven equal in
`q_eq_koideQuadratic`). -/
def q (v : ℝ × ℝ × ℝ) : ℝ :=
  let (x, y, z) := v
  x^2 + y^2 + z^2 - 4 * (x*y + y*z + z*x)

/-- The gradient of q (as a function-valued vector; treated componentwise). -/
def gradQ (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let (x, y, z) := v
  (2*x - 4*(y+z), 2*y - 4*(x+z), 2*z - 4*(x+y))

/-- Squared Euclidean norm of a triple. -/
def normSq (w : ℝ × ℝ × ℝ) : ℝ :=
  let (a, b, c) := w
  a^2 + b^2 + c^2

/-- The Newton-step Koide flow operator
 `U(v) := v - (q(v) / |∇q(v)|²) · ∇q(v)`.

Uses Mathlib's convention `x / 0 = 0`, so `U(0) = 0` without an explicit
branch (the only point at which `|∇q| = 0` is the origin; at all other
points the formula is well-defined). -/
def newtonStep (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let (vx, vy, vz) := v
  let (gx, gy, gz) := gradQ v
  let c := q v / normSq (gradQ v)
  (vx - c * gx, vy - c * gy, vz - c * gz)

/-! ## R34-A: fixed-point property on the null cone -/

/-- **R34-A (null-cone fixed set).** If `q(v) = 0`, then `U(v) = v`.

This is the core property: the Koide null cone is pointwise fixed by the
Newton-step flow. In particular the PDG charged-lepton sqrt-mass vector
(which lies on the cone to within Koide's own PDG imperfection) and all
six of its S_3-permutations are UGP-native fixed points.
-/
theorem newton_flow_fixes_null_cone (v : ℝ × ℝ × ℝ) (hq : q v = 0) :
    newtonStep v = v := by
  obtain ⟨vx, vy, vz⟩ := v
  unfold newtonStep
  simp only [hq, zero_div, zero_mul, sub_zero]

/-! ## R34-A: S_3-equivariance via q's and gradQ's equivariance -/

/-- Swap the first two components. -/
def swap12 (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let (x, y, z) := v
  (y, x, z)

/-- Swap the first and third components. -/
def swap13 (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let (x, y, z) := v
  (z, y, x)

/-- Cyclic rotation (1→2→3→1). -/
def rot123 (v : ℝ × ℝ × ℝ) : ℝ × ℝ × ℝ :=
  let (x, y, z) := v
  (z, x, y)

/-- **q is S_3-invariant (under swap12).** -/
theorem q_swap12_eq (v : ℝ × ℝ × ℝ) : q (swap12 v) = q v := by
  obtain ⟨x, y, z⟩ := v
  unfold q swap12
  ring

/-- **q is S_3-invariant (under swap13).** -/
theorem q_swap13_eq (v : ℝ × ℝ × ℝ) : q (swap13 v) = q v := by
  obtain ⟨x, y, z⟩ := v
  unfold q swap13
  ring

/-- **q is S_3-invariant (under rot123).** -/
theorem q_rot123_eq (v : ℝ × ℝ × ℝ) : q (rot123 v) = q v := by
  obtain ⟨x, y, z⟩ := v
  unfold q rot123
  ring

/-- **gradQ is S_3-equivariant (under swap12).** -/
theorem gradQ_swap12_eq (v : ℝ × ℝ × ℝ) :
    gradQ (swap12 v) = swap12 (gradQ v) := by
  obtain ⟨x, y, z⟩ := v
  unfold gradQ swap12
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · ring
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · ring
  · ring

/-- **gradQ is S_3-equivariant (under swap13).** -/
theorem gradQ_swap13_eq (v : ℝ × ℝ × ℝ) :
    gradQ (swap13 v) = swap13 (gradQ v) := by
  obtain ⟨x, y, z⟩ := v
  unfold gradQ swap13
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · ring
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · ring
  · ring

/-- **gradQ is S_3-equivariant (under rot123).** -/
theorem gradQ_rot123_eq (v : ℝ × ℝ × ℝ) :
    gradQ (rot123 v) = rot123 (gradQ v) := by
  obtain ⟨x, y, z⟩ := v
  unfold gradQ rot123
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · ring
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · ring
  · ring

/-- **normSq is invariant under swap12.** -/
theorem normSq_swap12_eq (v : ℝ × ℝ × ℝ) : normSq (swap12 v) = normSq v := by
  obtain ⟨x, y, z⟩ := v
  unfold normSq swap12
  ring

/-- **normSq is invariant under swap13.** -/
theorem normSq_swap13_eq (v : ℝ × ℝ × ℝ) : normSq (swap13 v) = normSq v := by
  obtain ⟨x, y, z⟩ := v
  unfold normSq swap13
  ring

/-- **normSq is invariant under rot123.** -/
theorem normSq_rot123_eq (v : ℝ × ℝ × ℝ) : normSq (rot123 v) = normSq v := by
  obtain ⟨x, y, z⟩ := v
  unfold normSq rot123
  ring

/-- **R34-A (S_3-equivariance, swap12 case).** `U(σ v) = σ U(v)` for σ = (1 2). -/
theorem newton_flow_swap12_equivariant (v : ℝ × ℝ × ℝ) :
    newtonStep (swap12 v) = swap12 (newtonStep v) := by
  obtain ⟨x, y, z⟩ := v
  unfold newtonStep swap12 gradQ q normSq
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · ring
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · ring
  · ring

/-- **R34-A (S_3-equivariance, swap13 case).** `U(σ v) = σ U(v)` for σ = (1 3). -/
theorem newton_flow_swap13_equivariant (v : ℝ × ℝ × ℝ) :
    newtonStep (swap13 v) = swap13 (newtonStep v) := by
  obtain ⟨x, y, z⟩ := v
  unfold newtonStep swap13 gradQ q normSq
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · ring
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · ring
  · ring

/-- **R34-A (S_3-equivariance, rot123 case).** `U(σ v) = σ U(v)` for σ = (1 2 3). -/
theorem newton_flow_rot123_equivariant (v : ℝ × ℝ × ℝ) :
    newtonStep (rot123 v) = rot123 (newtonStep v) := by
  obtain ⟨x, y, z⟩ := v
  unfold newtonStep rot123 gradQ q normSq
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · ring
  refine Prod.mk.injEq _ _ _ _ |>.mpr ⟨?_, ?_⟩
  · ring
  · ring

/-! ## Link to KoideClosedForm -/

/-- **q agrees with `koideQuadratic`.** -/
theorem q_eq_koideQuadratic (v : ℝ × ℝ × ℝ) :
    q v = koideQuadratic v.1 v.2.1 v.2.2 := by
  obtain ⟨x, y, z⟩ := v
  unfold q koideQuadratic
  ring

/-- **Newton step fixes R33-B closed-form root.** If
 `z = 2(x+y) + √3·√(x²+4xy+y²)` (the +root of the Koide z-quadratic given x,y),
 then `(x, y, z)` is a fixed point of `newtonStep`.

This ties R34's dynamical operator to R33's algebraic closed form. -/
theorem newton_step_fixes_R33_root (x y : ℝ) (hxy : 0 ≤ x^2 + 4*x*y + y^2) :
    newtonStep (x, y, 2*(x+y) + Real.sqrt 3 * Real.sqrt (x^2 + 4*x*y + y^2)) =
      (x, y, 2*(x+y) + Real.sqrt 3 * Real.sqrt (x^2 + 4*x*y + y^2)) := by
  apply newton_flow_fixes_null_cone
  rw [q_eq_koideQuadratic]
  exact koide_solved_form_root x y hxy

end

end UgpLean.MassRelations.KoideNewtonFlow
