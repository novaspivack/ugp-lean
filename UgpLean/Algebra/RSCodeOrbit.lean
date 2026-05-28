import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Fin.VecNotation
import Mathlib.Tactic
import UgpLean.Substrate.GEQECCode

/-!
# GTE Generation Orbit Vectors as RS Codewords (EPIC_078 / OQ-QG-9)

Certifies that the three GTE generation orbit vectors over GF(7), evaluated at the
PSC-admissible winding classes `{0, 2, 3, 4, 6}`, are codewords of the `[5, 3, 3]₇`
Reed–Solomon code:

- `gen1` = (1, 1, 1, 1, 1) — evaluation of the constant polynomial `f(x) = 1`
- `gen2` = (0, 2, 3, 4, 6) — evaluation of the identity polynomial `f(x) = x`
- `gen3` = (0, 4, 2, 2, 1) — evaluation of the quadratic polynomial `f(x) = x²`

The three vectors are linearly independent over ZMod 7, spanning the message space
of dimension `k = 3 = N_gen = n − d + 1`.

All theorems: zero sorry, zero custom axioms.
-/

namespace UgpLean.Algebra.RSCodeOrbit

/-- PSC-admissible RS evaluation points in fixed order: `{0, 2, 3, 4, 6} ⊂ GF(7)`. -/
def eval_points : Fin 5 → ZMod 7 := ![0, 2, 3, 4, 6]

/-- Generation-1 orbit vector: constant polynomial `f(x) = 1`. -/
def gen1 : Fin 5 → ZMod 7 := ![1, 1, 1, 1, 1]

/-- Generation-2 orbit vector: identity polynomial `f(x) = x`. -/
def gen2 : Fin 5 → ZMod 7 := ![0, 2, 3, 4, 6]

/-- Generation-3 orbit vector: quadratic polynomial `f(x) = x²`. -/
def gen3 : Fin 5 → ZMod 7 := ![0, 4, 2, 2, 1]

/-- Message dimension of the `[5, 3, 3]₇` RS code: `k = n − d + 1 = 5 − 3 + 1 = 3`. -/
def rsMessageDimension : ℕ := 3

/-- `gen1` is the evaluation of `f(x) = 1` at the PSC-admissible points. -/
theorem gen1_is_constant_poly :
    ∀ i : Fin 5, gen1 i = 1 := by decide

/-- `gen2` is the evaluation of `f(x) = x` at the PSC-admissible points. -/
theorem gen2_is_identity_poly :
    ∀ i : Fin 5, gen2 i = eval_points i := by decide

/-- `gen3` is the evaluation of `f(x) = x²` at the PSC-admissible points. -/
theorem gen3_is_square_poly :
    ∀ i : Fin 5, gen3 i = eval_points i ^ 2 := by decide

/-- `N_gen = 3` equals the RS message dimension `k = n − d + 1`. -/
theorem ngen_equals_rs_dimension : rsMessageDimension = 5 - 3 + 1 := rfl

/-- The three generation orbit vectors are linearly independent over GF(7). -/
theorem orbit_vectors_linearly_independent :
    ∀ a1 a2 a3 : ZMod 7,
      (∀ i : Fin 5, a1 * gen1 i + a2 * gen2 i + a3 * gen3 i = 0) →
        a1 = 0 ∧ a2 = 0 ∧ a3 = 0 := by decide

/-- Master bundle: GTE generation orbit vectors are RS codeword evaluations. -/
theorem gte_orbit_vectors_are_rs_codewords :
    (∀ i : Fin 5, gen1 i = 1) ∧
      (∀ i : Fin 5, gen2 i = eval_points i) ∧
      (∀ i : Fin 5, gen3 i = eval_points i ^ 2) ∧
      rsMessageDimension = 5 - 3 + 1 ∧
      (∀ a1 a2 a3 : ZMod 7,
        (∀ i : Fin 5, a1 * gen1 i + a2 * gen2 i + a3 * gen3 i = 0) →
          a1 = 0 ∧ a2 = 0 ∧ a3 = 0) := by
  refine ⟨gen1_is_constant_poly, gen2_is_identity_poly, gen3_is_square_poly, rfl, ?_⟩
  exact orbit_vectors_linearly_independent

end UgpLean.Algebra.RSCodeOrbit
