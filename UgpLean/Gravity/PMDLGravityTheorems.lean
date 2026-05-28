import Mathlib.Data.ZMod.Basic
import UgpLean.Gravity.PSCQECWaldConnections
import UgpLean.Universality.PhiMDLUniversality

/-!
# PMDL Gravity Theorems (EPIC_079)

Machine certification of the GTE polynomial's gravitational role on PSC-admissible
winding classes over GF(7):

1. **Mass table** — `p(w,w,w)` on `{0,2,3,4,6}` matches the SM gravitational hierarchy.
2. **Vacuum fixed-point uniqueness** — `x = 0` is the only solution of `p(x,x,x) = x`.
3. **MDL cubic uniqueness** — exactly one cubic `f(w) = aw + bw² + cw³` matches the hierarchy.
4. **Unified polynomial** — Role 1 (Rule 110) via `rule110_z7_poly_rep`; Role 3 (gravity mass).

Role 2 (gauge winding conservation at SM vertices) is numerically CatA in EPIC_079;
formal Lean integration deferred to a future module.

## Status

CatAL — zero sorry, zero custom axioms (Theorems 1–5).
-/

namespace UgpLean.Gravity.PMDLGravityTheorems

open UgpLean.Gravity.PSCQECWaldConnections
open UgpLean.Universality.PhiMDLUniversality

/-- The GTE polynomial `p(L,C,R) = C + R − C·R − L·C·R` over GF(7). -/
def gtePolynomial (L C R : ZMod 7) : ZMod 7 :=
  C + R - C * R - L * C * R

/-- Diagonal restriction `p(w,w,w) = 2w − w² − w³` over GF(7). -/
def diagonalMass (w : ZMod 7) : ZMod 7 :=
  2 * w - w ^ 2 - w ^ 3

/-- Cubic ansatz for MDL gravity coupling on PSC inputs. -/
def cubicGravityCoupling (abc : ZMod 7 × ZMod 7 × ZMod 7) (w : ZMod 7) : ZMod 7 :=
  match abc with
  | (a, ⟨b, c⟩) => a * w + b * w ^ 2 + c * w ^ 3

/-- PSC-admissible winding classes used for the gravitational mass table. -/
def pscWindingInputs : Finset (ZMod 7) := pscAdmissibleWindingClasses

/-- Unique MDL cubic coefficients `(a,b,c) = (2,6,6)` over GF(7). -/
def mdlUniqueCoefficients : ZMod 7 × ZMod 7 × ZMod 7 :=
  ((2 : ZMod 7), ⟨(6 : ZMod 7), (6 : ZMod 7)⟩)

-- ============================================================
-- I. GF(7) diagonal identity and mass table (Theorem 1)
-- ============================================================

theorem diagonal_mass_eq_gte_polynomial (w : ZMod 7) :
    diagonalMass w = gtePolynomial w w w := by
  unfold diagonalMass gtePolynomial; ring

theorem p_w_w_w_zero : gtePolynomial 0 0 0 = 0 := by
  unfold gtePolynomial; decide

theorem p_w_w_w_two : gtePolynomial 2 2 2 = 6 := by
  unfold gtePolynomial; decide

theorem p_w_w_w_three : gtePolynomial 3 3 3 = 5 := by
  unfold gtePolynomial; decide

theorem p_w_w_w_four : gtePolynomial 4 4 4 = 5 := by
  unfold gtePolynomial; decide

theorem p_w_w_w_six : gtePolynomial 6 6 6 = 5 := by
  unfold gtePolynomial; decide

/-- Diagonal mass values on PSC-admissible inputs (computational mass table). -/
theorem psc_gravitational_mass_table :
    diagonalMass 0 = 0 ∧
      diagonalMass 2 = 6 ∧
      diagonalMass 3 = 5 ∧
      diagonalMass 4 = 5 ∧
      diagonalMass 6 = 5 := by
  unfold diagonalMass; decide

-- ============================================================
-- II. Vacuum fixed-point uniqueness (Theorem 2)
-- ============================================================

theorem vacuum_unique_fixed_point_z7 :
    ∀ x : ZMod 7, diagonalMass x = x → x = 0 := by
  decide

-- ============================================================
-- III. Gravitational mass hierarchy (Theorem 3)
-- ============================================================

theorem gte_gravity_mass_hierarchy :
    diagonalMass 0 = 0 ∧
      diagonalMass 2 = 6 ∧
      diagonalMass 3 = 5 ∧
      diagonalMass 4 = 5 ∧
      diagonalMass 6 = 5 := by
  unfold diagonalMass; decide

-- ============================================================
-- IV. MDL uniqueness of cubic polynomial (Theorem 4)
-- ============================================================

def cubicMatchesPscHierarchy (abc : ZMod 7 × ZMod 7 × ZMod 7) : Prop :=
  let f := cubicGravityCoupling abc
  f 0 = 0 ∧ f 2 = 6 ∧ f 3 = 5 ∧ f 4 = 5 ∧ f 6 = 5

private lemma cubic_coefficients_unique (abc : ZMod 7 × ZMod 7 × ZMod 7)
    (h : cubicMatchesPscHierarchy abc) : abc = mdlUniqueCoefficients := by
  rcases abc with ⟨a, ⟨b, c⟩⟩
  fin_cases a <;> fin_cases b <;> fin_cases c <;>
    unfold cubicMatchesPscHierarchy cubicGravityCoupling at h <;>
    first | native_decide | (cases h; contradiction)

theorem unique_cubic_gravity_coupling :
    ∃! abc : ZMod 7 × ZMod 7 × ZMod 7, cubicMatchesPscHierarchy abc := by
  use mdlUniqueCoefficients
  constructor
  · unfold cubicMatchesPscHierarchy cubicGravityCoupling mdlUniqueCoefficients; decide
  · exact cubic_coefficients_unique

theorem mdl_unique_coefficients :
    cubicMatchesPscHierarchy mdlUniqueCoefficients ∧
      ∀ abc, cubicMatchesPscHierarchy abc → abc = mdlUniqueCoefficients := by
  refine ⟨?_, cubic_coefficients_unique⟩
  unfold cubicMatchesPscHierarchy cubicGravityCoupling mdlUniqueCoefficients; decide

theorem mdl_coupling_is_diagonal_mass :
    ∀ w : ZMod 7, cubicGravityCoupling mdlUniqueCoefficients w = diagonalMass w := by
  intro w
  fin_cases w <;>
    unfold cubicGravityCoupling diagonalMass mdlUniqueCoefficients <;>
    native_decide

-- ============================================================
-- V. Unified polynomial three-role statement (Theorem 5)
-- ============================================================

private lemma binary_z7_eq_bool_embed (z : ZMod 7) (h : z = 0 ∨ z = 1) :
    z = bool_to_z7 (z7_to_bool z) := by
  rcases h with rfl | rfl <;> decide

/-- Role 1: on binary Z₇ inputs `{0,1}`, `p` agrees with Rule 110 via `rule110_z7_poly_rep`. -/
theorem gte_polynomial_rule110_on_binary (L C R : ZMod 7)
    (hL : L = 0 ∨ L = 1) (hC : C = 0 ∨ C = 1) (hR : R = 0 ∨ R = 1) :
    gtePolynomial L C R =
      bool_to_z7 (rule110_output (z7_to_bool L) (z7_to_bool C) (z7_to_bool R)) := by
  have h := rule110_z7_poly_rep (z7_to_bool L) (z7_to_bool C) (z7_to_bool R)
  rw [← binary_z7_eq_bool_embed L hL,
      ← binary_z7_eq_bool_embed C hC,
      ← binary_z7_eq_bool_embed R hR] at h
  exact h.symm

/-- **gte_polynomial_three_roles_k_zero** (CatAL):
    The same 19-bit GTE polynomial operates in two Lean-certified roles at K_extra = 0:

    - **Role 1 (spatial):** on binary tape cells, `p` equals Rule 110 (`rule110_z7_poly_rep`).
    - **Role 3 (gravity):** on PSC diagonal inputs, `p(w,w,w)` gives the mass hierarchy.

    Role 2 (gauge: SM vertex winding conservation) is established numerically in EPIC_079;
    Lean formalization is deferred pending a dedicated gauge-conservation module. -/
theorem gte_polynomial_three_roles_k_zero :
    (∀ (l c r : ZMod 7),
        (l = 0 ∨ l = 1) → (c = 0 ∨ c = 1) → (r = 0 ∨ r = 1) →
          gtePolynomial l c r =
            bool_to_z7 (rule110_output (z7_to_bool l) (z7_to_bool c) (z7_to_bool r)))
      ∧
        (let mass w := gtePolynomial w w w
         mass 0 = 0 ∧ mass 2 = 6 ∧ mass 3 = 5 ∧ mass 4 = 5 ∧ mass 6 = 5) := by
  refine ⟨fun l c r hL hC hR => gte_polynomial_rule110_on_binary l c r hL hC hR, ?_⟩
  unfold gtePolynomial; decide

end UgpLean.Gravity.PMDLGravityTheorems
