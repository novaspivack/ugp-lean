import Mathlib.Data.ZMod.Basic

/-!
# Electric Charge as Linear Term of GTE Polynomial

The electric charge Q(w) = w/3 for PSC winding numbers.
In GF(7): 3Q(w) = p(0,w,0) = w exactly.

This shows gravity and EM are the cubic-vs-linear degree split of one polynomial:
- Gravity source: p(w_x,w_y,w_z) (degree-3 cross-tape diagonal)
- EM charge:     p(0,w,0) = w     (degree-1 center projection)
-/

namespace ChargeFromPolynomial

def gtePolynomial (L C R : ZMod 7) : ZMod 7 := C + R - C * R - L * C * R

/-- p(0,w,0) = w for all w ∈ ZMod 7 -/
theorem gte_poly_center_projection (w : ZMod 7) :
    gtePolynomial 0 w 0 = w := by
  simp [gtePolynomial]

/-- The electric charge (×3, mod 7) is exactly the center projection of p -/
theorem gte_charge_is_linear_projection :
    ∀ w : ZMod 7, gtePolynomial 0 w 0 = w := by
  intro w
  simp [gtePolynomial]

/-- Verify for all PSC-admissible winding numbers -/
theorem gte_charge_psc_table :
    let p := gtePolynomial
    p 0 0 0 = 0 ∧
    p 0 2 0 = 2 ∧
    p 0 3 0 = 3 ∧
    p 0 4 0 = 4 ∧
    p 0 6 0 = 6 := by
  decide

/--
Gravity is the degree-3 diagonal; EM is the degree-1 center term.
Both from the same 19-bit polynomial p(L,C,R) = C+R-CR-LCR mod 7.
-/
theorem gravity_em_degree_split :
    let p := gtePolynomial
    (p 2 2 2 = 6) ∧
    (p 0 2 0 = 2) ∧
    (p 0 0 0 = 0) ∧
    (p 3 3 3 = 5) ∧
    (p 0 3 0 = 3) := by
  decide

-- === Tape Role Asymmetry ===

/-- Tape_x (L position) alone gives zero gravitational source for any winding -/
theorem l_tape_zero_source (w : ZMod 7) :
    gtePolynomial w 0 0 = 0 := by
  simp [gtePolynomial]

/-- Tape_y and tape_z (C,R positions) give linear single-tape sources = electric charge × 3 -/
theorem tape_role_asymmetry :
    ∀ w : ZMod 7,
    gtePolynomial 0 w 0 = w ∧    -- tape_y alone: p(0,w,0) = w (EM charge source)
    gtePolynomial 0 0 w = w := by  -- tape_z alone: p(0,0,w) = w (EM charge source)
  decide

/-- The GTE polynomial is NOT additively separable: no functions f,g,h exist such that
    p(L,C,R) = f(L)+g(C)+h(R) for all PSC inputs. Witness: p(0,2,2)=0 ≠ p(0,2,0)+p(0,0,2)=4 -/
theorem non_separability_witness :
    gtePolynomial 0 2 2 ≠ gtePolynomial 0 2 0 + gtePolynomial 0 0 2 := by decide

/-- Gravity source requires cross-tape coordination: p(L,0,0)=0 for ALL L, but p(L,C,R)
    is the cubic −LCR cross-term when C,R ≠ 0. EM comes from degree-1 linear terms;
    gravity from degree-3 cubic. -/
theorem gravity_requires_cross_tape_coordination :
    -- Single-tape source from L alone: always zero
    (∀ w : ZMod 7, gtePolynomial w 0 0 = 0) ∧
    -- Full cross-tape (u-quark): maximum gravitational source
    (gtePolynomial 2 2 2 = 6) ∧
    -- L alone vs full: zero vs nonzero gravitational source
    (gtePolynomial 2 0 0 = 0) ∧
    (gtePolynomial 2 0 0 ≠ gtePolynomial 2 2 2) := by
  decide

end ChargeFromPolynomial
