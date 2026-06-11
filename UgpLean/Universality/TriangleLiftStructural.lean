import Mathlib
import UgpLean.Universality.CUP4TotalParity
import UgpLean.Universality.PhiMDLUniversality
import UgpLean.Polynomial.EisensteinIdentities

/-!
# Structural route to the direct-interpolation lift

Möbius-inversion (full-rank) proofs complementing the exhaustive-census
certificates of `TriangleLiftTheorem`:

* the eight binary evaluations determine the multilinear GF(7) coefficients
  uniquely (explicit inclusion–exclusion inversion — no enumeration);
* the parity-orbit ring evaluations plus vacuum transparency force the
  interpolant `p` in the multilinear function class;
* the MDL sparsity floor in its strongest form: ANY polynomial over GF(7)
  in canonical reduced form (per-variable degree ≤ 6 — a class containing a
  representative of every polynomial function on GF(7)³) whose binary
  restriction is Rule 110 flattens exactly to `p` and therefore has at least
  four monomials.

All theorems: zero sorry, zero custom axioms.
-/

set_option maxHeartbeats 800000

namespace UgpLean.Universality.TriangleLiftStructural

open UgpLean
open UgpLean.Universality
open UgpLean.Universality.PhiMDLUniversality
open UgpLean.Polynomial.EisensteinIdentities

-- ════════════════════════════════════════════════════════════════
-- §1  Multilinear function class indexed by variable-support triples
-- ════════════════════════════════════════════════════════════════

/-- Multilinear monomial value for support flags `(L?, C?, R?)`. -/
def mlMonomialVal (c : Bool × Bool × Bool) (L C R : ZMod 7) : ZMod 7 :=
  (cond c.1 L 1) * (cond c.2.1 C 1) * (cond c.2.2 R 1)

/-- Evaluation of a multilinear coefficient function. -/
def evalML (a : Bool × Bool × Bool → ZMod 7) (L C R : ZMod 7) : ZMod 7 :=
  ∑ c, a c * mlMonomialVal c L C R

/-- Coefficient function of `p(L,C,R) = C + R − C·R − L·C·R`. -/
def polyPFun : Bool × Bool × Bool → ZMod 7
  | (false, false, false) => 0
  | (true,  false, false) => 0
  | (false, true,  false) => 1
  | (false, false, true)  => 1
  | (true,  true,  false) => 0
  | (true,  false, true)  => 0
  | (false, true,  true)  => -1
  | (true,  true,  true)  => -1

/-- The interpolant's evaluation agrees with `poly_p` on all of GF(7)³. -/
theorem evalML_polyPFun_eq_poly_p :
    ∀ L C R : ZMod 7, evalML polyPFun L C R = poly_p L C R := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- §2  Möbius inversion: eight binary points determine the coefficients
-- ════════════════════════════════════════════════════════════════

/-- **Structural full-rank theorem**: the multilinear monomials are linearly
    independent on `{0,1}³` — a multilinear GF(7) rule whose eight binary
    evaluations match Rule 110 has the coefficients of `p`, by explicit
    inclusion–exclusion inversion of the binary Vandermonde system. -/
theorem multilinear_binary_determination
    (a : Bool × Bool × Bool → ZMod 7)
    (h : ∀ L C R : Bool,
      evalML a (bool_to_z7 L) (bool_to_z7 C) (bool_to_z7 R) =
        bool_to_z7 (rule110_output L C R)) :
    a = polyPFun := by
  have h000 := h false false false
  have h001 := h false false true
  have h010 := h false true false
  have h011 := h false true true
  have h100 := h true false false
  have h101 := h true false true
  have h110 := h true true false
  have h111 := h true true true
  simp only [evalML, mlMonomialVal, bool_to_z7, rule110_output,
    Fintype.sum_prod_type, Fintype.sum_bool, Bool.cond_true, Bool.cond_false,
    if_true, if_false, Bool.false_eq_true,
    mul_one, mul_zero, add_zero, zero_add]
    at h000 h001 h010 h011 h100 h101 h110 h111
  funext c
  obtain ⟨l, c2, r⟩ := c
  cases l <;> cases c2 <;> cases r
  · show a (false, false, false) = 0
    linear_combination h000
  · show a (false, false, true) = 1
    linear_combination h001 - h000
  · show a (false, true, false) = 1
    linear_combination h010 - h000
  · show a (false, true, true) = -1
    linear_combination h011 - h010 - h001 + h000
  · show a (true, false, false) = 0
    linear_combination h100 - h000
  · show a (true, false, true) = 0
    linear_combination h101 - h100 - h001 + h000
  · show a (true, true, false) = 0
    linear_combination h110 - h100 - h010 + h000
  · show a (true, true, true) = -1
    linear_combination h111 - h110 - h101 - h011 + h100 + h010 + h001 - h000

-- ════════════════════════════════════════════════════════════════
-- §3  Orbit + vacuum transparency force the interpolant (no enumeration)
-- ════════════════════════════════════════════════════════════════

/-- GF(7) image of a parity bit. -/
def z7OfParity (b : Fin 2) : ZMod 7 := (b.val : ZMod 7)

/-- A multilinear rule satisfies the ten parity-orbit ring evaluations
    (`smGen1 → smGen2`, `smGen2 → smGen3` on the 5-ring) together with
    vacuum transparency. -/
def SatisfiesOrbitVT (a : Bool × Bool × Bool → ZMod 7) : Prop :=
  (∀ i : Fin 5,
    evalML a (z7OfParity (smGen1 (i + 4))) (z7OfParity (smGen1 i))
      (z7OfParity (smGen1 (i + 1))) = z7OfParity (smGen2 i)) ∧
  (∀ i : Fin 5,
    evalML a (z7OfParity (smGen2 (i + 4))) (z7OfParity (smGen2 i))
      (z7OfParity (smGen2 (i + 1))) = z7OfParity (smGen3 i)) ∧
  evalML a 0 0 0 = 0

/-- The interpolant satisfies the orbit and vacuum-transparency constraints. -/
theorem polyPFun_satisfies_orbit_vt : SatisfiesOrbitVT polyPFun := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

/-- **Structural lift theorem**: the parity-orbit ring evaluations cover seven
    of the eight binary neighbourhoods; vacuum transparency supplies the eighth;
    Möbius inversion then forces the interpolant — uniqueness in the multilinear
    function class with no enumeration. -/
theorem orbit_vt_forces_interpolant (a : Bool × Bool × Bool → ZMod 7)
    (h : SatisfiesOrbitVT a) : a = polyPFun := by
  obtain ⟨h1, h2, hvt⟩ := h
  apply multilinear_binary_determination
  intro L C R
  cases L <;> cases C <;> cases R
  · exact hvt   -- (0,0,0): vacuum transparency
  · exact h1 3  -- (0,0,1): generation-1 ring position 3
  · exact h2 1  -- (0,1,0): generation-2 ring position 1
  · exact h1 4  -- (0,1,1): generation-1 ring position 4
  · exact h1 2  -- (1,0,0): generation-1 ring position 2
  · exact h2 0  -- (1,0,1): generation-2 ring position 0
  · exact h1 1  -- (1,1,0): generation-1 ring position 1
  · exact h1 0  -- (1,1,1): generation-1 ring position 0

/-- Existence and uniqueness bundle for the structural lift. -/
theorem orbit_interpolation_lift_structural :
    SatisfiesOrbitVT polyPFun ∧
    ∀ a : Bool × Bool × Bool → ZMod 7, SatisfiesOrbitVT a → a = polyPFun :=
  ⟨polyPFun_satisfies_orbit_vt, orbit_vt_forces_interpolant⟩

-- ════════════════════════════════════════════════════════════════
-- §4  Sparsity floor over the full canonical polynomial class
-- ════════════════════════════════════════════════════════════════

/-- Exponent triple `(e_L, e_C, e_R)` of canonical monomial `m` (base-7 digits;
    per-variable degree ≤ 6). -/
def gf7Exp (m : Fin 343) : ℕ × ℕ × ℕ :=
  (m.val / 49 % 7, m.val / 7 % 7, m.val % 7)

/-- Value of one canonical monomial. -/
def gf7MonomialVal (m : Fin 343) (L C R : ZMod 7) : ZMod 7 :=
  L ^ (gf7Exp m).1 * C ^ (gf7Exp m).2.1 * R ^ (gf7Exp m).2.2

/-- Evaluation of a canonical-form polynomial (per-variable degree ≤ 6 —
    every polynomial function on GF(7)³ has a representative in this class). -/
def evalGF7 (g : Fin 343 → ZMod 7) (L C R : ZMod 7) : ZMod 7 :=
  ∑ m, g m * gf7MonomialVal m L C R

/-- Support class of a monomial: which variables occur with positive exponent. -/
def gf7Class (m : Fin 343) : Bool × Bool × Bool :=
  (decide (0 < (gf7Exp m).1), decide (0 < (gf7Exp m).2.1),
   decide (0 < (gf7Exp m).2.2))

/-- Exponent flattening: coefficients summed by support class. -/
def flattenGF7 (g : Fin 343 → ZMod 7) (c : Bool × Bool × Bool) : ZMod 7 :=
  ∑ m ∈ Finset.univ.filter (fun m => gf7Class m = c), g m

/-- On binary inputs every canonical monomial equals its support-class
    multilinear monomial (`x^e = x` on `{0,1}` for `e ≥ 1`). -/
theorem gf7_monomial_binary_eq :
    ∀ m : Fin 343, ∀ L C R : Bool,
      gf7MonomialVal m (bool_to_z7 L) (bool_to_z7 C) (bool_to_z7 R) =
        mlMonomialVal (gf7Class m) (bool_to_z7 L) (bool_to_z7 C) (bool_to_z7 R) := by
  native_decide

/-- **Flattening homomorphism on binary inputs**: exponent flattening preserves
    every binary evaluation of every canonical-form polynomial. -/
theorem gf7_flattening_binary_agreement (g : Fin 343 → ZMod 7) (L C R : Bool) :
    evalGF7 g (bool_to_z7 L) (bool_to_z7 C) (bool_to_z7 R) =
      evalML (flattenGF7 g) (bool_to_z7 L) (bool_to_z7 C) (bool_to_z7 R) := by
  unfold evalGF7 evalML flattenGF7
  simp only [Finset.sum_filter, Finset.sum_mul]
  rw [Finset.sum_comm]
  refine Finset.sum_congr rfl fun m _ => ?_
  simp [ite_mul, zero_mul, Finset.sum_ite_eq, gf7_monomial_binary_eq m L C R]

/-- Each nonzero flattened support class contains a nonzero monomial: the
    class count bounds the monomial count from below. -/
theorem flattened_class_count_le_monomial_count (g : Fin 343 → ZMod 7) :
    (Finset.univ.filter fun c => flattenGF7 g c ≠ 0).card ≤
      (Finset.univ.filter fun m => g m ≠ 0).card := by
  have hsub : (Finset.univ.filter fun c => flattenGF7 g c ≠ 0) ⊆
      (Finset.univ.filter fun m => g m ≠ 0).image gf7Class := by
    intro c hc
    rw [Finset.mem_filter] at hc
    by_contra hnot
    apply hc.2
    refine Finset.sum_eq_zero fun m hm => ?_
    by_contra hgm
    exact hnot (Finset.mem_image.mpr
      ⟨m, Finset.mem_filter.mpr ⟨Finset.mem_univ m, hgm⟩,
        (Finset.mem_filter.mp hm).2⟩)
  exact le_trans (Finset.card_le_card hsub) Finset.card_image_le

/-- The interpolant has exactly four nonzero support classes. -/
theorem polyPFun_support_card :
    (Finset.univ.filter fun c => polyPFun c ≠ 0).card = 4 := by decide

/-- **MDL sparsity floor (strongest form)**: any canonical-form polynomial over
    GF(7) whose binary restriction is Rule 110 flattens exactly to the
    interpolant `p` and therefore has at least four monomials.  Multilinearity
    is MDL-forced: `p` itself realizes the floor with four monomials. -/
theorem gf7_rule110_sparsity_floor (g : Fin 343 → ZMod 7)
    (h : ∀ L C R : Bool,
      evalGF7 g (bool_to_z7 L) (bool_to_z7 C) (bool_to_z7 R) =
        bool_to_z7 (rule110_output L C R)) :
    flattenGF7 g = polyPFun ∧
      4 ≤ (Finset.univ.filter fun m => g m ≠ 0).card := by
  have hflat : flattenGF7 g = polyPFun := by
    apply multilinear_binary_determination
    intro L C R
    rw [← gf7_flattening_binary_agreement g L C R]
    exact h L C R
  refine ⟨hflat, ?_⟩
  have h4 : (Finset.univ.filter fun c => flattenGF7 g c ≠ 0).card = 4 := by
    rw [hflat]; exact polyPFun_support_card
  calc 4 = (Finset.univ.filter fun c => flattenGF7 g c ≠ 0).card := h4.symm
    _ ≤ (Finset.univ.filter fun m => g m ≠ 0).card :=
        flattened_class_count_le_monomial_count g

end UgpLean.Universality.TriangleLiftStructural
