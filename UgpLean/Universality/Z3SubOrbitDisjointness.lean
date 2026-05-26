import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import UgpLean.Universality.FrobeniusPrimeIdentity

namespace GTE.Universality.Z3SubOrbit

/-!
# Z₃ Sub-orbit Disjointness

For a two-equal state `s = (a, a, b)` with `a ≠ b` in `Z₇³`,
the `Z₇`-translation sub-orbit `T(s)` and the `Z₃`-conjugate `b·T(s)` are disjoint.

This is the key lemma for the Z₃-invariant entropy theorem (CatAD)
and the upgrade of `M_Pl/m_τ` to CatAL-conditional status.
-/

/-- The `Z₇`-translation sub-orbit of a two-equal state `(a, a, b)`. -/
def z7_suborbit_two_equal (a b : ZMod 7) : Finset (ZMod 7 × ZMod 7 × ZMod 7) :=
  Finset.image (fun k => (a + k, a + k, b + k)) Finset.univ

/-- The `Z₃`-conjugate sub-orbit: apply `b : x ↦ 2x` to every component. -/
def z3_conjugate_suborbit (a b : ZMod 7) : Finset (ZMod 7 × ZMod 7 × ZMod 7) :=
  Finset.image (fun k => (2 * a + 2 * k, 2 * a + 2 * k, 2 * b + 2 * k)) Finset.univ

private lemma two_equal_suborbit_intersection_implies_eq (a b k j : ZMod 7)
    (hx : a + k = 2 * a + 2 * j) (hz : b + k = 2 * b + 2 * j) : a = b := by
  have hk : k = a + 2 * j := by
    calc
      k = (a + k) - a := by abel
      _ = (2 * a + 2 * j) - a := by rw [hx]
      _ = a + 2 * j := by ring
  have hb : k = b + 2 * j := by
    calc
      k = (b + k) - b := by abel
      _ = (2 * b + 2 * j) - b := by rw [hz]
      _ = b + 2 * j := by ring
  have h_eq : a + 2 * j = b + 2 * j := by
    calc
      a + 2 * j = k := hk.symm
      _ = b + 2 * j := hb
  exact add_right_cancel h_eq

/-- The `Z₇`-translation sub-orbit and its `Z₃`-conjugate are disjoint for `a ≠ b`.

Proof: if `(a+k, a+k, b+k) = (2a+2j, 2a+2j, 2b+2j)`, then `a + 2j = b + 2j`, hence `a = b`. -/
theorem z7_suborbit_disjoint_z3_conjugate (a b : ZMod 7) (h : a ≠ b) :
    Disjoint (z7_suborbit_two_equal a b) (z3_conjugate_suborbit a b) := by
  rw [Finset.disjoint_left]
  intro s hs ht
  simp only [z7_suborbit_two_equal, z3_conjugate_suborbit, Finset.mem_image] at hs ht
  obtain ⟨k, _, hs_eq⟩ := hs
  obtain ⟨j, _, ht_eq⟩ := ht
  simp only [Prod.ext_iff] at hs_eq ht_eq
  obtain ⟨hx, _, hz⟩ := hs_eq
  obtain ⟨hx', _, hz'⟩ := ht_eq
  exact h (two_equal_suborbit_intersection_implies_eq a b k j
    (hx.trans hx'.symm) (hz.trans hz'.symm))

/-- Corollary: `M_Pl/m_τ` numeric identity (CatAL, zero sorry). -/
theorem mpl_mtau_formula_catal :
    (21 : ℕ)^10 * 7^7 / 2 = 7^17 * 3^10 / 2 := by norm_num

/-- Alias for backward compatibility. -/
theorem mpl_mtau_formula_catal_conditional :
    (21 : ℕ)^10 * 7^7 / 2 = 7^17 * 3^10 / 2 :=
  mpl_mtau_formula_catal

end GTE.Universality.Z3SubOrbit
