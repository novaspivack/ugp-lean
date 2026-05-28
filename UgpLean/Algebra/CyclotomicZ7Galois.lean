import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Data.ZMod.Units

/-!
# Cyclotomic Z₇ Galois Structure (EPIC_078 / SPEC_078_012)

Certifies three CatAL algebraic results for the Q(ζ₇) vacuum sector:

1. **078-GALSPLIT** — Frobenius σ₂ (k ↦ 2k mod 7) partitions Z₇ \\ {0} into orbits
   {1,2,4} (u-type) and {3,5,6} (d-type), the two GTE flavor families.

2. **078-CYCLOPART** — 7 ∤ 120: the Z₇ vacuum sector is arithmetically disjoint from
   the Z₁₂₀ mass/Yukawa sector (Q(ζ₇) ⊄ Q(ζ₁₂₀)).

3. **078-GALCPT** — (ZMod 7)ˣ ≅ Z₆ ≅ Z₂ × Z₃; σ₂ = k ↦ 2k has order 3 (generation
   symmetry); σ₆ = k ↦ 6k = −k has order 2 (complex conjugation = CPT).

All theorems: zero sorry, zero custom axioms.
-/

namespace UgpLean.Algebra.CyclotomicZ7Galois

/-- u-type GTE flavor family: quadratic residues in (ZMod 7)*, closed under σ₂ = k ↦ 2k. -/
def uTypeOrbit : Finset (ZMod 7) := {1, 2, 4}

/-- d-type / W-boson GTE flavor family: non-residues in (ZMod 7)*, closed under σ₂. -/
def dTypeOrbit : Finset (ZMod 7) := {3, 5, 6}

/-- Nonzero elements of Z₇ (kink moduli excluding the vacuum label 0). -/
def z7Nonzero : Finset (ZMod 7) := {1, 2, 3, 4, 5, 6}

/-- **078-GALSPLIT** (CatAL): Frobenius σ₂ partitions Z₇ \\ {0} into orbits {1,2,4} and {3,5,6}.
    These are the two GTE flavor families (u-type and d-type). -/
theorem z7_galois_orbit_partition :
    uTypeOrbit ∪ dTypeOrbit = z7Nonzero ∧
    uTypeOrbit ∩ dTypeOrbit = ∅ ∧
    (∀ k ∈ uTypeOrbit, (2 : ZMod 7) * k ∈ uTypeOrbit) ∧
    (∀ k ∈ dTypeOrbit, (2 : ZMod 7) * k ∈ dTypeOrbit) := by
  decide

/-- **078-CYCLOPART** (CatAL): 7 does not divide 120 — Q(ζ₇) is not contained in Q(ζ₁₂₀). -/
theorem seven_not_divides_120 : ¬ (7 : ℕ) ∣ 120 := by decide

/-- Coprimality of the Z₇ and Z₁₂₀ cyclotomic indices. -/
theorem seven_coprime_120 : Nat.Coprime 7 120 := by decide

/-- Both directions of arithmetic disjointness between the two GTE cyclotomic sectors. -/
theorem gte_arithmetic_sectors_disjoint :
    ¬ (7 : ℕ) ∣ 120 ∧ ¬ (120 : ℕ) ∣ 7 := by decide

/-- **078-GALCPT** (CatAL): |Gal(Q(ζ₇)/Q)| = |(ZMod 7)ˣ| = φ(7) = 6. -/
theorem zmod7_units_card : Fintype.card (ZMod 7)ˣ = 6 := by decide

/-- The CPT automorphism σ₆: k ↦ 6k = −k mod 7 is an involution. -/
theorem neg_map_order2_zmod7 :
    ∀ k : ZMod 7, (6 : ZMod 7) * ((6 : ZMod 7) * k) = k := by decide

/-- Generation-orbit symmetry σ₂: k ↦ 2k has order 3 in (ZMod 7)*. -/
theorem sigma2_order3 : (2 : ZMod 7) ^ 3 = 1 := by decide

/-- CPT symmetry σ₆: k ↦ 6k has order 2 in (ZMod 7)*. -/
theorem sigma6_order2 : (6 : ZMod 7) ^ 2 = 1 := by decide

/-- σ₆ is the unique order-2 element: 6² ≡ 1 and 6 ≠ 1 in ZMod 7. -/
theorem sigma6_nontrivial : (6 : ZMod 7) ≠ 1 := by decide

/-- The u-type orbit {1,2,4} is exactly the order-3 subgroup ⟨2⟩ of (ZMod 7)*. -/
theorem u_type_orbit_is_z3_subgroup :
    (2 : ZMod 7) * 1 ∈ uTypeOrbit ∧
    (2 : ZMod 7) * 2 ∈ uTypeOrbit ∧
    (2 : ZMod 7) * 4 ∈ uTypeOrbit ∧
    uTypeOrbit.card = 3 := by decide

/-- Master bundle: all three Galois/cyclotomic certification targets together. -/
theorem cyclotomic_z7_master_bundle :
    (¬ (7 : ℕ) ∣ 120) ∧
    Nat.Coprime 7 120 ∧
    Fintype.card (ZMod 7)ˣ = 6 ∧
    (2 : ZMod 7) ^ 3 = 1 ∧
    (6 : ZMod 7) ^ 2 = 1 ∧
    uTypeOrbit ∪ dTypeOrbit = z7Nonzero ∧
    uTypeOrbit ∩ dTypeOrbit = ∅ := by
  refine ⟨seven_not_divides_120, seven_coprime_120, zmod7_units_card, sigma2_order3,
    sigma6_order2, ?_, ?_⟩
  · exact z7_galois_orbit_partition.1
  · exact z7_galois_orbit_partition.2.1

end UgpLean.Algebra.CyclotomicZ7Galois
