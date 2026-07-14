import Mathlib.NumberTheory.Cyclotomic.Gal
import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots

/-!
# UgpLean.Algebra.CyclotomicZ7GaloisGroup — The Actual Galois Group of Q(ζ₇)/Q

Upgrades the arithmetic certificates of `CyclotomicZ7Galois.lean` (which works
in `(ZMod 7)ˣ`) to statements about the **actual Galois group**
`Gal(Q(ζ₇)/Q) = (CyclotomicField 7 ℚ) ≃ₐ[ℚ] (CyclotomicField 7 ℚ)`,
via Mathlib's `IsCyclotomicExtension.autEquivPow` (Galois group of a cyclotomic
extension ≃* `(ZMod n)ˣ`, using irreducibility of the cyclotomic polynomial
over ℚ).

## Main results (zero sorry, zero custom axioms)

- `galois_z7_cyclic_order_6`: `Gal(Q(ζ₇)/Q)` has order 6 **and** is cyclic —
  the full `Gal(Q(ζ₇)/Q) ≅ Z₆` statement.
- `galois_z7_cpt_generator`: the automorphism corresponding to
  `σ₆ : ζ₇ ↦ ζ₇⁻¹ = ζ̄₇` (the unit `-1 ∈ (ZMod 7)ˣ`, i.e. complex
  conjugation = CPT under the Φ_MDL kink identification) has order exactly 2.
- `galois_z7_generation_subgroup_order_3`: the automorphism corresponding to
  the Frobenius σ₂ (generation symmetry) has order exactly 3, so
  `Z₆ = Z₂ × Z₃ = CPT × generation`.
-/

namespace UgpLean.Algebra.CyclotomicZ7GaloisGroup

open Polynomial IsCyclotomicExtension

noncomputable section

/-- The seventh cyclotomic field Q(ζ₇). -/
abbrev K7 : Type := CyclotomicField 7 ℚ

instance : NeZero ((7 : ℕ) : ℚ) := ⟨by norm_num⟩

instance : Fact (Nat.Prime 7) := ⟨by decide⟩

instance : IsCyclotomicExtension {7} ℚ K7 :=
  CyclotomicField.isCyclotomicExtension 7 ℚ

/-- The cyclotomic polynomial Φ₇ is irreducible over ℚ. -/
theorem cyclotomic_seven_irreducible : Irreducible (cyclotomic 7 ℚ) :=
  cyclotomic.irreducible_rat (by norm_num)

/-- The Galois group of Q(ζ₇)/Q, as ℚ-algebra automorphisms of the
    cyclotomic field. -/
abbrev GalZ7 := K7 ≃ₐ[ℚ] K7

/-- The canonical isomorphism `Gal(Q(ζ₇)/Q) ≃* (ZMod 7)ˣ`. -/
def galEquivUnits : GalZ7 ≃* (ZMod 7)ˣ :=
  autEquivPow K7 cyclotomic_seven_irreducible

instance : Fintype GalZ7 := Fintype.ofEquiv (ZMod 7)ˣ galEquivUnits.symm.toEquiv

/-- **galois_z7_cyclic_order_6** (CatAL): the Galois group of Q(ζ₇)/Q is
    cyclic of order 6 — `Gal(Q(ζ₇)/Q) ≅ Z₆`.

    Proved through the actual field-theoretic Galois group (not an arithmetic
    proxy): `Gal(Q(ζ₇)/Q) ≃* (ZMod 7)ˣ` by irreducibility of Φ₇ over ℚ, and
    `(ZMod 7)ˣ` is the cyclic group of order φ(7) = 6. -/
theorem galois_z7_cyclic_order_6 :
    Fintype.card GalZ7 = 6 ∧ IsCyclic GalZ7 := by
  constructor
  · rw [Fintype.card_congr galEquivUnits.toEquiv]
    decide
  · exact isCyclic_of_surjective galEquivUnits.symm.toMonoidHom
      galEquivUnits.symm.surjective

/-- The CPT automorphism: the element of Gal(Q(ζ₇)/Q) corresponding to the
    unit `-1 ∈ (ZMod 7)ˣ`, i.e. `σ₆ : ζ₇ ↦ ζ₇⁶ = ζ₇⁻¹ = ζ̄₇` (complex
    conjugation; kink ↔ anti-kink under the Φ_MDL identification). -/
def cptAut : GalZ7 := galEquivUnits.symm (-1)

/-- **galois_z7_cpt_generator** (CatAL): the CPT automorphism
    `σ₆ : ζ₇ ↦ ζ₇⁻¹` has order exactly 2 in Gal(Q(ζ₇)/Q) — it generates the
    unique Z₂ factor in `Gal(Q(ζ₇)/Q) ≅ Z₆ = Z₂ × Z₃`. -/
theorem galois_z7_cpt_generator : orderOf cptAut = 2 := by
  rw [cptAut, galEquivUnits.symm.orderOf_eq]
  exact orderOf_eq_prime (by decide) (by decide)

/-- The generation-symmetry automorphism: the element of Gal(Q(ζ₇)/Q)
    corresponding to the Frobenius unit `2 ∈ (ZMod 7)ˣ`
    (`σ₂ : ζ₇ ↦ ζ₇²`, whose orbits {1,2,4} and {3,5,6} are the two GTE
    flavor families — see `CyclotomicZ7Galois.z7_galois_orbit_partition`). -/
def generationAut : GalZ7 :=
  galEquivUnits.symm (ZMod.unitOfCoprime 2 (by decide))

/-- **galois_z7_generation_subgroup_order_3** (CatAL): the Frobenius
    generation-symmetry automorphism σ₂ has order exactly 3 in Gal(Q(ζ₇)/Q) —
    it generates the Z₃ factor in `Gal(Q(ζ₇)/Q) ≅ Z₂ × Z₃ = CPT × generation`. -/
theorem galois_z7_generation_subgroup_order_3 : orderOf generationAut = 3 := by
  rw [generationAut, galEquivUnits.symm.orderOf_eq]
  exact orderOf_eq_prime (by decide) (by decide)

end

end UgpLean.Algebra.CyclotomicZ7GaloisGroup
