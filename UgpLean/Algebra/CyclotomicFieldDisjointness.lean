import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import Mathlib.LinearAlgebra.Dimension.Free

/-!
# Cyclotomic field disjointness: Q(ζ₇) and Q(ζ₁₂₀)

Proves the field-theoretic content of the GTE sector-disjointness claim: the Z₇
vacuum sector's cyclotomic field Q(ζ₇) is arithmetically independent of the Z₁₂₀
mass/Yukawa sector's cyclotomic field Q(ζ₁₂₀).

## Main result

- `cyclotomic_z7_not_embeddable_in_z120`: there is no ℚ-algebra embedding
  `CyclotomicField 7 ℚ →ₐ[ℚ] CyclotomicField 120 ℚ`. Equivalently, Q(ζ₇) is not
  contained in Q(ζ₁₂₀).

Proof: `[Q(ζ₇):Q] = φ(7) = 6` and `[Q(ζ₁₂₀):Q] = φ(120) = 32`; any embedding would
force 6 ∣ 32, which is false.
-/

namespace UgpLean.Algebra.CyclotomicFieldDisjointness

open Polynomial IsCyclotomicExtension

noncomputable section

/-- The seventh cyclotomic field Q(ζ₇). -/
abbrev K7 : Type := CyclotomicField 7 ℚ

/-- The 120th cyclotomic field Q(ζ₁₂₀). -/
abbrev K120 : Type := CyclotomicField 120 ℚ

instance : NeZero ((7 : ℕ) : ℚ) := ⟨by norm_num⟩

instance : NeZero ((120 : ℕ) : ℚ) := ⟨by norm_num⟩

instance : IsCyclotomicExtension {7} ℚ K7 :=
  CyclotomicField.isCyclotomicExtension 7 ℚ

instance : IsCyclotomicExtension {120} ℚ K120 :=
  CyclotomicField.isCyclotomicExtension 120 ℚ

/-- The cyclotomic polynomial Φ₇ is irreducible over ℚ. -/
theorem cyclotomic_seven_irreducible : Irreducible (cyclotomic 7 ℚ) :=
  cyclotomic.irreducible_rat (by norm_num)

/-- The cyclotomic polynomial Φ₁₂₀ is irreducible over ℚ. -/
theorem cyclotomic_onetwenty_irreducible : Irreducible (cyclotomic 120 ℚ) :=
  cyclotomic.irreducible_rat (by norm_num)

/-- `[Q(ζ₇):Q] = φ(7) = 6`. -/
theorem finrank_cyclotomic_seven_eq_six : Module.finrank ℚ K7 = 6 := by
  rw [IsCyclotomicExtension.finrank K7 cyclotomic_seven_irreducible]
  decide

/-- `[Q(ζ₁₂₀):Q] = φ(120) = 32`. -/
theorem finrank_cyclotomic_onetwenty_eq_thirtytwo : Module.finrank ℚ K120 = 32 := by
  rw [IsCyclotomicExtension.finrank K120 cyclotomic_onetwenty_irreducible]
  decide

/-- 6 does not divide 32 — the obstruction to embedding Q(ζ₇) in Q(ζ₁₂₀). -/
theorem finrank_seven_not_dvd_finrank_onetwenty :
    ¬ Module.finrank ℚ K7 ∣ Module.finrank ℚ K120 := by
  rw [finrank_cyclotomic_seven_eq_six, finrank_cyclotomic_onetwenty_eq_thirtytwo]
  decide

/-- A ℚ-algebra embedding K ↪ L forces `[K:Q] ∣ [L:Q]`. -/
theorem finrank_dvd_of_algHom {K L : Type*} [Field K] [Field L] [Algebra ℚ K] [Algebra ℚ L]
    [FiniteDimensional ℚ K] [FiniteDimensional ℚ L] (f : K →ₐ[ℚ] L) :
    Module.finrank ℚ K ∣ Module.finrank ℚ L := by
  algebraize [f.toRingHom]
  rw [← Module.finrank_mul_finrank ℚ K L]
  exact dvd_mul_right _ _

/-- **cyclotomic_z7_not_embeddable_in_z120** (CatAL): Q(ζ₇) does not embed in Q(ζ₁₂₀) as
    a ℚ-algebra — the Z₇ vacuum sector's cyclotomic field is arithmetically independent of
    the Z₁₂₀ mass/Yukawa sector's. -/
theorem cyclotomic_z7_not_embeddable_in_z120 : ¬ Nonempty (K7 →ₐ[ℚ] K120) := by
  rintro ⟨f⟩
  exact finrank_seven_not_dvd_finrank_onetwenty (finrank_dvd_of_algHom f)

end

end UgpLean.Algebra.CyclotomicFieldDisjointness
