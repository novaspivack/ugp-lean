import Mathlib.NumberTheory.Cyclotomic.Basic
import Mathlib.NumberTheory.Cyclotomic.PrimitiveRoots
import Mathlib.FieldTheory.SplittingField.IsSplittingField
import Mathlib.RingTheory.Polynomial.Cyclotomic.Roots
import UgpLean.CyclotomicCompleteness.CoxeterBiconditional

/-!
# CyclotomicContainment

## SPEC_042_CYX — Cyclotomic Completeness: Field-Theoretic Embedding

We prove the field-theoretic content of the Coxeter-Conductor theorem:
if h | 60, then Q(ζ_{2h}) embeds in Q(ζ₁₂₀), formalized as:

**Theorem A** (`cyclotomic120_contains_primitive_root`): `CyclotomicField 120 ℚ` contains a
primitive 2h-th root of unity whenever h | 60. Zero sorry.

**Theorem B** (`cyclotomic_field_embedding`): There is a ℚ-algebra embedding
`CyclotomicField (2h) ℚ →ₐ[ℚ] CyclotomicField 120 ℚ` whenever h | 60. Zero sorry.

### Proof of Theorem A

`CyclotomicField 120 ℚ` is defined as `SplittingField (cyclotomic 120 ℚ)`, so the cyclotomic
polynomial has a root ζ₀ inside it. The lemma `isRoot_cyclotomic_iff_charZero` (from
`Mathlib.RingTheory.Polynomial.Cyclotomic.Roots`) converts root-of-cyclotomic to `IsPrimitiveRoot`.
Then `IsPrimitiveRoot.pow` powers ζ₀ to produce a primitive 2h-th root.

### Proof of Theorem B

We use:
- `IsCyclotomicExtension.union_of_isPrimitiveRoot`: the primitive 2h-th root ζ gives a
  `{120 ∪ {2h}}`-cyclotomic extension structure on `CyclotomicField 120 ℚ`
- `IsCyclotomicExtension.splits_cyclotomic`: `cyclotomic (2h) ℚ` splits in this extension
- `Polynomial.IsSplittingField.lift`: the universal property gives the embedding

Note: `IsCyclotomicExtension {120} ℚ (CyclotomicField 120 ℚ)` is obtained by explicitly
invoking `CyclotomicField.isCyclotomicExtension` (the `[NeZero (n : K)]` instance at line 705
of Basic.lean), providing `NeZero (120 : ℚ)` explicitly to avoid instance search loops
from the `[CharZero K]` instance that recurses for concrete numerals.
-/

namespace UgpLean.CyclotomicCompleteness

open IsCyclotomicExtension Polynomial Set

/-! ### Auxiliary: explicit NeZero (120 : ℚ) -/

-- The IsCyclotomicExtension {120} instance needs NeZero (120 : ℚ).
-- We provide it explicitly to avoid the definitional loop in the [CharZero K] instance
-- (which recurses: IsCyclotomicExtension {120} → {119+1} = {120} → loop).
private lemma ne_zero_120_rat : NeZero (120 : ℚ) := ⟨by norm_num⟩

/-! ### Theorem A: Primitive root existence -/

/-- If `h ∣ 60`, then `CyclotomicField 120 ℚ` contains a primitive 2h-th root of unity.
    Zero sorry. Uses only `SplittingField` and `IsPrimitiveRoot` machinery. -/
theorem cyclotomic120_contains_primitive_root (h : ℕ) (hdvd : h ∣ 60) :
    ∃ ζ : CyclotomicField 120 ℚ, IsPrimitiveRoot ζ (2 * h) := by
  have h2h_dvd : 2 * h ∣ 120 := (two_h_dvd_120_iff_h_dvd_60 h).mpr hdvd
  -- CyclotomicField 120 ℚ is the splitting field of cyclotomic 120 ℚ.
  -- Its IsSplittingField instance gives Splits ((cyclotomic 120 ℚ).map ...).
  -- We use Splits.exists_eval_eq_zero to extract a root ζ₀.
  -- Use SplittingField.splits directly to avoid IsSplittingField instance synthesis issues.
  -- CyclotomicField 120 ℚ = SplittingField (cyclotomic 120 ℚ) by definition.
  -- SplittingField.splits gives Splits over (cyclotomic 120 ℚ).SplittingField (= CyclotomicField 120 ℚ).
  have hdeg : 0 < (cyclotomic 120 ℚ).degree := degree_cyclotomic_pos 120 ℚ (by norm_num)
  obtain ⟨ζ₀, hζ₀⟩ := Polynomial.Splits.exists_eval_eq_zero
    (Polynomial.SplittingField.splits (cyclotomic 120 ℚ))
    (by rw [degree_map]; exact hdeg.ne')
  -- simp [map_cyclotomic]: rewrites the mapped polynomial to cyclotomic in the SplittingField type
  simp only [Polynomial.map_cyclotomic] at hζ₀
  -- Convert eval = 0 to IsRoot, then IsRoot to IsPrimitiveRoot (CharZero version)
  rw [← IsRoot.def, isRoot_cyclotomic_iff_charZero (by norm_num : 0 < 120)] at hζ₀
  -- hζ₀ : IsPrimitiveRoot ζ₀ 120. CyclotomicField 120 ℚ = SplittingField definitionally.
  -- Now power to get primitive 2h-th root.
  exact ⟨ζ₀ ^ (120 / (2 * h)), hζ₀.pow (by norm_num) (Nat.div_mul_cancel h2h_dvd).symm⟩

/-! ### Theorem B: Field embedding via splitting field universal property -/

/-- If `h ∣ 60`, there is a ℚ-algebra embedding `CyclotomicField (2h) ℚ →ₐ[ℚ] CyclotomicField 120 ℚ`.
    This formalizes "Q(ζ_{2h}) ⊆ Q(ζ₁₂₀)" as a field-theoretic embedding. Zero sorry. -/
theorem cyclotomic_field_embedding (h : ℕ) (hpos : 0 < h) (hdvd : h ∣ 60) :
    Nonempty (CyclotomicField (2 * h) ℚ →ₐ[ℚ] CyclotomicField 120 ℚ) := by
  have h2h_dvd : 2 * h ∣ 120 := (two_h_dvd_120_iff_h_dvd_60 h).mpr hdvd
  have h2h_ne : 2 * h ≠ 0 := by omega
  -- NeZero (2*h : ℕ) for module-level NeZero constraints
  haveI hNe2h : NeZero (2 * h) := ⟨h2h_ne⟩
  -- NeZero (2*h : ℚ) for CyclotomicField (2*h) ℚ instances
  haveI hNe2hRat : NeZero ((2 * h : ℕ) : ℚ) := ⟨by exact_mod_cast h2h_ne⟩
  -- NeZero (120 : ℚ) for IsCyclotomicExtension {120} — needed for union_of_isPrimitiveRoot
  haveI hNe120Q : NeZero (120 : ℚ) := ne_zero_120_rat
  -- IsCyclotomicExtension {120} ℚ (CyclotomicField 120 ℚ): invoke the [NeZero (n : K)] instance
  -- explicitly by name to bypass the [CharZero K] recursive instance at line 733 of Basic.lean.
  haveI h120 : IsCyclotomicExtension ({120} : Set ℕ) ℚ (CyclotomicField 120 ℚ) :=
    CyclotomicField.isCyclotomicExtension (n := 120) (K := ℚ)
  -- Get a primitive 2h-th root inside CyclotomicField 120 ℚ
  obtain ⟨ζ, hζ⟩ := cyclotomic120_contains_primitive_root h hdvd
  -- union_of_isPrimitiveRoot (S A B explicit; n implicit) at line 208 of Basic.lean:
  -- S is explicit because variable {S} comes at line 221 (after this theorem at 208).
  haveI h_union : IsCyclotomicExtension ({120} ∪ {2 * h}) ℚ (CyclotomicField 120 ℚ) :=
    IsCyclotomicExtension.union_of_isPrimitiveRoot ({120} : Set ℕ) ℚ (CyclotomicField 120 ℚ) hζ
  -- splits_cyclotomic (K L explicit; n, S implicit) at line 520 of Basic.lean (Field section).
  have hSplits : Splits ((cyclotomic (2 * h) ℚ).map (algebraMap ℚ (CyclotomicField 120 ℚ))) :=
    IsCyclotomicExtension.splits_cyclotomic ℚ (CyclotomicField 120 ℚ)
      (mem_union_right {120} (mem_singleton_iff.mpr rfl))
  -- IsSplittingField instance for CyclotomicField (2h) ℚ = SplittingField (cyclotomic (2h) ℚ)
  haveI hSF : IsSplittingField ℚ (CyclotomicField (2 * h) ℚ) (cyclotomic (2 * h) ℚ) := by
    delta CyclotomicField; exact Polynomial.IsSplittingField.splittingField _
  -- IsSplittingField.lift (L : Type) (f : K[X]) (hf : Splits ...) : L →ₐ[K] F
  exact ⟨Polynomial.IsSplittingField.lift (CyclotomicField (2 * h) ℚ) (cyclotomic (2 * h) ℚ)
    hSplits⟩

/-- Corollary: the embedding is injective (AlgHom between fields is always injective). -/
theorem cyclotomic_field_embedding_injective (h : ℕ) (hpos : 0 < h) (hdvd : h ∣ 60) :
    ∃ f : CyclotomicField (2 * h) ℚ →ₐ[ℚ] CyclotomicField 120 ℚ, Function.Injective f := by
  obtain ⟨f⟩ := cyclotomic_field_embedding h hpos hdvd
  exact ⟨f, f.injective⟩

/-!
### Per-algebra embedding certificates

Specializations to the simple Lie algebras in the Coxeter-Conductor theorem.
-/

/-- G₂ (h=6): CyclotomicField 12 ℚ embeds in CyclotomicField 120 ℚ. -/
theorem g2_cyclotomic_embedding :
    Nonempty (CyclotomicField 12 ℚ →ₐ[ℚ] CyclotomicField 120 ℚ) :=
  cyclotomic_field_embedding 6 (by norm_num) (by norm_num)

/-- F₄/E₆ (h=12): CyclotomicField 24 ℚ embeds in CyclotomicField 120 ℚ. -/
theorem f4_e6_cyclotomic_embedding :
    Nonempty (CyclotomicField 24 ℚ →ₐ[ℚ] CyclotomicField 120 ℚ) :=
  cyclotomic_field_embedding 12 (by norm_num) (by norm_num)

/-- E₈ (h=30): CyclotomicField 60 ℚ embeds in CyclotomicField 120 ℚ. -/
theorem e8_cyclotomic_embedding :
    Nonempty (CyclotomicField 60 ℚ →ₐ[ℚ] CyclotomicField 120 ℚ) :=
  cyclotomic_field_embedding 30 (by norm_num) (by norm_num)

end UgpLean.CyclotomicCompleteness
