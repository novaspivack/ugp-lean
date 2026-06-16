import Mathlib.Data.ZMod.Basic

/-!
# GTE polynomial Lipschitz constant over GF(7) (EPIC_092 / 092-B8)

The discrete update polynomial p(L,C,R) = C + R − CR − LCR over GF(7) has
single-input symmetric Lipschitz constant 3 under exhaustive enumeration.
-/

namespace UgpLean.GTE.PolynomialLipschitz

/-- The GTE cubic over GF(7): p(L,C,R) = C + R − CR − LCR. -/
def p_GTE (L C R : ZMod 7) : ZMod 7 := C + R - C * R - L * C * R

/-- Wrapped distance on GF(7): min(d, 7 − d) for d = |a − b| in {0,…,6}. -/
def wdist (a b : ZMod 7) : ℕ :=
  let d := (a - b).val
  min d (7 - d)

theorem gte_polynomial_lipschitz_le_3 :
    (∀ L C R : ZMod 7, wdist (p_GTE (L + 1) C R) (p_GTE L C R) ≤ 3) ∧
    (∀ L C R : ZMod 7, wdist (p_GTE L (C + 1) R) (p_GTE L C R) ≤ 3) ∧
    (∀ L C R : ZMod 7, wdist (p_GTE L C (R + 1)) (p_GTE L C R) ≤ 3) := by
  refine ⟨?_, ?_, ?_⟩ <;> intro L C R <;> fin_cases L <;> fin_cases C <;> fin_cases R <;>
    decide

theorem gte_lipschitz_tight :
    ∃ L C R : ZMod 7, wdist (p_GTE (L + 1) C R) (p_GTE L C R) = 3 := by
  exact ⟨0, 1, 3, by decide⟩

theorem gte_lipschitz_constant_eq_3 :
    ((∀ L C R : ZMod 7, wdist (p_GTE (L + 1) C R) (p_GTE L C R) ≤ 3) ∧
      (∀ L C R : ZMod 7, wdist (p_GTE L (C + 1) R) (p_GTE L C R) ≤ 3) ∧
      ∀ L C R : ZMod 7, wdist (p_GTE L C (R + 1)) (p_GTE L C R) ≤ 3) ∧
    ∃ L C R : ZMod 7, wdist (p_GTE (L + 1) C R) (p_GTE L C R) = 3 :=
  And.intro gte_polynomial_lipschitz_le_3 ⟨0, 1, 3, by decide⟩

end UgpLean.GTE.PolynomialLipschitz
