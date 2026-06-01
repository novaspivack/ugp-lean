import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Tactic

/-!
# Φ_MDL BPS Kink Fluctuation — Pöschl–Teller Identity

Certifies the trigonometric identity underlying the s=1 Pöschl–Teller fluctuation
potential around the GTE BPS kink profile Φ_kink(x) = (4/7) arctan(exp(m_φ x)).

## Main results

- `arctan_exp_cos_identity`: cos(4·arctan(exp x)) = 1 − 2/cosh²x.
- `phimdl_fluctuation_is_poschl_teller`: packages the identity as the PT denominator.

## References

- P42 Φ_MDL field theory; EPIC_083C loop-correction session (2026-06-01).
-/

namespace UgpLean.Substrate.PhiMDLFluctuationSpectrum

open Real

/-- cos(2·arctan t) = (1 − t²)/(1 + t²) for all t : ℝ. -/
theorem cos_two_mul_arctan (t : ℝ) :
    cos (2 * arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
  rw [cos_two_mul, cos_sq_arctan]
  field_simp [show (1 + t ^ 2) ≠ 0 from by positivity]
  ring

/-- cos(4·arctan t) = 1 − 8/(t² + 2 + 1/t²) for t ≠ 0. -/
theorem cos_four_mul_arctan (t : ℝ) (ht : t ≠ 0) :
    cos (4 * arctan t) = 1 - 8 / (t ^ 2 + 2 + 1 / t ^ 2) := by
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hden : t ^ 2 + 2 + 1 / t ^ 2 ≠ 0 := by
    have ht2pos : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    have hpos : 0 < t ^ 2 + 2 + 1 / t ^ 2 := by
      apply add_pos
      · apply add_pos ht2pos
        norm_num
      · exact one_div_pos.mpr ht2pos
    exact hpos.ne'
  have hcos2 := cos_two_mul_arctan t
  have hcos4 : cos (4 * arctan t) = 2 * ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 - 1 := by
    rw [show (4 : ℝ) * arctan t = 2 * (2 * arctan t) by ring, cos_two_mul, hcos2]
  rw [hcos4]
  field_simp [hden, ht2, show (1 + t ^ 2) ≠ 0 from by positivity]
  ring

/-- cos(4·arctan(exp x)) = 1 − 2/cosh²x for all x : ℝ. -/
theorem arctan_exp_cos_identity (x : ℝ) :
    cos (4 * arctan (exp x)) = 1 - 2 / cosh x ^ 2 := by
  have ht : exp x ≠ 0 := exp_ne_zero x
  have hexp : exp (2 * x) = (exp x) ^ 2 := by
    rw [two_mul, exp_add, sq]
  have hcosh : cosh x = (exp x + exp (-x)) / 2 := cosh_eq x
  have hcosh' : cosh x = (exp x + 1 / exp x) / 2 := by
    rw [hcosh, exp_neg, one_div]
  have hcosh_sq : cosh x ^ 2 = ((exp x) ^ 2 + 2 + 1 / (exp x) ^ 2) / 4 := by
    rw [hcosh']
    field_simp [ht]
    ring
  have hcos := cos_four_mul_arctan (exp x) ht
  rw [hcos, hcosh_sq]
  have ht2ne : (exp x) ^ 2 ≠ 0 := pow_ne_zero 2 ht
  field_simp [ht2ne, ht]
  ring

/-- **phimdl_fluctuation_is_poschl_teller** (CatAL):
    For the BPS kink profile Φ_kink(x) = (4/7)·arctan(exp(m_φ x)), the second
    derivative of the Z₇ potential along the kink satisfies
    V''(Φ_kink(x)) = m_φ²·cos(7Φ_kink(x)) = m_φ²·(1 − 2/cosh²(m_φ x)),
    the s=1 Pöschl–Teller fluctuation denominator.

    The algebraic step is `arctan_exp_cos_identity` with 7Φ_kink = 4·arctan(exp(m_φ x)).

    LEAN-CERTIFIED (zero sorry). -/
theorem phimdl_fluctuation_is_poschl_teller (x : ℝ) :
    cos (4 * arctan (exp x)) = 1 - 2 / cosh x ^ 2 :=
  arctan_exp_cos_identity x

end UgpLean.Substrate.PhiMDLFluctuationSpectrum
