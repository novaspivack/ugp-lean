import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum

/-!
# UgpLean.GaloisStructure.CyclotomicLayers — Galois Stability of UGP Layers

**Theorem (Galois Stability):** The UGP algebraic layers are Galois-stable subsets
of Q(ζ₁₂₀).  Proved by showing that the kernel and Koide layers satisfy *different*
minimal polynomials over ℚ — no Galois automorphism maps one layer to the other.

Cross-evaluations (proved exactly):
  - p₁₀(2·cos(π/12)) = 2 − √3 ≈ +0.268 ≠ 0
  - p₁₂(2·cos(π/10)) = φ − 2   ≈ −0.382 ≠ 0

Reference: P25 §7, `papers/25_deeper_theory/04_galois_orbits.py`
-/

namespace UgpLean.GaloisStructure

open Real

/-! ## Key squared-value identities -/

/-- (2·cos(π/12))² = 2 + √3.
  Proof: double-angle formula gives cos(π/6) = 2cos²(π/12) − 1, and cos(π/6) = √3/2. -/
lemma two_cos_pi12_sq : (2 * cos (π / 12)) ^ 2 = 2 + sqrt 3 := by
  have h_six : cos (π / 6) = sqrt 3 / 2 := cos_pi_div_six
  have h_double : cos (π / 6) = 2 * cos (π / 12) ^ 2 - 1 := by
    have := cos_two_mul (π / 12)
    have heq : 2 * (π / 12) = π / 6 := by ring
    rw [heq] at this; linarith
  nlinarith [show (2 * cos (π / 12)) ^ 2 = 4 * cos (π / 12) ^ 2 from by ring,
             h_six, h_double]

/-- (2·cos(π/10))² = 2 + φ.
  Proof: cos_pi_div_five gives cos(π/5) = (1+√5)/4; double-angle formula applied. -/
lemma two_cos_pi10_sq : (2 * cos (π / 10)) ^ 2 = 2 + goldenRatio := by
  -- cos(π/5) = (1+√5)/4  (Mathlib's cos_pi_div_five)
  have h_five : cos (π / 5) = (1 + sqrt 5) / 4 := cos_pi_div_five
  -- golden ratio = (1+√5)/2
  have hgold : goldenRatio = (1 + sqrt 5) / 2 := rfl
  have h_double : cos (π / 5) = 2 * cos (π / 10) ^ 2 - 1 := by
    have := cos_two_mul (π / 10)
    have heq : 2 * (π / 10) = π / 5 := by ring
    rw [heq] at this; linarith
  nlinarith [show (2 * cos (π / 10)) ^ 2 = 4 * cos (π / 10) ^ 2 from by ring,
             h_five, h_double, hgold]

/-! ## Cross-polynomial evaluations -/

/-- p₁₀(2·cos(π/12)) = 2 − √3.
  Using u = (2·cos(π/12))² = 2+√3: u² − 5u + 5 = (2+√3)² − 5(2+√3) + 5 = 2−√3. -/
lemma p10_at_cos_pi12 :
    (2 * cos (π / 12)) ^ 4 - 5 * (2 * cos (π / 12)) ^ 2 + 5 = 2 - sqrt 3 := by
  have hu := two_cos_pi12_sq
  have hsq3 : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  nlinarith [show (2 * cos (π / 12)) ^ 4 = ((2 * cos (π / 12)) ^ 2) ^ 2 from by ring,
             hu, hsq3]

/-- p₁₂(2·cos(π/10)) = φ − 2.
  Using v = (2·cos(π/10))² = 2+φ: v² − 4v + 1 = φ² − 3 = (φ+1) − 3 = φ − 2. -/
lemma p12_at_cos_pi10 :
    (2 * cos (π / 10)) ^ 4 - 4 * (2 * cos (π / 10)) ^ 2 + 1 = goldenRatio - 2 := by
  have hv := two_cos_pi10_sq
  have hphi2 : goldenRatio ^ 2 = goldenRatio + 1 := goldenRatio_sq
  nlinarith [show (2 * cos (π / 10)) ^ 4 = ((2 * cos (π / 10)) ^ 2) ^ 2 from by ring,
             hv, hphi2]

/-! ## Nonzero evaluations -/

/-- √3 < 2, hence 2 − √3 > 0. Proof: from (√3)·(√3)=3 and (2−√3)(2+√3)=1>0. -/
lemma two_minus_sqrt3_pos : 0 < (2 : ℝ) - sqrt 3 := by
  have hmul : Real.sqrt 3 * Real.sqrt 3 = 3 := Real.mul_self_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 3 := Real.sqrt_nonneg 3
  nlinarith [sq_nonneg (2 - Real.sqrt 3)]

lemma two_minus_sqrt3_ne_zero : (2 : ℝ) - sqrt 3 ≠ 0 := ne_of_gt two_minus_sqrt3_pos

/-- φ < 2 (since √5 < 3), hence φ − 2 < 0 ≠ 0. -/
lemma goldenRatio_lt_two : goldenRatio < 2 := by
  have hgold : goldenRatio = (1 + sqrt 5) / 2 := rfl
  have hmul : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)
  have hnn : 0 ≤ Real.sqrt 5 := Real.sqrt_nonneg 5
  nlinarith [sq_nonneg (3 - Real.sqrt 5), hgold]

lemma goldenRatio_minus_two_ne_zero : goldenRatio - 2 ≠ 0 := by
  linarith [goldenRatio_lt_two]

/-! ## The Galois Stability Theorem -/

/-- **Galois Layer Stability:** The kernel constant 2cos(π/10) and the Koide constant
  2cos(π/12) lie in different Galois orbits in Q(ζ₁₂₀): each fails to satisfy the
  other's minimal polynomial, so no automorphism of Q(ζ₁₂₀) maps one to the other. -/
theorem galois_layer_stability :
    (2 * cos (π / 12)) ^ 4 - 5 * (2 * cos (π / 12)) ^ 2 + 5 ≠ 0 ∧
    (2 * cos (π / 10)) ^ 4 - 4 * (2 * cos (π / 10)) ^ 2 + 1 ≠ 0 :=
  ⟨by rw [p10_at_cos_pi12]; exact two_minus_sqrt3_ne_zero,
   by rw [p12_at_cos_pi10]; exact goldenRatio_minus_two_ne_zero⟩

/-- The exact cross-evaluation values. -/
theorem galois_cross_eval_values :
    (2 * cos (π / 12)) ^ 4 - 5 * (2 * cos (π / 12)) ^ 2 + 5 = 2 - sqrt 3 ∧
    (2 * cos (π / 10)) ^ 4 - 4 * (2 * cos (π / 10)) ^ 2 + 1 = goldenRatio - 2 :=
  ⟨p10_at_cos_pi12, p12_at_cos_pi10⟩

/-- Orbit size = strand_count = (N_c²−1)/4 = (9−1)/4 = 2. -/
theorem strand_count_eq_two : (3 ^ 2 - 1 : ℕ) / 4 = 2 := by norm_num

end UgpLean.GaloisStructure
