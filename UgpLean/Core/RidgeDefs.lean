import Mathlib.NumberTheory.Divisors

/-!
# UgpLean.Core.RidgeDefs — Ridge Definition

The UGP is defined over integer ridges R_n = 2^n - 16.
At level n=10, R_10 = 1008.

Reference: UGP Main Paper, main_n10_ridge.py
-/

namespace UgpLean

/-- The ridge value at level n: R_n = 2^n - 16 -/
def ridge (n : ℕ) : ℕ := 2^n - 16

/-- At n=10, R_10 = 1008 -/
theorem ridge_10 : ridge 10 = 1008 := by native_decide

/-- Strict-ridge divisor threshold: b₂ > 15 -/
def strictRidgeMin : ℕ := 16

/-- UGP-1 parameters: s = 7, g = 13, t = 20 -/
def ugp1_s : ℕ := 7
def ugp1_g : ℕ := 13
def ugp1_t : ℕ := 20

theorem ugp1_params : ugp1_s = 7 ∧ ugp1_g = 13 ∧ ugp1_t = 20 := by native_decide

/-- Divisors of R_n that qualify for strict-ridge (b₂ > 15) -/
def strictRidgeDivisors (n : ℕ) : Finset ℕ :=
  (Nat.divisors (ridge n)).filter (fun b₂ => b₂ ≥ strictRidgeMin)

end UgpLean
