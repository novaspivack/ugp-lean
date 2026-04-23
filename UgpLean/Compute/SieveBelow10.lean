import UgpLean.Compute.Sieve
import UgpLean.Compute.SieveExtended

/-!
# UgpLean.Compute.SieveBelow10 — Ridge Minimality: n=10 is the smallest admissible level

This module proves that for every ridge level n ∈ {5, 6, 7, 8, 9}, the prime-locked
mirror-dual sieve produces zero survivors. Combined with `ridgeSurvivors_10`
(which gives exactly 2 survivors at n=10), this establishes that **n=10 is the
smallest ridge level admitting a prime-locked mirror-dual survivor pair**.

Ridge levels n ≤ 4 are excluded because `ridge n = 2^n − 16` underflows to 0
for n ≤ 4, so no factorization-based sieve can operate.

**Main theorem:** `n10_is_minimal_admissible_ridge`

Reference: Paper 5 "The Uniqueness of the Universal Generative Principle" §3,
Theorem "Computational Uniqueness of the UGP" (previously verified computationally
for n ∈ [4, 30]; now machine-checked in Lean for the minimality claim n ∈ [5, 9]).

This addresses the reviewer concern about Ridge Minimality being "asserted rather
than demonstrated" — it is now Lean-certified.
-/

namespace UgpLean

-- Individual emptiness proofs for n = 5, 6, 7, 8, 9.
-- Each is a pure decidable computation: enumerate all divisor-antidiagonal pairs
-- of ridge(n), check prime-lock + mirror for each, confirm none pass.

/-- At n=5, the prime-locked mirror-dual sieve yields zero survivors. -/
theorem ridgeSurvivors_5_empty : ridgeSurvivorsFinset 5 = ∅ := by native_decide

/-- At n=6, the prime-locked mirror-dual sieve yields zero survivors. -/
theorem ridgeSurvivors_6_empty : ridgeSurvivorsFinset 6 = ∅ := by native_decide

/-- At n=7, the prime-locked mirror-dual sieve yields zero survivors. -/
theorem ridgeSurvivors_7_empty : ridgeSurvivorsFinset 7 = ∅ := by native_decide

/-- At n=8, the prime-locked mirror-dual sieve yields zero survivors. -/
theorem ridgeSurvivors_8_empty : ridgeSurvivorsFinset 8 = ∅ := by native_decide

/-- At n=9, the prime-locked mirror-dual sieve yields zero survivors. -/
theorem ridgeSurvivors_9_empty : ridgeSurvivorsFinset 9 = ∅ := by native_decide

/-- **Ridge Minimality Theorem.**
 For every ridge level n with 5 ≤ n < 10, the prime-locked mirror-dual
 sieve yields zero survivors. Combined with `ridgeSurvivors_10` (which
 gives exactly 2 survivors), this proves that n=10 is the smallest ridge
 level admitting a prime-locked mirror-dual survivor pair.

 Ridge levels n ≤ 4 have ridge(n) = 2^n − 16 ≤ 0, so the sieve is
 vacuously empty (no positive factorizations exist). -/
theorem n10_is_minimal_admissible_ridge (n : ℕ) (h5 : 5 ≤ n) (h10 : n < 10) :
    ridgeSurvivorsFinset n = ∅ := by
  interval_cases n <;> simp_all [ridgeSurvivors_5_empty, ridgeSurvivors_6_empty,
    ridgeSurvivors_7_empty, ridgeSurvivors_8_empty, ridgeSurvivors_9_empty]

/-- The combined statement: n=10 is the first ridge level with any survivors. -/
theorem ridge_minimality_and_existence :
    (∀ n, 5 ≤ n → n < 10 → ridgeSurvivorsFinset n = ∅) ∧
    ridgeSurvivorsFinset 10 = {(24, 42), (42, 24)} :=
  ⟨n10_is_minimal_admissible_ridge, ridgeSurvivors_10⟩

end UgpLean
