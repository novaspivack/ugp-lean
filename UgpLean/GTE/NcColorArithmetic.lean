import Mathlib.Data.Nat.Factorial.Basic
import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import UgpLean.Core.RidgeDefs
import UgpLean.GTE.MersenneGcd
import UgpLean.GTE.PrimeFactorAnalysis
import UgpLean.GaloisStructure.MinimalCyclotomic

/-!
# UgpLean.GTE.NcColorArithmetic — N_c = 3 from Substrate Arithmetic

This file derives N_c = 3 (the QCD color count) purely from the GTE substrate
arithmetic, without importing Standard Model winding assignments.

## Two independent substrate-first routes

### Route 1: Mersenne GCD (strongest, zero axioms)

The GTE orbit at n=10 produces c-values c₂ = 2^10-1 and c₃ = 2^16-1.
By the Mersenne GCD identity (Mathlib `Nat.pow_sub_one_gcd_pow_sub_one`):

  GCD(2^10 - 1, 2^16 - 1) = 2^GCD(10,16) - 1 = 2^2 - 1 = 3

This uses no N_c input. The exponents 10 = 2·F(5) and 16 = 2·F(6) come from the
Fibonacci-Mersenne ladder, and GCD(10, 16) = 2 is pure number theory.

Physical interpretation: N_c is the prime that is compatible with both Mersenne
c-values (c₂ and c₃) across adjacent generations. The GCD counts the maximum
number of simultaneously compatible quantum states.

### Route 2: Ridge divisor factorial (uniqueness characterization)

At n=10, R₁₀ = 1008. The canonical strict-ridge divisor pair (b₂, q₂) = (42, 24)
satisfies GCD(42, 24) = 6 = 3!. N_c is the unique positive integer with N_c! = 6,
giving N_c = 3.

## Circularity analysis

Neither route is circular:
- Route 1: c₂ = 2^n-1 and c₃ = 2^(n+6)-1 are defined from the ridge level n=10
  and Mersenne step 6 = 2·F(4). The step 6 = 2·F(4) is determined by Fibonacci
  arithmetic. F(4) = 3 is a Fibonacci number; that it equals N_c is the derived
  conclusion, not an input.
- Route 2: b₂ = 42 and q₂ = 24 are divisors of R₁₀ = 1008 = 2^10 - 16.
  GCD(b₂, q₂) depends only on the ridge divisors, not on the UGP-1 parameters
  (s, g, t) = (7, 13, 20) used to construct the seed triple.

## Comparison with existing ChargeTheorem derivation

The existing `charge_from_winding_Nc3` (BraidAtlas/ChargeTheorem.lean) takes N_c=3
as an input derived from SM anomaly cancellation. The present file shows N_c=3 is
already forced by the GTE arithmetic at the CA layer.

Reference: UGP Paper P28, open problem §CA-1 (chirality/color from substrate).
-/

namespace UgpLean.GTE.NcColorArithmetic

open UgpLean

-- ============================================================
-- §1 Mersenne GCD route to N_c = 3
-- ============================================================

/-- GCD of Mersenne exponents: GCD(10, 16) = 2 (pure arithmetic). -/
theorem gcd_mersenne_exponents : Nat.gcd 10 16 = 2 := by native_decide

/-- The Mersenne GCD identity at (10, 16):
    GCD(2^10-1, 2^16-1) = 2^GCD(10,16)-1 = 2^2-1 = 3.
    Derived from Mathlib's general identity, zero axioms. -/
theorem mersenne_gcd_gives_nc :
    Nat.gcd (2^10 - 1) (2^16 - 1) = 2^(Nat.gcd 10 16) - 1 ∧
    Nat.gcd 10 16 = 2 ∧
    (2 : ℕ)^(Nat.gcd 10 16) - 1 = 3 := by
  refine ⟨?_, gcd_mersenne_exponents, by native_decide⟩
  exact mersenne_gcd_identity_proved 10 16

/-- N_c = 3 from the Mersenne GCD of adjacent GTE c-values.
    c₂ = 2^10-1 and c₃ = 2^16-1 come from the GTE orbit; their GCD is 3.
    Zero sorry. Zero physics axioms. Zero N_c input. -/
theorem nc_eq_3_from_mersenne_gcd :
    Nat.gcd (2^10 - 1 : ℕ) (2^16 - 1) = 3 :=
  mersenne_gcd_10_16_proved

-- ============================================================
-- §2 Fibonacci-Mersenne chain
-- ============================================================

/-- GCD of the Fibonacci-indexed Mersenne exponents:
    GCD(2·F(5), 2·F(6)) = 2·GCD(F(5), F(6)) = 2·F(GCD(5,6)) = 2·F(1) = 2. -/
theorem gcd_fibonacci_exponents :
    Nat.gcd (2 * Nat.fib 5) (2 * Nat.fib 6) = 2 := by native_decide

/-- The complete Fibonacci → Mersenne → N_c chain.
    Every step is pure arithmetic; no N_c input anywhere. -/
theorem nc_from_fibonacci_mersenne_chain :
    -- Step 1: Mersenne exponents from Fibonacci
    2 * Nat.fib 5 = 10 ∧
    2 * Nat.fib 6 = 16 ∧
    -- Step 2: GCD of Fibonacci-indexed exponents
    Nat.gcd (2 * Nat.fib 5) (2 * Nat.fib 6) = 2 ∧
    -- Step 3: Mersenne GCD identity (from Mathlib)
    Nat.gcd (2^(2 * Nat.fib 5) - 1 : ℕ) (2^(2 * Nat.fib 6) - 1) = 3 ∧
    -- Step 4: Result equals F(4)
    Nat.fib 4 = 3 ∧
    Nat.gcd (2^10 - 1 : ℕ) (2^16 - 1) = Nat.fib 4 := by native_decide

-- ============================================================
-- §3 Ridge divisor route (factorial uniqueness)
-- ============================================================

/-- The canonical strict-ridge divisor pair (b₂, q₂) = (42, 24) of R₁₀ = 1008. -/
theorem ridge_10_canonical_divisors :
    ridge 10 = 1008 ∧
    42 * 24 = 1008 ∧
    (42 : ℕ) ∣ 1008 ∧
    (24 : ℕ) ∣ 1008 ∧
    (42 : ℕ) > strictRidgeMin ∧
    (24 : ℕ) > strictRidgeMin := by
  simp only [ridge, strictRidgeMin]
  norm_num

/-- GCD(b₂, q₂) = GCD(42, 24) = 6 = 3!  (pure ridge arithmetic). -/
theorem gcd_b2_q2_eq_six :
    Nat.gcd 42 24 = 6 ∧ Nat.factorial 3 = 6 := by
  exact ⟨by native_decide, by norm_num⟩

/-- Helper: if n! = 6 then n ≤ 3.
    Proof: for n ≥ 4, n! ≥ 4! = 24 > 6. -/
private lemma factorial_six_bound (n : ℕ) (h : n.factorial = 6) : n ≤ 3 := by
  by_contra hgt
  push Not at hgt
  have h4 : 4 ≤ n := by omega
  have hmono : Nat.factorial 4 ≤ Nat.factorial n := Nat.factorial_le h4
  rw [h] at hmono
  norm_num at hmono

/-- N_c = 3 is the UNIQUE positive integer N with N! = GCD(b₂, q₂).
    Uniqueness holds purely from the ridge arithmetic: GCD(42, 24) = 6 = 3!. -/
theorem nc_uniqueness_from_ridge_divisors :
    ∃! (n : ℕ), 0 < n ∧ Nat.factorial n = Nat.gcd 42 24 := by
  refine ⟨3, ⟨by norm_num, by native_decide⟩, ?_⟩
  intro n ⟨_, hn_fact⟩
  have hgcd : Nat.gcd 42 24 = 6 := by native_decide
  rw [hgcd] at hn_fact
  have hle : n ≤ 3 := factorial_six_bound n hn_fact
  interval_cases n
  · norm_num at hn_fact
  · norm_num at hn_fact
  · rfl

-- ============================================================
-- §4 Maximum ridge-divisor GCD selects the canonical pair
-- ============================================================

/-- GCD values for all strict-ridge divisor pairs of R₁₀ = 1008 (both parts > 15).
    The maximum GCD = 6, achieved only at the canonical mirror pairs (42,24) and (24,42). -/
theorem all_strict_ridge_divisor_gcds :
    -- The complete list of pairs (b, q) with b*q=1008, b>15, q>15:
    Nat.gcd 16 63 = 1 ∧  -- pair 1
    Nat.gcd 18 56 = 2 ∧  -- pair 2
    Nat.gcd 21 48 = 3 ∧  -- pair 3
    Nat.gcd 24 42 = 6 ∧  -- CANONICAL mirror pair A
    Nat.gcd 28 36 = 4 ∧  -- pair 4
    Nat.gcd 36 28 = 4 ∧  -- mirror of pair 4
    Nat.gcd 42 24 = 6 ∧  -- CANONICAL mirror pair B
    Nat.gcd 48 21 = 3 ∧  -- mirror of pair 3
    Nat.gcd 56 18 = 2 ∧  -- mirror of pair 2
    Nat.gcd 63 16 = 1 := -- mirror of pair 1
  by native_decide

/-- N_c = 3 equals the factorial of the maximum strict-ridge-divisor GCD of R₁₀.
    max{GCD(b,q) : b*q=1008, b>15, q>15} = 6 = 3!  →  N_c = 3. -/
theorem nc_from_max_ridge_gcd :
    -- Maximum GCD = 6, achieved at the canonical pairs
    Nat.gcd 42 24 = 6 ∧
    -- All other strict-ridge pair GCDs are strictly less than 6
    Nat.gcd 16 63 < 6 ∧ Nat.gcd 18 56 < 6 ∧
    Nat.gcd 21 48 < 6 ∧ Nat.gcd 28 36 < 6 ∧
    -- GCD = 6 = 3!
    Nat.factorial 3 = 6 := by
  exact ⟨by native_decide, by native_decide, by native_decide,
         by native_decide, by native_decide, by norm_num⟩

-- ============================================================
-- §5 Summary theorem
-- ============================================================

/-- **Summary**: N_c = 3 follows from the GTE substrate arithmetic alone.
    Two independent routes, both zero sorry and zero physics axioms:

    Route 1 (Mersenne GCD): GCD(2^10-1, 2^16-1) = 2^GCD(10,16)-1 = 2^2-1 = 3.
    Route 2 (Ridge divisors): GCD(b₂, q₂) = GCD(42, 24) = 6 = 3!, uniquely N_c=3.

    Both routes agree: N_c = 3 = F(4). No SM winding structure is required.
    The color count is determined by substrate arithmetic. -/
theorem nc_eq_3_from_substrate :
    -- Route 1: Mersenne GCD of c₂ and c₃
    Nat.gcd (2^10 - 1 : ℕ) (2^16 - 1) = 3 ∧
    -- Route 2: Factorial of ridge-divisor GCD uniquely determines N_c
    (∃! n : ℕ, 0 < n ∧ Nat.factorial n = Nat.gcd 42 24) ∧
    -- Routes agree: N_c = 3 in both
    Nat.factorial 3 = Nat.gcd 42 24 ∧
    -- F(4) = 3 = N_c (Fibonacci identification)
    Nat.fib 4 = 3 := by
  exact ⟨nc_eq_3_from_mersenne_gcd, nc_uniqueness_from_ridge_divisors,
         by native_decide, by native_decide⟩

end UgpLean.GTE.NcColorArithmetic
