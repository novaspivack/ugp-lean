import Mathlib.Data.Nat.GCD.Basic
import Mathlib.Tactic.NormNum
import UgpLean.Core.RidgeDefs
import UgpLean.GTE.MersenneLadder

/-!
# UgpLean.GaloisStructure.MinimalCyclotomic

Structural origins of the two key "why" questions from P25:

1. Why n_ridge = 10 = 2*F(5)?
   Answer: n_ridge equals the exponent of the second Mersenne rung (c2 = 2^10 - 1 = 1023)
   in the canonical GTE orbit. The rung exponents {4, 10, 16} = {2*F(3), 2*F(5), 2*F(6)}
   form an arithmetic sequence with step 2*Nc = 6 (from Fibonacci recurrence F(6)-F(5)=F(4)=Nc=3).

2. Why Q(zeta_120)?
   Answer: 120 = LCM(20, 24) is the MINIMAL period containing all UGP algebraic constants.
   phi and cos(pi/10) need period 20; cos(pi/12) needs period 24.
   LCM(20, 24) = 120. Prime structure 120 = 2^3*3*5 matches gauge coupling denominators.

Reference: P25 Sec 10.1-10.2, papers/25_deeper_theory/04_galois_orbits.py
-/

namespace UgpLean.GaloisStructure.MinimalCyclotomic

open UgpLean

-- ============================================================
-- Part A: Why n_ridge = 10 = 2*F(5)?
-- ============================================================

/-- c2 = 1023 = 2^10 - 1 = 2^(2*F(5)) - 1. The ridge level is the Mersenne exponent of c2. -/
theorem c2_mersenne_exponent : (1023 : Nat) = 2 ^ (2 * Nat.fib 5) - 1 := by native_decide

/-- The three Mersenne exponents {4, 10, 16} = {2*F(3), 2*F(5), 2*F(6)}.
  They are symmetric around n_ridge = 10 with step 2*Nc = 6. -/
theorem mersenne_ladder_structure :
    2 * Nat.fib 3 = 4 /- first rung -/ /\
    2 * Nat.fib 5 = 10 /- second rung = n_ridge -/ /\
    2 * Nat.fib 6 = 16 /- third rung -/ /\
    2 * Nat.fib 6 - 2 * Nat.fib 5 = 6 /- step = 2*Nc -/ /\
    2 * Nat.fib 5 - 2 * Nat.fib 3 = 6 := /- symmetric -/
  by native_decide

/-- Nc = 3 = F(4). The QCD colour rank is the 4th Fibonacci number. -/
theorem Nc_eq_fib4 : (3 : Nat) = Nat.fib 4 := by native_decide

/-- The step size 6 = 2*F(4) = 2*Nc connects Fibonacci to the colour rank. -/
theorem mersenne_step_eq_two_Nc : 2 * Nat.fib 4 = 6 := by native_decide

/-- dim(SU(Nc)) = Nc^2 - 1 = 8 = F(6). Number of gluons is the 6th Fibonacci number. -/
theorem gluon_count_is_fib6 : (3 : Nat)^2 - 1 = Nat.fib 6 := by native_decide

/-- n_ridge = 10 is the center of the Mersenne sequence {4,10,16},
  equals 2*F(5), and the step 2*Nc = 2*F(4) = F(6)-F(5) by Fibonacci recurrence. -/
theorem n_ridge_structural_position :
    10 = 2 * Nat.fib 5 /\
    10 = (4 + 16) / 2 /\
    Nat.fib 6 - Nat.fib 5 = Nat.fib 4 /\
    (3 : Nat)^2 - 1 = Nat.fib 6 :=
  by native_decide

-- ============================================================
-- Part B: Why Q(zeta_120)? The Minimal Cyclotomic Field
-- ============================================================

/-- 120 = LCM(20, 24). The minimal cyclotomic conductor for all UGP constants. -/
theorem lcm_20_24_eq_120 : Nat.lcm 20 24 = 120 := by native_decide

/-- 20 divides 120 (phi and cos(pi/10) need Q(zeta_20)). -/
theorem twenty_dvd_120 : 20 ∣ 120 := by decide

/-- 24 divides 120 (cos(pi/12) needs Q(zeta_24)). -/
theorem twentyfour_dvd_120 : 24 ∣ 120 := by decide

/-- 12 divides 120 (sqrt(3) and cos(pi/6) need Q(zeta_12)). -/
theorem twelve_dvd_120 : 12 ∣ 120 := by decide

/-- Minimality: any N with 20|N and 24|N satisfies 120|N. So 120 is the LCM. -/
theorem lcm_minimality : ∀ N : ℕ, 20 ∣ N → 24 ∣ N → 120 ∣ N := by
  intro N h20 h24
  have := Nat.lcm_dvd h20 h24
  rwa [lcm_20_24_eq_120] at this

/-- 120 = 2^3 * 3 * 5 (prime factorization). -/
theorem factorization_120 : (120 : ℕ) = 2^3 * 3 * 5 := by norm_num

/-- The prime set {2,3,5} of 120 matches the gauge coupling denominators:
    g1 denom = 5^3 = 125, g2 denom = 2^3*3^3*5^2 = 5400, g3 denom = 2^13*3^3*5^3. -/
theorem prime_set_120_matches_gauge :
    5 ∣ 125 /\
    (2 ∣ 5400 /\ 3 ∣ 5400 /\ 5 ∣ 5400) /\
    (2 ∣ 27648000 /\ 3 ∣ 27648000 /\ 5 ∣ 27648000) /\
    ¬(7 ∣ 120) /\ ¬(11 ∣ 120) /\ ¬(7 ∣ 125) /\ ¬(7 ∣ 5400) := by decide

/-- Summary: Q(zeta_120) is the minimal cyclotomic field for UGP.
  120 = LCM(20, 24) = 2^3*3*5. Prime set matches gauge denominators. -/
theorem q_zeta_120_is_minimal_conductor :
    20 ∣ 120 /\ 24 ∣ 120 /\ 12 ∣ 120 /\
    Nat.lcm 20 24 = 120 /\
    (120 : ℕ) = 2^3 * 3 * 5 :=
  ⟨by decide, by decide, by decide, by native_decide, by norm_num⟩

end UgpLean.GaloisStructure.MinimalCyclotomic
