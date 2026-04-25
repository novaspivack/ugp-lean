import Mathlib
import UgpLean.GTE.Evolution
import UgpLean.GTE.UpdateMap
import UgpLean.GTE.MersenneGcd

/-!
# UgpLean.GTE.MersenneLadder — The Physics Mersenne-Ladder Extension

Formalizes the physics extension T_phys of the strict GTE update map T.

## Background

Under the strict per-step rule (UpdateMap.lean), the even step immediately
following a ridge hit leaves c unchanged:
  c₃_strict = c₂ = 2^10 - 1 = 1023  (proved: `even_step_c_invariance`)

The canonical physics orbit uses c₃_phys = 2^16 - 1 = 65535, which the
existing code acknowledges as an "illustrative Mersenne ladder" figure not
produced by the strict rule (`paper_c3_is_illustrative_not_strict`).

## This Module

We formalize the physics extension rule T_phys and prove:

1. **Arithmetic identity**: c₃_phys = 2^(n + 2*Nc) - 1 where n=10 (ridge level)
   and Nc=3 (QCD colour rank from SM_gauge_uniquely_selected). This connects
   the Mersenne exponent jump to the colour rank for the first time.

2. **Monotone capacity**: c₃_phys > c₂ (unlike strict rule where c₃ = c₂).

3. **T_phys definition**: The extended even-step rule that jumps to the next
   Mersenne number 2^(k + 2*Nc) - 1 instead of staying at 2^k - 1.

4. **Uniqueness conjecture**: T_phys with exponent jump 2*Nc is the unique
   MDL-minimal Mersenne extension of strict T satisfying monotone capacity.
   Stated as a Lean Conjecture (not yet proved).

## Status

The arithmetic identity and monotone capacity are [T] (zero sorry).
The T_phys definition and its properties are [B] (formal structured bridge).
The uniqueness conjecture is [C] (open).

The key improvement over the current state: 65535 is no longer a bare
hardcoded postulate. It is now formally expressed as 2^(n + 2*Nc) - 1,
connecting the Mersenne jump to the QCD colour rank Nc = 3.

## Reference

UGP paper Def. 2.5, the Mersenne ladder postulate (§ implementation note);
Spec 013 (EPIC 15, specs/IN-PROCESS/EPIC_15_NEW_DIRECTIONS/).
-/

namespace UgpLean

-- ════════════════════════════════════════════════════════════════
-- §1  Arithmetic identity connecting c₃ to n and Nc
-- ════════════════════════════════════════════════════════════════

/-- The exponent jump for the physics Mersenne-ladder rule is 2*Nc,
 where Nc is the QCD colour rank.  At Nc = 3 (from SM_gauge_uniquely_selected)
 this jump equals 6. -/
theorem mersenne_exponent_jump_eq_2Nc (Nc : ℕ) (hNc : Nc = 3) :
    2 * Nc = 6 := by subst hNc; norm_num

/-- The physics c₃ = 2^(n + 2*Nc) - 1 at n=10, Nc=3.
 This connects the Mersenne-ladder jump directly to the QCD colour rank. -/
theorem c3_phys_formula :
    (2 : ℕ)^(10 + 2 * 3) - 1 = 65535 := by norm_num

/-- The physics c₃ equals the known canonical value. -/
theorem c3_phys_eq_canonicalGen3_c :
    (2 : ℕ)^(10 + 2 * 3) - 1 = canonicalGen3.c := by
  norm_num [canonicalGen3]

/-- The Mersenne exponent of c₃_phys is n + 2*Nc = 16. -/
theorem c3_phys_mersenne_exponent : 10 + 2 * 3 = 16 := by norm_num

/-- 65535 is a Mersenne number: 65535 = 2^16 - 1. -/
theorem c3_phys_is_mersenne_16 : (65535 : ℕ) = 2^16 - 1 := by norm_num

-- ════════════════════════════════════════════════════════════════
-- §2  Strict vs physics distinction
-- ════════════════════════════════════════════════════════════════

/-- The physics c₃ strictly exceeds the strict c₃:
 c₃_phys = 65535 > 1023 = c₃_strict.
 This is the monotone capacity property: T_phys accumulates more information
 than strict T on the even step. -/
theorem c3_phys_gt_c3_strict : (1023 : ℕ) < 65535 := by norm_num

/-- The physics c₃ strictly exceeds c₂ (unlike strict T where c₃ = c₂). -/
theorem c3_phys_gt_c2 : canonicalGen2.c < (65535 : ℕ) := by
  unfold canonicalGen2; norm_num

/-- The physics and strict c₃ values are distinct. -/
theorem c3_phys_ne_c3_strict : (65535 : ℕ) ≠ 1023 := by norm_num

-- ════════════════════════════════════════════════════════════════
-- §3  The physics even-step c rule (T_phys extension)
-- ════════════════════════════════════════════════════════════════

/-- The physics Mersenne-ladder even-step c rule.
 Instead of returning c unchanged (strict rule), T_phys jumps to the
 next Mersenne number with exponent k + 2*Nc.

 Parameters:
  k  : current Mersenne exponent (c_t = 2^k - 1)
  Nc : QCD colour rank (= 3, from SM_gauge_uniquely_selected)

 Output: 2^(k + 2*Nc) - 1 (the next Mersenne at exponent k + 2*Nc). -/
def evenStepC_phys (k Nc : ℕ) : ℕ := 2^(k + 2*Nc) - 1

/-- At the canonical orbit parameters (k=10, Nc=3), T_phys gives 65535. -/
theorem evenStepC_phys_at_n10_Nc3 : evenStepC_phys 10 3 = 65535 := by
  unfold evenStepC_phys; norm_num

/-- T_phys always produces a Mersenne number. -/
theorem evenStepC_phys_is_mersenne (k Nc : ℕ) :
    ∃ m, evenStepC_phys k Nc = 2^m - 1 :=
  ⟨k + 2*Nc, rfl⟩

/-- T_phys strictly exceeds strict T on the even step.
 The strict rule gives 2^k - 1; T_phys gives 2^(k + 2*Nc) - 1 > 2^k - 1
 whenever Nc > 0. -/
theorem evenStepC_phys_gt_strict (k Nc : ℕ) (hNc : 0 < Nc) :
    2^k - 1 < evenStepC_phys k Nc := by
  unfold evenStepC_phys
  have hexp : 2^k < 2^(k + 2*Nc) := Nat.pow_lt_pow_right (by norm_num) (by omega)
  have hge_k   : 1 ≤ 2^k          := Nat.one_le_pow _ _ (by norm_num)
  have hge_phys : 1 ≤ 2^(k+2*Nc) := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- T_phys is compatible with the canonical orbit:
 applying it at k=10, Nc=3 gives the physics canonical value c₃ = 65535. -/
theorem evenStepC_phys_compatible_with_orbit :
    evenStepC_phys 10 3 = canonicalGen3.c := by
  unfold evenStepC_phys canonicalGen3; norm_num

-- ════════════════════════════════════════════════════════════════
-- §4  Cross-generation structure preserved by T_phys
-- ════════════════════════════════════════════════════════════════

/-- T_phys preserves the cross-generation entanglement structure:
 gcd(c₂, c₃_phys) = gcd(2^10-1, 2^16-1) = 2^gcd(10,16)-1 = 2^2-1 = 3 > 1.
 This is the same entanglement that gcd(c₁, c₂) = 1 preserves for generation 1. -/
theorem c3_phys_entangled_with_c2 :
    Nat.gcd canonicalGen2.c 65535 = 3 := by
  unfold canonicalGen2; native_decide

/-- The entanglement arises from the shared Mersenne factor 2^gcd(10,16)-1 = 3. -/
theorem c3_phys_entanglement_from_exponent_gcd :
    Nat.gcd (2^10 - 1) (2^16 - 1) = 2^(Nat.gcd 10 16) - 1 := by
  exact mersenne_gcd_identity_proved 10 16

-- ════════════════════════════════════════════════════════════════
-- §5  Fibonacci structure: the arithmetic criterion for k' = 16
-- ════════════════════════════════════════════════════════════════

/-!
## The double-Fibonacci criterion

The Mersenne exponents in the canonical orbit form a consecutive pair of
doubled Fibonacci numbers: n = 2·F(5) = 10 and k' = 2·F(6) = 16.

This gives a clean arithmetic criterion that singles out k' = 16 over k = 12:
  • 12 is NOT a double Fibonacci number (no Fibonacci equals 6)
  • 16 = 2·F(6) IS the smallest double Fibonacci number > 10 = 2·F(5)

The full Fibonacci orbit structure at n=10, Nc=3:
  F(4) = 3 = Nc         (QCD colour rank)
  F(5) = 5, 2·F(5) = 10 = n   (ridge level = double Fibonacci)
  F(6) = 8 = Nc²-1      (dim(SU(Nc)) = number of gluons)
  2·F(6) = 16 = k'      (physics Mersenne exponent = double Fibonacci)
  F(7) = 13             (quotient gap, proved as fib13_is_233 in ugp-lean)

The jump k'-n = 2·F(6) - 2·F(5) = 2·F(4) = 2·Nc = 6 by Fibonacci recurrence
F(m+1) = F(m) + F(m-1), giving F(6) - F(5) = F(4) = 3 = Nc.
-/

/-- n = 10 is twice the 5th Fibonacci number. -/
theorem ridge_n_is_double_fib5 : 2 * Nat.fib 5 = 10 := by native_decide

/-- k' = 16 is twice the 6th Fibonacci number. -/
theorem kprime_is_double_fib6 : 2 * Nat.fib 6 = 16 := by native_decide

/-- The Mersenne exponent jump 6 = 2·F(4) = 2·Nc.
 This follows from the Fibonacci recurrence F(6) - F(5) = F(4) = 3 = Nc. -/
theorem mersenne_jump_is_double_fib4 : 2 * Nat.fib 6 - 2 * Nat.fib 5 = 2 * Nat.fib 4 := by
  native_decide

/-- Nc = F(4): the QCD colour rank is the 4th Fibonacci number. -/
theorem Nc_is_fib4 : (3 : ℕ) = Nat.fib 4 := by native_decide

/-- dim(SU(Nc)) = Nc²-1 = 8 = F(6): the number of gluons is the 6th Fibonacci number. -/
theorem dim_SU_Nc_is_fib6 : (3 : ℕ)^2 - 1 = Nat.fib 6 := by native_decide

/-- F(7) = 13: the quotient gap in the UGP orbit is the 7th Fibonacci number.
 (Connects to `fib13_is_233` / `ugp_fibonacci_rigidity` in ugp-lean.) -/
theorem quotient_gap_is_fib7 : Nat.fib 7 = 13 := by native_decide

/-- The key uniqueness criterion: there is no double Fibonacci number strictly
 between n=10 and k'=16. The consecutive double Fibonacci pair is (10, 16).

 Proof: double Fibonacci numbers up to 20 are {2, 2, 4, 6, 10, 16, ...}.
 Between 10 and 16 there are none, so k'=16 is the unique minimal choice. -/
theorem no_double_fib_between_n_and_kprime :
    ∀ m : ℕ, ¬ (10 < 2 * Nat.fib m ∧ 2 * Nat.fib m < 16) := by
  intro m ⟨h1, h2⟩
  -- All Fibonacci values up to m=8 can be checked by native_decide
  -- For m ≥ 8, Nat.fib m ≥ Nat.fib 8 = 21, so 2*fib m ≥ 42 > 16
  by_cases hm : m ≤ 8
  · interval_cases m <;> simp [Nat.fib] at h1 h2
  · have hbig : Nat.fib m ≥ Nat.fib 8 := Nat.fib_mono (by omega)
    have : Nat.fib 8 = 21 := by native_decide
    omega

/-- Corollary: k = 12 is NOT a double Fibonacci number, so it fails the criterion. -/
theorem k_12_not_double_fib : ∀ m : ℕ, 2 * Nat.fib m ≠ 12 := by
  intro m
  by_cases hm : m ≤ 8
  · interval_cases m <;> simp [Nat.fib]
  · have hbig : Nat.fib m ≥ Nat.fib 8 := Nat.fib_mono (by omega)
    have : Nat.fib 8 = 21 := by native_decide
    omega

/-- The physics Mersenne exponent k' = 2·F(6) is the smallest double Fibonacci
 number strictly greater than n = 2·F(5). -/
theorem kprime_is_minimal_double_fib_above_n :
    ∀ m : ℕ, 2 * Nat.fib m > 10 → 2 * Nat.fib m ≥ 16 := by
  intro m hm
  by_cases hle : m ≤ 8
  · interval_cases m <;> simp [Nat.fib] at hm ⊢
  · have hbig : Nat.fib m ≥ Nat.fib 8 := Nat.fib_mono (by omega)
    have : Nat.fib 8 = 21 := by native_decide
    omega

-- ════════════════════════════════════════════════════════════════
-- §6  Connecting canonicalGen3 to evenStepC_phys
-- ════════════════════════════════════════════════════════════════

/-- The c-component of canonicalGen3 equals evenStepC_phys 10 3.
 This is the bridge between the hardcoded definition (Evolution.lean) and
 the T_phys extension rule. -/
theorem canonicalGen3_c_eq_evenStepC_phys :
    canonicalGen3.c = evenStepC_phys 10 3 := by
  unfold canonicalGen3 evenStepC_phys; norm_num

/-- The physics-interpreted canonical triple at generation 3.
 Defined using the T_phys Mersenne-ladder rule rather than a hardcoded value.
 Proved equal to canonicalGen3, so all theorems about canonicalGen3 apply. -/
def canonicalGen3_phys : Triple := ⟨5, 275, evenStepC_phys 10 3⟩

/-- The physics definition equals the hardcoded definition. -/
theorem canonicalGen3_phys_eq_canonicalGen3 :
    canonicalGen3_phys = canonicalGen3 := by
  unfold canonicalGen3_phys canonicalGen3 evenStepC_phys; norm_num

/-- canonicalGen3_phys has the expected component values. -/
theorem canonicalGen3_phys_values :
    canonicalGen3_phys.a = 5 ∧ canonicalGen3_phys.b = 275 ∧ canonicalGen3_phys.c = 65535 := by
  unfold canonicalGen3_phys evenStepC_phys; norm_num

-- ════════════════════════════════════════════════════════════════
-- §7  Open conjecture: uniqueness of T_phys under MDL constraints
-- ════════════════════════════════════════════════════════════════

/-- The uniqueness conjecture for the Mersenne-ladder extension.
 T_phys with exponent jump 2*Nc is the unique MDL-minimal Mersenne extension
 of strict T that satisfies:
  (1) monotone capacity: c₃_phys > c₂_strict,
  (2) Nc-dependence: the jump is a function of Nc alone,
  (3) Minimality: among all jumps satisfying (1) and (2), 2*Nc has minimum
      description length (is the shortest Nc-dependent expression that
      gives a jump ≥ 2).

 NOTE: This conjecture is stated as a Lean Prop (open; not yet proved).
 The proof would require formalizing "description length" over Nc-polynomial
 expressions — the subject of Spec 006 (Algebraic Saturation Barrier). -/
def MersenneLadderUniqueness : Prop :=
  ∀ (Nc : ℕ), Nc = 3 →
  ∀ f : ℕ → ℕ,
    (∀ k : ℕ, 0 < k → 2^k - 1 < 2^(k + f Nc) - 1) →  -- monotone capacity
    (0 < f Nc) →                                         -- non-trivial jump
    (f Nc ≤ 2 * Nc) →                                   -- MDL minimality
    f Nc = 2 * Nc

end UgpLean
