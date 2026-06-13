import Mathlib

/-!
# GTE-admissible primes and Pisano periods

Vacuum-uniqueness admissible primes satisfy `π(q) = 2(q+1)` among primes `q ≡ 3 (mod 4)`
with `(5/q) = −1` (CatAD biconditional; epic 089-R04c).

**Certified here (CatAL):** finite Pisano-period checks on key admissible primes
`{3, 7, 23, 43}` and non-admissible prime powers `{9, 25, 49}`.

**Open (CatAD):** general-q biconditional without finite enumeration.

All theorems: zero sorry, zero custom axioms.
-/

namespace UgpLean.Polynomial.AdmissiblePrimes

/-- Smallest positive `k ≤ bound` with `fib k ≡ 0` and `fib (k+1) ≡ 1` mod `q`,
    when such a `k` exists within the search bound. -/
def computePisanoPeriod (q : ℕ) (bound : ℕ) : Option ℕ :=
  (List.range bound).foldl
    (init := (none : Option ℕ))
    fun acc i =>
      match acc with
      | some _ => acc
      | none =>
        let k := i + 1
        if Nat.fib k % q == 0 && Nat.fib (k + 1) % q == 1 then some k else none

-- ════════════════════════════════════════════════════════════════
-- §1  Verified Pisano periods for admissible primes
-- ════════════════════════════════════════════════════════════════

theorem pisano_period_3_eq_8 : computePisanoPeriod 3 100 = some 8 := by
  native_decide

theorem pisano_period_7_eq_16 : computePisanoPeriod 7 100 = some 16 := by
  native_decide

theorem pisano_period_23_eq_48 : computePisanoPeriod 23 200 = some 48 := by
  native_decide

theorem pisano_period_43_eq_88 : computePisanoPeriod 43 200 = some 88 := by
  native_decide

theorem admissible_pisano_check :
    computePisanoPeriod 3 100 = some (2 * (3 + 1)) ∧
    computePisanoPeriod 7 100 = some (2 * (7 + 1)) := by
  native_decide

/-- **admissible_iff_pisano_twice_q_plus_one** (CatAL — finite certificate):
    The key GTE-admissible primes `{3, 7, 23, 43}` satisfy `π(q) = 2(q+1)`.
    The general biconditional among `q ≡ 3 (mod 4)` with `(5/q) = −1` is CatAD. -/
theorem admissible_iff_pisano_twice_q_plus_one :
    computePisanoPeriod 3 200 = some (2 * (3 + 1)) ∧
    computePisanoPeriod 7 200 = some (2 * (7 + 1)) ∧
    computePisanoPeriod 23 200 = some (2 * (23 + 1)) ∧
    computePisanoPeriod 43 200 = some (2 * (43 + 1)) := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- §2  Prime powers are not GTE-admissible
-- ════════════════════════════════════════════════════════════════

theorem prime_power_9_not_admissible :
    computePisanoPeriod 9 200 ≠ some (2 * (9 + 1)) := by
  native_decide

theorem prime_power_25_not_admissible :
    computePisanoPeriod 25 200 ≠ some (2 * (25 + 1)) := by
  native_decide

theorem prime_power_49_not_admissible :
    computePisanoPeriod 49 200 ≠ some (2 * (49 + 1)) := by
  native_decide

/-- **prime_power_not_admissible** (CatAL — finite certificate):
    No tested prime power `p^k` (`k ≥ 2`) satisfies `π(p^k) = 2(p^k+1)`. -/
theorem prime_power_not_admissible :
    computePisanoPeriod 9 200 ≠ some (2 * (9 + 1)) ∧
    computePisanoPeriod 25 200 ≠ some (2 * (25 + 1)) ∧
    computePisanoPeriod 49 200 ≠ some (2 * (49 + 1)) := by
  native_decide

end UgpLean.Polynomial.AdmissiblePrimes
