import Mathlib
import UgpLean.Core.MirrorDefs
import UgpLean.Core.RidgeDefs

/-!
# UgpLean.Compute.PrimeLock — Prime-Lock Criterion

The prime-lock requires that c₁ = b₁·q₁ + 20 be prime.

For n=10 survivors (24,42) and (42,24):
- (24,42) → c₁ = 2137, which is prime
- (42,24) → c₁ = 823, which is prime

Reference: UGP Paper, main_n10_ridge.py
-/

namespace UgpLean

/-- 823 is prime (from mirror pair (42,24)) -/
theorem prime_823 : Nat.Prime 823 := by native_decide

/-- 2137 is prime (from mirror pair (24,42)) -/
theorem prime_2137 : Nat.Prime 2137 := by native_decide

/-- Prime-lock: c₁ must be prime for a survivor pair -/
def PrimeLock (c₁ : ℕ) : Prop := Nat.Prime c₁

/-- The two n=10 survivor c₁ values are both prime -/
theorem n10_survivor_c1_primes : Nat.Prime leptonC1 ∧ Nat.Prime mirrorC1 := by
  simp only [leptonC1, mirrorC1]
  exact ⟨prime_823, prime_2137⟩

/-- Mirror prime-lock: both (42,24) and (24,42) yield prime c₁ ∈ {823, 2137}. -/
theorem mirror_prime_lock :
    Nat.Prime (c1FromPair (b1FromPair 42 24) (q1FromQ2 24)) ∧
    Nat.Prime (c1FromPair (b1FromPair 24 42) (q1FromQ2 42)) := by
  simp only [b1FromPair, q1FromQ2, c1FromPair, ugp1_s, ugp1_g, ugp1_t]
  exact ⟨prime_823, prime_2137⟩

/-- Prime-lock reduces to a divisor test: c₁ is determined entirely by b₂|R.
  c₁ = (b₂ + R/b₂ + 7)(R/b₂ - 13) + 20 where R = 2^n - 16. -/
theorem c1_from_divisor (n : ℕ) (b₂ q₂ : ℕ) (_hprod : b₂ * q₂ = ridge n) :
    c1FromPair (b1FromPair b₂ q₂) (q1FromQ2 q₂) =
    (b₂ + q₂ + ugp1_s) * (q₂ - ugp1_g) + ugp1_t := by
  unfold c1FromPair b1FromPair q1FromQ2; rfl

end UgpLean
