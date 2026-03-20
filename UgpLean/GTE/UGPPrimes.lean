import Mathlib
import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs
import UgpLean.Compute.PrimeLock
import UgpLean.GTE.MirrorDualConjecture

/-!
# UgpLean.GTE.UGPPrimes — The UGP Prime Predicate and Existence Theorems

This file defines the formal `IsUGPPrime` predicate matching OEIS A394412,
proves that 823 and 2137 satisfy it with explicit witnesses, and establishes
that UGP primes exist at multiple distinct ridge levels.

## OEIS A394412

Primes p such that b*(q+13) = 2^n - 16 and p = (b+q+20)*q + 20
for some integers b ≥ 16, q ≥ 3, n ≥ 5.

First terms: 823, 2137, 9007, 27817, 46681, ...
57 terms computed up to 10^8.

## What is proved here

1. `IsUGPPrime`: the formal predicate (matching A394412)
2. `c1Val_eq_c1FromPair`: the two formulations of the UGP formula agree
3. `is_ugp_prime_823`: 823 is a UGP prime with witnesses (b=42, q=11, n=10)
4. `is_ugp_prime_2137`: 2137 is a UGP prime with witnesses (b=24, q=29, n=10)
5. `ugp_primes_exist`: UGP primes exist (constructive witness: 823)
6. `ten_ugp_primes`: 10 distinct UGP primes machine-checked across n=10,13,16

## Relationship to the mirror-dual conjecture

Each `MirrorDualPair n b₂ q₂` witnesses two UGP primes simultaneously.
The five certified mirror-dual pairs give 10 distinct UGP primes.
Infinitely many UGP primes would follow from the Mirror-Dual Conjecture (open).
-/

namespace UgpLean

-- ════════════════════════════════════════════════════════════════
-- §1  The IsUGPPrime predicate (matching OEIS A394412)
-- ════════════════════════════════════════════════════════════════

/-- A prime p is a **UGP prime** (OEIS A394412) if there exist
    integers b ≥ 16, q ≥ 3, n ≥ 5 such that:
      b * (q + 13) = 2^n - 16   (ridge divisor condition)
      p = (b + q + 20) * q + 20  (prime-lock formula)

    Note: b = b₂ (the smaller ridge divisor), q = q₁ = q₂ - 13
    (the first-generation quotient). The formula expands as:
      p = b₁ * q₁ + 20  where b₁ = b₂ + q₂ + 7 = b + q + 13 + 7 = b + q + 20. -/
def IsUGPPrime (p : ℕ) : Prop :=
  ∃ b q n : ℕ,
    16 ≤ b ∧ 3 ≤ q ∧ 5 ≤ n ∧
    b * (q + 13) = 2^n - 16 ∧
    p = (b + q + 20) * q + 20 ∧
    Nat.Prime p

-- ════════════════════════════════════════════════════════════════
-- §2  Bridge: c1Val = c1FromPair
-- ════════════════════════════════════════════════════════════════

/-- The two formulations of the UGP prime formula agree:
    c1Val b₂ q₂ = c1FromPair (b1FromPair b₂ q₂) (q1FromQ2 q₂)

    c1Val uses the raw formula (b₂+q₂+7)*(q₂-13)+20.
    c1FromPair uses the structured definitions b1FromPair and q1FromQ2.
    They are definitionally equal. -/
theorem c1Val_eq_c1FromPair (b₂ q₂ : ℕ) (_ : 13 ≤ q₂) :
    c1Val b₂ q₂ = c1FromPair (b1FromPair b₂ q₂) (q1FromQ2 q₂) := by
  unfold c1Val c1FromPair b1FromPair q1FromQ2 ugp1_s ugp1_g ugp1_t
  omega

/-- c1Val 42 24 = 823 (lepton seed) -/
theorem c1Val_42_24 : c1Val 42 24 = 823 := by native_decide

/-- c1Val 24 42 = 2137 (mirror seed) -/
theorem c1Val_24_42 : c1Val 24 42 = 2137 := by native_decide

-- ════════════════════════════════════════════════════════════════
-- §3  Explicit UGP prime witnesses
-- ════════════════════════════════════════════════════════════════

/-- **823 is a UGP prime** with witnesses b=42, q=11, n=10.
    42*(11+13) = 42*24 = 1008 = 2^10-16 ✓
    (42+11+20)*11+20 = 73*11+20 = 823 ✓  -/
theorem is_ugp_prime_823 : IsUGPPrime 823 :=
  ⟨42, 11, 10, by norm_num, by norm_num, by norm_num,
   by native_decide, by native_decide, prime_823⟩

/-- **2137 is a UGP prime** with witnesses b=24, q=29, n=10.
    24*(29+13) = 24*42 = 1008 = 2^10-16 ✓
    (24+29+20)*29+20 = 73*29+20 = 2137 ✓  -/
theorem is_ugp_prime_2137 : IsUGPPrime 2137 :=
  ⟨24, 29, 10, by norm_num, by norm_num, by norm_num,
   by native_decide, by native_decide, prime_2137⟩

-- ════════════════════════════════════════════════════════════════
-- §4  Existence theorems
-- ════════════════════════════════════════════════════════════════

/-- **UGP primes exist.** Constructive witness: 823. -/
theorem ugp_primes_exist : ∃ p : ℕ, IsUGPPrime p :=
  ⟨823, is_ugp_prime_823⟩

/-- **Two distinct UGP primes exist at n=10.** -/
theorem two_ugp_primes_at_n10 :
    IsUGPPrime 823 ∧ IsUGPPrime 2137 ∧ (823 : ℕ) ≠ 2137 :=
  ⟨is_ugp_prime_823, is_ugp_prime_2137, by norm_num⟩

-- ════════════════════════════════════════════════════════════════
-- §5  Ten machine-checked UGP primes across three ridge levels
-- ════════════════════════════════════════════════════════════════

/-!
The ten UGP primes with their witnesses (b, q, n):
  n=10: 823  (b=42,  q=11,   n=10)
        2137 (b=24,  q=29,   n=10)
  n=13: 9007  (b=146, q=43,   n=13)
        27817 (b=56,  q=133,  n=13)
  n=16: 46681  (b=1560, q=29,   n=16)
        83389  (b=420,  q=143,  n=16)
        92801  (b=360,  q=169,  n=16)
        190523 (b=182,  q=347,  n=16)
        237301 (b=156,  q=407,  n=16)
        2489143 (b=42,  q=1547, n=16)
-/

/-- **Ten distinct UGP primes are machine-checked** across n=10, 13, 16. -/
theorem ten_ugp_primes :
    IsUGPPrime 823 ∧ IsUGPPrime 2137 ∧
    IsUGPPrime 9007 ∧ IsUGPPrime 27817 ∧
    IsUGPPrime 46681 ∧ IsUGPPrime 83389 ∧
    IsUGPPrime 92801 ∧ IsUGPPrime 190523 ∧
    IsUGPPrime 237301 ∧ IsUGPPrime 2489143 :=
  ⟨is_ugp_prime_823,
   is_ugp_prime_2137,
   ⟨146, 43,   13, by norm_num, by norm_num, by norm_num, by native_decide, by native_decide, by native_decide⟩,
   ⟨56,  133,  13, by norm_num, by norm_num, by norm_num, by native_decide, by native_decide, by native_decide⟩,
   ⟨1560, 29,  16, by norm_num, by norm_num, by norm_num, by native_decide, by native_decide, by native_decide⟩,
   ⟨420,  143, 16, by norm_num, by norm_num, by norm_num, by native_decide, by native_decide, by native_decide⟩,
   ⟨360,  169, 16, by norm_num, by norm_num, by norm_num, by native_decide, by native_decide, by native_decide⟩,
   ⟨182,  347, 16, by norm_num, by norm_num, by norm_num, by native_decide, by native_decide, by native_decide⟩,
   ⟨156,  407, 16, by norm_num, by norm_num, by norm_num, by native_decide, by native_decide, by native_decide⟩,
   ⟨42,  1547, 16, by norm_num, by norm_num, by norm_num, by native_decide, by native_decide, by native_decide⟩⟩

/-- UGP primes exist at three distinct ridge levels (n=10, 13, 16). -/
theorem ugp_primes_at_three_levels :
    (∃ p, IsUGPPrime p ∧ ∃ b q : ℕ, b * (q + 13) = 2^10 - 16 ∧ p = (b+q+20)*q+20) ∧
    (∃ p, IsUGPPrime p ∧ ∃ b q : ℕ, b * (q + 13) = 2^13 - 16 ∧ p = (b+q+20)*q+20) ∧
    (∃ p, IsUGPPrime p ∧ ∃ b q : ℕ, b * (q + 13) = 2^16 - 16 ∧ p = (b+q+20)*q+20) :=
  ⟨⟨823,  is_ugp_prime_823,  42,  11,  by native_decide, by native_decide⟩,
   ⟨9007, ten_ugp_primes.2.2.1, 146, 43, by native_decide, by native_decide⟩,
   ⟨46681, ten_ugp_primes.2.2.2.2.1, 1560, 29, by native_decide, by native_decide⟩⟩

-- ════════════════════════════════════════════════════════════════
-- §6  Infinitude question
-- ════════════════════════════════════════════════════════════════

/-- The infinitude of UGP primes is open. It would follow from the
    Mirror-Dual Conjecture: if there are infinitely many mirror-dual
    pairs, each pair witnesses two UGP primes.

    Computational evidence: 30 mirror-dual pairs found for n ≤ 50,
    giving 60 UGP primes (with 57 independently verified up to 10^8
    via exhaustive sieve, submitted as OEIS A394412). -/
def UGPPrimeInfinitudeConjecture : Prop :=
  ∀ N : ℕ, ∃ p : ℕ, N ≤ p ∧ IsUGPPrime p

end UgpLean
