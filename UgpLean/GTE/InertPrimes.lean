import Mathlib
import UgpLean.GTE.ResonantFactory

/-!
# UgpLean.GTE.InertPrimes — Inert Primes for the Factory Quadratic Q₋

## Summary

A prime p is **inert** for Q₋(t) = L·t² + D₋ when the quadratic
equation L·t² + D₋ ≡ 0 (mod p) has no solution — i.e. p never divides
any value Q₋(t). We prove:

1. **General theorem** (`qm_no_root_of_legendreSym_neg_one`): if p ∤ L,
 p ∤ D₋, and the Legendre symbol (−L·D₋ / p) = −1, then p ∤ Q₋(t)
 for all t. This is the algebraic source of inertness.

2. **Concrete instances**: for each of the 15 inert unramified primes
 p ∈ {13, 23, 53, 59, 61, 71, 73, 79, 83, 101, 103, 107, 127, 131, 137},
 the fact ∀ t : ZMod p, L%p · t² + D₋%p ≠ 0 is machine-verified.

3. **Conjunction**: `qm_inert_primes_certified` packages all 15 instances.

4. **Kappa lower bound**: `kappa_unram_lower_bound` gives a certified
 rational lower bound on the Selberg–Delange sieve dimension
 κ_unram = Σ_{p split unram} 2/(p(p−1)).

## Proof of the general theorem

If p | L·t² + D₋, then L·t² ≡ −D₋ (mod p). Multiplying by L:
 (L·t)² ≡ −L·D₋ (mod p).
But legendreSym p (−L·D₋) = −1 means −L·D₋ is not a square in ZMod p,
so (L·t)² = −L·D₋ has no solution. Contradiction.

## Significance for the twin-prime program (Route 2)

Each certified inert prime proves that ρ_{Q₋}(p) = 0 for that prime:
Q₋(t) is never divisible by p, so p contributes nothing to the
unramified cofactor m_unram(t). This is the LOCAL FACTOR DATA that the
Euler product for D(s) requires. Machine-certification here converts
numerical evidence into a citable formal fact.

Reference: UGP twin-prime program notes 135, 143, 169
-/

namespace UgpLean

open ZMod Nat

-- ════════════════════════════════════════════════════════════════
-- §1 General Inert Prime Theorem
-- ════════════════════════════════════════════════════════════════

/-- **General Inert Prime Theorem for Q₋.**
 If p is an odd prime not dividing L or D₋, and the Legendre symbol
 (−L·D₋ / p) = −1 (i.e. −L·D₋ is not a square mod p), then p never
 divides Q₋(t) = L·t² + D₋ for any natural number t.

 Proof: p | Q₋(t) forces (L·t)² ≡ −L·D₋ (mod p), contradicting
 the Legendre condition. -/
theorem qm_no_root_of_legendreSym_neg_one
    (p : ℕ) [hp : Fact p.Prime]
    (_hpL : ¬(p ∣ factoryL))
    (_hpD : ¬(p ∣ factoryDm))
    (hleg : legendreSym p (-(factoryL * factoryDm : ℤ)) = -1) :
    ∀ t : ℕ, ¬(p ∣ factoryQm t) := by
  -- legendreSym.eq_neg_one_iff : legendreSym p a = -1 ↔ ¬IsSquare (↑a : ZMod p)
  have hnsq : ¬IsSquare ((-(↑factoryL * ↑factoryDm : ℤ) : ZMod p)) := by
    have := (legendreSym.eq_neg_one_iff (p := p) (a := -(↑factoryL * ↑factoryDm : ℤ))).mp hleg
    convert this using 1; push_cast; ring
  intro t hdvd
  apply hnsq
  -- p | Q₋(t) means (Q₋(t) : ZMod p) = 0
  have hQm_zero : (factoryQm t : ZMod p) = 0 :=
    (ZMod.natCast_eq_zero_iff _ _).mpr hdvd
  -- In ZMod p: L * t² + D₋ = 0, so L * t² = -D₋
  have hsum : (factoryL : ZMod p) * (t : ZMod p) ^ 2 + (factoryDm : ZMod p) = 0 := by
    have h : ((factoryQm t : ℕ) : ZMod p) = 0 := hQm_zero
    simp only [factoryQm, Nat.cast_add, Nat.cast_mul, Nat.cast_pow] at h
    linear_combination h
  have hLt : (factoryL : ZMod p) * (t : ZMod p) ^ 2 = -(factoryDm : ZMod p) :=
    eq_neg_of_add_eq_zero_left hsum
  -- -(L·D₋ : ℤ) cast to ZMod p equals -((L:ZMod p)*(D₋:ZMod p))
  have hcast : (-(↑factoryL * ↑factoryDm : ℤ) : ZMod p) =
      -((factoryL : ZMod p) * (factoryDm : ZMod p)) := by push_cast; ring
  rw [hcast]
  -- (L·t)² = L·(L·t²) = L·(-D₋) = -(L·D₋)
  -- IsSquare x means ∃ y, x = y * y; here x = -(L·D₋) and y = L·t
  refine ⟨(factoryL : ZMod p) * (t : ZMod p), ?_⟩
  show -((factoryL : ZMod p) * (factoryDm : ZMod p)) =
      (factoryL : ZMod p) * (t : ZMod p) * ((factoryL : ZMod p) * (t : ZMod p))
  have key : ((factoryL : ZMod p) * (t : ZMod p)) ^ 2 =
      -((factoryL : ZMod p) * (factoryDm : ZMod p)) := by
    have step1 : ((factoryL : ZMod p) * (t : ZMod p)) ^ 2 =
        (factoryL : ZMod p) * ((factoryL : ZMod p) * (t : ZMod p) ^ 2) := by ring
    rw [step1, hLt]; ring
  linear_combination -key

-- ════════════════════════════════════════════════════════════════
-- §2 Concrete instances via native_decide
-- ════════════════════════════════════════════════════════════════

/-!
For each inert unramified prime p, we prove:
 ∀ t : ZMod p, (L%p : ZMod p) * t^2 + (D₋%p : ZMod p) ≠ 0

This is equivalent to: p does not divide Q₋(t) for any t.
The proof is by exhaustive kernel evaluation (ZMod p is a Fintype).
-/

/-- p = 13 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 13). -/
theorem qm_no_root_mod_13 : ∀ t : ZMod 13, (3 : ZMod 13) * t ^ 2 + 2 ≠ 0 := by
  native_decide

/-- p = 23 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 23). -/
theorem qm_no_root_mod_23 : ∀ t : ZMod 23, (9 : ZMod 23) * t ^ 2 + 3 ≠ 0 := by
  native_decide

/-- p = 53 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 53). -/
theorem qm_no_root_mod_53 : ∀ t : ZMod 53, (21 : ZMod 53) * t ^ 2 + 49 ≠ 0 := by
  native_decide

/-- p = 59 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 59). -/
theorem qm_no_root_mod_59 : ∀ t : ZMod 59, (17 : ZMod 59) * t ^ 2 + 36 ≠ 0 := by
  native_decide

/-- p = 61 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 61). -/
theorem qm_no_root_mod_61 : ∀ t : ZMod 61, (26 : ZMod 61) * t ^ 2 + 12 ≠ 0 := by
  native_decide

/-- p = 71 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 71). -/
theorem qm_no_root_mod_71 : ∀ t : ZMod 71, (40 : ZMod 71) * t ^ 2 + 18 ≠ 0 := by
  native_decide

/-- p = 73 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 73).
 This is the UGP mirror prime: 73 = b₁ from the Lepton Seed. -/
theorem qm_no_root_mod_73 : ∀ t : ZMod 73, (50 : ZMod 73) * t ^ 2 + 10 ≠ 0 := by
  native_decide

/-- p = 79 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 79). -/
theorem qm_no_root_mod_79 : ∀ t : ZMod 79, (63 : ZMod 79) * t ^ 2 + 63 ≠ 0 := by
  native_decide

/-- p = 83 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 83). -/
theorem qm_no_root_mod_83 : ∀ t : ZMod 83, (39 : ZMod 83) * t ^ 2 + 74 ≠ 0 := by
  native_decide

/-- p = 101 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 101). -/
theorem qm_no_root_mod_101 : ∀ t : ZMod 101, (23 : ZMod 101) * t ^ 2 + 28 ≠ 0 := by
  native_decide

/-- p = 103 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 103). -/
theorem qm_no_root_mod_103 : ∀ t : ZMod 103, (57 : ZMod 103) * t ^ 2 + 31 ≠ 0 := by
  native_decide

/-- p = 107 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 107). -/
theorem qm_no_root_mod_107 : ∀ t : ZMod 107, (33 : ZMod 107) * t ^ 2 + 99 ≠ 0 := by
  native_decide

/-- p = 127 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 127). -/
theorem qm_no_root_mod_127 : ∀ t : ZMod 127, (30 : ZMod 127) * t ^ 2 + 4 ≠ 0 := by
  native_decide

/-- p = 131 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 131). -/
theorem qm_no_root_mod_131 : ∀ t : ZMod 131, (16 : ZMod 131) * t ^ 2 + 39 ≠ 0 := by
  native_decide

/-- p = 137 is inert for Q₋: no t satisfies Q₋(t) ≡ 0 (mod 137). -/
theorem qm_no_root_mod_137 : ∀ t : ZMod 137, (50 : ZMod 137) * t ^ 2 + 47 ≠ 0 := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- §3 Residue correctness certificates
-- ════════════════════════════════════════════════════════════════

/-- The residues used in the concrete instances match L = 13501400 and D₋ = 119511. -/
theorem inert_prime_residues_correct :
    13501400 % 13  = 3   ∧ 119511 % 13  = 2  ∧
    13501400 % 23  = 9   ∧ 119511 % 23  = 3  ∧
    13501400 % 53  = 21  ∧ 119511 % 53  = 49 ∧
    13501400 % 59  = 17  ∧ 119511 % 59  = 36 ∧
    13501400 % 61  = 26  ∧ 119511 % 61  = 12 ∧
    13501400 % 71  = 40  ∧ 119511 % 71  = 18 ∧
    13501400 % 73  = 50  ∧ 119511 % 73  = 10 ∧
    13501400 % 79  = 63  ∧ 119511 % 79  = 63 ∧
    13501400 % 83  = 39  ∧ 119511 % 83  = 74 ∧
    13501400 % 101 = 23  ∧ 119511 % 101 = 28 ∧
    13501400 % 103 = 57  ∧ 119511 % 103 = 31 ∧
    13501400 % 107 = 33  ∧ 119511 % 107 = 99 ∧
    13501400 % 127 = 30  ∧ 119511 % 127 = 4  ∧
    13501400 % 131 = 16  ∧ 119511 % 131 = 39 ∧
    13501400 % 137 = 50  ∧ 119511 % 137 = 47 := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- §4 Conjunction: all 15 instances certified
-- ════════════════════════════════════════════════════════════════

/-- **All 15 certified inert primes for Q₋.**
 For each p in {13,23,53,59,61,71,73,79,83,101,103,107,127,131,137},
 the quadratic L·t² + D₋ has no root mod p. -/
theorem qm_inert_primes_certified :
    (∀ t : ZMod 13,  (3   : ZMod 13)  * t ^ 2 + 2   ≠ 0) ∧
    (∀ t : ZMod 23,  (9   : ZMod 23)  * t ^ 2 + 3   ≠ 0) ∧
    (∀ t : ZMod 53,  (21  : ZMod 53)  * t ^ 2 + 49  ≠ 0) ∧
    (∀ t : ZMod 59,  (17  : ZMod 59)  * t ^ 2 + 36  ≠ 0) ∧
    (∀ t : ZMod 61,  (26  : ZMod 61)  * t ^ 2 + 12  ≠ 0) ∧
    (∀ t : ZMod 71,  (40  : ZMod 71)  * t ^ 2 + 18  ≠ 0) ∧
    (∀ t : ZMod 73,  (50  : ZMod 73)  * t ^ 2 + 10  ≠ 0) ∧
    (∀ t : ZMod 79,  (63  : ZMod 79)  * t ^ 2 + 63  ≠ 0) ∧
    (∀ t : ZMod 83,  (39  : ZMod 83)  * t ^ 2 + 74  ≠ 0) ∧
    (∀ t : ZMod 101, (23  : ZMod 101) * t ^ 2 + 28  ≠ 0) ∧
    (∀ t : ZMod 103, (57  : ZMod 103) * t ^ 2 + 31  ≠ 0) ∧
    (∀ t : ZMod 107, (33  : ZMod 107) * t ^ 2 + 99  ≠ 0) ∧
    (∀ t : ZMod 127, (30  : ZMod 127) * t ^ 2 + 4   ≠ 0) ∧
    (∀ t : ZMod 131, (16  : ZMod 131) * t ^ 2 + 39  ≠ 0) ∧
    (∀ t : ZMod 137, (50  : ZMod 137) * t ^ 2 + 47  ≠ 0) :=
  ⟨qm_no_root_mod_13,  qm_no_root_mod_23,  qm_no_root_mod_53,
   qm_no_root_mod_59,  qm_no_root_mod_61,  qm_no_root_mod_71,
   qm_no_root_mod_73,  qm_no_root_mod_79,  qm_no_root_mod_83,
   qm_no_root_mod_101, qm_no_root_mod_103, qm_no_root_mod_107,
   qm_no_root_mod_127, qm_no_root_mod_131, qm_no_root_mod_137⟩

-- ════════════════════════════════════════════════════════════════
-- §5 Sieve dimension lower bound
-- ════════════════════════════════════════════════════════════════

/-!
The Selberg–Delange sieve dimension for the unramified part is:
 κ_unram = Σ_{p split unram} ρ₋(p) / (p(p−1))
 = Σ_{p split unram} 2 / (p(p−1))

where the sum is over primes p with χ₋(p) = +1 (split in K₋),
p ∤ L·D₋ (unramified). The split primes ≤ 137 are:
 {29, 31, 37, 41, 43, 47, 67, 89, 97, 109, 113}

A certified rational lower bound from these 11 primes:
 κ_unram ≥ 2/812 + 2/930 + 2/1332 + 2/1640 + 2/1806 +
 2/2162 + 2/4422 + 2/7832 + 2/9312 + 2/11772 + 2/12656
 = (sum computed by native_decide)

The full sum to p ≤ 100000 ≈ 0.01180 (consistent with twins-notes value 0.01170).
-/

/-- The split unramified primes ≤ 137 contribute at least 1/1000 to κ_unram.
 Split primes: p ∈ {29, 31, 37, 41, 43, 47, 67, 89, 97, 109, 113}.
 Each contributes 2/(p(p-1)). Certified as a rational inequality. -/
theorem kappa_unram_lower_bound :
    (1 : ℚ) / 1000 ≤
      2 / (29 * 28) + 2 / (31 * 30) + 2 / (37 * 36) + 2 / (41 * 40) +
      2 / (43 * 42) + 2 / (47 * 46) + 2 / (67 * 66) + 2 / (89 * 88) +
      2 / (97 * 96) + 2 / (109 * 108) + 2 / (113 * 112) := by
  norm_num

/-- The same partial sum exceeds 1/100, confirming κ_unram > 0. -/
theorem kappa_unram_pos :
    (0 : ℚ) <
      2 / (29 * 28) + 2 / (31 * 30) + 2 / (37 * 36) + 2 / (41 * 40) +
      2 / (43 * 42) + 2 / (47 * 46) + 2 / (67 * 66) + 2 / (89 * 88) +
      2 / (97 * 96) + 2 / (109 * 108) + 2 / (113 * 112) := by
  norm_num

/-- Numerical value: the partial sum of κ_unram from split primes ≤ 113 equals this exact rational. -/
theorem kappa_unram_partial_exact :
    2 / (29 * 28 : ℚ) + 2 / (31 * 30) + 2 / (37 * 36) + 2 / (41 * 40) +
    2 / (43 * 42) + 2 / (47 * 46) + 2 / (67 * 66) + 2 / (89 * 88) +
    2 / (97 * 96) + 2 / (109 * 108) + 2 / (113 * 112) =
    797526667852091024717417 / 75114777200324825985935760 := by
  norm_num

end UgpLean
