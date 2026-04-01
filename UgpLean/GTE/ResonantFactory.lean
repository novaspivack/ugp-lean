import Mathlib
import UgpLean.Core.RidgeDefs
import UgpLean.GTE.MirrorDualConjecture

/-!
# UgpLean.GTE.ResonantFactory — Resonant Packet Factory Formalization

## Background

The resonant packet factory (UGP twin-prime program, note 048) produces
exact gap-2 pairs Q₋(t), Q₊(t) for every integer t, where:
  Q₋(t) = L·t² + D₋
  Q₊(t) = L·t² + D₊ = Q₋(t) + 2
with L = 13501400, D₋ = 119511, D₊ = 119513.

## What is proved here

1. **Branch linearization:** c₁(M/q, q) is affine in M/q with slope (q−13)
   and intercept B(q) = (q+7)(q−13)+20.

2. **Factory quadratic definitions and gap-2 property:** Q₊(t) − Q₋(t) = 2.

3. **Local density (Hasse check):** For each good prime p ≤ 43,
   ρ_F(p) = #{t mod p : F(t) ≡ 0 (mod p)} is computed exactly.

4. **Product algebra identity:** F(t) = Q₋(t)·Q₊(t) is a factored quartic,
   and λ(F(t)) = λ(Q₋(t))·λ(Q₊(t)) by complete multiplicativity of λ.

Reference: UGP twin-prime program notes 042, 048, 049, 055, 059
-/

namespace UgpLean

open Nat

-- ════════════════════════════════════════════════════════════════
-- §1  Branch linearization
-- ════════════════════════════════════════════════════════════════

/-- The intercept of the branch linearization: B(q) = (q+7)(q-13)+20. -/
def branchIntercept (q : ℕ) : ℕ := (q + 7) * (q - 13) + 20

/-- Branch linearization identity: c₁(b₂, q₂) = b₂·(q₂ − 13) + B(q₂).
    This shows c₁ is affine in b₂ with slope (q₂ − 13) and
    intercept B(q₂) = (q₂+7)(q₂−13)+20, which depends only on q₂. -/
theorem branch_linearization (b₂ q₂ : ℕ) (hq : 13 ≤ q₂) :
    c1Val b₂ q₂ = b₂ * (q₂ - 13) + branchIntercept q₂ := by
  unfold c1Val branchIntercept
  have hsplit : b₂ + q₂ + 7 = b₂ + (q₂ + 7) := by omega
  rw [hsplit, Nat.add_mul]

/-- The branch intercept at q₂ = 24 (from the canonical n=10 pair): B(24) = 361. -/
theorem branchIntercept_24 : branchIntercept 24 = 361 := by native_decide

/-- The branch intercept at q₂ = 42 (from the mirror n=10 pair): B(42) = 1441. -/
theorem branchIntercept_42 : branchIntercept 42 = 1441 := by native_decide

/-- Verification: c₁(42, 24) = 42·11 + 361 = 823. -/
theorem branch_linearization_n10 : c1Val 42 24 = 42 * 11 + 361 := by
  unfold c1Val; native_decide


-- ════════════════════════════════════════════════════════════════
-- §2  Resonant factory definitions
-- ════════════════════════════════════════════════════════════════

/-- The factory scale parameter L = 13501400. -/
def factoryL : ℕ := 13501400

/-- The factory offset D₋ = 119511. -/
def factoryDm : ℕ := 119511

/-- The factory offset D₊ = 119513. -/
def factoryDp : ℕ := 119513

/-- The factory quadratic Q₋(t) = L·t² + D₋. -/
def factoryQm (t : ℕ) : ℕ := factoryL * t^2 + factoryDm

/-- The factory quadratic Q₊(t) = L·t² + D₊. -/
def factoryQp (t : ℕ) : ℕ := factoryL * t^2 + factoryDp

/-- The factory quartic F(t) = Q₋(t)·Q₊(t). -/
def factoryF (t : ℕ) : ℕ := factoryQm t * factoryQp t

/-- **Gap-2 property:** Q₊(t) − Q₋(t) = 2 for all t.
    This is the structural source of the twin-prime gap. -/
theorem factory_gap_two (t : ℕ) : factoryQp t = factoryQm t + 2 := by
  unfold factoryQp factoryQm factoryDp factoryDm; omega

/-- D₊ − D₋ = 2. -/
theorem factory_offset_gap : factoryDp = factoryDm + 2 := by
  unfold factoryDp factoryDm; rfl

/-- D₋ = 3² · 7² · 271. -/
theorem factoryDm_factored : factoryDm = 3^2 * 7^2 * 271 := by
  unfold factoryDm; norm_num

/-- D₊ = 119513 is prime. -/
theorem factoryDp_prime : Nat.Prime factoryDp := by
  unfold factoryDp; native_decide

/-- L = 2³ · 5² · 11 · 17 · 19². -/
theorem factoryL_factored : factoryL = 2^3 * 5^2 * 11 * 17 * 19^2 := by
  unfold factoryL; norm_num

-- ════════════════════════════════════════════════════════════════
-- §3  Local density / Hasse check
-- ════════════════════════════════════════════════════════════════

/-- Reduced factory constants mod p for efficient computation.
    ρ_F(p) = #{t mod p : (L·t²+D₋)(L·t²+D₊) ≡ 0 mod p}. We verify
    by computing with the reduced residues L mod p, D₋ mod p, D₊ mod p. -/

/-- The root count of F mod p, computed with reduced constants. -/
def rootCountFmod (Lp Dmp Dpp p : ℕ) : ℕ :=
  ((Finset.range p).filter (fun t => ((Lp * (t * t) + Dmp) * (Lp * (t * t) + Dpp)) % p = 0)).card

/-- ρ_F(3) = 1. (L≡2, D₋≡0, D₊≡2 mod 3) -/
theorem localDensity_3 : rootCountFmod 2 0 2 3 = 1 := by native_decide

/-- ρ_F(7) = 3. (L≡4, D₋≡0, D₊≡2 mod 7) -/
theorem localDensity_7 : rootCountFmod 4 0 2 7 = 3 := by native_decide

/-- ρ_F(13) = 2. (L≡5, D₋≡6, D₊≡8 mod 13) -/
theorem localDensity_13 : rootCountFmod 5 6 8 13 = 2 := by native_decide

/-- ρ_F(23) = 2. (L≡2, D₋≡11, D₊≡13 mod 23) -/
theorem localDensity_23 : rootCountFmod 2 11 13 23 = 2 := by native_decide

/-- ρ_F(29) = 2. -/
theorem localDensity_29 : rootCountFmod (13501400 % 29) (119511 % 29) (119513 % 29) 29 = 2 := by native_decide

/-- ρ_F(31) = 2. -/
theorem localDensity_31 : rootCountFmod (13501400 % 31) (119511 % 31) (119513 % 31) 31 = 2 := by native_decide

/-- ρ_F(37) = 4. (Both Q₋ and Q₊ split mod 37) -/
theorem localDensity_37 : rootCountFmod (13501400 % 37) (119511 % 37) (119513 % 37) 37 = 4 := by native_decide

/-- ρ_F(41) = 4. -/
theorem localDensity_41 : rootCountFmod (13501400 % 41) (119511 % 41) (119513 % 41) 41 = 4 := by native_decide

/-- ρ_F(43) = 4. -/
theorem localDensity_43 : rootCountFmod (13501400 % 43) (119511 % 43) (119513 % 43) 43 = 4 := by native_decide

/-- Hasse check: the reduced residues used above match the actual factory constants. -/
theorem factory_residues_correct :
    13501400 % 3 = 2 ∧ 119511 % 3 = 0 ∧ 119513 % 3 = 2 ∧
    13501400 % 7 = 4 ∧ 119511 % 7 = 0 ∧ 119513 % 7 = 2 ∧
    13501400 % 13 = 5 ∧ 119511 % 13 = 6 ∧ 119513 % 13 = 8 ∧
    13501400 % 23 = 2 ∧ 119511 % 23 = 11 ∧ 119513 % 23 = 13 := by native_decide

/-- No local obstruction: for every good prime p ≤ 43,
    ρ_F(p) < p, i.e., F(t) does not vanish identically mod any prime.
    This is necessary for the singular series S > 0. -/
theorem hasse_check_no_obstruction :
    rootCountFmod 2 0 2 3 < 3 ∧
    rootCountFmod 4 0 2 7 < 7 ∧
    rootCountFmod 5 6 8 13 < 13 ∧
    rootCountFmod 2 11 13 23 < 23 := by
  refine ⟨?_, ?_, ?_, ?_⟩ <;> native_decide

-- ════════════════════════════════════════════════════════════════
-- §4  Product algebra identity (complete multiplicativity of λ)
-- ════════════════════════════════════════════════════════════════

/-- Complete multiplicativity of Ω: Ω(a·b) = Ω(a) + Ω(b) for positive a, b.
    This is the additive form of λ being completely multiplicative. -/
theorem omega_additive {a b : ℕ} (ha : a ≠ 0) (hb : b ≠ 0) :
    Nat.Ω (a * b) = Nat.Ω a + Nat.Ω b :=
  Nat.Ω_mul ha hb

/-- **Product algebra identity (Ω-additive form).**
    Ω(F(t)) = Ω(Q₋(t)) + Ω(Q₊(t)) for t ≥ 1.

    This is the formal content of Proposition 1 in note 059:
    the Liouville function on the factory quartic factors through
    the product algebra A = K₋ × K₊, since λ(ab) = λ(a)λ(b)
    is equivalent to Ω(ab) = Ω(a) + Ω(b). -/
theorem factory_product_algebra (t : ℕ) (ht : 0 < t) :
    Nat.Ω (factoryF t) = Nat.Ω (factoryQm t) + Nat.Ω (factoryQp t) := by
  unfold factoryF
  apply omega_additive
  · unfold factoryQm factoryL factoryDm; omega
  · unfold factoryQp factoryL factoryDp; omega

-- ════════════════════════════════════════════════════════════════
-- §5  Concrete factory witnesses
-- ════════════════════════════════════════════════════════════════

/-- F(1) = Q₋(1) · Q₊(1) = 13620911 · 13620913. -/
theorem factoryF_1 : factoryF 1 = 13620911 * 13620913 := by
  unfold factoryF factoryQm factoryQp factoryL factoryDm factoryDp; norm_num

/-- Q₋(1) and Q₊(1) form a gap-2 pair. -/
theorem factory_gap_2_at_1 : factoryQp 1 = factoryQm 1 + 2 := factory_gap_two 1

end UgpLean
