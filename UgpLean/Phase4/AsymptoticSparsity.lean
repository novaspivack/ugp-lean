import Mathlib.Data.Nat.Sqrt
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs
import UgpLean.Core.SievePredicates
import UgpLean.Compute.Sieve
import UgpLean.Phase4.DeltaUGP

/-!
# UgpLean.Phase4.AsymptoticSparsity — The Asymptotic Sparsity Theorem

**Theorem (Asymptotic Sparsity):** The joint constraint of arithmetic admissibility
(Stage-1 mirror-dual sieve) and physical viability (Stage-2 b₁=73 match) has
exactly one solution across all ridge levels: (n=10, b₁=73).

**Part 1 (Finite check n ∈ [4,12]):** For each n, verify by `native_decide` that
no element of the finite set `ridgeSurvivorsFinset n` has b₂+q₂+7=73.

**Part 2 (Analytic bound n ≥ 13):** AM-GM over ℤ: b₂*q₂≥8176, b₂,q₂≥16
→ b₂+q₂≥180 → b₁=b₂+q₂+7≥187>73.

Reference: P25 §4, `papers/25_deeper_theory/01_asymptotic_sieve.py`
-/

namespace UgpLean.Phase4.AsymptoticSparsity

open UgpLean

/-! ## Part 0: Trivial case n < 4 -/

/-- For n < 4, ridge n = 0 in Nat, so no divisor pair with b₂,q₂ ≥ 16 exists.
  Any `isMirrorDualSurvivorAt n b₂ q₂` for n < 4 is False (vacuously true). -/
theorem no_survivor_small_n (n b₂ q₂ : ℕ) (hn : n < 4)
    (hsurv : isMirrorDualSurvivorAt n b₂ q₂) : False := by
  obtain ⟨hprod, hb₂, _, hq₂, _⟩ := hsurv
  -- ridge n = 2^n - 16 = 0 for n ≤ 3 (Nat truncation)
  have hridge : ridge n = 0 := by
    unfold ridge
    have hpow : 2 ^ n ≤ 16 := by
      calc 2 ^ n ≤ 2 ^ 3 := Nat.pow_le_pow_right (by norm_num) (by omega)
        _ = 8 := by norm_num
        _ ≤ 16 := by norm_num
    omega
  -- b₂ * q₂ = 0, but b₂ ≥ 16 and q₂ ≥ 16 → contradiction
  rw [hridge] at hprod
  have : b₂ * q₂ ≥ 16 * 16 := Nat.mul_le_mul hb₂ hq₂
  omega

/-! ## Part 1: Finite check n ∈ [4,12] -/

/-- At n=10, the pair (24,42) is a survivor with b₁=24+42+7=73. -/
theorem stage2_survivor_10 :
    isMirrorDualSurvivorAt 10 24 42 ∧ 24 + 42 + 7 = 73 := by
  constructor
  · exact (isMirrorDualSurvivorAt_iff 10 24 42).mpr (by native_decide)
  · norm_num

/-- For n=4, no ridgeSurvivor has b₁=73. (ridgeSurvivorsFinset 4 = ∅ since R₄=0.) -/
theorem no_stage2_at_4 :
    ∀ p ∈ ridgeSurvivorsFinset 4, p.1 + p.2 + 7 ≠ 73 := by native_decide

theorem no_stage2_at_5  : ∀ p ∈ ridgeSurvivorsFinset 5,  p.1 + p.2 + 7 ≠ 73 := by native_decide
theorem no_stage2_at_6  : ∀ p ∈ ridgeSurvivorsFinset 6,  p.1 + p.2 + 7 ≠ 73 := by native_decide
theorem no_stage2_at_7  : ∀ p ∈ ridgeSurvivorsFinset 7,  p.1 + p.2 + 7 ≠ 73 := by native_decide
theorem no_stage2_at_8  : ∀ p ∈ ridgeSurvivorsFinset 8,  p.1 + p.2 + 7 ≠ 73 := by native_decide
theorem no_stage2_at_9  : ∀ p ∈ ridgeSurvivorsFinset 9,  p.1 + p.2 + 7 ≠ 73 := by native_decide
theorem no_stage2_at_11 : ∀ p ∈ ridgeSurvivorsFinset 11, p.1 + p.2 + 7 ≠ 73 := by native_decide
theorem no_stage2_at_12 : ∀ p ∈ ridgeSurvivorsFinset 12, p.1 + p.2 + 7 ≠ 73 := by native_decide

/-- Prop-level version: for n ∈ {4..12}\{10}, no survivor has b₁=73. -/
theorem no_stage2_finite (n : ℕ) (hn1 : 4 ≤ n) (hn2 : n ≤ 12) (hne : n ≠ 10) :
    ∀ b₂ q₂, isMirrorDualSurvivorAt n b₂ q₂ → b₂ + q₂ + 7 ≠ 73 := by
  intro b₂ q₂ hsurv
  have hmem := (isMirrorDualSurvivorAt_iff n b₂ q₂).mp hsurv
  interval_cases n
  · exact no_stage2_at_4  ⟨b₂, q₂⟩ hmem
  · exact no_stage2_at_5  ⟨b₂, q₂⟩ hmem
  · exact no_stage2_at_6  ⟨b₂, q₂⟩ hmem
  · exact no_stage2_at_7  ⟨b₂, q₂⟩ hmem
  · exact no_stage2_at_8  ⟨b₂, q₂⟩ hmem
  · exact no_stage2_at_9  ⟨b₂, q₂⟩ hmem
  · contradiction  -- n = 10 excluded by hne
  · exact no_stage2_at_11 ⟨b₂, q₂⟩ hmem
  · exact no_stage2_at_12 ⟨b₂, q₂⟩ hmem

/-! ## Part 2: Analytic bound for n ≥ 13 -/

/-- For n ≥ 13, ridge n ≥ 8176 (= 2¹³ − 16). -/
lemma ridge_ge_8176 (n : ℕ) (hn : n ≥ 13) : ridge n ≥ 8176 := by
  unfold ridge
  have hpow : 2 ^ 13 ≤ 2 ^ n := Nat.pow_le_pow_right (by norm_num) hn
  have h13 : (2 : ℕ) ^ 13 = 8192 := by norm_num
  omega

/-- For n ≥ 13, any mirror-dual survivor has b₁ = b₂+q₂+7 ≥ 187 > 73.
  Key: AM-GM over ℤ with hint (b₂-q₂)² ≥ 0 derives b₂+q₂ ≥ 180. -/
theorem no_stage2_large_n (n b₂ q₂ : ℕ) (hn : n ≥ 13)
    (hsurv : isMirrorDualSurvivorAt n b₂ q₂) :
    b₂ + q₂ + 7 ≠ 73 := by
  obtain ⟨hprod, hb₂, _, hq₂, _⟩ := hsurv
  have hR  : b₂ * q₂ ≥ 8176 := hprod ▸ ridge_ge_8176 n hn
  have hR' : (b₂ : ℤ) * q₂ ≥ 8176 := by exact_mod_cast hR
  have hb₂': (b₂ : ℤ) ≥ 16 := by exact_mod_cast hb₂
  have hq₂': (q₂ : ℤ) ≥ 16 := by exact_mod_cast hq₂
  -- AM-GM: (b₂−q₂)² ≥ 0 → (b₂+q₂)² ≥ 4·b₂·q₂ ≥ 32704 > 180² = 32400
  have hsum : (b₂ : ℤ) + q₂ ≥ 180 := by
    nlinarith [sq_nonneg ((b₂ : ℤ) - q₂)]
  exact_mod_cast by omega

/-! ## The Main Theorem -/

/-- **Asymptotic Sparsity Theorem:**
  (n=10, b₂=24, q₂=42, b₁=73) is the UNIQUE Stage-2 survivor across all n ≥ 4. -/
theorem asymptotic_sparsity :
    -- Existence
    isMirrorDualSurvivorAt 10 24 42 ∧ 24 + 42 + 7 = 73 ∧
    -- Uniqueness for n ∈ [4,12]
    (∀ n, 4 ≤ n → n ≤ 12 → n ≠ 10 →
       ∀ b₂ q₂, isMirrorDualSurvivorAt n b₂ q₂ → b₂ + q₂ + 7 ≠ 73) ∧
    -- Uniqueness for n ≥ 13
    (∀ n b₂ q₂, n ≥ 13 → isMirrorDualSurvivorAt n b₂ q₂ → b₂ + q₂ + 7 ≠ 73) :=
  ⟨stage2_survivor_10.1, stage2_survivor_10.2,
   no_stage2_finite,
   fun n b₂ q₂ hn h => no_stage2_large_n n b₂ q₂ hn h⟩

/-! ## The Complete Universal Theorem -/

/-- **Asymptotic Sparsity — Universal Form:**
  For ALL n : ℕ, the unique solution to the joint Stage-1+Stage-2 constraint is
  n=10, b₂=24, q₂=42, b₁=73.
  This is the strongest form: a single ∀ n : ℕ statement with no range restriction. -/
theorem asymptotic_sparsity_universal :
    -- Existence: n=10 is a solution
    isMirrorDualSurvivorAt 10 24 42 ∧ 24 + 42 + 7 = 73 ∧
    -- Uniqueness: for ALL n, if (b₂,q₂) is a survivor with b₁=73, then n=10
    ∀ n b₂ q₂ : ℕ, isMirrorDualSurvivorAt n b₂ q₂ → b₂ + q₂ + 7 = 73 → n = 10 := by
  refine ⟨stage2_survivor_10.1, stage2_survivor_10.2, ?_⟩
  intro n b₂ q₂ hsurv hb1
  by_contra hne
  -- Three cases: n < 4, n ∈ [4,12]\{10}, n ≥ 13
  rcases Nat.lt_or_ge n 4 with hn4 | hn4
  · exact (no_survivor_small_n n b₂ q₂ hn4 hsurv).elim
  · rcases Nat.lt_or_ge n 13 with hn12 | hn13
    · have hn12' : n ≤ 12 := by omega
      exact no_stage2_finite n hn4 hn12' hne b₂ q₂ hsurv (by omega)
    · exact absurd hb1 (no_stage2_large_n n b₂ q₂ hn13 hsurv)

end UgpLean.Phase4.AsymptoticSparsity
