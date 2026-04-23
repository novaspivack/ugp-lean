import Mathlib.Tactic
import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs
import UgpLean.GTE.MirrorDualConjecture

/-!
# UgpLean.GTE.MirrorShift — General Mirror-Shift Algebra

## Summary

For any divisor pair (b₂, q₂) at a ridge level, the two c₁-values produced
by the pair and its reverse satisfy a universal algebraic law:

 c₁(b₂, q₂) ≡ ugp1_t (mod b₁)
 c₁(q₂, b₂) ≡ ugp1_t (mod b₁)

where b₁ = b₁FromPair b₂ q₂ = b₂ + q₂ + ugp1_s is symmetric.

And when q₂ > b₂ (so the larger factor is q₂):

 c₁(b₂, q₂) - c₁(q₂, b₂) **does not** vanish in general,
 but both values share the residue ugp1_t mod b₁.

More precisely, for q₂ > b₂ ≥ 13:

 c₁Val b₂ q₂ - c₁Val q₂ b₂ = b₁FromPair b₂ q₂ * (q₂ - b₂)

since:
 c₁Val b₂ q₂ = b₁ * (q₂ - 13) + 20
 c₁Val q₂ b₂ = b₁ * (b₂ - 13) + 20
 difference = b₁ * ((q₂ - 13) - (b₂ - 13)) = b₁ * (q₂ - b₂)

At n=10: b₁ = 73, q₂ - b₂ = 42 - 24 = 18, so shift = 73 × 18 = 1314.

## Theorems

1. `c1Val_mod_b1`: c₁Val b₂ q₂ ≡ ugp1_t (mod b₁FromPair b₂ q₂) [general]
2. `mirror_c1_mod_b1`: c₁Val q₂ b₂ ≡ ugp1_t (mod b₁FromPair b₂ q₂) [by b₁ symmetry]
3. `mirror_shift_formula`: c₁Val b₂ q₂ - c₁Val q₂ b₂ = b₁ * (q₂ - b₂) [when q₂ ≥ b₂, b₂ ≥ 13]
4. `lepton_shift_is_18_times_b1`: the n=10 shift 1314 = 73 × 18 [instance of (3)]
5. `mirror_shift_divides_b1`: b₁ ∣ (c₁Val b₂ q₂ - c₁Val q₂ b₂) [b₁ always divides the shift]

Reference: UGP Project notes 143, 147
-/

namespace UgpLean

open Nat

-- ════════════════════════════════════════════════════════════════
-- §1 General shared-residue theorem
-- ════════════════════════════════════════════════════════════════

/-- **General shared residue:** For any pair (b₂, q₂), the c₁-value is
 congruent to ugp1_t modulo b₁FromPair b₂ q₂.

 Proof: c₁Val b₂ q₂ = b₁ * (q₂ - 13) + 20,
 so c₁Val b₂ q₂ % b₁ = 20 % b₁ = ugp1_t (when b₁ > ugp1_t = 20). -/
theorem c1Val_mod_b1 (b₂ q₂ : ℕ) (_hq : ugp1_g ≤ q₂) (hb1 : ugp1_t < b1FromPair b₂ q₂) :
    c1Val b₂ q₂ % b1FromPair b₂ q₂ = ugp1_t := by
  -- Unfold to raw arithmetic: c1Val b₂ q₂ = (b₂+q₂+7)*(q₂-13)+20, b1FromPair = b₂+q₂+7
  simp only [c1Val, b1FromPair, ugp1_s, ugp1_g, ugp1_t] at *
  -- Goal: ((b₂+q₂+7)*(q₂-13)+20) % (b₂+q₂+7) = 20
  set b₁ := b₂ + q₂ + 7
  have hmod_prod : (b₁ * (q₂ - 13)) % b₁ = 0 := Nat.mul_mod_right b₁ _
  have hmod_sum : (b₁ * (q₂ - 13) + 20) % b₁ = 20 % b₁ := by
    conv_lhs => rw [Nat.add_mod, hmod_prod, Nat.zero_add, Nat.mod_mod_of_dvd _ (dvd_refl b₁)]
  rw [hmod_sum]
  exact Nat.mod_eq_of_lt hb1

/-- **Mirror shared residue:** c₁Val q₂ b₂ also ≡ ugp1_t (mod b₁FromPair b₂ q₂).
 Uses that b₁FromPair is symmetric: b₁FromPair b₂ q₂ = b₁FromPair q₂ b₂. -/
theorem mirror_c1_mod_b1 (b₂ q₂ : ℕ) (hb : ugp1_g ≤ b₂) (hb1 : ugp1_t < b1FromPair b₂ q₂) :
    c1Val q₂ b₂ % b1FromPair b₂ q₂ = ugp1_t := by
  have hsym : b1FromPair q₂ b₂ = b1FromPair b₂ q₂ := by
    unfold b1FromPair; omega
  rw [← hsym]
  exact c1Val_mod_b1 q₂ b₂ hb (hsym ▸ hb1)

/-- **Both c-values in a mirror pair share residue ugp1_t mod b₁:**
 If b₂ ≥ 13, q₂ ≥ 13, and b₁ > 20, both c₁Val b₂ q₂ and c₁Val q₂ b₂
 are ≡ 20 (mod b₁). -/
theorem mirror_pair_shared_residue (b₂ q₂ : ℕ)
    (hb : ugp1_g ≤ b₂) (hq : ugp1_g ≤ q₂) (hb1 : ugp1_t < b1FromPair b₂ q₂) :
    c1Val b₂ q₂ % b1FromPair b₂ q₂ = ugp1_t ∧
    c1Val q₂ b₂ % b1FromPair b₂ q₂ = ugp1_t :=
  ⟨c1Val_mod_b1 b₂ q₂ hq hb1, mirror_c1_mod_b1 b₂ q₂ hb hb1⟩

-- ════════════════════════════════════════════════════════════════
-- §2 General mirror shift formula
-- ════════════════════════════════════════════════════════════════

/-- **General mirror shift formula:** When q₂ ≥ b₂ and both ≥ ugp1_g = 13:
 c₁Val b₂ q₂ - c₁Val q₂ b₂ = b₁FromPair b₂ q₂ * (q₂ - b₂).

 Proof:
 c₁Val b₂ q₂ = b₁ * (q₂ - 13) + 20
 c₁Val q₂ b₂ = b₁ * (b₂ - 13) + 20
 b₁ = b₂ + q₂ + 7 (symmetric)
 Since q₂ ≥ b₂ ≥ 13, both subtracted terms are well-defined.
 c₁Val b₂ q₂ - c₁Val q₂ b₂
 = (b₁ * (q₂ - 13) + 20) - (b₁ * (b₂ - 13) + 20)
 = b₁ * (q₂ - 13) - b₁ * (b₂ - 13)
 = b₁ * ((q₂ - 13) - (b₂ - 13))
 = b₁ * (q₂ - b₂). -/
theorem mirror_shift_formula (b₂ q₂ : ℕ)
    (hb : ugp1_g ≤ b₂) (hq : ugp1_g ≤ q₂) (hle : b₂ ≤ q₂) :
    c1Val b₂ q₂ - c1Val q₂ b₂ = b1FromPair b₂ q₂ * (q₂ - b₂) := by
  -- Lift to ℤ to avoid ℕ subtraction issues
  -- Key: c1Val b₂ q₂ = b₁ * (q₂ - 13) + 20 ≥ c1Val q₂ b₂ = b₁ * (b₂ - 13) + 20
  -- since q₂ ≥ b₂ ≥ 13 means q₂ - 13 ≥ b₂ - 13.
  have hb13 : ugp1_g ≤ b₂ := hb
  have hq13 : ugp1_g ≤ q₂ := hq
  simp only [c1Val, b1FromPair, ugp1_s, ugp1_g] at *
  -- c1Val b₂ q₂ = (b₂ + q₂ + 7) * (q₂ - 13) + 20
  -- c1Val q₂ b₂ = (q₂ + b₂ + 7) * (b₂ - 13) + 20
  -- b₁ = b₂ + q₂ + 7; note b₂ + q₂ + 7 = q₂ + b₂ + 7
  -- We need: (b₂+q₂+7)*(q₂-13)+20 - ((q₂+b₂+7)*(b₂-13)+20) = (b₂+q₂+7)*(q₂-b₂)
  -- Equivalently (adding c1Val q₂ b₂ to both sides):
  -- c1Val b₂ q₂ = c1Val q₂ b₂ + b₁ * (q₂ - b₂)
  suffices h : (b₂ + q₂ + 7) * (q₂ - 13) + 20 =
      (q₂ + b₂ + 7) * (b₂ - 13) + 20 + (b₂ + q₂ + 7) * (q₂ - b₂) by
    omega
  nlinarith [Nat.sub_add_cancel hb, Nat.sub_add_cancel hq, Nat.sub_add_cancel hle]

/-- **b₁ always divides the mirror shift:**
 b₁FromPair b₂ q₂ ∣ (c₁Val b₂ q₂ - c₁Val q₂ b₂) when q₂ ≥ b₂ ≥ 13. -/
theorem mirror_shift_divides_b1 (b₂ q₂ : ℕ)
    (hb : ugp1_g ≤ b₂) (hq : ugp1_g ≤ q₂) (hle : b₂ ≤ q₂) :
    b1FromPair b₂ q₂ ∣ (c1Val b₂ q₂ - c1Val q₂ b₂) := by
  rw [mirror_shift_formula b₂ q₂ hb hq hle]
  exact dvd_mul_right _ _

-- ════════════════════════════════════════════════════════════════
-- §3 Concrete instances: n=10 Lepton pair
-- ════════════════════════════════════════════════════════════════

/-- At n=10 with (b₂, q₂) = (24, 42): the shift is b₁ * (q₂ - b₂) = 73 * 18 = 1314. -/
theorem lepton_shift_is_18_times_b1 :
    c1Val 24 42 - c1Val 42 24 = b1FromPair 24 42 * (42 - 24) := by
  unfold c1Val b1FromPair; native_decide

/-- Numerical check: c₁Val 24 42 - c₁Val 42 24 = 1314. -/
theorem lepton_shift_val : c1Val 24 42 - c1Val 42 24 = 1314 := by
  unfold c1Val; native_decide

/-- The n=10 shift 1314 = 73 * 18 = 2 * 3² * 73. -/
theorem lepton_shift_factored :
    c1Val 24 42 - c1Val 42 24 = 2 * 3^2 * leptonB := by
  unfold c1Val leptonB; native_decide

/-- Shared residue at n=10 (instance of the general theorem):
 823 ≡ 20 (mod 73) and 2137 ≡ 20 (mod 73). -/
theorem lepton_pair_shared_residue_n10 :
    c1Val 42 24 % b1FromPair 42 24 = ugp1_t ∧
    c1Val 24 42 % b1FromPair 24 42 = ugp1_t := by
  unfold c1Val b1FromPair ugp1_t; native_decide

-- ════════════════════════════════════════════════════════════════
-- §4 Instances at n=13 and n=16
-- ════════════════════════════════════════════════════════════════

/-- At n=13 with pair (56, 146): b₁ = 209, q₂ - b₂ = 90, shift = 209 * 90 = 18810. -/
theorem shift_n13 :
    c1Val 56 146 - c1Val 146 56 = b1FromPair 56 146 * (146 - 56) := by
  unfold c1Val b1FromPair; native_decide

/-- Shared residue at n=13: both c-values ≡ 20 (mod 209). -/
theorem shared_residue_n13 :
    c1Val 146 56 % b1FromPair 146 56 = ugp1_t ∧
    c1Val 56 146 % b1FromPair 56 146 = ugp1_t := by
  unfold c1Val b1FromPair ugp1_t; native_decide

/-- At n=16 with pair (42, 1560): b₁ = 1609, shift = 1609 * 1518. -/
theorem shift_n16_a :
    c1Val 42 1560 - c1Val 1560 42 = b1FromPair 42 1560 * (1560 - 42) := by
  unfold c1Val b1FromPair; native_decide

/-- Shared residue at n=16 (42, 1560 pair): both c-values ≡ 20 (mod 1609). -/
theorem shared_residue_n16_a :
    c1Val 1560 42 % b1FromPair 1560 42 = ugp1_t ∧
    c1Val 42 1560 % b1FromPair 42 1560 = ugp1_t := by
  unfold c1Val b1FromPair ugp1_t; native_decide

end UgpLean
