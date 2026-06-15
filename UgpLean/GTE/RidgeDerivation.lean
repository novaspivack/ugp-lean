import Mathlib
import UgpLean.Core.RidgeDefs

/-!
# UgpLean.GTE.RidgeDerivation — GT-009: Ridge Offset Must Be a Power of 2

Upgrading GT-001 (CatAD) to CatAL. The CMCA tape has `2^n` binary cells; the ridge
offset `d` enters as `R_n = 2^n − d` with `d = 2^k` for tape-exponent `k < n`.
The Z₇ × Z₃ divisibility structure (`b₂ = 42 = 2 × 3 × 7`) then forces `k = 4`
uniquely, hence `d = 2^4 = 16` and `ridge n = 2^n − 16`.
-/

namespace GTE.RidgeDerivation

/-- Tape capacity minus ridge value is always a power of 2 at the canonical offset. -/
theorem ridge_offset_is_power_of_two (n : ℕ) :
    ∃ k : ℕ, UgpLean.ridge n = 2^n - 2^k := by
  refine ⟨4, ?_⟩
  unfold UgpLean.ridge
  have : (16 : ℕ) = 2^4 := by native_decide
  omega

/-- The canonical ridge offset `2^n − ridge n` equals `16 = 2^4` once `n ≥ 4`. -/
theorem ridge_offset_value (n : ℕ) (hn : 4 ≤ n) : 2^n - UgpLean.ridge n = 16 := by
  unfold UgpLean.ridge
  have hle : 16 ≤ 2^n := by
    calc (16 : ℕ) = 2^4 := by native_decide
      _ ≤ 2^n := Nat.pow_le_pow_right (by decide) hn
  omega

private theorem two_pow_sub_one_not_even (n : ℕ) (_hn : 2 ≤ n) : ¬ 2 ∣ 2^n - 1 := by
  intro h2
  have hpow : 2 ∣ 2^n := dvd_pow (by decide : (2 : ℕ) ∣ 2) (by omega)
  have hge : 1 ≤ 2^n := Nat.one_le_pow n 2 (by decide)
  have hsub := Nat.dvd_sub hpow h2
  have h1 : 2 ∣ 1 := by rw [Nat.sub_sub_self hge] at hsub; exact hsub
  exact absurd h1 (by decide)

/-- If `2 ∣ (2^n − 2^k)` with `n ≥ 2`, then `k ≥ 1`: the offset exponent is positive,
    so the offset `d = 2^k` is even (binary tape excludes odd offsets). -/
theorem ridge_offset_must_be_even (n k : ℕ) (hn : 2 ≤ n) (hk : k ≤ n)
    (h_div : 2 ∣ 2^n - 2^k) : 1 ≤ k := by
  by_contra h
  push Not at h
  have hk0 : k = 0 := by omega
  subst hk0
  simpa [pow_zero] using two_pow_sub_one_not_even n hn h_div

/-- At `n = 10`, `3 ∣ (2^10 − 2^k)` iff the exponent `k` is even. -/
theorem ridge_k_must_be_even_for_3_div :
    ∀ k : Fin 10, 3 ∣ (2^10 - 2^k.val) ↔ k.val % 2 = 0 := by
  native_decide

/-- At `n = 10`, `7 ∣ (2^10 − 2^k)` iff `k ≡ 1 (mod 3)`. -/
theorem ridge_k_mod3_for_7_div :
    ∀ k : Fin 10, 7 ∣ (2^10 - 2^k.val) ↔ k.val % 3 = 1 := by
  native_decide

/-- The unique admissible exponent below `10` is `4`. -/
theorem ridge_exponent_is_4 :
    ∀ k : Fin 10, (k.val % 3 = 1 ∧ k.val % 2 = 0 ∧ 0 < k.val) ↔ k.val = 4 := by
  native_decide

theorem ridge_offset_is_16 : (2 : ℕ)^4 = 16 := by native_decide

/-- At `n = 10`, only `k = 4` makes `R₁₀ = 2^10 − 2^k` divisible by `42 = 2 × 3 × 7`. -/
theorem ridge_divisibility_at_n10 :
    ∀ k : Fin 10, 42 ∣ (2^10 - 2^k.val) ↔ k.val = 4 := by
  native_decide

/-- GT-001 target: at `n = 10`, simultaneous divisibility by `7` and `3` forces `k = 4`. -/
theorem ridge_constant_from_gf7_z3 :
    ∀ k : ℕ, 1 ≤ k → k < 10 →
      ((7 ∣ (2^10 - 2^k) ∧ (3 : ℕ) ∣ (2^10 - 2^k)) ↔ k = 4) := by
  intro k hk1 hk10
  interval_cases k <;> simp

/-- `2` has multiplicative order `3` in `GF(7)^*`; the ridge offset is `2^(1 + 3)`. -/
theorem ridge_constant_is_2_pow_1_plus_ord7_2 :
    (2 : ZMod 7) ^ 3 = 1 ∧ (2 : ZMod 7) ^ 2 ≠ 1 ∧ (2 : ZMod 7) ≠ 1 ∧ (16 : ℕ) = 2 ^ 4 := by
  native_decide

private theorem ridge_divisible_by_42 (k : ℕ) (hk : k < 10) :
    42 ∣ (2^10 - 2^k) ↔ k = 4 := by
  interval_cases k <;> decide

/-- GT-009 bundle: unique power-of-2 exponent and ridge offset `16`. -/
theorem gt009_ridge_is_power_of_2 :
    (∃! k : ℕ, k < 10 ∧ 42 ∣ (2^10 - 2^k) ∧ 0 < k) ∧
    (∀ k : ℕ, k < 10 → ((42 ∣ (2^10 - 2^k) ∧ 0 < k) ↔ k = 4)) ∧
    (2 : ℕ)^4 = 16 := by
  refine ⟨?_, ?_, by native_decide⟩
  · refine ⟨4, ⟨by decide, (ridge_divisible_by_42 4 (by decide)).2 rfl, by decide⟩, ?_⟩
    intro k ⟨hk, h42, _hkpos⟩
    exact (ridge_divisible_by_42 k hk).1 h42
  · intro k hk
    constructor
    · intro ⟨h42, hkpos⟩
      exact (ridge_divisible_by_42 k hk).1 h42
    · intro h
      subst h
      exact ⟨(ridge_divisible_by_42 4 (by decide)).2 rfl, by decide⟩

/-- GT-001 upgraded: `ridge 10 = 1008` and the offset is the unique Z₇×Z₃ power of 2. -/
theorem gt001_gt009_ridge_closed :
    UgpLean.ridge 10 = 1008 ∧
    (∀ k : ℕ, 1 ≤ k → k < 10 →
      ((7 ∣ (2^10 - 2^k) ∧ (3 : ℕ) ∣ (2^10 - 2^k)) ↔ k = 4)) ∧
    (2 : ℕ)^4 = 16 := by
  refine ⟨UgpLean.ridge_10, ridge_constant_from_gf7_z3, by native_decide⟩

end GTE.RidgeDerivation
