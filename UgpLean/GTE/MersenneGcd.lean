import Mathlib
import UgpLean.GTE.UpdateMap

/-!
# UgpLean.GTE.MersenneGcd — The Mersenne GCD Identity (from Mathlib)

Proves: gcd(2^a - 1, 2^b - 1) = 2^gcd(a,b) - 1

This is a direct corollary of Mathlib's `Nat.pow_sub_one_gcd_pow_sub_one`,
which proves the general identity gcd(a^b - 1, a^c - 1) = a^gcd(b,c) - 1.

This eliminates the `mersenne_gcd_identity` axiom in UpdateMap.lean.
-/

namespace UgpLean

/-- The Mersenne GCD identity: gcd(2^a - 1, 2^b - 1) = 2^gcd(a,b) - 1.

    This is the a=2 case of Mathlib's Nat.pow_sub_one_gcd_pow_sub_one.
    No custom axioms required. -/
theorem mersenne_gcd_identity_proved (a b : ℕ) :
    Nat.gcd (2^a - 1) (2^b - 1) = 2^(Nat.gcd a b) - 1 :=
  Nat.pow_sub_one_gcd_pow_sub_one 2 a b

/-- Corollary: if gcd(a,b) > 1, then gcd(2^a-1, 2^b-1) > 1. -/
theorem mersenne_entanglement_proved (a b : ℕ)
    (hgcd : 1 < Nat.gcd a b) :
    1 < Nat.gcd (2^a - 1) (2^b - 1) := by
  rw [mersenne_gcd_identity_proved a b]
  have h2 : 2 ≤ Nat.gcd a b := hgcd
  have : 2^2 ≤ 2^(Nat.gcd a b) := Nat.pow_le_pow_right (by norm_num) h2
  have hpow : 1 ≤ 2^(Nat.gcd a b) := Nat.one_le_pow _ _ (by norm_num)
  omega

/-- Specific case: gcd(2^10 - 1, 2^16 - 1) = 3, proved from the identity. -/
theorem mersenne_gcd_10_16_proved :
    Nat.gcd (2^10 - 1) (2^16 - 1) = 3 := by
  rw [mersenne_gcd_identity_proved 10 16]
  native_decide

end UgpLean
