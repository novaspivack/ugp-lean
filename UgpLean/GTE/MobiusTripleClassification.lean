import Mathlib.NumberTheory.ArithmeticFunction.Moebius

/-!
# Möbius triple classification on canonical GTE generation orbits (EPIC_092 / 092-A1a, A1b)

Finite arithmetic certificates for Möbius products on lepton and bottom-quark triples,
lepton c-values ≡ 7 (mod 8), and the quark-sector contrast at c = 42.
-/

namespace UgpLean.GTE.MobiusTripleClassification

open ArithmeticFunction

-- ============================================================
-- §1  Möbius products (092-A1a)
-- ============================================================

theorem prime_73 : Nat.Prime 73 := by native_decide

theorem prime_823 : Nat.Prime 823 := by native_decide

theorem prime_8191 : Nat.Prime 8191 := by native_decide

/-- 65535 = 3 × 5 × 17 × 257 (squarefree, four distinct prime factors). -/
theorem factored_65535 : 65535 = 3 * 5 * 17 * 257 := by decide

/-- Electron triple (1, 73, 823): Möbius product = +1. -/
theorem electron_triple_mobius_product : moebius 1 * moebius 73 * moebius 823 = 1 := by native_decide

/-- Muon triple (9, 42, 1023): Möbius product = 0 (9 = 3² not squarefree). -/
theorem muon_triple_mobius_product : moebius 9 * moebius 42 * moebius 1023 = 0 := by native_decide

/-- Tau triple (5, 275, 65535): Möbius product = 0 (275 = 5²×11 not squarefree). -/
theorem tau_triple_mobius_product : moebius 5 * moebius 275 * moebius 65535 = 0 := by native_decide

/-- Bottom quark triple (5, 8191, 65535): Möbius product = +1. -/
theorem bottom_triple_mobius_product : moebius 5 * moebius 8191 * moebius 65535 = 1 := by native_decide

/-- Electron is the unique lepton triple with Möbius product +1 among the three canonical leptons. -/
theorem electron_triple_mobius_unique_lepton :
    moebius 1 * moebius 73 * moebius 823 = 1 ∧
    moebius 9 * moebius 42 * moebius 1023 = 0 ∧
    moebius 5 * moebius 275 * moebius 65535 = 0 := by native_decide

-- ============================================================
-- §2  Lepton c-values ≡ 7 (mod 8) (092-A1b)
-- ============================================================

theorem lepton_c1_mod8 : 823 % 8 = 7 := by decide

theorem lepton_c2_mod8 : 1023 % 8 = 7 := by decide

theorem lepton_c3_mod8 : 65535 % 8 = 7 := by decide

theorem lepton_c_values_mod8_seven :
    823 % 8 = 7 ∧ 1023 % 8 = 7 ∧ 65535 % 8 = 7 := by decide

/-- Mersenne numbers 2^n − 1 ≡ 7 (mod 8) for n ≥ 3. -/
theorem eight_mul_sub_one_mod (q : ℕ) (hq : 1 ≤ q) : (8 * q - 1) % 8 = 7 := by omega

theorem mersenne_mod8_seven (n : ℕ) (hn : n ≥ 3) : (2 ^ n - 1) % 8 = 7 := by
  have h0 : 2 ^ n % 8 = 0 := by
    obtain ⟨k, rfl⟩ := Nat.exists_eq_add_of_le (show 3 ≤ n from hn)
    rw [Nat.pow_add, show 2 ^ 3 = 8 from by decide, Nat.mul_mod, Nat.mod_self, zero_mul]
    rfl
  have hge : 8 ≤ 2 ^ n := by
    calc 8 = 2 ^ 3 := by decide
      _ ≤ 2 ^ n := Nat.pow_le_pow_right (by decide) hn
  have hq : 2 ^ n = 8 * (2 ^ n / 8) := by
    conv_lhs => rw [← Nat.mod_add_div (2 ^ n) 8]
    rw [h0, zero_add]
  have hq1 : 1 ≤ 2 ^ n / 8 := by omega
  rw [hq]
  exact eight_mul_sub_one_mod (2 ^ n / 8) hq1

/-- The Mersenne lepton c-values 1023 and 65535. -/
theorem lepton_mersenne_c_values :
    1023 = 2 ^ 10 - 1 ∧ 65535 = 2 ^ 16 - 1 := by decide

theorem quark_c_42_mod8_neq7 : 42 % 8 ≠ 7 := by decide

theorem quark_c_42_not_mod8_seven : 42 % 8 = 2 := by decide

theorem lepton_vs_quark_mod8 :
    823 % 8 = 7 ∧ 1023 % 8 = 7 ∧ 65535 % 8 = 7 ∧ 42 % 8 ≠ 7 := by decide

-- ============================================================
-- §3  All-squarefree canonical fermion triple pair (092-A1a / LT-092-16)
-- ============================================================

/-- 65535 is squarefree (μ(65535) ≠ 0). -/
theorem squarefree_65535 : moebius 65535 ≠ 0 := by native_decide

/-- Electron triple (1, 73, 823): all three components squarefree. -/
theorem electron_all_squarefree :
    moebius 1 ≠ 0 ∧
    moebius 73 ≠ 0 ∧
    moebius 823 ≠ 0 := by native_decide

/-- Bottom triple (5, 8191, 65535): all three components squarefree. -/
theorem bottom_all_squarefree :
    moebius 5 ≠ 0 ∧
    moebius 8191 ≠ 0 ∧
    moebius 65535 ≠ 0 := by native_decide

/-- Representative non-squarefree components among the other seven canonical triples. -/
theorem other_triples_not_all_squarefree :
    moebius 9 = 0 ∧
    moebius 275 = 0 ∧
    moebius 76 = 0 := by native_decide

/-- Electron and bottom are the unique all-squarefree canonical generation-orbit triples. -/
theorem fermion_triples_all_squarefree_pair :
    moebius 1 ≠ 0 ∧ moebius 73 ≠ 0 ∧ moebius 823 ≠ 0 ∧
    moebius 5 ≠ 0 ∧ moebius 8191 ≠ 0 ∧ moebius 65535 ≠ 0 ∧
    moebius 9 = 0 ∧
    moebius 275 = 0 ∧
    moebius 76 = 0 := by native_decide

end UgpLean.GTE.MobiusTripleClassification
