import Mathlib
import Mathlib.NumberTheory.LegendreSymbol.ZModChar
import UgpLean.Polynomial.GoldenQuadratic
import UgpLean.Polynomial.EisensteinIdentities
import UgpLean.MassRelations.HiggsQuartic

/-!
# Biquadratic compositum of the golden and Eisenstein master quadratics

The discriminants `disc(x²+x−1) = +5 = N_fam` and `disc(x²+x+1) = −3 = −N_gen`
generate the biquadratic field `K = ℚ(√−3, √5)` of conductor `15 = N_gen · N_fam`.

The corpus alphabet class (split in `ℤ[ω]`, inert in `ℤ[φ]`) is the Artin condition
`q ≡ 7, 13 (mod 15)`. Complete splitting in `K` is `q ≡ 1, 4 (mod 15)`.

All theorems: zero sorry, zero custom axioms.
-/

namespace UgpLean.Polynomial.BiquadraticCompositum

open UgpLean.Polynomial.GoldenQuadratic
open UgpLean.Polynomial.EisensteinIdentities
open UgpLean.MassRelations.HiggsQuartic

instance : Fact (Nat.Prime 3) := ⟨by decide⟩

def n_fam : ℕ := 5

def biquadraticConductor : ℕ := 15

theorem biquadratic_conductor_identity :
    biquadraticConductor = n_gen * n_fam ∧
    biquadraticConductor = 3 * 5 ∧
    n_gen = 3 ∧ n_fam = 5 := by
  unfold biquadraticConductor n_gen n_fam
  norm_num

-- ════════════════════════════════════════════════════════════════
-- §1  Eisenstein master quadratic (mirror of `exists_golden_root_iff_square_five`)
-- ════════════════════════════════════════════════════════════════

private lemma four_ne_zero_zmod_prime {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) : (4 : ZMod q) ≠ 0 := by
  intro h0
  have h4dvd : q ∣ 4 := (ZMod.natCast_eq_zero_iff 4 q).mp h0
  rcases h4dvd with ⟨k, hk⟩
  have hk' : q * k = 4 := by linarith [hk]
  rcases k with _ | _ | k
  · norm_num at hk'
  · have hq4 : q = 4 := by linarith [hk']
    subst hq4
    exact absurd Fact.out (by decide : ¬ Nat.Prime 4)
  · have hkmul : q * (k + 2) = 4 := by simpa using hk'
    by_cases hk0 : k = 0
    · subst hk0
      have : q = 2 := by linarith [hkmul]
      exact hq2 this
    · have hqge : 2 ≤ q := Nat.Prime.two_le Fact.out
      have hkge : 3 ≤ k + 2 := by omega
      nlinarith

private lemma two_ne_zero_zmod_prime {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h0
  have h2 : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h0
  have h2q : q = 2 := (Nat.prime_dvd_prime_iff_eq Fact.out (by decide : Nat.Prime 2)).mp h2
  exact hq2 h2q

lemma eisenstein_root_add_one_eq {q : ℕ} (x : ZMod q) :
    (x ^ 2 + x + 1 = 0) ↔ (x ^ 2 + x - (-1 : ZMod q) = 0) := by
  constructor <;> intro h <;> convert h using 1 <;> ring

theorem exists_eisenstein_root_iff_square_minus_three
    {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3) (hq2 : q ≠ 2) :
    (∃ x : ZMod q, x ^ 2 + x + 1 = 0) ↔ IsSquare ((-3 : ℤ) : ZMod q) := by
  have h2 := two_ne_zero_zmod_prime hq2
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨2 * x + 1, ?_⟩
    have hx' : x ^ 2 + x - (-1 : ZMod q) = 0 := by convert hx using 1; ring
    have h_root : x ^ 2 + x = -1 := sub_eq_zero.mp hx'
    have h_eq : (2 * x + 1) * (2 * x + 1) = ((-3 : ℤ) : ZMod q) := by
      calc (2 * x + 1) * (2 * x + 1)
        _ = (2 * x + 1) ^ 2 := by ring
        _ = 4 * (x ^ 2 + x) + 1 := by ring
        _ = ((-3 : ℤ) : ZMod q) := by norm_num [h_root]
    exact h_eq.symm
  · rintro ⟨s, hs⟩
    set y := (s - 1) / 2
    refine ⟨y, ?_⟩
    have hs' : s * s = ((-3 : ℤ) : ZMod q) := hs.symm
    have h2y : 2 * y + 1 = s := by
      dsimp [y]
      calc 2 * y + 1
        _ = 2 * ((s - 1) / 2) + 1 := rfl
        _ = s - 1 + 1 := by rw [mul_div_cancel₀ _ h2]
        _ = s := by ring
    have h4 : 4 * (y ^ 2 + y + 1) = 0 := by
      calc 4 * (y ^ 2 + y + 1)
        _ = (2 * y + 1) ^ 2 + 3 := by ring
        _ = s ^ 2 + 3 := by rw [h2y]
        _ = 0 := by rw [pow_two, hs']; ring
    rcases mul_eq_zero.mp h4 with h4zero | hy
    · exact absurd h4zero (four_ne_zero_zmod_prime hq2)
    · exact hy

private lemma neg_three_ne_zero {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3) : ((-3 : ℤ) : ZMod q) ≠ 0 :=
  show ((-3 : ℤ) : ZMod q) ≠ 0 from by
    intro h0
    have h3z : (3 : ZMod q) = 0 := by
      have : (3 : ZMod q) = -((-3 : ℤ) : ZMod q) := by ring
      rw [this, h0, neg_zero]
    exact hq3 ((Nat.prime_dvd_prime_iff_eq Fact.out (by decide : Nat.Prime 3)).mp
      ((ZMod.natCast_eq_zero_iff 3 q).mp h3z))

private lemma isSquare_minus_three_iff_legendre_one
    {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3) :
    IsSquare ((-3 : ℤ) : ZMod q) ↔ legendreSym q (-3) = 1 := by
  have hneg : (( -3 : ℤ) : ZMod q) ≠ 0 := neg_three_ne_zero hq3
  constructor
  · intro h
    rw [legendreSym.eq_one_iff (p := q) (a := (-3 : ℤ)) hneg]
    exact h
  · intro h
    rw [← legendreSym.eq_one_iff (p := q) (a := (-3 : ℤ)) hneg]
    exact h

private lemma isSquare_mod_three_iff_residue {q : ℕ} (hq0 : (q : ZMod 3) ≠ 0) :
    IsSquare (q : ZMod 3) ↔ q % 3 = 1 := by
  rw [← ZMod.natCast_mod q 3]
  have hbound : q % 3 < 3 := Nat.mod_lt q (by decide : 0 < 3)
  interval_cases hres : q % 3
  · rw [← ZMod.natCast_mod q 3] at hq0
    simp [hres] at hq0
  all_goals { decide }

private lemma chi4_mul_neg_one_pow_div_two {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) :
    (ZMod.χ₄ q : ℤ) * (-1 : ℤ) ^ (q / 2) = 1 := by
  have hq1 : q % 2 = 1 := by omega
  rw [ZMod.χ₄_eq_neg_one_pow hq1, ← pow_two, sq_neg_one, one_pow]

private lemma legendreSym_q_neg_three_eq_legendreSym_three_q
    {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3) (hq2 : q ≠ 2) :
    legendreSym q (-3) = legendreSym 3 q := by
  have hQR := legendreSym.quadratic_reciprocity' (p := 3) (q := q) (by decide) hq2
  have hexp : 3 / 2 * (q / 2) = q / 2 := by norm_num
  calc legendreSym q (-3)
    _ = legendreSym q (-1) * legendreSym q 3 := by
      rw [← legendreSym.mul (p := q), show (-3 : ℤ) = (-1) * 3 by ring]
    _ = legendreSym q (-1) * ((-1 : ℤ) ^ (q / 2) * legendreSym 3 q) := by
      congr 1
      norm_cast at hQR ⊢
      rw [hQR, hexp]
    _ = legendreSym 3 q * (legendreSym q (-1) * (-1 : ℤ) ^ (q / 2)) := by ring
    _ = legendreSym 3 q := by
      rw [legendreSym.at_neg_one hq2, chi4_mul_neg_one_pow_div_two hq2, mul_one]

theorem master_eisenstein_split_iff_mod3
    {q : ℕ} [Fact q.Prime] (hq3 : q ≠ 3) (hq2 : q ≠ 2) :
    ((∃ x : ZMod q, x ^ 2 + x + 1 = 0) ↔ IsSquare ((-3 : ℤ) : ZMod q)) ∧
      (IsSquare ((-3 : ℤ) : ZMod q) ↔ q % 3 = 1) := by
  constructor
  · exact exists_eisenstein_root_iff_square_minus_three hq3 hq2
  · have hleg := isSquare_minus_three_iff_legendre_one hq3
    have hq0 : (q : ZMod 3) ≠ 0 := by
      intro h0
      have h3dvd : 3 ∣ q := (ZMod.natCast_eq_zero_iff q 3).mp h0
      have : q = 3 := ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 3) Fact.out).mp h3dvd).symm
      exact hq3 this
    have h3q : legendreSym 3 q = 1 ↔ IsSquare (q : ZMod 3) :=
      legendreSym.eq_one_iff' (p := 3) hq0
    have hres := isSquare_mod_three_iff_residue hq0
    constructor
    · intro h
      rw [hleg, legendreSym_q_neg_three_eq_legendreSym_three_q hq3 hq2, h3q] at h
      exact hres.mp h
    · intro h
      rw [hleg, legendreSym_q_neg_three_eq_legendreSym_three_q hq3 hq2, h3q]
      exact hres.mpr h

-- ════════════════════════════════════════════════════════════════
-- §2  Mod-15 residue characterization
-- ════════════════════════════════════════════════════════════════

theorem residue_alphabet_class_mod15 (r : Fin 15) :
    (r.val % 3 = 1 ∧ (r.val % 5 = 2 ∨ r.val % 5 = 3)) ↔
      r.val % 15 = 7 ∨ r.val % 15 = 13 := by
  fin_cases r <;> decide

theorem residue_complete_split_mod15 (r : Fin 15) :
    (r.val % 3 = 1 ∧ (r.val % 5 = 1 ∨ r.val % 5 = 4)) ↔
      r.val % 15 = 1 ∨ r.val % 15 = 4 := by
  fin_cases r <;> decide

-- ════════════════════════════════════════════════════════════════
-- §3  Φ₆ stability on the GTE ladder
-- ════════════════════════════════════════════════════════════════

theorem phi6_ladder_values :
    phi6 2 = 3 ∧
    phi6 3 = 7 ∧
    phi6 4 = 13 ∧
    phi6 5 = 21 ∧
    phi6 7 = 43 ∧
    phi6 9 = 73 ∧
    phi6 6 = 31 ∧
    phi6 8 = 57 := by
  unfold phi6
  norm_num

theorem phi6_ladder_prime_residues :
    (7 : ℕ) % 15 = 7 ∧
    (13 : ℕ) % 15 = 13 ∧
    (43 : ℕ) % 15 = 13 ∧
    (73 : ℕ) % 15 = 13 ∧
    (31 : ℕ) % 15 = 1 ∧
    (57 : ℕ) % 15 = 12 := by
  norm_num

theorem phi6_ladder_rungs_in_alphabet_class :
    ((7 : ℕ) % 15 = 7 ∨ (7 : ℕ) % 15 = 13) ∧
    ((13 : ℕ) % 15 = 7 ∨ (13 : ℕ) % 15 = 13) ∧
    ((43 : ℕ) % 15 = 7 ∨ (43 : ℕ) % 15 = 13) ∧
    ((73 : ℕ) % 15 = 7 ∨ (73 : ℕ) % 15 = 13) := by
  norm_num

theorem phi6_gap_six_not_alphabet :
    (31 : ℕ) % 15 = 1 ∧
    ¬ ((31 : ℕ) % 15 = 7 ∨ (31 : ℕ) % 15 = 13) := by
  norm_num

theorem phi6_gap_eight_composite :
    57 = 3 * 19 ∧ ¬ Nat.Prime 57 := by
  constructor
  · norm_num
  · decide

theorem phi6_residue_mod5_table :
    phi6 2 % 5 = 3 ∧
    phi6 3 % 5 = 2 ∧
    phi6 4 % 5 = 3 ∧
    phi6 5 % 5 = 1 ∧
    phi6 6 % 5 = 1 ∧
    phi6 7 % 5 = 3 ∧
    phi6 8 % 5 = 2 ∧
    phi6 9 % 5 = 3 := by
  unfold phi6
  norm_num

private theorem phi6_mod5_inert_of_residue {r : ℕ} (hr2 : r = 2 ∨ r = 3 ∨ r = 4) :
    phi6 r % 5 ≠ 1 ∧ phi6 r % 5 ≠ 4 := by
  rcases hr2 with h2 | h3 | h4
  · subst h2; decide
  · subst h3; decide
  · subst h4; decide

theorem phi6_ladder_mod5_inert :
    phi6 2 % 5 = 3 ∧
    phi6 3 % 5 = 2 ∧
    phi6 4 % 5 = 3 ∧
    phi6 7 % 5 = 3 ∧
    phi6 9 % 5 = 3 ∧
    phi6 2 % 5 ≠ 1 ∧ phi6 2 % 5 ≠ 4 ∧
    phi6 3 % 5 ≠ 1 ∧ phi6 3 % 5 ≠ 4 ∧
    phi6 4 % 5 ≠ 1 ∧ phi6 4 % 5 ≠ 4 ∧
    phi6 7 % 5 ≠ 1 ∧ phi6 7 % 5 ≠ 4 ∧
    phi6 9 % 5 ≠ 1 ∧ phi6 9 % 5 ≠ 4 := by
  unfold phi6
  norm_num

theorem phi6_stability_class_lemma :
    phi6_ladder_values ∧
    phi6_ladder_prime_residues ∧
    phi6_ladder_rungs_in_alphabet_class ∧
    phi6_gap_six_not_alphabet ∧
    phi6_gap_eight_composite ∧
    phi6_residue_mod5_table ∧
    phi6_ladder_mod5_inert ∧
    (Nat.Prime 7 ∧ Nat.Prime 13 ∧ Nat.Prime 43 ∧ Nat.Prime 73) ∧
    (Nat.Prime 31 ∧ ¬ Nat.Prime 21) := by
  refine ⟨phi6_ladder_values, phi6_ladder_prime_residues, phi6_ladder_rungs_in_alphabet_class,
    phi6_gap_six_not_alphabet, phi6_gap_eight_composite, phi6_residue_mod5_table,
    phi6_ladder_mod5_inert, ?_, ?_⟩
  · exact ⟨by decide, by decide, by decide, by decide⟩
  · exact ⟨by decide, by decide⟩

private theorem mod15_alphabet_residue_split_eisenstein {q : ℕ}
    (h : q % 15 = 7 ∨ q % 15 = 13) : q % 3 = 1 := by
  rcases h with h7 | h13 <;> omega

private theorem mod15_alphabet_residue_inert_golden {q : ℕ}
    (h : q % 15 = 7 ∨ q % 15 = 13) : q % 5 ≠ 1 ∧ q % 5 ≠ 4 := by
  rcases h with h7 | h13 <;> omega

private theorem mod15_complete_split_residue {q : ℕ} (h : q % 15 = 1 ∨ q % 15 = 4) :
    q % 3 = 1 ∧ (q % 5 = 1 ∨ q % 5 = 4) := by
  rcases h with h1 | h4 <;> omega

theorem biquadratic_compositum_alphabet_class :
    biquadratic_conductor_identity ∧
    (∀ r : Fin 15,
      (r.val % 3 = 1 ∧ (r.val % 5 = 2 ∨ r.val % 5 = 3)) ↔
        r.val % 15 = 7 ∨ r.val % 15 = 13) ∧
    (∀ r : Fin 15,
      (r.val % 3 = 1 ∧ (r.val % 5 = 1 ∨ r.val % 5 = 4)) ↔
        r.val % 15 = 1 ∨ r.val % 15 = 4) ∧
    (∀ {q : ℕ} [Fact q.Prime], q ≠ 3 → q ≠ 5 → q ≠ 2 →
      (q % 15 = 7 ∨ q % 15 = 13) →
        ((∃ x : ZMod q, x ^ 2 + x + 1 = 0) ∧
          ¬ (∃ x : ZMod q, x ^ 2 + x = 1))) ∧
    (∀ {q : ℕ} [Fact q.Prime], q ≠ 3 → q ≠ 5 → q ≠ 2 →
      (q % 15 = 1 ∨ q % 15 = 4) →
        ((∃ x : ZMod q, x ^ 2 + x + 1 = 0) ∧
          (∃ x : ZMod q, x ^ 2 + x = 1))) ∧
    (∀ {q : ℕ} [Fact q.Prime], q ≠ 3 → q ≠ 2 →
      ((∃ x : ZMod q, x ^ 2 + x + 1 = 0) ↔ IsSquare ((-3 : ℤ) : ZMod q)) ∧
        (IsSquare ((-3 : ℤ) : ZMod q) ↔ q % 3 = 1)) ∧
    (∀ {q : ℕ} [Fact q.Prime], q ≠ 5 → q ≠ 2 →
      ((∃ x : ZMod q, x ^ 2 + x = 1) ↔ IsSquare (5 : ZMod q)) ∧
        (IsSquare (5 : ZMod q) ↔ q % 5 = 1 ∨ q % 5 = 4)) := by
  refine ⟨biquadratic_conductor_identity, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · intro r; exact residue_alphabet_class_mod15 r
  · intro r; exact residue_complete_split_mod15 r
  · intro q _ hq3 hq5 hq2 hmod
    have h3 := mod15_alphabet_residue_split_eisenstein hmod
    have heis := (master_eisenstein_split_iff_mod3 (q := q) hq3 hq2).2.mpr h3
    have hnoroot : ¬ ∃ x : ZMod q, x ^ 2 + x = 1 := by
      intro hroot
      rcases hroot with ⟨x, hx⟩
      have his : IsSquare (5 : ZMod q) :=
        (master_quadratic_split_iff_qr5 (q := q) hq5 hq2).1.mp ⟨x, hx⟩
      have : q % 5 = 1 ∨ q % 5 = 4 :=
        (master_quadratic_split_iff_qr5 (q := q) hq5 hq2).2.mpr his
      omega
    exact ⟨⟨_, (master_eisenstein_split_iff_mod3 (q := q) hq3 hq2).1.mpr heis⟩, hnoroot⟩
  · intro q _ hq3 hq5 hq2 hmod
    have hsplit := mod15_complete_split_residue hmod
    have heis := (master_eisenstein_split_iff_mod3 (q := q) hq3 hq2).2.mpr hsplit.1
    rcases hsplit.2 with h5 | h5
    · have hs := (master_quadratic_split_iff_qr5 (q := q) hq5 hq2).2.mp (Or.inl h5)
      exact ⟨⟨_, (master_eisenstein_split_iff_mod3 (q := q) hq3 hq2).1.mpr heis⟩,
        (master_quadratic_split_iff_qr5 (q := q) hq5 hq2).1.mpr hs⟩
    · have hs := (master_quadratic_split_iff_qr5 (q := q) hq5 hq2).2.mp (Or.inr h5)
      exact ⟨⟨_, (master_eisenstein_split_iff_mod3 (q := q) hq3 hq2).1.mpr heis⟩,
        (master_quadratic_split_iff_qr5 (q := q) hq5 hq2).1.mpr hs⟩
  · intro q _ hq3 hq2
    exact master_eisenstein_split_iff_mod3 hq3 hq2
  · intro q _ hq5 hq2
    exact master_quadratic_split_iff_qr5 hq5 hq2

end UgpLean.Polynomial.BiquadraticCompositum
