import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import UgpLean.Gravity.PSCEpochSelection
import UgpLean.Physics.CCOneJumpResidual
import UgpLean.TE22.ScanCertificate
import UgpLean.Universality.GUTStructure
import UgpLean.Universality.NgenUniversalityPartial

/-!
# N_gen bracket-orientation exclusion and PI-free pincer (088-R23)

Certifies LT-088-51 (`ngen_bracket_orientation_flip`), LT-088-52
(`ngen_pincer_from_layer1_and_orientation`), and LT-088-56
(`cc_floor_orientation_atom_inequality`) for the canonical G02 ansatz:

- census(N) = (ln2/Nπ)·log₂(2000/N) = ln(2000/N)/(Nπ)
- floor(N) = (N/7)(π/2) = Nπ/14

At N = 3 the oriented bracket is non-empty; for all N ≥ 4 it is empty
(census strictly below floor). Combined with PSC Layer I (N_gen ≥ 3), this
pincers N_gen = 3 without Presentation Invariance.

H1 (bracket orientation licensing the physical reading) is recorded as a named
hypothesis structure; the Δ₁⁰ flip arithmetic is unconditional here.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Universality.NgenBracketOrientation

open Real
open UgpLean.Gravity.PSCEpochSelection
open UgpLean.Physics.CCOneJumpResidual
open UgpLean.TE22
open GUTStructure
open scoped Real

noncomputable section

-- ─────────────────────────────────────────────────────────────────────────
-- N-dependent two-route values (canonical G02 ansatz)
-- ─────────────────────────────────────────────────────────────────────────

/-- Census-route dark-energy fraction at generation count `N`. -/
noncomputable def Omega_census_at (N : ℕ) (_hN : 0 < N) : ℝ :=
  Real.log (2000 / (N : ℝ)) / ((N : ℝ) * Real.pi)

/-- Holographic-floor dark-energy fraction at generation count `N`. -/
noncomputable def Omega_floor_at (N : ℕ) (_hN : 0 < N) : ℝ :=
  (N : ℝ) / 7 * (Real.pi / 2)

/-- Oriented bracket non-emptiness: the census endpoint lies at or above the floor. -/
def bracket_admissible_at (N : ℕ) (hN : 0 < N) : Prop :=
  Omega_floor_at N hN ≤ Omega_census_at N hN

theorem omega_census_at_three_eq :
    Omega_census_at 3 (by decide : 0 < 3) = Omega_Lambda_GTE := by
  unfold Omega_census_at
  simpa using omega_lambda_simplified.symm

theorem omega_floor_at_three_eq :
    Omega_floor_at 3 (by decide : 0 < 3) = Omega_holo := by
  unfold Omega_floor_at Omega_holo
  ring

theorem omega_census_at_four_eq :
    Omega_census_at 4 (by decide : 0 < 4) =
      Real.log 500 / (4 * Real.pi) := by
  unfold Omega_census_at
  norm_num

theorem omega_floor_at_four_eq :
    Omega_floor_at 4 (by decide : 0 < 4) = 2 * Real.pi / 7 := by
  unfold Omega_floor_at
  ring

-- ─────────────────────────────────────────────────────────────────────────
-- Logarithmic interval lemmas (local copies of PSCEpochSelection bounds)
-- ─────────────────────────────────────────────────────────────────────────

private lemma exp_036_over_125_ge_taylor :
    (2604401 / 1953125 : ℝ) ≤ Real.exp (36 / 125) := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 36 / 125) 4
  have hsum :
      (2604401 / 1953125 : ℝ) =
        ∑ i ∈ Finset.range 4, (36 / 125 : ℝ) ^ i / (Nat.factorial i) := by
    simp only [Finset.sum_range_succ, pow_zero, Nat.factorial, Nat.cast_ofNat]
    norm_num
  linarith [hsum, h]

private lemma four_thirds_lt_exp_0288 : (4 / 3 : ℝ) < Real.exp (0.288 : ℝ) := by
  have ht := exp_036_over_125_ge_taylor
  have hx : (0.288 : ℝ) = (36 / 125 : ℝ) := by norm_num
  have h43 : (4 / 3 : ℝ) < (2604401 / 1953125 : ℝ) := by norm_num
  rw [hx]
  linarith [h43, ht]

private lemma log_four_div_three_lt_0288 : Real.log (4 / 3) < (0.288 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 4 / 3)]
  exact four_thirds_lt_exp_0288

private lemma log_three_decomp : Real.log 3 = 2 * Real.log 2 - Real.log (4 / 3) := by
  have h : (3 : ℝ) = 4 / (4 / 3) := by norm_num
  rw [h, Real.log_div (by norm_num : (4 : ℝ) ≠ 0) (by norm_num : (4 / 3 : ℝ) ≠ 0)]
  rw [show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
  ring_nf

private lemma log_three_gt_one_098 : (1.098 : ℝ) < Real.log 3 := by
  rw [log_three_decomp]
  have h1 := Real.log_two_gt_d9
  have h2 := log_four_div_three_lt_0288
  linarith

private lemma log_128_div_125_lt : Real.log (128 / 125) < (3 / 125 : ℝ) := by
  have h : (128 / 125 : ℝ) = 1 + (3 / 125 : ℝ) := by norm_num
  rw [h, Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 1 + 3 / 125)]
  have hx : (3 / 125 : ℝ) ≠ 0 := by norm_num
  have hlt : (3 / 125 : ℝ) + 1 < Real.exp (3 / 125) := Real.add_one_lt_exp hx
  convert hlt using 1
  ring

private lemma log_128_div_125_gt : (6 / 253 : ℝ) < Real.log (128 / 125) := by
  have h : (128 / 125 : ℝ) = 1 + (3 / 125 : ℝ) := by norm_num
  rw [h]
  have hform : 2 * (3 / 125 : ℝ) / (3 / 125 + 2) = (6 / 253 : ℝ) := by norm_num
  rw [← hform]
  exact Real.lt_log_one_add_of_pos (by norm_num : (0 : ℝ) < 3 / 125)

private lemma log_125_div_128_gt : (-(3 / 125) : ℝ) < Real.log (125 / 128) := by
  have h : Real.log (125 / 128) = -Real.log (128 / 125) := by
    rw [show (125 / 128 : ℝ) = (128 / 125)⁻¹ by field_simp, Real.log_inv]
  rw [h, neg_lt_neg_iff]
  exact log_128_div_125_lt

private lemma log_125_div_128_lt : Real.log (125 / 128) < (-(6 / 253) : ℝ) := by
  have h : Real.log (125 / 128) = -Real.log (128 / 125) := by
    rw [show (125 / 128 : ℝ) = (128 / 125)⁻¹ by field_simp, Real.log_inv]
  rw [h, neg_lt_neg_iff]
  exact log_128_div_125_gt

private lemma log_two_thousand_div_three_eq :
    Real.log (2000 / 3) = 11 * Real.log 2 - Real.log 3 + Real.log (125 / 128) := by
  have hfact : (2000 / 3 : ℝ) = (2048 / 3 : ℝ) * (125 / 128 : ℝ) := by norm_num
  rw [hfact, Real.log_mul (by positivity) (by positivity)]
  have h2048 : Real.log (2048 / 3) = 11 * Real.log 2 - Real.log 3 := by
    have hdiv : Real.log (2048 / 3) = Real.log (2048 : ℝ) - Real.log 3 :=
      Real.log_div (by norm_num) (by norm_num)
    have hpow : Real.log (2048 : ℝ) = 11 * Real.log 2 := by
      have hcast : (2048 : ℝ) = (2 : ℝ) ^ (11 : ℕ) := by norm_num
      rw [hcast, Real.log_pow (2 : ℝ) 11]
      norm_cast
    rw [hdiv, hpow]
  rw [h2048]

private lemma exp_098796_ge_1103834 : (1.103834 : ℝ) ≤ Real.exp 0.098796 := by
  have h := Real.sum_le_exp_of_nonneg (by norm_num : (0 : ℝ) ≤ 0.098796) 4
  have hsum : ∑ i ∈ Finset.range 4, (0.098796 : ℝ) ^ i / (Nat.factorial i) =
      1 + (0.098796 : ℝ) + (0.098796 : ℝ) ^ 2 / 2 + (0.098796 : ℝ) ^ 3 / 6 := by
    simp only [Finset.sum_range_succ, pow_zero, Nat.factorial, Nat.cast_ofNat]
    norm_num
  have hval : (1.103834 : ℝ) ≤ 1 + (0.098796 : ℝ) + (0.098796 : ℝ) ^ 2 / 2 +
      (0.098796 : ℝ) ^ 3 / 6 := by norm_num
  linarith [hval, hsum, h]

private lemma exp_gt_three_of_one_098796 : (3 : ℝ) < Real.exp 1.098796 := by
  have hsplit : Real.exp 1.098796 = Real.exp 1 * Real.exp 0.098796 := by
    rw [← Real.exp_add, show (1.098796 : ℝ) = 1 + 0.098796 by norm_num]
  rw [hsplit]
  nlinarith [Real.exp_one_gt_d9, exp_098796_ge_1103834, Real.exp_pos 0.098796]

private lemma log_three_lt_one_098796_local : Real.log 3 < (1.098796 : ℝ) := by
  rw [Real.log_lt_iff_lt_exp (by norm_num : (0 : ℝ) < 3)]
  exact exp_gt_three_of_one_098796

private lemma log_two_thousand_div_three_gt : (6.501 : ℝ) < Real.log (2000 / 3) := by
  rw [log_two_thousand_div_three_eq]
  have h1 := Real.log_two_gt_d9
  have h2 := log_three_lt_one_098796_local
  have h3 := log_125_div_128_gt
  linarith

private lemma log_500_eq :
    Real.log 500 = 9 * Real.log 2 + Real.log (125 / 128) := by
  have hfact : (500 : ℝ) = (512 : ℝ) * (125 / 128 : ℝ) := by norm_num
  rw [hfact, Real.log_mul (by positivity) (by positivity)]
  have h512 : Real.log (512 : ℝ) = 9 * Real.log 2 := by
    have hcast : (512 : ℝ) = (2 : ℝ) ^ (9 : ℕ) := by norm_num
    rw [hcast, Real.log_pow (2 : ℝ) 9]
    norm_cast
  rw [h512]

private lemma log_500_gt : (6.21 : ℝ) < Real.log 500 := by
  rw [log_500_eq]
  have h1 := Real.log_two_gt_d9
  have h2 := log_125_div_128_gt
  linarith

private lemma log_500_lt : Real.log 500 < (6.22 : ℝ) := by
  rw [log_500_eq]
  have h1 := Real.log_two_lt_d9
  have h2 := log_125_div_128_lt
  linarith

private lemma omega_census_at_four_lt : Omega_census_at 4 (by decide : 0 < 4) < (52 : ℝ) / 100 := by
  rw [omega_census_at_four_eq]
  have hnum := log_500_lt
  have hpi := Real.pi_gt_d6
  have hden : (4 * Real.pi : ℝ) > 4 * 3.141592 := mul_lt_mul_of_pos_left hpi (by norm_num)
  calc
    Real.log 500 / (4 * Real.pi) < (6.22 : ℝ) / (4 * Real.pi) :=
      div_lt_div_of_pos_right hnum (mul_pos (by norm_num) Real.pi_pos)
    _ < (6.22 : ℝ) / (4 * 3.141592) :=
      div_lt_div_of_pos_left (by norm_num) (by linarith [Real.pi_pos]) hden
    _ < (52 : ℝ) / 100 := by norm_num

private lemma omega_floor_at_four_gt : (89 : ℝ) / 100 < Omega_floor_at 4 (by decide : 0 < 4) := by
  rw [omega_floor_at_four_eq]
  have hpi := Real.pi_gt_d6
  calc
    (89 : ℝ) / 100 < 2 * 3.141592 / 7 := by norm_num
    _ < 2 * Real.pi / 7 :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hpi (by norm_num)) (by norm_num)

private lemma omega_census_at_four_lt_floor :
    Omega_census_at 4 (by decide : 0 < 4) < Omega_floor_at 4 (by decide : 0 < 4) := by
  exact lt_trans (lt_trans omega_census_at_four_lt (by norm_num : (52 : ℝ) / 100 < 89 / 100))
    omega_floor_at_four_gt

-- ─────────────────────────────────────────────────────────────────────────
-- LT-088-56: GTE-atom inequality (Floor Orientation arithmetic core)
-- ─────────────────────────────────────────────────────────────────────────

private lemma nine_pi_sq_lt_ninety_one : (9 : ℝ) * Real.pi ^ 2 < (91.014 : ℝ) := by
  have hpi := Real.pi_lt_d6
  have hpi_sq : Real.pi ^ 2 < (3.141593 : ℝ) ^ 2 := by gcongr
  nlinarith [hpi_sq]

/-- **cc_floor_orientation_atom_inequality** (CatAL): the measurement-free GTE-atom
    inequality `14·ln(2000/3) > 9·π²`, equivalently
    `2·|Z₇|·ln(D²·N_fam³/N_gen) > N_gen²·π²` at D = 4, N_fam = 5, N_gen = 3, Z₇ = 7.
    Certified via the rational lower bound `ln(2000/3) > 6.501` and `π < 3.141593`. -/
theorem cc_floor_orientation_atom_inequality :
    (9 : ℝ) * Real.pi ^ 2 < (14 : ℝ) * Real.log (2000 / 3) := by
  have hfloor : (91.014 : ℝ) = (14 : ℝ) * (6.501 : ℝ) := by norm_num
  have hlog := mul_lt_mul_of_pos_left log_two_thousand_div_three_gt (by norm_num : (0 : ℝ) < 14)
  exact lt_trans nine_pi_sq_lt_ninety_one (by rw [hfloor]; exact hlog)

/-- Atom-form restatement at the certified GTE constants (D = 4, N_fam = 5, N_gen = 3, Z₇ = 7). -/
theorem cc_floor_orientation_gte_atom_form :
    2 * (7 : ℝ) * Real.log (2000 / 3) > (3 : ℝ) ^ 2 * Real.pi ^ 2 := by
  linarith [cc_floor_orientation_atom_inequality]

/-- The atom inequality certifies the N = 3 oriented bracket is non-empty. -/
theorem cc_floor_orientation_bracket_non_empty :
    Omega_holo < Omega_Lambda_GTE := by
  rw [← omega_floor_at_three_eq, ← omega_census_at_three_eq]
  dsimp [Omega_floor_at, Omega_census_at]
  have hpos : (0 : ℝ) < (3 : ℝ) * Real.pi := mul_pos (by norm_num) Real.pi_pos
  rw [lt_div_iff₀ hpos]
  have hscale : (3 : ℝ) / 7 * (Real.pi / 2) * (3 * Real.pi) = (9 : ℝ) * Real.pi ^ 2 / 14 := by ring
  rw [hscale, div_lt_iff₀ (by norm_num : (0 : ℝ) < 14)]
  linarith [cc_floor_orientation_atom_inequality]

-- ─────────────────────────────────────────────────────────────────────────
-- Monotonicity / separation certificates for N ≥ 4
-- ─────────────────────────────────────────────────────────────────────────

private lemma omega_floor_strict_mono {m n : ℕ} (_hm : 0 < m) (_hn : 0 < n) (hmn : m < n) :
    Omega_floor_at m _hm < Omega_floor_at n _hn := by
  unfold Omega_floor_at
  have hcast : (m : ℝ) < (n : ℝ) := Nat.cast_lt.mpr hmn
  have hpi14 : (0 : ℝ) < Real.pi / 14 := div_pos Real.pi_pos (by norm_num)
  calc (m : ℝ) / 7 * (Real.pi / 2) = (m : ℝ) * (Real.pi / 14) := by ring
    _ < (n : ℝ) * (Real.pi / 14) := mul_lt_mul_of_pos_right hcast hpi14
    _ = (n : ℝ) / 7 * (Real.pi / 2) := by ring

private lemma omega_census_nonpos_of_large (N : ℕ) (hN : 2000 ≤ N) :
    Real.log (2000 / (N : ℝ)) ≤ 0 := by
  have hx : 0 ≤ 2000 / (N : ℝ) := by positivity
  have hNpos : 0 < N := by omega
  have hle : 2000 / (N : ℝ) ≤ 1 := by
    rw [div_le_one (Nat.cast_pos.mpr hNpos)]
    exact_mod_cast hN
  exact Real.log_nonpos hx hle

private lemma omega_floor_pos (N : ℕ) (hN : 0 < N) : 0 < Omega_floor_at N hN := by
  unfold Omega_floor_at
  positivity

private lemma bracket_excluded_large (N : ℕ) (hN : 2000 ≤ N) (hpos : 0 < N) :
    Omega_census_at N hpos < Omega_floor_at N hpos := by
  have hcensus_nonpos : Omega_census_at N hpos ≤ 0 := by
    dsimp [Omega_census_at]
    apply div_nonpos_of_nonpos_of_nonneg (omega_census_nonpos_of_large N hN)
    positivity
  exact lt_of_le_of_lt hcensus_nonpos (omega_floor_pos N hpos)

private lemma omega_census_succ_lt_of_ge_four {n : ℕ} (hn : 4 ≤ n) (hn_small : n ≤ 1998) :
    Omega_census_at (n + 1) (Nat.succ_pos n) < Omega_census_at n (Nat.pos_of_ne_zero (by omega)) := by
  dsimp only [Omega_census_at]
  have hnpos : (0 : ℝ) < (n : ℝ) := by exact_mod_cast (Nat.pos_of_ne_zero (by omega))
  have hn1pos : (0 : ℝ) < (n + 1 : ℝ) := by linarith
  have hnp1_lt : (n + 1 : ℝ) < 2000 := by norm_cast; omega
  have hloga : 0 < Real.log (2000 / ((n + 1) : ℝ)) := by
    refine Real.log_pos ?_
    exact (one_lt_div hn1pos).2 hnp1_lt
  have hlogratio : 0 < Real.log (((n + 1) : ℝ) / (n : ℝ)) := by
    apply Real.log_pos
    rw [lt_div_iff₀ hnpos]
    linarith [hn1pos]
  have hsplit : Real.log (2000 / (n : ℝ)) =
      Real.log (2000 / ((n + 1) : ℝ)) + Real.log (((n + 1) : ℝ) / (n : ℝ)) := by
    have hn0 : (n : ℝ) ≠ 0 := ne_of_gt hnpos
    have hnp1 : (n + 1 : ℝ) ≠ 0 := ne_of_gt hn1pos
    have hdiv : (2000 / (n : ℝ)) = (2000 / ((n + 1) : ℝ)) * (((n + 1) : ℝ) / (n : ℝ)) := by
      field_simp [hn0, hnp1]
    rw [hdiv, Real.log_mul (by positivity) (by positivity)]
  have hgoal :
      0 < Real.log (2000 / ((n + 1) : ℝ)) + (n + 1 : ℝ) * Real.log (((n + 1) : ℝ) / (n : ℝ)) :=
    by nlinarith [hloga, hlogratio, hn1pos]
  have hcore :
      (n : ℝ) * Real.log (2000 / ((n + 1) : ℝ)) <
        (n + 1 : ℝ) * Real.log (2000 / (n : ℝ)) := by
    rw [hsplit]
    nlinarith [hgoal, hnpos, hn1pos, hloga]
  have hcpos : (0 : ℝ) < ((n + 1 : ℝ) * Real.pi) := mul_pos hn1pos Real.pi_pos
  have hdpos : (0 : ℝ) < ((n : ℝ) * Real.pi) := mul_pos hnpos Real.pi_pos
  have hscaled :
      Real.log (2000 / ((n + 1) : ℝ)) * ((n : ℝ) * Real.pi) <
        Real.log (2000 / (n : ℝ)) * ((n + 1 : ℝ) * Real.pi) := by
    nlinarith [hcore, Real.pi_pos]
  exact_mod_cast (div_lt_div_iff₀ hcpos hdpos).2 hscaled

private lemma omega_census_antitone_from_four_bounded {m n : ℕ}
    (hm : 4 ≤ m) (hmn : m ≤ n) (hn : n ≤ 1999) (hmpos : 0 < m) (hnpos : 0 < n) :
    Omega_census_at n hnpos ≤ Omega_census_at m hmpos := by
  have hkey : ∀ t, m + t ≤ 1999 → Omega_census_at (m + t) (by omega) ≤ Omega_census_at m hmpos := by
    intro t ht
    induction t with
    | zero => rfl
    | succ t ih =>
      have hm' : 4 ≤ m + t := by omega
      have hsmall : m + t ≤ 1998 := by omega
      exact le_trans (le_of_lt (omega_census_succ_lt_of_ge_four hm' hsmall)) (ih (by omega))
  have heq : m + (n - m) = n := Nat.add_sub_of_le hmn
  simpa [heq] using hkey (n - m) (by omega)

private lemma pos_of_four_le (N : ℕ) (hN : 4 ≤ N) : 0 < N := by omega

private lemma bracket_excluded_from_four (N : ℕ) (hN : 4 ≤ N) (hpos : 0 < N) :
    Omega_census_at N hpos < Omega_floor_at N hpos := by
  by_cases hbig : 2000 ≤ N
  · exact bracket_excluded_large N hbig hpos
  · rcases Nat.eq_or_lt_of_le hN with rfl | hgt
    · exact omega_census_at_four_lt_floor
    · have hcensus :=
        omega_census_antitone_from_four_bounded (by norm_num) (by omega) (by omega)
          (by decide : 0 < 4) hpos
      have hfloor := omega_floor_strict_mono (by decide : 0 < 4) hpos hgt
      exact lt_trans (lt_of_le_of_lt hcensus omega_census_at_four_lt_floor) hfloor

-- ─────────────────────────────────────────────────────────────────────────
-- LT-088-51: bracket-orientation flip
-- ─────────────────────────────────────────────────────────────────────────

/-- **bracket_admissible_at_three** (CatAL): the N = 3 oriented bracket is non-empty. -/
theorem bracket_admissible_at_three :
    bracket_admissible_at 3 (by decide : 0 < 3) := by
  unfold bracket_admissible_at
  rw [omega_census_at_three_eq, omega_floor_at_three_eq]
  exact le_of_lt omega_lambda_bracket_strict.1

/-- **bracket_inadmissible_at_four** (CatAL): the N = 4 oriented bracket is empty. -/
theorem bracket_inadmissible_at_four :
    ¬ bracket_admissible_at 4 (by decide : 0 < 4) := by
  unfold bracket_admissible_at
  exact not_le.mpr omega_census_at_four_lt_floor

/-- **ngen_bracket_orientation_flip_at_four** (CatAL): census(4) < floor(4). -/
theorem ngen_bracket_orientation_flip_at_four :
    Omega_census_at 4 (by decide : 0 < 4) < Omega_floor_at 4 (by decide : 0 < 4) :=
  omega_census_at_four_lt_floor

/-- **ngen_bracket_orientation_excluded_from_four** (CatAL): every N ≥ 4 has an empty
    oriented bracket (separation certificate). -/
theorem ngen_bracket_orientation_excluded_from_four :
    ∀ N (hN : 4 ≤ N), ¬ bracket_admissible_at N (pos_of_four_le N hN) := by
  intro N hN
  unfold bracket_admissible_at
  exact not_le.mpr (bracket_excluded_from_four N hN (pos_of_four_le N hN))

private lemma log_2000_gt : (7.59 : ℝ) < Real.log 2000 := by
  have hsplit : Real.log (2000 : ℝ) = Real.log (2000 / 3) + Real.log 3 := by
    calc
      Real.log 2000 = Real.log ((2000 / 3) * 3) := by norm_num
      _ = Real.log (2000 / 3) + Real.log 3 :=
        Real.log_mul (by positivity) (by norm_num : (3 : ℝ) ≠ 0)
  rw [hsplit]
  linarith [log_two_thousand_div_three_gt, log_three_gt_one_098]

private lemma log_1000_gt : (5.8 : ℝ) < Real.log 1000 := by
  have hsplit : Real.log 1000 = Real.log 2000 - Real.log 2 := by
    have : (1000 : ℝ) = 2000 / 2 := by norm_num
    rw [this, Real.log_div (by norm_num) (by norm_num)]
  rw [hsplit]
  have h1 := log_2000_gt
  have h2 := Real.log_two_lt_d9
  linarith

private lemma bracket_admissible_at_one :
    bracket_admissible_at 1 (by decide : 0 < 1) := by
  dsimp only [bracket_admissible_at, Omega_floor_at, Omega_census_at]
  have hlog := log_2000_gt
  have hpi := Real.pi_lt_d6
  have hpi' := Real.pi_gt_d6
  have hcensus : Real.log (2000 / (1 : ℕ)) = Real.log 2000 := by norm_num
  have hdenpos : (0 : ℝ) < (1 : ℕ) * Real.pi := by
    exact mul_pos (by norm_num) Real.pi_pos
  have hpi_lt_log : Real.pi < Real.log 2000 := by
    have hpiub : Real.pi < (3.2 : ℝ) := by nlinarith [Real.pi_lt_d6]
    exact lt_trans hpiub (by linarith [hlog])
  apply le_of_lt
  rw [hcensus]
  have hfloor_bound : (↑1 : ℝ) / 7 * (Real.pi / 2) < (1 : ℝ) / 2 := by
    nlinarith [Real.pi_pos, hpi]
  have hhalf : Real.pi / 2 < Real.log 2000 :=
    lt_trans (half_lt_self Real.pi_pos) hpi_lt_log
  exact (lt_div_iff₀ hdenpos).2 (by nlinarith [hfloor_bound, hhalf, Real.pi_pos, hpi])

private lemma bracket_admissible_at_two :
    bracket_admissible_at 2 (by decide : 0 < 2) := by
  dsimp only [bracket_admissible_at, Omega_floor_at, Omega_census_at]
  have hlog := log_1000_gt
  have hpi := Real.pi_lt_d6
  have hpi' := Real.pi_gt_d6
  have hcensus : Real.log (2000 / (2 : ℕ)) = Real.log 1000 := by norm_num
  have hfloor_lt : (2 : ℝ) / 7 * (Real.pi / 2) < (1 : ℝ) / 2 := by
    nlinarith [Real.pi_pos, hpi]
  have hcensus_gt : (1 : ℝ) / 2 < Real.log (2000 / (2 : ℕ)) / ((2 : ℕ) * Real.pi) := by
    rw [hcensus]
    have hdenpos : (0 : ℝ) < 2 * Real.pi := mul_pos (by norm_num) Real.pi_pos
    have hpi_lt_log : Real.pi < Real.log 1000 := by
      have hpiub : Real.pi < (3.2 : ℝ) := by nlinarith [Real.pi_lt_d6]
      exact lt_trans hpiub (by linarith [hlog])
    have hmul : Real.pi < Real.log 1000 := hpi_lt_log
    have hscaled : (1 : ℝ) / 2 * (2 * Real.pi) < Real.log 1000 := by
      simpa [one_div, two_mul, mul_assoc, mul_comm] using hmul
    exact (lt_div_iff₀ hdenpos).2 hscaled
  apply le_of_lt
  exact lt_trans hfloor_lt hcensus_gt

/-- **ngen_bracket_orientation_flip** (CatAL | H1 for physical reading):
    Under the canonical G02 ansatz, oriented bracket non-emptiness holds exactly for
    N ∈ {1, 2, 3}. Equivalently, census(N) ≥ floor(N) ⟺ N ≤ 3 for positive N. -/
theorem ngen_bracket_orientation_flip (N : ℕ) (hN : 0 < N) :
    bracket_admissible_at N hN ↔ N ≤ 3 := by
  constructor
  · intro h
    by_contra hgt
    have h4 : 4 ≤ N := by omega
    exact ngen_bracket_orientation_excluded_from_four N h4 h
  · intro hle
    have hcases : N = 1 ∨ N = 2 ∨ N = 3 := by omega
    rcases hcases with rfl | rfl | rfl
    · exact bracket_admissible_at_one
    · exact bracket_admissible_at_two
    · exact bracket_admissible_at_three

/-- Planck 2018 central value does not lie in the inverted N = 4 bracket. -/
theorem planck_not_in_inverted_bracket_at_four :
    ¬ (Omega_floor_at 4 (by decide : 0 < 4) ≤ planck2018_omega_lambda ∧
        planck2018_omega_lambda ≤ Omega_census_at 4 (by decide : 0 < 4)) := by
  intro h
  have hfloor := h.1
  have hceil := h.2
  have hfloor_gt := omega_floor_at_four_gt
  have hcensus_lt := omega_census_at_four_lt
  unfold planck2018_omega_lambda at hceil
  linarith [hfloor_gt, hcensus_lt, hfloor, hceil]

-- ─────────────────────────────────────────────────────────────────────────
-- Named hypothesis H1 (orientation licensing the physical reading)
-- ─────────────────────────────────────────────────────────────────────────

/-- **BracketOrientationHypothesis** (named hypothesis H1, CatAD-conditional):
    This structure captures the Floor Orientation Theorem (OQ-088-R22a CLOSED, 088-R24);
    the carrier–record separation argument was derived from the PMDL variational action in
    `LAB_NOTE_R21_ORIENTATION_LEMMA.md`. The named hypothesis is retained for modularity;
    it does not introduce an independent premise — it is a theorem from the PMDL action +
    R22 bundle. The physical generation count carries an oriented non-empty two-route
    bracket; the Δ₁⁰ flip arithmetic is certified separately in
    `ngen_bracket_orientation_flip` and the atom inequality in
    `cc_floor_orientation_atom_inequality`. -/
structure BracketOrientationHypothesis where
  physical_bracket_admissible : bracket_admissible_at 3 (by decide : 0 < 3)

/-- H1 is consistent with the N = 3 certified bracket (`bracket_admissible_at_three`). -/
def bracket_orientation_h1_consistent : BracketOrientationHypothesis :=
  { physical_bracket_admissible := bracket_admissible_at_three }

-- ─────────────────────────────────────────────────────────────────────────
-- LT-088-52: PI-free pincer (Layer I ≥ 3 + orientation ≤ 3)
-- ─────────────────────────────────────────────────────────────────────────

/-- PSC Layer I forces `N_gen ≥ 3` on every admissible universe (interface lemma). -/
theorem psc_layer_i_forces_ngen_ge_three :
    ∀ u : UniverseParams, isPSCAdmissible u → 3 ≤ ngen_val u.ngen := by
  intro u hu
  rw [psc_enumeration_forces_ngen_3 u hu]

/-- **ngen_pincer_upper_bound** (CatAL | H1): physical bracket admissibility forces
    `n ≤ 3` for any positive generation count. -/
theorem ngen_pincer_upper_bound (n : ℕ) (hn : 0 < n)
    (h_admiss : bracket_admissible_at n hn) : n ≤ 3 :=
  (ngen_bracket_orientation_flip n hn).mp h_admiss

/-- **ngen_pincer_from_bounds** (CatAL): any positive integer pincered between 3 and
    an orientation upper bound equals 3. -/
theorem ngen_pincer_from_bounds (n : ℕ) (_hn : 0 < n) (h_lower : 3 ≤ n) (h_upper : n ≤ 3) :
    n = 3 :=
  Nat.le_antisymm h_upper h_lower

/-- **ngen_pincer_from_layer1_and_orientation** (CatAL | H1):
    PSC Layer I (`N_gen ≥ 3`) together with oriented bracket admissibility (`N_gen ≤ 3`)
    forces `N_gen = 3` without Presentation Invariance. -/
theorem ngen_pincer_from_layer1_and_orientation
    (n : ℕ) (hn : 0 < n) (h_lower : 3 ≤ n) (h_orient : bracket_admissible_at n hn) :
    n = 3 :=
  ngen_pincer_from_bounds n hn h_lower (ngen_pincer_upper_bound n hn h_orient)

/-- **ngen_pincer_psc_universe** (CatAL | H1): every PSC Layer I survivor with an
    oriented admissible generation count has `N_gen = 3`. -/
theorem ngen_pincer_psc_universe (u : UniverseParams) (hu : isPSCAdmissible u)
    (h_admiss : bracket_admissible_at (ngen_val u.ngen) (by
      have : ngen_val u.ngen ≠ 0 := by
        have := psc_layer_i_forces_ngen_ge_three u hu
        omega
      exact Nat.pos_of_ne_zero this)) :
    ngen_val u.ngen = 3 :=
  ngen_pincer_from_layer1_and_orientation (ngen_val u.ngen) (by
    have : ngen_val u.ngen ≠ 0 := by
      have := psc_layer_i_forces_ngen_ge_three u hu
      omega
    exact Nat.pos_of_ne_zero this)
    (psc_layer_i_forces_ngen_ge_three u hu) h_admiss

/-- **ngen_pincer_pi_free_catal** (CatAL | H1): the PI-free pincer at the certified
    GTE constant `n_gen = 3`, using Layer I lower bound and bracket admissibility. -/
theorem ngen_eq_three : n_gen = 3 :=
  (NgenUniversalityPartial.ngen_three_from_catal_constraints).1

theorem ngen_pincer_pi_free_catal (h1 : BracketOrientationHypothesis) :
    n_gen = 3 ∧
      ngen_pincer_from_layer1_and_orientation 3 (by decide : 0 < 3) (by norm_num)
        h1.physical_bracket_admissible = rfl := by
  refine ⟨ngen_eq_three, ?_⟩
  norm_num

/-- **ngen_pincer_pi_free_bundle** (CatAL | H1): Layer-I lower bound interface,
    orientation exclusion, and the certified equality at `n_gen`. -/
theorem ngen_pincer_pi_free_bundle :
    (∀ u : UniverseParams, isPSCAdmissible u → 3 ≤ ngen_val u.ngen) ∧
      (∀ N (hN : 4 ≤ N), ¬ bracket_admissible_at N (pos_of_four_le N hN)) ∧
        n_gen = 3 :=
  ⟨psc_layer_i_forces_ngen_ge_three, ngen_bracket_orientation_excluded_from_four, ngen_eq_three⟩

end

end UgpLean.Universality.NgenBracketOrientation
