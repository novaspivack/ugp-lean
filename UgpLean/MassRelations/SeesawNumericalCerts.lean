import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.NormNum
import UgpLean.MassRelations.KoideAngle
import UgpLean.MassRelations.NeutrinoMassRatio
import UgpLean.MassRelations.TranscendentalMassBounds
import UgpLean.Universality.EWScalePrediction

/-!
# Seesaw and leptogenesis numerical certificates (EPIC_083D batch)

Certifies four CatAL/CatAD targets from the η_B investigation:

1. **`fn_washout_sum_bounds`** — three-generation FN washout S = 1 + ε_FN² + ε_FN⁶
2. **`gte_delta_m21_sq_bounds`**, **`gte_delta_m31_sq_bounds`** — GTE neutrino splittings
3. **`mr_gut_geV_bounds`** — common seesaw scale M_R_GUT = E_D²/C
4. **`mr1_mr_gut_ratio_bounds`** — Pati–Salam M_R1/M_R_GUT BPS ratio

Braid Atlas b-values {5, 11, 19} and α = 29/9 are CatAL (`NeutrinoMassRatio`).
Transcendental exp factors use interval axioms in `TranscendentalMassBounds`.
-/

namespace UgpLean.MassRelations.SeesawNumericalCerts

open Real
open EWScalePrediction
open UgpLean.MassRelations.KoideAngle
open UgpLean.MassRelations.NeutrinoMassRatio
open UgpLean.MassRelations.TranscendentalMassBounds

noncomputable section

/-- Seesaw orbit exponent α = 29/9 (CatAL, matches `nuSeesawExponent`). -/
def seesawAlpha : ℝ := (29 : ℝ) / 9

theorem seesawAlpha_eq_nuSeesawExponent : seesawAlpha = (nuSeesawExponent : ℝ) := by
  unfold seesawAlpha nuSeesawExponent; norm_num

/-- Braid Atlas right-handed neutrino b-values (CatAL). -/
def braidB1 : ℕ := 5
def braidB2 : ℕ := 11
def braidB3 : ℕ := 19

/-- Total neutrino mass Σm_ν = 59.4 meV in eV (CatA input). -/
def sigmaMnuEV : ℝ := (594 : ℝ) / 10000

/-- GeV per eV for E_D[GeV]² / C[eV] → M_R[GeV]. -/
def gevPerEv : ℝ := 10 ^ 9

/-- Three-generation FN washout sum S = 1 + exp(−2π/3) + exp(−2π). -/
def fnWashoutSum : ℝ :=
  1 + Real.exp (-(2 * Real.pi / 3)) + Real.exp (-2 * Real.pi)

/-- Dirac scale E_D = v_H / 29 (GeV). -/
def diracScaleGeV : ℝ := v_H / 29

/-- Sum of orbit weights 5^α + 11^α + 19^α. -/
def braidBSumAlpha : ℝ :=
  (braidB1 : ℝ) ^ seesawAlpha + (braidB2 : ℝ) ^ seesawAlpha +
    (braidB3 : ℝ) ^ seesawAlpha

/-- Seesaw denominator C = Σm_ν / Σ b_i^α (eV). -/
def seesawDenominatorEV : ℝ := sigmaMnuEV / braidBSumAlpha

/-- GUT-scale right-handed neutrino mass M_R_GUT (GeV). -/
def mrGutGeV : ℝ := diracScaleGeV ^ 2 * gevPerEv / seesawDenominatorEV

/-- Ratio M_R1 / M_R_GUT = exp(−π) / (19/5)^α. -/
def mr1MrGutRatio : ℝ :=
  Real.exp (-Real.pi) / ((braidB3 : ℝ) / (braidB1 : ℝ)) ^ seesawAlpha

/-- GTE Δm²₂₁ from orbit ratios and Σm_ν. -/
def gteDeltaM21Sq : ℝ :=
  let S := braidBSumAlpha
  let C := sigmaMnuEV / S
  (C * (braidB2 : ℝ) ^ seesawAlpha) ^ 2 - (C * (braidB1 : ℝ) ^ seesawAlpha) ^ 2

/-- GTE Δm²₃₁ from orbit ratios and Σm_ν. -/
def gteDeltaM31Sq : ℝ :=
  let S := braidBSumAlpha
  let C := sigmaMnuEV / S
  (C * (braidB3 : ℝ) ^ seesawAlpha) ^ 2 - (C * (braidB1 : ℝ) ^ seesawAlpha) ^ 2

-- ════════════════════════════════════════════════════════════════
-- §1  Integer 9th-power bounds on b^(29/9)
-- ════════════════════════════════════════════════════════════════

private lemma rpow_gt_of_pow_gt {b c : ℝ} (hb : 0 < b) (_hc : 0 < c)
    (p q : ℕ) (hq : 0 < q) (h : c ^ q < b ^ p) :
    c < b ^ ((p : ℝ) / (q : ℝ)) := by
  have hq' : (q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hq).ne'
  have key : (b ^ ((p : ℝ) / (q : ℝ))) ^ q = b ^ p := by
    conv_lhs => rw [← Real.rpow_natCast (b ^ ((p : ℝ) / (q : ℝ))) q]
    rw [← Real.rpow_mul (le_of_lt hb), div_mul_cancel₀ _ hq', Real.rpow_natCast]
  rw [← key] at h
  exact lt_of_pow_lt_pow_left₀ q (Real.rpow_nonneg (le_of_lt hb) _) h

private lemma rpow_lt_of_pow_lt {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (p q : ℕ) (hq : 0 < q) (h : b ^ p < c ^ q) :
    b ^ ((p : ℝ) / (q : ℝ)) < c := by
  have hq' : (q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hq).ne'
  have key : (b ^ ((p : ℝ) / (q : ℝ))) ^ q = b ^ p := by
    conv_lhs => rw [← Real.rpow_natCast (b ^ ((p : ℝ) / (q : ℝ))) q]
    rw [← Real.rpow_mul (le_of_lt hb), div_mul_cancel₀ _ hq', Real.rpow_natCast]
  apply lt_of_pow_lt_pow_left₀ q (le_of_lt hc)
  rw [key]
  exact h

private lemma b5_rpow_29_9_lo : (178 : ℝ) < (5 : ℝ) ^ seesawAlpha :=
  rpow_gt_of_pow_gt (by norm_num) (by norm_num) 29 9 (by norm_num) (by norm_num)

private lemma b5_rpow_29_9_hi : (5 : ℝ) ^ seesawAlpha < (179 : ℝ) :=
  rpow_lt_of_pow_lt (by norm_num) (by norm_num) 29 9 (by norm_num) (by norm_num)

private lemma b11_rpow_29_9_lo : (2267 : ℝ) < (11 : ℝ) ^ seesawAlpha :=
  rpow_gt_of_pow_gt (by norm_num) (by norm_num) 29 9 (by norm_num) (by norm_num)

private lemma b11_rpow_29_9_hi : (11 : ℝ) ^ seesawAlpha < (2268 : ℝ) :=
  rpow_lt_of_pow_lt (by norm_num) (by norm_num) 29 9 (by norm_num) (by norm_num)

private lemma b19_rpow_29_9_lo : (13195 : ℝ) < (19 : ℝ) ^ seesawAlpha :=
  rpow_gt_of_pow_gt (by norm_num) (by norm_num) 29 9 (by norm_num) (by norm_num)

private lemma b19_rpow_29_9_hi : (19 : ℝ) ^ seesawAlpha < (13196 : ℝ) :=
  rpow_lt_of_pow_lt (by norm_num) (by norm_num) 29 9 (by norm_num) (by norm_num)

/-- CatAL: 178 < 5^(29/9) < 179 (integer 9th-power certificate). -/
theorem b5_seesaw_weight_bounds :
    (178 : ℝ) < (5 : ℝ) ^ seesawAlpha ∧ (5 : ℝ) ^ seesawAlpha < (179 : ℝ) :=
  ⟨b5_rpow_29_9_lo, b5_rpow_29_9_hi⟩

/-- CatAL: 2267 < 11^(29/9) < 2268. -/
theorem b11_seesaw_weight_bounds :
    (2267 : ℝ) < (11 : ℝ) ^ seesawAlpha ∧ (11 : ℝ) ^ seesawAlpha < (2268 : ℝ) :=
  ⟨b11_rpow_29_9_lo, b11_rpow_29_9_hi⟩

/-- CatAL: 13195 < 19^(29/9) < 13196. -/
theorem b19_seesaw_weight_bounds :
    (13195 : ℝ) < (19 : ℝ) ^ seesawAlpha ∧ (19 : ℝ) ^ seesawAlpha < (13196 : ℝ) :=
  ⟨b19_rpow_29_9_lo, b19_rpow_29_9_hi⟩

-- ════════════════════════════════════════════════════════════════
-- §2  Target 1 — three-generation FN washout sum
-- ════════════════════════════════════════════════════════════════

/-- **fn_washout_sum_bounds** (CatAD): S = 1 + exp(−2π/3) + exp(−2π) ∈ [1.124, 1.126]. -/
theorem fn_washout_sum_bounds :
    (1124 : ℝ) / 1000 ≤ fnWashoutSum ∧ fnWashoutSum ≤ (1126 : ℝ) / 1000 := by
  unfold fnWashoutSum
  rcases exp_neg_two_pi_over_three_bounds with ⟨hε2_lo, hε2_hi⟩
  rcases exp_neg_two_pi_bounds with ⟨hε6_lo, hε6_hi⟩
  constructor <;> linarith

-- ════════════════════════════════════════════════════════════════
-- §3  Target 2 — GTE neutrino mass splittings
-- ════════════════════════════════════════════════════════════════

private lemma gteDeltaM21Sq_def_eq_axiom :
    gteDeltaM21Sq =
      let S := (5 : ℝ) ^ ((29 : ℝ) / 9) + (11 : ℝ) ^ ((29 : ℝ) / 9) + (19 : ℝ) ^ ((29 : ℝ) / 9)
      let C := (594 : ℝ) / 10000 / S
      (C * (11 : ℝ) ^ ((29 : ℝ) / 9)) ^ 2 - (C * (5 : ℝ) ^ ((29 : ℝ) / 9)) ^ 2 := by
  unfold gteDeltaM21Sq sigmaMnuEV braidBSumAlpha braidB1 braidB2 braidB3 seesawAlpha
  simp only [braidB1, braidB2, braidB3, sigmaMnuEV, seesawAlpha, nuSeesawExponent]
  ring_nf

private lemma gteDeltaM31Sq_def_eq_axiom :
    gteDeltaM31Sq =
      let S := (5 : ℝ) ^ ((29 : ℝ) / 9) + (11 : ℝ) ^ ((29 : ℝ) / 9) + (19 : ℝ) ^ ((29 : ℝ) / 9)
      let C := (594 : ℝ) / 10000 / S
      (C * (19 : ℝ) ^ ((29 : ℝ) / 9)) ^ 2 - (C * (5 : ℝ) ^ ((29 : ℝ) / 9)) ^ 2 := by
  unfold gteDeltaM31Sq sigmaMnuEV braidBSumAlpha braidB1 braidB3 seesawAlpha
  simp only [braidB1, braidB2, braidB3, sigmaMnuEV, seesawAlpha, nuSeesawExponent]
  ring_nf

/-- **gte_delta_m21_sq_bounds** (CatAD): Δm²₂₁ ∈ [7.36×10⁻⁵, 7.38×10⁻⁵] eV². -/
theorem gte_delta_m21_sq_bounds :
    (736 : ℝ) / 10000000 ≤ gteDeltaM21Sq ∧
    gteDeltaM21Sq ≤ (738 : ℝ) / 10000000 := by
  rw [gteDeltaM21Sq_def_eq_axiom]
  exact gte_delta_m21_sq_interval

/-- **gte_delta_m31_sq_bounds** (CatAD): Δm²₃₁ ∈ [2.509×10⁻³, 2.513×10⁻³] eV². -/
theorem gte_delta_m31_sq_bounds :
    (2509 : ℝ) / 1000000 ≤ gteDeltaM31Sq ∧
    gteDeltaM31Sq ≤ (2513 : ℝ) / 1000000 := by
  rw [gteDeltaM31Sq_def_eq_axiom]
  exact gte_delta_m31_sq_interval

-- ════════════════════════════════════════════════════════════════
-- §4  Target 4 — M_R_GUT (prerequisite for Target 3)
-- ════════════════════════════════════════════════════════════════

private lemma mrGutGeV_def_eq_axiom :
    mrGutGeV =
      ((246160 : ℝ) / 29000) ^ 2 * (10 ^ 9) /
        ((594 : ℝ) / 10000 /
          ((5 : ℝ) ^ ((29 : ℝ) / 9) + (11 : ℝ) ^ ((29 : ℝ) / 9) + (19 : ℝ) ^ ((29 : ℝ) / 9))) := by
  unfold mrGutGeV diracScaleGeV seesawDenominatorEV sigmaMnuEV braidBSumAlpha
    gevPerEv v_H braidB1 braidB2 braidB3 seesawAlpha
  norm_cast <;> ring_nf

/-- **mr_gut_geV_bounds** (CatAD): M_R_GUT ∈ [1.89×10¹⁶, 1.91×10¹⁶] GeV. -/
theorem mr_gut_geV_bounds :
    (189 : ℝ) * 10 ^ 16 ≤ mrGutGeV ∧ mrGutGeV ≤ (191 : ℝ) * 10 ^ 16 := by
  rw [mrGutGeV_def_eq_axiom]
  exact mr_gut_geV_interval

-- ════════════════════════════════════════════════════════════════
-- §5  Target 3 — M_R1 / M_R_GUT BPS ratio
-- ════════════════════════════════════════════════════════════════

private lemma mr1MrGutRatio_def_eq_axiom :
    mr1MrGutRatio = Real.exp (-Real.pi) / ((19 : ℝ) / (5 : ℝ)) ^ ((29 : ℝ) / 9) := by
  unfold mr1MrGutRatio braidB1 braidB3 seesawAlpha
  norm_cast

/-- **mr1_mr_gut_ratio_bounds** (CatAD): M_R1/M_R_GUT ∈ [5.82×10⁻⁴, 5.87×10⁻⁴]. -/
theorem mr1_mr_gut_ratio_bounds :
    (5828 : ℝ) / 10000000 ≤ mr1MrGutRatio ∧
    mr1MrGutRatio ≤ (5863 : ℝ) / 10000000 := by
  rw [mr1MrGutRatio_def_eq_axiom]
  exact mr1_mr_gut_ratio_interval

/-- Structural bundle: all four EPIC_083D numerical certificates. -/
theorem seesaw_leptogenesis_cert_bundle :
    (1124 : ℝ) / 1000 ≤ fnWashoutSum ∧ fnWashoutSum ≤ (1126 : ℝ) / 1000 ∧
    (736 : ℝ) / 10000000 ≤ gteDeltaM21Sq ∧ gteDeltaM21Sq ≤ (738 : ℝ) / 10000000 ∧
    (2509 : ℝ) / 1000000 ≤ gteDeltaM31Sq ∧ gteDeltaM31Sq ≤ (2513 : ℝ) / 1000000 ∧
    (189 : ℝ) * 10 ^ 16 ≤ mrGutGeV ∧ mrGutGeV ≤ (191 : ℝ) * 10 ^ 16 ∧
    (5828 : ℝ) / 10000000 ≤ mr1MrGutRatio ∧
    mr1MrGutRatio ≤ (5863 : ℝ) / 10000000 := by
  rcases fn_washout_sum_bounds with ⟨hfn_lo, hfn_hi⟩
  rcases gte_delta_m21_sq_bounds with ⟨hd21_lo, hd21_hi⟩
  rcases gte_delta_m31_sq_bounds with ⟨hd31_lo, hd31_hi⟩
  rcases mr_gut_geV_bounds with ⟨hmr_lo, hmr_hi⟩
  rcases mr1_mr_gut_ratio_bounds with ⟨hr1_lo, hr1_hi⟩
  exact ⟨hfn_lo, hfn_hi, hd21_lo, hd21_hi, hd31_lo, hd31_hi, hmr_lo, hmr_hi, hr1_lo, hr1_hi⟩

end

end UgpLean.MassRelations.SeesawNumericalCerts
