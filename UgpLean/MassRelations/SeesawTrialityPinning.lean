import Mathlib.Analysis.SpecialFunctions.Pow.Real
import UgpLean.Polynomial.EisensteinIdentities
import UgpLean.MassRelations.SeesawNumericalCerts
import UgpLean.MassRelations.NeutrinoSector
import UgpLean.Algebra.TrialityInterface

/-!
# Seesaw triality pinning — RH neutrino seed transport

Certifies the structural pinning of LH neutrino mass eigenstates to triality
generation slots via the GTE seesaw orbit map.

## Decide-class (CatAL)

- RH braid seeds `b_{R,1}=5`, `b_{R,2}=11`, `b_{R,3}=19` (from `SeesawNumericalCerts`)
- Strict seed ordering `5 < 11 < 19`
- Eisenstein norm status: `19 = N(−5−3ω)`; `5` and `11` are not Eisenstein norms
- Uniqueness: `19` is the unique Eisenstein norm among `{5,11,19}`

## Analysis-class

- Strict monotonicity of the seesaw map `m(b) = C · b^{29/9}` for `C > 0`
- Normal mass ordering `m_{ν,1} < m_{ν,2} < m_{ν,3}` conditional on the corpus
  seesaw formula `m_{ν,k} = C · b_{R,k}^{29/9}` with `C = Σm_ν / Σ_j b_{R,j}^{29/9}`

Physical meaning: RH seed labels transport through the monotone seesaw map to LH
mass eigenstates; the unique Eisenstein norm seed `b_{R,3}=19` parallels the charged-lepton
selection `b_{gen1}=73`; normal ordering is structural given seed ordering.

All theorems: zero sorry, zero custom axioms.
-/

namespace UgpLean.MassRelations.SeesawTrialityPinning

open Real
open GUTStructure
open UgpLean.Polynomial.EisensteinIdentities
open UgpLean.MassRelations.SeesawNumericalCerts
open UgpLean.MassRelations.NeutrinoSector
open UgpLean.Algebra.TrialityInterface

noncomputable section

-- ════════════════════════════════════════════════════════════════
-- §0  RH seed aliases (reuse corpus definitions)
-- ════════════════════════════════════════════════════════════════

/-- Right-handed neutrino braid seed for generation 1 (`SeesawNumericalCerts.braidB1`). -/
abbrev b_R1 : ℕ := braidB1

/-- Right-handed neutrino braid seed for generation 2 (`SeesawNumericalCerts.braidB2`). -/
abbrev b_R2 : ℕ := braidB2

/-- Right-handed neutrino braid seed for generation 3 (`SeesawNumericalCerts.braidB3`). -/
abbrev b_R3 : ℕ := braidB3

/-- PMNS-sector `b_R2` matches the seesaw braid seed (CatAL). -/
theorem b_R2_eq_neutrino_sector : b_R2 = NeutrinoSector.b_R2 := rfl

/-- PMNS-sector `b_R3` matches the seesaw braid seed (CatAL). -/
theorem b_R3_eq_neutrino_sector : b_R3 = NeutrinoSector.b_R3 := rfl

/-- **rh_seed_values** (CatAL): certified RH braid seeds `{5, 11, 19}`. -/
theorem rh_seed_values : b_R1 = 5 ∧ b_R2 = 11 ∧ b_R3 = 19 :=
  ⟨rfl, rfl, rfl⟩

-- ════════════════════════════════════════════════════════════════
-- §1  Strict seed ordering
-- ════════════════════════════════════════════════════════════════

/-- **rh_seed_ordering** (CatAL): `b_{R,1} < b_{R,2} < b_{R,3}`. -/
theorem rh_seed_ordering : b_R1 < b_R2 ∧ b_R2 < b_R3 := by
  unfold b_R1 b_R2 b_R3 braidB1 braidB2 braidB3
  decide

-- ════════════════════════════════════════════════════════════════
-- §2  Eisenstein norm status
-- ════════════════════════════════════════════════════════════════

/-- A natural number is an Eisenstein norm when it equals `N(a+bω)=a²−ab+b²`. -/
def IsEisensteinNormNat (n : ℕ) : Prop :=
  ∃ a b : ℤ, eisensteinNorm a b = n

private lemma eisensteinNorm_mod3_eq_quad (a b : ℤ) :
    eisensteinNorm a b % 3 =
      ((a % 3) ^ 2 - (a % 3) * (b % 3) + (b % 3) ^ 2) % 3 := by
  have ha : a ≡ a % 3 [ZMOD 3] := (Int.mod_modEq a 3).symm
  have hb : b ≡ b % 3 [ZMOD 3] := (Int.mod_modEq b 3).symm
  have hquad :
      eisensteinNorm a b ≡ (a % 3) ^ 2 - (a % 3) * (b % 3) + (b % 3) ^ 2 [ZMOD 3] := by
    unfold eisensteinNorm
    exact ha.pow 2 |>.sub (ha.mul hb) |>.add (hb.pow 2)
  exact hquad.eq

private lemma eisensteinNorm_mod3_ne_two (a b : ℤ) : eisensteinNorm a b % 3 ≠ 2 := by
  rw [eisensteinNorm_mod3_eq_quad]
  have ha : a % 3 = 0 ∨ a % 3 = 1 ∨ a % 3 = 2 := by omega
  have hb : b % 3 = 0 ∨ b % 3 = 1 ∨ b % 3 = 2 := by omega
  rcases ha with ha | ha | ha <;> rcases hb with hb | hb | hb <;> simp [ha, hb]

/-- If `n ≡ 2 (mod 3)`, then `n` is not an Eisenstein norm (standard residue criterion). -/
theorem not_eisenstein_norm_of_mod3_two (n : ℕ) (hn : n % 3 = 2) :
    ¬ IsEisensteinNormNat n := by
  intro h
  rcases h with ⟨a, b, heq⟩
  have hn' : (n : ℤ) % 3 = 2 := by exact_mod_cast hn
  have hcontra := eisensteinNorm_mod3_ne_two a b
  rw [heq, hn'] at hcontra
  exact hcontra rfl

/-- **braidB1_not_eisenstein_norm** (CatAL): `5` is not an Eisenstein norm (`5 ≡ 2 mod 3`). -/
theorem braidB1_not_eisenstein_norm : ¬ IsEisensteinNormNat b_R1 := by
  unfold b_R1 braidB1
  exact not_eisenstein_norm_of_mod3_two 5 (by decide)

/-- **braidB2_not_eisenstein_norm** (CatAL): `11` is not an Eisenstein norm (`11 ≡ 2 mod 3`). -/
theorem braidB2_not_eisenstein_norm : ¬ IsEisensteinNormNat b_R2 := by
  unfold b_R2 braidB2
  exact not_eisenstein_norm_of_mod3_two 11 (by decide)

/-- **braidB3_eisenstein_norm_witness** (CatAL): `19 = N(−5−3ω)`. -/
theorem braidB3_eisenstein_norm_witness :
    IsEisensteinNormNat b_R3 ∧ eisensteinNorm (-5) (-3) = 19 := by
  refine ⟨?_, by unfold eisensteinNorm; norm_num⟩
  unfold IsEisensteinNormNat b_R3 braidB3
  exact ⟨-5, -3, by unfold eisensteinNorm; norm_num⟩

/-- **braidB3_is_eisenstein_norm** (CatAL): `19` is an Eisenstein norm. -/
theorem braidB3_is_eisenstein_norm : IsEisensteinNormNat b_R3 :=
  braidB3_eisenstein_norm_witness.1

/-- **rh_seed_unique_eisenstein_norm** (CatAL): exactly one Eisenstein norm among `{5,11,19}`. -/
theorem rh_seed_unique_eisenstein_norm :
    ¬ IsEisensteinNormNat b_R1 ∧
    ¬ IsEisensteinNormNat b_R2 ∧
    IsEisensteinNormNat b_R3 ∧
    (∀ n : ℕ, n = b_R1 ∨ n = b_R2 ∨ n = b_R3 → IsEisensteinNormNat n → n = b_R3) := by
  refine ⟨braidB1_not_eisenstein_norm, braidB2_not_eisenstein_norm,
    braidB3_is_eisenstein_norm, ?_⟩
  intro n hn hEN
  rcases hn with rfl | rfl | rfl
  · exact (braidB1_not_eisenstein_norm hEN).elim
  · exact (braidB2_not_eisenstein_norm hEN).elim
  · rfl

-- ════════════════════════════════════════════════════════════════
-- §3  Seesaw mass map and monotonicity (analysis-class)
-- ════════════════════════════════════════════════════════════════

/-- Seesaw normalization `C = Σm_ν / Σ_j b_{R,j}^{29/9}` (eV). -/
def seesawNormalizationEV : ℝ := seesawDenominatorEV

/-- GTE seesaw mass `m_ν(b) = C · b^{29/9}` for braid index `b`. -/
def seesawNeutrinoMass (b : ℕ) : ℝ :=
  seesawNormalizationEV * (b : ℝ) ^ seesawAlpha

/-- Certified LH neutrino masses from the three RH seeds. -/
def mNu1 : ℝ := seesawNeutrinoMass b_R1
def mNu2 : ℝ := seesawNeutrinoMass b_R2
def mNu3 : ℝ := seesawNeutrinoMass b_R3

private lemma seesawAlpha_pos : (0 : ℝ) < seesawAlpha := by
  unfold seesawAlpha
  norm_num

private lemma seesawNormalizationEV_pos : (0 : ℝ) < seesawNormalizationEV := by
  unfold seesawNormalizationEV seesawDenominatorEV sigmaMnuEV braidBSumAlpha
    braidB1 braidB2 braidB3 seesawAlpha
  positivity

private lemma nat_cast_pos {n : ℕ} (hn : 0 < n) : (0 : ℝ) < (n : ℝ) := by
  exact_mod_cast hn

private lemma nat_cast_le_one {n : ℕ} (hn : 1 ≤ n) : (1 : ℝ) ≤ (n : ℝ) := by
  exact_mod_cast hn

/-- **seesaw_power_strict_mono** (CatAL analysis):
    for `C > 0` and `α = 29/9 > 0`, the map `b ↦ C · b^α` is strictly increasing on `ℕ_{>0}`. -/
theorem seesaw_power_strict_mono {b₁ b₂ : ℕ} (hb₁ : 0 < b₁) (hlt : b₁ < b₂) :
    seesawNeutrinoMass b₁ < seesawNeutrinoMass b₂ := by
  unfold seesawNeutrinoMass
  have hb₁' : (0 : ℝ) ≤ (b₁ : ℝ) := le_of_lt (nat_cast_pos hb₁)
  have hpow : (b₁ : ℝ) ^ seesawAlpha < (b₂ : ℝ) ^ seesawAlpha :=
    Real.rpow_lt_rpow hb₁' (mod_cast hlt) seesawAlpha_pos
  exact mul_lt_mul_of_pos_left hpow seesawNormalizationEV_pos

/-- **seesaw_mass_formula** (CatAL): masses match the corpus seesaw law. -/
theorem seesaw_mass_formula :
    mNu1 = seesawNormalizationEV * (b_R1 : ℝ) ^ seesawAlpha ∧
    mNu2 = seesawNormalizationEV * (b_R2 : ℝ) ^ seesawAlpha ∧
    mNu3 = seesawNormalizationEV * (b_R3 : ℝ) ^ seesawAlpha := by
  unfold mNu1 mNu2 mNu3 seesawNeutrinoMass
  exact ⟨rfl, rfl, rfl⟩

/-- **seesaw_normal_ordering_from_seed_ordering** (CatAL analysis):
    under the certified seesaw formula, `b_{R,1} < b_{R,2} < b_{R,3}` implies
    normal ordering `m_{ν,1} < m_{ν,2} < m_{ν,3}`. -/
theorem seesaw_normal_ordering_from_seed_ordering :
    mNu1 < mNu2 ∧ mNu2 < mNu3 := by
  have hb1 : 0 < b_R1 := by unfold b_R1 braidB1; decide
  have hb2 : 0 < b_R2 := by unfold b_R2 braidB2; decide
  rcases rh_seed_ordering with ⟨h12, h23⟩
  exact ⟨seesaw_power_strict_mono hb1 h12, seesaw_power_strict_mono hb2 h23⟩

/-- Integer-weight ordering certificate from `SeesawNumericalCerts` bounds (decide-class). -/
theorem seesaw_weight_ordering :
    (178 : ℝ) < (5 : ℝ) ^ seesawAlpha ∧
    (5 : ℝ) ^ seesawAlpha < (11 : ℝ) ^ seesawAlpha ∧
    (11 : ℝ) ^ seesawAlpha < (19 : ℝ) ^ seesawAlpha ∧
    (13195 : ℝ) < (19 : ℝ) ^ seesawAlpha := by
  rcases b5_seesaw_weight_bounds with ⟨h5_lo, h5_hi⟩
  rcases b11_seesaw_weight_bounds with ⟨h11_lo, h11_hi⟩
  rcases b19_seesaw_weight_bounds with ⟨h19_lo, _h19_hi⟩
  exact ⟨h5_lo,
    lt_trans h5_hi (lt_trans (by norm_num : (179 : ℝ) < 2267) h11_lo),
    lt_trans h11_hi (lt_trans (by norm_num : (2268 : ℝ) < 13195) h19_lo),
    h19_lo⟩

-- ════════════════════════════════════════════════════════════════
-- §4  Pinning bundle
-- ════════════════════════════════════════════════════════════════

/-- **neutrino_slot_pinning_certificate** (CatAL decide + CatAL analysis):
    RH seed ordering, Eisenstein selection, and normal mass ordering under the
    certified GTE seesaw map; PMNS orbit-ratio seeds align with `NeutrinoSector`. -/
theorem neutrino_slot_pinning_certificate :
    (b_R1 = 5 ∧ b_R2 = 11 ∧ b_R3 = 19) ∧
    (b_R1 < b_R2 ∧ b_R2 < b_R3) ∧
    (¬ IsEisensteinNormNat b_R1 ∧
      ¬ IsEisensteinNormNat b_R2 ∧
      IsEisensteinNormNat b_R3 ∧
      ∀ n : ℕ, n = b_R1 ∨ n = b_R2 ∨ n = b_R3 → IsEisensteinNormNat n → n = b_R3) ∧
    (mNu1 < mNu2 ∧ mNu2 < mNu3) ∧
    b_R2 = NeutrinoSector.b_R2 ∧
    b_R3 = NeutrinoSector.b_R3 ∧
    (↑NeutrinoSector.b_R3 / ↑GUTStructure.b_gen2 = (19 : ℚ) / 42) ∧
    ((NeutrinoSector.b_R2 : ℚ) / b_gen1 < 1) := by
  exact ⟨rh_seed_values, rh_seed_ordering, rh_seed_unique_eisenstein_norm,
    seesaw_normal_ordering_from_seed_ordering, b_R2_eq_neutrino_sector,
    b_R3_eq_neutrino_sector, pmns_atm_sin_sq, pmns_reactor_sin_val⟩

/-- **seesaw_triality_pinning_bundle**: full certificate including triality gen1 pinning. -/
theorem seesaw_triality_pinning_bundle :
    (b_R1 = 5 ∧ b_R2 = 11 ∧ b_R3 = 19) ∧
    (b_R1 < b_R2 ∧ b_R2 < b_R3) ∧
    (mNu1 < mNu2 ∧ mNu2 < mNu3) ∧
    IsEisensteinNormNat b_R3 ∧
    (f4Frob F4Elem.one = F4Elem.one ∧
      applySlotPerm spinorSwapPerm frobeniusFixedCentral = frobeniusFixedCentral) ∧
    eisensteinNorm (-5) (-3) = 19 := by
  refine And.intro rh_seed_values ?_
  refine And.intro rh_seed_ordering ?_
  refine And.intro seesaw_normal_ordering_from_seed_ordering ?_
  refine And.intro braidB3_is_eisenstein_norm ?_
  refine And.intro G6_gen1_pinned_to_vector_slot ?_
  exact braidB3_eisenstein_norm_witness.2

end

end UgpLean.MassRelations.SeesawTrialityPinning
