import Mathlib.Tactic
import UgpLean.Algebra.F21SU3Embedding
import UgpLean.MassRelations.NeutrinoSector
import UgpLean.Universality.CasimirB0Relation

/-!
# PMNS atmospheric angle NLO arithmetic certificates

Route A from the F₂₁-normalized RH neutrino cascade product:
`sin²θ₂₃^NLO = b_{R2} × b_{R3} / |F₂₁|² = 11 × 19 / 21² = 209/441`.

The physical identification of the NLO formula from the Φ_MDL Lagrangian is
CatB/PARTIAL; the rational identities below are CatAL (pure arithmetic).
-/

namespace UgpLean.MassRelations.PMNSNLOCorrection

open UgpLean.MassRelations.NeutrinoSector
open UgpLean.Algebra.F21SU3Embedding
open UgpLean.Universality.CasimirB0Relation

/-- **two_b_R2_eq_F21_succ** (CatAL): `2 × b_{R2} = |F₂₁| + 1`, i.e. `22 = 21 + 1`. -/
theorem two_b_R2_eq_F21_succ : 2 * b_R2 = 7 * 3 + 1 := by
  unfold b_R2
  decide

/-- **ngen_eq_nfam_minus_two** (CatAL): `N_gen = N_fam − 2`, i.e. `3 = 5 − 2`. -/
theorem ngen_eq_nfam_minus_two : (3 : ℕ) = 5 - 2 := by decide

/-- **pmns_atm_nlo_candidate** (CatAL): F₂₁-normalized product
    `sin²θ₂₃^NLO = b_{R2} × b_{R3} / |F₂₁|² = 209/441`. -/
theorem pmns_atm_nlo_candidate : (b_R2 * b_R3 : ℚ) / (21 * 21) = 209 / 441 := by
  norm_num [b_R2, b_R3]

/-- **pmns_atm_nlo_formula** (CatAL): alias for the F₂₁-normalized NLO atmospheric mixing candidate. -/
theorem pmns_atm_nlo_formula : (b_R2 * b_R3 : ℚ) / (21 * 21) = 209 / 441 :=
  pmns_atm_nlo_candidate

/-- **pmns_atm_nlo_in_1sigma** (CatAL): `209/441` is within 1σ of NuFIT 6.0 IC24 NH
    `sin²θ₂₃ = 0.470` (1σ width 0.013). -/
theorem pmns_atm_nlo_in_1sigma :
    |(209 : ℚ) / 441 - 470 / 1000| < 13 / 1000 := by norm_num

end UgpLean.MassRelations.PMNSNLOCorrection
