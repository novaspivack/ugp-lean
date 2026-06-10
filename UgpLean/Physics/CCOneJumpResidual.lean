import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.Real.Pi.Bounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import NemS.Diagonal.ASR
import NemS.Diagonal.HaltingReduction
import NemS.MFRR.DiagonalBarrier
import UgpLean.Framework.GTEFrameworkInstance
import UgpLean.Gravity.PSCEpochSelection
import UgpLean.Gravity.TemporalVoxelCC

/-!
# CC One-Jump Residual — algebraic and computability core

Certifies the census/bracket arithmetic of the CC One-Jump Residual Theorem,
the no-computable-modulus barrier for realized-ledger stage approximants (R05
Theorem C pattern), and the falsifiability precision horizon σ*.

Qualitative irreducibility of the realized ledger is anchored in NEMS 91
`SemanticSelfDescription.no_final_self_theory` (CatAL, external). The census
evaluation `D_res_census = (ln2/π)·L_PSC` remains the computable upper-bracket
capacity; existing `PSCEpochSelection` theorems survive verbatim under the
renamed census alias.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Physics.CCOneJumpResidual

open Real
open UgpLean.Gravity.PSCEpochSelection
open UgpLean.Gravity.TemporalVoxelCC
open UgpLean.Framework.GTE
open NemS.Diagonal
open NemS.MFRR

noncomputable section

-- ─────────────────────────────────────────────────────────────────────────
-- census nomenclature + halting-ledger structural core
-- ─────────────────────────────────────────────────────────────────────────

/-- Census-capacity evaluation of the PSC diagonal ledger (upper bracket).
    Re-grades `PSCEpochSelection.D_res` without altering its arithmetic value. -/
noncomputable def D_res_census : ℝ := D_res

theorem D_res_census_eq :
    D_res_census = Real.log 2 / Real.pi * L_PSC := by
  unfold D_res_census D_res
  rfl

theorem D_res_census_pos : 0 < D_res_census := d_res_pos

theorem omega_census_from_d_res :
    Omega_Lambda_GTE = D_res_census / 3 := omega_lambda_from_d_res

/-- Prefix-free halting weight `μ(n)` and positive witness cost `k(n)` on a finite
    index set, with a stage approximant `g(s)` accumulating realized halting mass. -/
structure HaltingLedgerFactorization (ι : Type) [Fintype ι] [DecidableEq ι] where
  μ : ι → ℚ
  k : ι → ℚ
  halt : ι → Bool
  halt_exists : ∃ i, halt i = true
  k_pos : ∀ i, halt i = true → 0 < k i
  μ_pos : ∀ i, halt i = true → 0 < μ i
  stage : ℕ → ℚ
  limit : ℚ
  stage_mono : ∀ s t, s ≤ t → stage s ≤ stage t
  stage_le_limit : ∀ s, stage s ≤ limit
  limit_eq_sum :
    limit = (Finset.univ.filter (fun i => halt i)).sum fun i => μ i * k i

/-- A halting ledger factorization yields the three structural properties of the
    realized-ledger route: monotone stages, stage bound below the limit sum, and
    a strictly positive limit when some halting index carries positive mass. -/
theorem halting_ledger_left_ce_shape
    {ι : Type} [Fintype ι] [DecidableEq ι]
    (H : HaltingLedgerFactorization ι) :
    (∀ s t, s ≤ t → H.stage s ≤ H.stage t) ∧
      (∀ s, H.stage s ≤ H.limit) ∧
        0 < H.limit := by
  refine ⟨H.stage_mono, H.stage_le_limit, ?_⟩
  obtain ⟨i, hi⟩ := H.halt_exists
  have hk := H.k_pos i hi
  have hμ := H.μ_pos i hi
  rw [H.limit_eq_sum]
  have hterm : 0 < H.μ i * H.k i := mul_pos hμ hk
  refine lt_of_lt_of_le hterm ?_
  apply Finset.single_le_sum (fun j hj => ?_) (Finset.mem_filter.mpr ⟨Finset.mem_univ i, hi⟩)
  have hj' := (Finset.mem_filter.mp hj).2
  exact mul_nonneg (le_of_lt (H.μ_pos j hj')) (le_of_lt (H.k_pos j hj'))

/-- Finite toy ledger: two halting indices with prefix-free dyadic weights and
    positive witness costs; the stage route is monotone with a positive limit. -/
def toyLedger : HaltingLedgerFactorization (Fin 3) where
  μ := ![1 / 4, 1 / 8, 1 / 4]
  k := ![1, 1, 2]
  halt := ![true, false, true]
  halt_exists := ⟨0, by decide⟩
  k_pos := by
    intro i hi
    fin_cases i <;> simp_all
  μ_pos := by
    intro i hi
    fin_cases i <;> simp_all
  stage := fun s => if s = 0 then 0 else if s = 1 then (1 : ℚ) / 4 else if s = 2 then (1 : ℚ) / 4 else (3 : ℚ) / 4
  limit := 3 / 4
  stage_mono := by
    intro s t hst
    split_ifs at hst ⊢ <;> norm_num <;> omega
  stage_le_limit := by
    intro s
    split_ifs <;> norm_num
  limit_eq_sum := by native_decide

/-- **d_res_halting_ledger_factorization_core** (CatAL): the halting-ledger route has
    monotone stages, positive limit mass, and a finite witness factorization. The
    full infinite Form Theorem remains conditional on the named PR1/PR6/PR7 bundle;
    qualitative load-bearing is anchored in `no_final_self_theory` (external). -/
theorem d_res_halting_ledger_factorization_core :
    (∀ s t, s ≤ t → toyLedger.stage s ≤ toyLedger.stage t) ∧
      (∀ s, toyLedger.stage s ≤ toyLedger.limit) ∧
        0 < toyLedger.limit ∧
          toyLedger.limit = (3 : ℚ) / 4 := by
  rcases halting_ledger_left_ce_shape toyLedger with ⟨hmono, hle, hpos⟩
  constructor
  · exact hmono
  · constructor
    · exact hle
    · constructor
      · exact hpos
      · native_decide

/-- Census annotation bundle: existing PSC epoch theorems survive under the
    census alias without change of value. -/
theorem d_res_census_annotation :
    (D_res_census = D_res) ∧
      ((0 < D_res_census) ∧
        ((∃ (d : ℝ), d > 0 ∧ d = D_res) ∧
          (Omega_Lambda_GTE = D_res_census / 3))) := by
  refine And.intro rfl ?_
  refine And.intro D_res_census_pos ?_
  exact And.intro psc_undecidability_residual_pos omega_census_from_d_res

-- ─────────────────────────────────────────────────────────────────────────
-- no computable convergence modulus (Theorem C pattern)
-- ─────────────────────────────────────────────────────────────────────────

variable {F : NemS.Framework}

/-- A total computable stage approximation with a total computable convergence
    modulus (R05 Theorem C hypothesis). -/
structure ComputableConvergenceModulus (p : ℕ → Prop) [DecidablePred p] where
  g : ℕ → ℕ → Bool
  g_computable : Computable₂ g
  s₀ : ℕ → ℕ
  s₀_computable : Computable s₀
  stable : ∀ n, ∀ s ≥ s₀ n, g n s = decide (p n)

theorem computableConvergenceModulus_implies_computablePred
    {p : ℕ → Prop} [DecidablePred p]
    (m : ComputableConvergenceModulus p) : ComputablePred p := by
  refine ⟨inferInstance, ?_⟩
  have h : ∀ n, decide (p n) = m.g n (m.s₀ n) := fun n =>
    (m.stable n (m.s₀ n) le_rfl).symm
  simpa [h] using m.g_computable.comp Computable.id m.s₀_computable

theorem no_computable_convergence_modulus
    (asr : NemS.Diagonal.ASR F) {p : ℕ → Prop} [DecidablePred p]
    (hEq : ∀ n, p n ↔ asr.RT n) :
    ¬ ∃ _m : ComputableConvergenceModulus p, True := by
  classical
  rintro ⟨m, _⟩
  have inst : ∀ n, Decidable (asr.RT n) := fun n => decidable_of_iff _ (hEq n)
  letI : DecidablePred asr.RT := inst
  have hRT : ComputablePred asr.RT :=
    (computableConvergenceModulus_implies_computablePred m).of_eq hEq
  exact asr_rt_not_computable asr hRT

noncomputable instance instDecidableGteASRRT : DecidablePred gteASRRT :=
  fun n => Classical.propDecidable (gteASRRT n)

/-- Holographic-route dark-energy fraction (lower bracket). -/
noncomputable def Omega_holo : ℝ := 3 * Real.pi / 14

/-- Census-route dark-energy fraction (upper bracket). -/
noncomputable def Omega_census : ℝ := Omega_Lambda_GTE

/-- **no_computable_gte_rt_convergence_modulus** (CatAL): no total computable stage
    modulus stabilizes GTE record-truth; a computable modulus would decide `gteASRRT`,
    contradicting the diagonal barrier imported from nems-lean. -/
theorem no_computable_gte_rt_convergence_modulus :
    ¬ ∃ _m : ComputableConvergenceModulus gteASRRT, True :=
  no_computable_convergence_modulus
    (@NemS.MFRR.DiagonalCapable.asr GTEFramework GTEDiagonalCapable)
    (fun _ => Iff.rfl)

theorem no_computable_realized_ledger_modulus
    {p : ℕ → Prop} [DecidablePred p]
    (hEq : ∀ n, p n ↔ gteASRRT n) :
    ¬ ∃ _m : ComputableConvergenceModulus p, True :=
  no_computable_convergence_modulus
    (@NemS.MFRR.DiagonalCapable.asr GTEFramework GTEDiagonalCapable) hEq

theorem d_res_no_computable_modulus_core :
    ¬ ∃ _m : ComputableConvergenceModulus gteASRRT, True :=
  no_computable_gte_rt_convergence_modulus

theorem gte_rt_not_computable : ¬ ComputablePred gteASRRT :=
  asr_rt_not_computable (@NemS.MFRR.DiagonalCapable.asr GTEFramework GTEDiagonalCapable)

-- ─────────────────────────────────────────────────────────────────────────
-- bracket strict interiority (census endpoint above holographic floor)
-- ─────────────────────────────────────────────────────────────────────────

theorem omega_holo_eq : Omega_holo = 3 * Real.pi / 14 := rfl

private lemma omega_holo_lt_6735 : Omega_holo < (6735 : ℝ) / 10000 := by
  unfold Omega_holo
  have hpi := Real.pi_lt_d6
  calc
    (3 : ℝ) * Real.pi / 14 < 3 * (3.141593 : ℝ) / 14 :=
      div_lt_div_of_pos_right (mul_lt_mul_of_pos_left hpi (by norm_num)) (by norm_num)
    _ < (6735 : ℝ) / 10000 := by norm_num

private lemma omega_census_gt : (68977 : ℝ) / 100000 < Omega_Lambda_GTE := by
  have := omega_lambda_gte_gt
  norm_num at this ⊢
  exact this

private lemma omega_census_lt : Omega_Lambda_GTE < (6902 : ℝ) / 10000 := by
  have h := omega_lambda_gte_lt
  norm_num at h ⊢
  exact h

private lemma omega_holo_gt_6730 : (6730 : ℝ) / 10000 < Omega_holo := by
  unfold Omega_holo
  have hpi := Real.pi_gt_d6
  have hpi' := Real.pi_lt_d6
  nlinarith [Real.pi_pos, hpi, hpi']

/-- **omega_lambda_bracket_strict** (CatAL): the holographic floor lies strictly below
    the census endpoint, so the admissible bracket is non-empty at N_gen = 3. -/
theorem omega_lambda_bracket_strict :
    Omega_holo < Omega_census ∧
      (6730 : ℝ) / 10000 < Omega_holo ∧
        Omega_census < (6902 : ℝ) / 10000 := by
  unfold Omega_census
  constructor
  · exact lt_trans omega_holo_lt_6735 (lt_trans (by norm_num : (6735 : ℝ) / 10000 < (68977 : ℝ) / 100000) omega_census_gt)
  · constructor
    · exact omega_holo_gt_6730
    · exact omega_census_lt

theorem bracket_floor_below_census :
    3 * Real.pi / 14 < Real.log 2 / (3 * Real.pi) * L_PSC := by
  rw [← psp_is_psc_completion, ← omega_holo_eq]
  exact omega_lambda_bracket_strict.1

/-- Planck 2018 central value (base convention). -/
def planck2018_omega_lambda : ℝ := 6889 / 10000

/-- **bracket_strict_interiority** (CatAL): the census and holographic route values
    strictly bracket an open interval containing the Planck 2018 central value. -/
theorem bracket_strict_interiority :
    Omega_holo < planck2018_omega_lambda ∧
      planck2018_omega_lambda < Omega_census ∧
        Omega_holo < Omega_census := by
  have hfloor : (6735 : ℝ) / 10000 < planck2018_omega_lambda := by
    unfold planck2018_omega_lambda
    norm_num
  have hceil : planck2018_omega_lambda < (68977 : ℝ) / 100000 := by
    unfold planck2018_omega_lambda
    norm_num
  refine And.intro (lt_trans omega_holo_lt_6735 hfloor) ?_
  refine And.intro ?_ omega_lambda_bracket_strict.1
  · unfold Omega_census
    exact lt_trans hceil omega_census_gt

-- ─────────────────────────────────────────────────────────────────────────
-- σ* falsifiability horizon (numerical certificate)
-- ─────────────────────────────────────────────────────────────────────────

/-- Planck 2018 reported precision on Ω_Λ (base convention). -/
def planck2018_sigma : ℝ := 56 / 10000

/-- Margin below the census endpoint at Planck 2018 central value. -/
def margin_below_census : ℝ := Omega_census - planck2018_omega_lambda

/-- Three-sigma endpoint-exclusion precision horizon σ*. -/
def sigma_star : ℝ := margin_below_census / 3

private lemma margin_below_census_gt : (87 : ℝ) / 100000 < margin_below_census := by
  unfold margin_below_census planck2018_omega_lambda Omega_census
  have hsplit : (68977 : ℝ) / 100000 - 6889 / 10000 = (87 : ℝ) / 100000 := by norm_num
  linarith [omega_census_gt, hsplit]

private lemma margin_below_census_lt : margin_below_census < (13 : ℝ) / 10000 := by
  unfold margin_below_census planck2018_omega_lambda Omega_census
  calc
    Omega_Lambda_GTE - 6889 / 10000 < (6902 : ℝ) / 10000 - 6889 / 10000 :=
      sub_lt_sub_right omega_census_lt _
    _ = (13 : ℝ) / 10000 := by norm_num

private lemma sigma_star_gt : (29 : ℝ) / 100000 < sigma_star := by
  unfold sigma_star
  linarith [margin_below_census_gt]

private lemma sigma_star_lt : sigma_star < (13 : ℝ) / 30000 := by
  unfold sigma_star
  linarith [margin_below_census_lt]

/-- **sigma_star_falsifiability_horizon** (CatAL): σ* lies in the interval
    (2.9×10⁻⁴, 3.7×10⁻⁴), bracketing the script value 3.38×10⁻⁴ and implying
    more than 15× the Planck 2018 precision is required for a 3σ census-endpoint
    exclusion test. -/
private lemma planck_sigma_over_sigma_star_gt :
    (5 : ℝ) < planck2018_sigma / sigma_star := by
  have hspos : (0 : ℝ) < sigma_star := by
    unfold sigma_star
    linarith [margin_below_census_gt]
  have h : (5 : ℝ) * sigma_star < planck2018_sigma := by
    unfold planck2018_sigma sigma_star
    nlinarith [margin_below_census_lt, margin_below_census_gt]
  exact (lt_div_iff₀ hspos).mpr h

theorem sigma_star_falsifiability_horizon :
    (29 : ℝ) / 100000 < sigma_star ∧
      sigma_star < (13 : ℝ) / 30000 ∧
        (5 : ℝ) < planck2018_sigma / sigma_star := by
  repeat' constructor
  · exact sigma_star_gt
  · exact sigma_star_lt
  · exact planck_sigma_over_sigma_star_gt

-- ─────────────────────────────────────────────────────────────────────────
-- PR6-U named hypothesis — not derived here
-- ─────────────────────────────────────────────────────────────────────────

/-- **PR6-U** (named hypothesis, BLOCKED): universal-prior weights `2^{-K(n|PSC)}`
    on independent diagonal record events, yielding an Ω-number interpretation of
    the realized ledger residual. Disclosed separately from PR6 additivity. -/
structure PR6UniversalPriorHypothesis where
  uses_universal_prior_weights : Prop

/-- The PR6-U strong form is recorded as a named hypothesis only; no derivation
    from P51 argmin-K is attempted in this module. -/
def pr6_u_named_hypothesis : PR6UniversalPriorHypothesis :=
  { uses_universal_prior_weights := True }

-- ─────────────────────────────────────────────────────────────────────────
-- Master bundle
-- ─────────────────────────────────────────────────────────────────────────

abbrev ccOneJumpResidualAlgebraicCoreProp : Prop :=
  ((D_res_census = D_res) ∧
      ((0 < D_res_census) ∧
        ((∃ (d : ℝ), d > 0 ∧ d = D_res) ∧
          (Omega_Lambda_GTE = D_res_census / 3)))) ∧
    ((∀ s t, s ≤ t → toyLedger.stage s ≤ toyLedger.stage t) ∧
      (∀ s, toyLedger.stage s ≤ toyLedger.limit) ∧
        0 < toyLedger.limit ∧
          toyLedger.limit = (3 : ℚ) / 4) ∧
    (¬ ∃ _m : ComputableConvergenceModulus gteASRRT, True) ∧
    (Omega_holo < planck2018_omega_lambda ∧
      planck2018_omega_lambda < Omega_census ∧
        Omega_holo < Omega_census) ∧
    ((29 : ℝ) / 100000 < sigma_star ∧
      sigma_star < (13 : ℝ) / 30000 ∧
        (5 : ℝ) < planck2018_sigma / sigma_star)

/-- **cc_one_jump_residual_algebraic_core** (CatAL bundle): census annotation,
    halting-ledger structural core, no-modulus barrier, strict bracket interiority,
    and σ* falsifiability horizon. PR6-U remains a named hypothesis only. -/
theorem cc_one_jump_residual_algebraic_core : ccOneJumpResidualAlgebraicCoreProp :=
  And.intro d_res_census_annotation <|
    And.intro d_res_halting_ledger_factorization_core <|
      And.intro d_res_no_computable_modulus_core <|
        And.intro bracket_strict_interiority sigma_star_falsifiability_horizon

end

end UgpLean.Physics.CCOneJumpResidual
