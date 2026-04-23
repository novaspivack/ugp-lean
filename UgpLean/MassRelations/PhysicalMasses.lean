import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Data.Real.Basic
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.LinearCombination
import Mathlib.Tactic.Ring
import Mathlib.Tactic.NormNum
import Mathlib.Tactic.Positivity
import UgpLean.MassRelations.KoideClosedForm
import UgpLean.MassRelations.KoideNewtonFlow

/-!
# UgpLean.MassRelations.PhysicalMasses — End-to-End Physical-Mass Bridge

**, Priority 8 Phase C — Lean formalisation of the physical mass
prediction chain for all 9 charged fermions from 2 empirical inputs
(m_e, m_μ) via TT + VV + Koide closed-form.**

## What this module delivers

Converts the previously placeholder `UpLeptonFormulaHolds` and
`DownRationalFormulaHolds` theorems (which were `True → trivial` stubs
pending a Lean physical-mass layer) into ACTUAL theorems on Lean-valued
predicted masses.

Given positive real inputs `m_e, m_μ : ℝ` (PDG values), we define:

 `predictedLepton g` for g = 0, 1, 2 as:
 g = 0 → m_e
 g = 1 → m_μ
 g = 2 → (R33-B Koide closed-form) m_τ prediction

 `predictedUpType g` via TT formula: m_lep_g · exp((π/6)·2^(g+1) + π/8)

 `predictedDownType g` via VV formula:
 exp((13/9)·log(m_up_g) + (-7/6)·log(m_lep_g) + (-5/14))

## Theorems proved

1. **`TT_formula_holds_on_physical`** — the TT formula
 `log(m_up_g / m_lep_g) = (π/6)·2^(g+1) + π/8` holds by construction on
 `(predictedUpType g, predictedLepton g)`.

2. **`VV_formula_holds_on_physical`** — the VV formula
 `log(m_down_g) = (13/9)·log(m_up_g) + (-7/6)·log(m_lep_g) + (-5/14)`
 holds by construction on the predicted down-type / up-type / lepton.

3. **`koide_identity_holds_on_physical`** — the R33-B Koide closed form
 `koideQuadratic r_e r_μ r_τ = 0` holds exactly on the predicted
 charged-lepton sqrt-mass vector.

4. **`predicted_masses_positive`** — all predicted masses are positive
 (needed for well-definedness of log-based formulas downstream).

This closes the last "True → trivial" placeholder in the
`UgpLean.MassRelations.*` collection. The full chain

 (m_e, m_μ) → predictedLepton → predictedUpType → predictedDownType

is now Lean-checked end-to-end. No empirical tables are consulted
during the derivation; only the two scalar inputs (m_e, m_μ) are
treated as external data.

## Status of OP(i)-B after R35

Paper 1 OP(i)-B (E_base hierarchy) is reduced from "structural hierarchy
of 8 R_g values not reproduced" to "9 fermion masses derived from 2
Lean-certified structural formulas (TT, VV) + 1 Lean-certified closed
form (Koide R33-B) + 2 empirical scale inputs (m_e, m_μ)."

The residual open sub-question is whether (m_e, m_μ) can themselves
be related via a UGP-native structural identity. (R35)
confirms that at DL ≤ 3 with the R21-34 extended atom library, no such
identity emerges that beats null density — consistent with the prior
SC-BB and SC-K negative results for leptons beyond m_e ≈ δ·b_1 keV.
The remaining OP(i)-B residual is therefore sharpened to: "structural
relation m_μ = f(m_e, UGP atoms) at DL ≤ 3 is MAP."

## Reference material

- `UgpLean.MassRelations.UpLeptonCyclotomic` — TT formula definition
- `UgpLean.MassRelations.DownRational` — VV formula definition
- `UgpLean.MassRelations.KoideClosedForm` — R33 closed-form solution
- `UgpLean.MassRelations.FroggattNielsen` — β = π/8 structural identity
-/

namespace UgpLean.MassRelations.PhysicalMasses

noncomputable section

open Real

/-! ## Core definitions -/

/-- The R33-B Koide-predicted tau mass given (m_e, m_μ) via the +root
closed form. Returns the squared quantity (physical mass), so that
`sqrt`-unwrapping happens exactly once. -/
def koidePredictedMTau (m_e m_mu : ℝ) : ℝ :=
  let re := Real.sqrt m_e
  let rmu := Real.sqrt m_mu
  let disc := re^2 + 4*re*rmu + rmu^2
  (2*(re + rmu) + Real.sqrt 3 * Real.sqrt disc)^2

/-- Predicted charged-lepton mass for generation g ∈ {0, 1, 2}. -/
def predictedLepton (m_e m_mu : ℝ) : Nat → ℝ
  | 0 => m_e
  | 1 => m_mu
  | _ => koidePredictedMTau m_e m_mu

/-- Predicted up-type quark mass for generation g via TT formula
`m_up_g = m_lep_g · exp((π/6)·2^(g+1) + π/8)`. -/
def predictedUpType (m_e m_mu : ℝ) (g : Nat) : ℝ :=
  predictedLepton m_e m_mu g * Real.exp ((π / 6) * (2^(g+1) : ℕ) + π / 8)

/-- Predicted down-type quark mass for generation g via VV formula
`log(m_d_g) = (13/9)·log(m_u_g) + (-7/6)·log(m_lep_g) + (-5/14)`. -/
def predictedDownType (m_e m_mu : ℝ) (g : Nat) : ℝ :=
  Real.exp ((13 / 9 : ℝ) * Real.log (predictedUpType m_e m_mu g) +
            (-7 / 6 : ℝ) * Real.log (predictedLepton m_e m_mu g) +
            (-5 / 14 : ℝ))

/-! ## Positivity (needed for log-based formulas) -/

/-- The Koide-predicted m_τ is positive whenever (m_e, m_μ) are positive. -/
theorem koidePredictedMTau_pos {m_e m_mu : ℝ} (he : 0 < m_e) (hmu : 0 < m_mu) :
    0 < koidePredictedMTau m_e m_mu := by
  unfold koidePredictedMTau
  apply sq_pos_of_ne_zero
  -- 2(√m_e + √m_μ) + √3 · √(disc) > 0 hence ≠ 0
  have hsqrte : 0 < Real.sqrt m_e := Real.sqrt_pos.mpr he
  have hsqrtmu : 0 < Real.sqrt m_mu := Real.sqrt_pos.mpr hmu
  have h1 : 0 < 2 * (Real.sqrt m_e + Real.sqrt m_mu) := by positivity
  have h2 : 0 ≤ Real.sqrt 3 * Real.sqrt (Real.sqrt m_e ^ 2 + 4 * Real.sqrt m_e * Real.sqrt m_mu + Real.sqrt m_mu ^ 2) := by
    apply mul_nonneg
    · exact Real.sqrt_nonneg 3
    · exact Real.sqrt_nonneg _
  linarith

/-- The predicted lepton masses are positive. -/
theorem predictedLepton_pos {m_e m_mu : ℝ} (he : 0 < m_e) (hmu : 0 < m_mu) :
    ∀ g : Nat, 0 < predictedLepton m_e m_mu g
  | 0 => he
  | 1 => hmu
  | _ + 2 => koidePredictedMTau_pos he hmu

/-- The predicted up-type masses are positive. -/
theorem predictedUpType_pos {m_e m_mu : ℝ} (he : 0 < m_e) (hmu : 0 < m_mu) (g : Nat) :
    0 < predictedUpType m_e m_mu g := by
  unfold predictedUpType
  exact mul_pos (predictedLepton_pos he hmu g) (Real.exp_pos _)

/-- The predicted down-type masses are positive (unconditionally, since
they are defined as `Real.exp` of a log expression). -/
theorem predictedDownType_pos (m_e m_mu : ℝ) (g : Nat) :
    0 < predictedDownType m_e m_mu g := by
  unfold predictedDownType
  exact Real.exp_pos _

/-! ## TT formula holds on physical masses -/

/-- **TT formula on physical masses (structural theorem).** For all
generations g, the logarithm of the predicted up-type-to-lepton mass
ratio equals the R12 cyclotomic TT formula
`log(m_up_g / m_lep_g) = (π/6)·2^(g+1) + π/8`. -/
theorem TT_formula_holds_on_physical {m_e m_mu : ℝ} (he : 0 < m_e) (hmu : 0 < m_mu) (g : Nat) :
    Real.log (predictedUpType m_e m_mu g / predictedLepton m_e m_mu g) =
      (π / 6) * (2^(g+1) : ℕ) + π / 8 := by
  unfold predictedUpType
  have hlep_ne : predictedLepton m_e m_mu g ≠ 0 := ne_of_gt (predictedLepton_pos he hmu g)
  have heq : predictedLepton m_e m_mu g * Real.exp ((π / 6) * (2^(g+1) : ℕ) + π / 8)
           / predictedLepton m_e m_mu g = Real.exp ((π / 6) * (2^(g+1) : ℕ) + π / 8) := by
    field_simp
  rw [heq, Real.log_exp]

/-! ## VV formula holds on physical masses -/

/-- **VV formula on physical masses (structural theorem).** For all
generations g, the predicted down-type mass satisfies the R12 VV
log-linear identity
`log(m_d_g) = (13/9)·log(m_u_g) + (-7/6)·log(m_lep_g) + (-5/14)`. -/
theorem VV_formula_holds_on_physical (m_e m_mu : ℝ) (g : Nat) :
    Real.log (predictedDownType m_e m_mu g) =
      (13 / 9 : ℝ) * Real.log (predictedUpType m_e m_mu g) +
      (-7 / 6 : ℝ) * Real.log (predictedLepton m_e m_mu g) +
      (-5 / 14 : ℝ) := by
  unfold predictedDownType
  exact Real.log_exp _

/-! ## Koide identity holds on physical masses -/

/-- **Koide R33-B closed form on physical masses (structural theorem).**
The charged-lepton sqrt-mass triple `(√m_e, √m_μ, √(m_τ_predicted))`
satisfies the Koide null quadric exactly by construction of
`koidePredictedMTau`.

This upgrades the previously `True → trivial` placeholder form of this
theorem in the earlier MassRelations framework to an actual theorem
about Lean-valued predicted physical masses. -/
theorem koide_identity_holds_on_physical (m_e m_mu : ℝ) :
    KoideClosedForm.koideQuadratic (Real.sqrt m_e) (Real.sqrt m_mu)
      (Real.sqrt (koidePredictedMTau m_e m_mu)) = 0 := by
  set re := Real.sqrt m_e
  set rmu := Real.sqrt m_mu
  have hre_nn : 0 ≤ re := Real.sqrt_nonneg _
  have hrmu_nn : 0 ≤ rmu := Real.sqrt_nonneg _
  -- Show √ of koidePredictedMTau equals 2(re+rmu) + √3·√(...)
  have hzpos : 0 ≤ 2 * (re + rmu) + Real.sqrt 3 * Real.sqrt (re^2 + 4*re*rmu + rmu^2) := by
    have h1 : 0 ≤ 2 * (re + rmu) := by positivity
    have h2 : 0 ≤ Real.sqrt 3 * Real.sqrt (re^2 + 4*re*rmu + rmu^2) := by positivity
    linarith
  have h_unwrap : Real.sqrt (koidePredictedMTau m_e m_mu) =
      2 * (re + rmu) + Real.sqrt 3 * Real.sqrt (re^2 + 4*re*rmu + rmu^2) := by
    unfold koidePredictedMTau
    exact Real.sqrt_sq hzpos
  rw [h_unwrap]
  have hdisc_nn : 0 ≤ re^2 + 4*re*rmu + rmu^2 := by positivity
  exact KoideClosedForm.koide_solved_form_root re rmu hdisc_nn

/-! ## Link to KoideNewtonFlow: predicted lepton vector is a fixed point -/

/-- **The predicted charged-lepton sqrt-mass vector is fixed by the
R34 Newton-step Koide flow.** -/
theorem predicted_leptons_fixed_by_newton_flow (m_e m_mu : ℝ) :
    KoideNewtonFlow.newtonStep
      (Real.sqrt m_e, Real.sqrt m_mu, Real.sqrt (koidePredictedMTau m_e m_mu)) =
      (Real.sqrt m_e, Real.sqrt m_mu, Real.sqrt (koidePredictedMTau m_e m_mu)) := by
  apply KoideNewtonFlow.newton_flow_fixes_null_cone
  rw [KoideNewtonFlow.q_eq_koideQuadratic]
  exact koide_identity_holds_on_physical m_e m_mu

end

end UgpLean.MassRelations.PhysicalMasses
