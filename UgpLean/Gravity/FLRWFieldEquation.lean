import Mathlib.Analysis.ODE.PicardLindelof
import Mathlib.Analysis.ODE.Gronwall
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Bounds
import Mathlib.Topology.EMetricSpace.Lipschitz
import UgpLean.Spacetime.PhiMDLZ7PotentialMDL

/-!
# Φ_MDL Klein–Gordon equation on an FLRW background — Picard–Lindelöf well-posedness (EPIC_078)

The homogeneous Φ_MDL field equation on a spatially flat FLRW background reduces to

  `φ̈ + 3 H(t) φ̇ + V'(φ) = 0`,

with Z₇ potential `V(φ) = m² (1 − cos 7φ) / 49` and derivative

  `V'(φ) = m² sin(7φ) / 7`.

Writing `y = (φ, φ̇) ∈ ℝ × ℝ`, this is the first-order system

  `ẏ = F(t, y)` with `F(t, (φ, ψ)) = (ψ, −3 H(t) ψ − V'(φ))`.

**CatAL certification:** `V'` is Lipschitz with constant `m²`; for any continuous
Hubble profile with a uniform bound `|H(t)| ≤ H₀`, the state field is Lipschitz on
closed balls. Picard–Lindelöf (`IsPicardLindelof`) then yields a unique local integral
curve for every initial data `(φ₀, φ̇₀)` at time `t₀`.

## Status

CatAL — zero sorry, zero custom axioms.
-/

namespace UgpLean.Gravity.FLRWFieldEquation

open GTE.Spacetime.PhiMDL
open Set Metric
open scoped NNReal

/-- Z₇ potential derivative `V'(φ) = m² sin(7φ) / 7`. -/
noncomputable def z7PotentialDerivative (m φ : ℝ) : ℝ :=
  m ^ 2 * Real.sin (7 * φ) / 7

/-- First-order FLRW state `(φ, φ̇)`. -/
abbrev FLRWState := ℝ × ℝ

/-- First-order vector field for `φ̈ + 3H(t)φ̇ + V'(φ) = 0`. -/
noncomputable def flrwPhimdlVectorField (H : ℝ → ℝ) (m : ℝ) (t : ℝ) (y : FLRWState) : FLRWState :=
  (y.2, -(3 * H t * y.2 + z7PotentialDerivative m y.1))

/-- Lipschitz constant for the `V'` term. -/
noncomputable def potentialLipschitz (m : ℝ) (_hm : 0 < m) : ℝ≥0 :=
  ⟨m ^ 2, sq_nonneg m⟩

/-- A physically admissible FLRW background supplies a continuous Hubble function and a
uniform bound `|H(t)| ≤ hubbleBound`. -/
structure FLRWBackground where
  H : ℝ → ℝ
  continuous_H : Continuous H
  hubbleBound : ℝ≥0
  hubble_bound_spec : ∀ t, |H t| ≤ hubbleBound

namespace FLRWBackground

variable (bg : FLRWBackground)

/-- Lipschitz constant for the first-order FLRW state field, given a uniform Hubble bound. -/
noncomputable def stateLipschitz (m : ℝ) (hm : 0 < m) : ℝ≥0 :=
  max 1 (3 * bg.hubbleBound + potentialLipschitz m hm)

end FLRWBackground

private theorem seven_mul_lipschitz : LipschitzWith 7 (fun φ : ℝ => 7 * φ) := by
  refine LipschitzWith.of_dist_le_mul (K := 7) (f := fun φ => 7 * φ) ?_
  intro x y
  calc
    |7 * x - 7 * y| = |7 * (x - y)| := by ring_nf
    _ = |7| * |x - y| := by rw [abs_mul]
    _ = 7 * |x - y| := by rw [abs_of_pos (show 0 < (7 : ℝ) by norm_num)]
    _ = 7 * dist x y := by rw [Real.dist_eq]
    _ ≤ (7 : ℝ≥0) * dist x y := by norm_cast

/-- **Z₇ potential derivative is Lipschitz** (CatAL).

    `|V'(φ₁) − V'(φ₂)| ≤ m² |φ₁ − φ₂|` because `sin` is 1-Lipschitz and `φ ↦ sin(7φ)` is
    7-Lipschitz. -/
theorem z7_potential_derivative_lipschitz (m : ℝ) (hm : 0 < m) :
    LipschitzWith (potentialLipschitz m hm) (fun φ : ℝ => z7PotentialDerivative m φ) := by
  have hsin7 := Real.lipschitzWith_sin.comp seven_mul_lipschitz
  refine LipschitzWith.of_dist_le_mul (K := potentialLipschitz m hm) ?_
  intro φ₁ φ₂
  have h := hsin7.dist_le_mul φ₁ φ₂
  simp [Function.comp, Real.dist_eq] at h
  rw [potentialLipschitz, Real.dist_eq, z7PotentialDerivative]
  have hm' : 0 ≤ m := le_of_lt hm
  calc
    |m ^ 2 * Real.sin (7 * φ₁) / 7 - m ^ 2 * Real.sin (7 * φ₂) / 7|
        = |(m ^ 2 / 7) * (Real.sin (7 * φ₁) - Real.sin (7 * φ₂))| := by ring_nf
    _ = (m ^ 2 / 7) * |Real.sin (7 * φ₁) - Real.sin (7 * φ₂)| := by
        rw [abs_mul, abs_of_nonneg (div_nonneg (pow_nonneg hm' 2) (by norm_num : (0 : ℝ) ≤ 7))]
    _ ≤ (m ^ 2 / 7) * (7 * |φ₁ - φ₂|) := by
        exact mul_le_mul_of_nonneg_left h (by positivity)
    _ = m ^ 2 * |φ₁ - φ₂| := by field_simp
    _ = (m ^ 2 : ℝ) * dist φ₁ φ₂ := by rw [Real.dist_eq]

/-- Bound `|V'(φ)| ≤ m²`. -/
theorem z7_potential_derivative_abs_le (m : ℝ) (hm : 0 < m) (φ : ℝ) :
    |z7PotentialDerivative m φ| ≤ m ^ 2 := by
  have h :
      |z7PotentialDerivative m φ| = m ^ 2 * |Real.sin (7 * φ)| / 7 := by
    simp [z7PotentialDerivative, abs_div, abs_mul, abs_of_nonneg (pow_nonneg (le_of_lt hm) 2),
      abs_of_pos (show 0 < (7 : ℝ) by norm_num)]
  rw [h]
  nlinarith [Real.abs_sin_le_one (7 * φ), abs_nonneg (Real.sin (7 * φ))]

private theorem dist_snd_le (y₁ y₂ : FLRWState) : dist y₁.2 y₂.2 ≤ dist y₁ y₂ := by
  rw [Prod.dist_eq]
  exact le_max_right _ _

private theorem dist_fst_le (y₁ y₂ : FLRWState) : dist y₁.1 y₂.1 ≤ dist y₁ y₂ := by
  rw [Prod.dist_eq]
  exact le_max_left _ _

/-- The first-order FLRW vector field is Lipschitz in state on every time slice. -/
theorem flrw_phimdl_vector_field_lipschitz (bg : FLRWBackground) (m : ℝ) (hm : 0 < m) (t : ℝ) :
    LipschitzWith (bg.stateLipschitz m hm) (flrwPhimdlVectorField bg.H m t) := by
  have hV := z7_potential_derivative_lipschitz m hm
  refine LipschitzWith.of_dist_le_mul (K := bg.stateLipschitz m hm) ?_
  intro y₁ y₂
  simp only [flrwPhimdlVectorField, FLRWBackground.stateLipschitz, Prod.dist_eq]
  have hH := bg.hubble_bound_spec t
  have hVp := hV.dist_le_mul y₁.1 y₂.1
  rw [potentialLipschitz, Real.dist_eq] at hVp
  have hψ :
      dist y₁.2 y₂.2 ≤ max 1 (3 * bg.hubbleBound + potentialLipschitz m hm) * dist y₁ y₂ := by
    calc
      dist y₁.2 y₂.2 ≤ dist y₁ y₂ := dist_snd_le y₁ y₂
      _ ≤ 1 * dist y₁ y₂ := by rw [one_mul]
      _ ≤ max 1 (3 * bg.hubbleBound + potentialLipschitz m hm) * dist y₁ y₂ :=
        mul_le_mul_of_nonneg_right (le_max_left _ _) dist_nonneg
  have hHmul :
      |3 * bg.H t * (y₁.2 - y₂.2)| ≤ 3 * (bg.hubbleBound : ℝ) * dist y₁.2 y₂.2 := by
    have heq : |3 * bg.H t * (y₁.2 - y₂.2)| = 3 * |bg.H t| * |y₁.2 - y₂.2| := by
      rw [abs_mul (3 * bg.H t) (y₁.2 - y₂.2), abs_mul (3 : ℝ) (bg.H t),
        abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
    rw [heq, Real.dist_eq]
    gcongr
  have hacc :
      dist (-(3 * bg.H t * y₁.2 + z7PotentialDerivative m y₁.1))
        (-(3 * bg.H t * y₂.2 + z7PotentialDerivative m y₂.1))
        ≤ max 1 (3 * bg.hubbleBound + potentialLipschitz m hm) * dist y₁ y₂ := by
    rw [Real.dist_eq]
    have hsum :
        |3 * bg.H t * y₁.2 + z7PotentialDerivative m y₁.1 -
            (3 * bg.H t * y₂.2 + z7PotentialDerivative m y₂.1)|
          ≤ |3 * bg.H t * (y₁.2 - y₂.2)| + |z7PotentialDerivative m y₁.1 - z7PotentialDerivative m y₂.1| := by
      rw [show 3 * bg.H t * y₁.2 + z7PotentialDerivative m y₁.1 -
              (3 * bg.H t * y₂.2 + z7PotentialDerivative m y₂.1) =
            3 * bg.H t * (y₁.2 - y₂.2) + (z7PotentialDerivative m y₁.1 - z7PotentialDerivative m y₂.1) by ring]
      exact abs_add_le _ _
    calc
      |-(3 * bg.H t * y₁.2 + z7PotentialDerivative m y₁.1) -
          (-(3 * bg.H t * y₂.2 + z7PotentialDerivative m y₂.1))|
          = |3 * bg.H t * y₁.2 + z7PotentialDerivative m y₁.1 -
              (3 * bg.H t * y₂.2 + z7PotentialDerivative m y₂.1)| := by
            rw [abs_sub_comm]
            congr 1
            ring
      _ ≤ |3 * bg.H t * (y₁.2 - y₂.2)| + |z7PotentialDerivative m y₁.1 - z7PotentialDerivative m y₂.1| := hsum
      _ ≤ 3 * (bg.hubbleBound : ℝ) * dist y₁.2 y₂.2 + (m ^ 2 : ℝ) * dist y₁.1 y₂.1 := add_le_add hHmul hVp
      _ ≤ (3 * (bg.hubbleBound : ℝ) + m ^ 2) * dist y₁ y₂ := by
            rw [add_mul]
            exact add_le_add
              (mul_le_mul_of_nonneg_left (dist_snd_le y₁ y₂) (by positivity))
              (mul_le_mul_of_nonneg_left (dist_fst_le y₁ y₂) (by positivity))
      _ ≤ max 1 (3 * bg.hubbleBound + potentialLipschitz m hm) * dist y₁ y₂ :=
            mul_le_mul_of_nonneg_right (le_max_right _ _) dist_nonneg
  exact max_le hψ hacc

/-- Nonnegative vector-field norm bound used in Picard–Lindelöf hypotheses. -/
noncomputable def flrwPhimdlVectorFieldNormBound (bg : FLRWBackground) (m : ℝ) (_hm : 0 < m)
    (x₀ : FLRWState) (a : ℝ≥0) : ℝ≥0 :=
  ⟨a + ‖x₀.2‖ + m ^ 2 + 3 * bg.hubbleBound * (a + ‖x₀.2‖), by positivity⟩

/-- Bound on the vector-field norm on a closed ball. -/
private theorem flrw_phimdl_vector_field_norm_le
    (bg : FLRWBackground) (m : ℝ) (hm : 0 < m) (t : ℝ) (x₀ : FLRWState) (a : ℝ≥0)
    (y : FLRWState) (hy : y ∈ closedBall x₀ a) :
    ‖flrwPhimdlVectorField bg.H m t y‖ ≤ flrwPhimdlVectorFieldNormBound bg m hm x₀ a := by
  simp only [flrwPhimdlVectorField, flrwPhimdlVectorFieldNormBound, Prod.norm_def]
  have hball := mem_closedBall.mp hy
  have hdist : |y.2 - x₀.2| ≤ (a : ℝ) := by simpa [Real.dist_eq] using le_trans (dist_snd_le y x₀) hball
  have hψ : |y.2| ≤ (a : ℝ) + ‖x₀.2‖ := by
    calc
      |y.2| = |y.2 - x₀.2 + x₀.2| := by ring_nf
      _ ≤ |y.2 - x₀.2| + |x₀.2| := abs_add_le _ _
      _ ≤ (a : ℝ) + ‖x₀.2‖ := add_le_add hdist (by simpa using abs_le_self x₀.2)
  have hV := z7_potential_derivative_abs_le m hm y.1
  have hH := bg.hubble_bound_spec t
  have hψ' : |y.2| ≤ (a : ℝ) + |x₀.2| := by
    rw [← Real.norm_eq_abs] at hψ
    exact hψ
  have hmul :
      |3 * bg.H t * y.2| = 3 * |bg.H t| * |y.2| := by
    rw [abs_mul (3 * bg.H t) y.2, abs_mul (3 : ℝ) (bg.H t),
      abs_of_nonneg (by norm_num : (0 : ℝ) ≤ 3)]
  have hacc :
      |-(3 * bg.H t * y.2 + z7PotentialDerivative m y.1)|
        ≤ 3 * (bg.hubbleBound : ℝ) * |y.2| + m ^ 2 := by
    calc
      |-(3 * bg.H t * y.2 + z7PotentialDerivative m y.1)|
          = |3 * bg.H t * y.2 + z7PotentialDerivative m y.1| := abs_neg _
      _ ≤ |3 * bg.H t * y.2| + |z7PotentialDerivative m y.1| := abs_add_le _ _
      _ ≤ 3 * |bg.H t| * |y.2| + m ^ 2 := by
            rw [hmul]
            exact add_le_add_right hV _
      _ ≤ 3 * (bg.hubbleBound : ℝ) * |y.2| + m ^ 2 := by
        have hstep :
            3 * |bg.H t| * |y.2| ≤ 3 * (bg.hubbleBound : ℝ) * |y.2| := by
          gcongr
        exact add_le_add hstep le_rfl
  have htail : 0 ≤ m ^ 2 + 3 * (bg.hubbleBound : ℝ) * ((a : ℝ) + |x₀.2|) := by positivity
  have hmono :
      (a : ℝ) + |x₀.2| ≤
        (a : ℝ) + |x₀.2| + m ^ 2 + 3 * (bg.hubbleBound : ℝ) * ((a : ℝ) + |x₀.2|) := by
    simpa [add_assoc, add_left_comm, add_comm] using
      le_add_of_nonneg_right (a := (a : ℝ) + |x₀.2|) htail
  have hψ_bound : |y.2| ≤ (flrwPhimdlVectorFieldNormBound bg m hm x₀ a : ℝ) := by
    simp only [flrwPhimdlVectorFieldNormBound, Real.norm_eq_abs]
    exact le_trans hψ' hmono
  have hacc_bound :
      3 * (bg.hubbleBound : ℝ) * |y.2| + m ^ 2 ≤
        (flrwPhimdlVectorFieldNormBound bg m hm x₀ a : ℝ) := by
    simp only [flrwPhimdlVectorFieldNormBound, Real.norm_eq_abs]
    have h1 :
        3 * (bg.hubbleBound : ℝ) * |y.2| ≤
          3 * (bg.hubbleBound : ℝ) * ((a : ℝ) + |x₀.2|) :=
      mul_le_mul_of_nonneg_left hψ' (show 0 ≤ 3 * (bg.hubbleBound : ℝ) from by positivity)
    have h2 :
        3 * (bg.hubbleBound : ℝ) * ((a : ℝ) + |x₀.2|) + m ^ 2 ≤
          (a : ℝ) + |x₀.2| + m ^ 2 + 3 * (bg.hubbleBound : ℝ) * ((a : ℝ) + |x₀.2|) := by
      linarith [show 0 ≤ (a : ℝ) + |x₀.2| from by positivity]
    exact le_trans (add_le_add h1 le_rfl) h2
  exact max_le (by simpa [Real.norm_eq_abs] using hψ_bound)
    (by simpa [Real.norm_eq_abs] using le_trans hacc hacc_bound)

/-- Build Picard–Lindelöf hypotheses on a symmetric interval around `t₀`. -/
noncomputable def flrwPhimdl_picardData (bg : FLRWBackground) (m : ℝ) (hm : 0 < m)
    (t₀ : ℝ) (x₀ : FLRWState) (a : ℝ≥0) (ha : 0 < a) (ε : ℝ) (hε : 0 < ε)
    (hε_le : ε ≤ (a : ℝ) / (2 * (flrwPhimdlVectorFieldNormBound bg m hm x₀ a + 1))) :
    IsPicardLindelof (flrwPhimdlVectorField bg.H m)
      (tmin := t₀ - ε) (tmax := t₀ + ε)
      ⟨t₀, by constructor <;> linarith [hε]⟩
      x₀ a 0 (flrwPhimdlVectorFieldNormBound bg m hm x₀ a) (bg.stateLipschitz m hm) where
  lipschitzOnWith t _ := (flrw_phimdl_vector_field_lipschitz bg m hm t).lipschitzOnWith
  continuousOn x hx := by
    apply ContinuousOn.prodMk
    · exact continuousOn_const
    · refine ContinuousOn.neg (ContinuousOn.add ?_ continuousOn_const)
      exact (continuousOn_const.mul bg.continuous_H.continuousOn).mul continuousOn_const
  norm_le t _ y hy := flrw_phimdl_vector_field_norm_le bg m hm t x₀ a y hy
  mul_max_le := by
    simp only [add_sub_cancel_left, sub_sub_cancel, max_self]
    set L := flrwPhimdlVectorFieldNormBound bg m hm x₀ a
    have hL : 0 ≤ (L : ℝ) := by positivity
    have hdiv : (L : ℝ) / (2 * ((L : ℝ) + 1)) ≤ 1 := by
      rw [div_le_one (by positivity : (0 : ℝ) < 2 * ((L : ℝ) + 1))]
      linarith
    have hchain :
        (L : ℝ) * ((a : ℝ) / (2 * ((L : ℝ) + 1))) ≤ (a : ℝ) := by
      calc
        (L : ℝ) * ((a : ℝ) / (2 * ((L : ℝ) + 1)))
            = (a : ℝ) * ((L : ℝ) / (2 * ((L : ℝ) + 1))) := by ring
        _ ≤ (a : ℝ) * 1 := mul_le_mul_of_nonneg_left hdiv (by exact_mod_cast le_of_lt ha)
        _ = (a : ℝ) := mul_one _
    refine le_trans (mul_le_mul_of_nonneg_left hε_le hL) ?_
    simp [sub_zero]
    exact hchain

/-- **Picard–Lindelöf existence** for the Φ_MDL-FLRW first-order system (CatAL). -/
theorem flrw_phimdl_local_solution_exists (bg : FLRWBackground) (m : ℝ) (hm : 0 < m)
    (t₀ : ℝ) (x₀ : FLRWState) :
    ∃ ε > 0, ∃ α : ℝ → FLRWState, α t₀ = x₀ ∧
      ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
        HasDerivWithinAt α (flrwPhimdlVectorField bg.H m t (α t)) (Icc (t₀ - ε) (t₀ + ε)) t := by
  let a : ℝ≥0 := 1
  have ha : 0 < a := zero_lt_one
  let L := flrwPhimdlVectorFieldNormBound bg m hm x₀ a
  let denom : ℝ := 2 * (L + 1)
  have hden : 0 < denom := by positivity
  let ε : ℝ := (a : ℝ) / denom
  have hε : 0 < ε := div_pos (by exact_mod_cast ha) hden
  have hε_le : ε ≤ (a : ℝ) / (2 * (L + 1)) := by simp [ε, denom]
  let hf := flrwPhimdl_picardData bg m hm t₀ x₀ a ha ε hε hε_le
  obtain ⟨α, hα₀, hα⟩ := hf.exists_eq_forall_mem_Icc_hasDerivWithinAt₀
  exact ⟨ε, hε, α, hα₀, hα⟩

/-- Uniqueness of FLRW Φ_MDL solutions on the Picard interval. -/
theorem flrw_phimdl_local_solution_unique (bg : FLRWBackground) (m : ℝ) (hm : 0 < m)
    {t₀ ε : ℝ} (hε : 0 < ε) (α β : ℝ → FLRWState)
    (hα₀ : α t₀ = β t₀)
    (hα : ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
      HasDerivWithinAt α (flrwPhimdlVectorField bg.H m t (α t)) (Icc (t₀ - ε) (t₀ + ε)) t)
    (hβ : ∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
      HasDerivWithinAt β (flrwPhimdlVectorField bg.H m t (β t)) (Icc (t₀ - ε) (t₀ + ε)) t) :
    EqOn α β (Icc (t₀ - ε) (t₀ + ε)) :=
  ODE_solution_unique_of_mem_Icc
    (v := flrwPhimdlVectorField bg.H m)
    (K := bg.stateLipschitz m hm)
    (s := fun _ => Set.univ)
    (a := t₀ - ε) (b := t₀ + ε)
    (t₀ := t₀) (f := α) (g := β)
    (by intro t' ht'; exact (flrw_phimdl_vector_field_lipschitz bg m hm t').lipschitzOnWith)
    (by constructor <;> linarith [hε])
    (HasDerivWithinAt.continuousOn hα)
    (fun t' ht' => (hα t' (Ioo_subset_Icc_self ht')).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2))
    (fun _ _ => trivial)
    (HasDerivWithinAt.continuousOn hβ)
    (fun t' ht' => (hβ t' (Ioo_subset_Icc_self ht')).hasDerivAt (Icc_mem_nhds ht'.1 ht'.2))
    (fun _ _ => trivial)
    hα₀

/-- **Well-posedness certificate** (CatAL): existence and interval-uniqueness via
Picard–Lindelöf + Gronwall. -/
theorem flrw_phimdl_equation_well_defined (bg : FLRWBackground) (m : ℝ) (hm : 0 < m)
    (t₀ : ℝ) (x₀ : FLRWState) :
    ∃ ε > 0, ∃ α : ℝ → FLRWState,
      α t₀ = x₀ ∧
        (∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
          HasDerivWithinAt α (flrwPhimdlVectorField bg.H m t (α t))
            (Icc (t₀ - ε) (t₀ + ε)) t) ∧
        ∀ β : ℝ → FLRWState,
          β t₀ = x₀ →
            (∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
              HasDerivWithinAt β (flrwPhimdlVectorField bg.H m t (β t))
                (Icc (t₀ - ε) (t₀ + ε)) t) →
              EqOn α β (Icc (t₀ - ε) (t₀ + ε)) := by
  obtain ⟨ε, hε, α, hα₀, hα⟩ := flrw_phimdl_local_solution_exists bg m hm t₀ x₀
  exact ⟨ε, hε, ⟨α, hα₀, hα, fun β hβ₀ hβ =>
    flrw_phimdl_local_solution_unique bg m hm hε α β (by rw [hα₀, hβ₀]) hα hβ⟩⟩

/-- Corollary: the Lipschitz constant for `V'` alone is `m²`. -/
theorem flrw_phimdl_potential_lipschitz_constant (m : ℝ) (hm : 0 < m) :
    ∃ L : ℝ≥0, L = potentialLipschitz m hm ∧
      LipschitzWith L (fun φ : ℝ => z7PotentialDerivative m φ) :=
  ⟨potentialLipschitz m hm, rfl, z7_potential_derivative_lipschitz m hm⟩

/-- Master bundle for EPIC_078 board: well-posedness + Lipschitz certificate. -/
theorem epic_078_flrw_phimdl_well_posed (bg : FLRWBackground) (m : ℝ) (hm : 0 < m)
    (t₀ : ℝ) (x₀ : FLRWState) :
    (∃ ε > 0, ∃ α : ℝ → FLRWState,
      α t₀ = x₀ ∧
        (∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
          HasDerivWithinAt α (flrwPhimdlVectorField bg.H m t (α t))
            (Icc (t₀ - ε) (t₀ + ε)) t) ∧
        ∀ β : ℝ → FLRWState,
          β t₀ = x₀ →
            (∀ t ∈ Icc (t₀ - ε) (t₀ + ε),
              HasDerivWithinAt β (flrwPhimdlVectorField bg.H m t (β t))
                (Icc (t₀ - ε) (t₀ + ε)) t) →
              EqOn α β (Icc (t₀ - ε) (t₀ + ε))) ∧
    (∃ L : ℝ≥0, L = potentialLipschitz m hm ∧
      LipschitzWith L (fun φ : ℝ => z7PotentialDerivative m φ)) :=
  ⟨flrw_phimdl_equation_well_defined bg m hm t₀ x₀,
   flrw_phimdl_potential_lipschitz_constant m hm⟩

end UgpLean.Gravity.FLRWFieldEquation
