-- SRRGNoGo.lean
-- Machine-checked formalization of the SRRG no-go theorem for dimensional transmutation.
--
-- THEOREM (SRRG No-Go):
--   The SRRG β-function β_η = κ(η − η₁)(η − η₂) with simple zeros at η₁, η₂
--   prevents finite-scale dimensional transmutation.
--
-- KEY ARGUMENT:
--   The Callan-Symanzik DT integral
--     I(η₁, η₂) = ∫_{η₁}^{η₂} dη / β_η
--   is not well-defined (the integrand is not interval-integrable) because:
--     near η₁: β_η ≈ κ(η₁ − η₂)(η − η₁)  [simple zero]
--     so 1/β_η ~ 1/(C(η − η₁)) which is NOT integrable at η₁.
--   Mathlib key: not_intervalIntegrable_of_sub_inv_isBigO_punctured.
--
-- PHYSICAL CONSEQUENCE:
--   The SRRG η-flow cannot generate the EW scale v ≈ 246 GeV through
--   dimensional transmutation. v remains a Category A/D anchor in UGP/PSC.
--
-- PROOF STATUS:
--   All sorries closed. Main theorem and all supporting lemmas fully proved.

import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.Analysis.SpecialFunctions.NonIntegrable
import Mathlib.Analysis.SpecialFunctions.Integrability.Basic
import Mathlib.Analysis.Calculus.Deriv.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Order.Filter.Basic

open scoped Topology
open Real Filter Set MeasureTheory intervalIntegral Asymptotics

noncomputable section

-- ─── Definition ────────────────────────────────────────────────────────────

/-- The SRRG β-function with simple zeros at η₁ and η₂. -/
def betaEta (κ η₁ η₂ η : ℝ) : ℝ := κ * (η - η₁) * (η - η₂)

-- ─── Basic algebraic properties ────────────────────────────────────────────

theorem betaEta_zero_at_eta1 (κ η₁ η₂ : ℝ) : betaEta κ η₁ η₂ η₁ = 0 := by
  simp [betaEta]

theorem betaEta_zero_at_eta2 (κ η₁ η₂ : ℝ) : betaEta κ η₁ η₂ η₂ = 0 := by
  simp [betaEta]

/-- In the interior (η₁ < η < η₂), β_η ≠ 0 when κ ≠ 0. -/
theorem betaEta_nonzero_interior (κ η₁ η₂ η : ℝ)
    (hκ : κ ≠ 0) (hη : η₁ < η) (hη2 : η < η₂) :
    betaEta κ η₁ η₂ η ≠ 0 := by
  simp only [betaEta, ne_eq]
  exact mul_ne_zero (mul_ne_zero hκ (sub_ne_zero.mpr hη.ne')) (sub_ne_zero.mpr hη2.ne)

-- ─── Linear behavior near the lower zero ────────────────────────────────────

/-- β_η / (η − η₁) = κ(η − η₂) for all η ≠ η₁ (the simple-zero factorization). -/
theorem betaEta_linear_zero_at_eta1 (κ η₁ η₂ : ℝ) (_hη : η₁ < η₂) (η : ℝ) (hne : η ≠ η₁) :
    betaEta κ η₁ η₂ η / (η - η₁) = κ * (η - η₂) := by
  simp only [betaEta]
  field_simp [sub_ne_zero.mpr hne]

/-- The limit of β_η / (η − η₁) at η₁ is κ(η₁ − η₂) (nonzero when κ ≠ 0, η₁ ≠ η₂). -/
theorem betaEta_simple_zero_limit (κ η₁ η₂ : ℝ) (_hκ : κ ≠ 0) (hη : η₁ < η₂) :
    Filter.Tendsto (fun η => betaEta κ η₁ η₂ η / (η - η₁))
                   (𝓝[≠] η₁) (𝓝 (κ * (η₁ - η₂))) := by
  have key : (fun η => betaEta κ η₁ η₂ η / (η - η₁)) =ᶠ[𝓝[≠] η₁] (fun η => κ * (η - η₂)) :=
    eventually_nhdsWithin_of_forall fun η hne =>
      betaEta_linear_zero_at_eta1 κ η₁ η₂ hη η hne
  have hg : Filter.Tendsto (fun η => κ * (η - η₂)) (𝓝[≠] η₁) (𝓝 (κ * (η₁ - η₂))) := by
    have : ContinuousAt (fun η : ℝ => κ * (η - η₂)) η₁ := by fun_prop
    exact this.tendsto.mono_left nhdsWithin_le_nhds
  exact hg.congr' key.symm

-- ─── Key BigO: (η − η₁)⁻¹ = O(1/β_η) near η₁ ────────────────────────────

/-- Near η₁, (η − η₁)⁻¹ = O(1/β_η) in the 𝓝[≠] sense.

    Proof: factorization (η−η₁)⁻¹ = κ(η−η₂) · (1/β_η) for η ≠ η₁, η ≠ η₂;
    κ(η−η₂) → κ(η₁−η₂) is continuous and bounded near η₁, giving the bound. -/
private lemma sub_inv_isBigO_betaEta_inv (κ η₁ η₂ : ℝ) (hκ : κ ≠ 0) (hη : η₁ < η₂) :
    (fun η => (η - η₁)⁻¹) =O[𝓝[≠] η₁] (fun η => 1 / betaEta κ η₁ η₂ η) := by
  -- η₂ ∉ 𝓝[≠] η₁ for small enough neighborhoods (since η₂ ≠ η₁)
  have hne₂ : ∀ᶠ η in 𝓝[≠] η₁, η ≠ η₂ := by
    apply eventually_nhdsWithin_of_eventually_nhds
    have h : η₁ ∈ ({η₂} : Set ℝ)ᶜ := by simp [hη.ne]
    exact isOpen_compl_singleton.mem_nhds h
  -- Factorization: (η−η₁)⁻¹ = κ(η−η₂) · (1/β_η) when η ≠ η₁, η ≠ η₂
  have heq : ∀ᶠ η in 𝓝[≠] η₁, (η - η₁)⁻¹ = κ * (η - η₂) * (1 / betaEta κ η₁ η₂ η) := by
    filter_upwards [self_mem_nhdsWithin, hne₂] with η hne₁ hne₂
    simp only [betaEta, one_div]
    field_simp [hκ, sub_ne_zero.mpr hne₁, sub_ne_zero.mpr hne₂]
  -- κ(η−η₂) is bounded: |κ(η−η₂)| ≤ ‖κ(η₁−η₂)‖ + 1 near η₁
  set M := ‖κ * (η₁ - η₂)‖ + 1
  have hbnd : ∀ᶠ η in 𝓝[≠] η₁, ‖κ * (η - η₂)‖ ≤ M := by
    have hcts : ContinuousAt (fun η : ℝ => κ * (η - η₂)) η₁ := by fun_prop
    have htend : Filter.Tendsto (fun η => κ * (η - η₂)) (𝓝[≠] η₁) (𝓝 (κ * (η₁ - η₂))) :=
      hcts.tendsto.mono_left nhdsWithin_le_nhds
    exact htend.norm.eventually (Iic_mem_nhds (lt_add_one _))
  -- Combine: ‖(η−η₁)⁻¹‖ = ‖κ(η−η₂)‖ · ‖1/β_η‖ ≤ M · ‖1/β_η‖
  apply IsBigO.of_bound M
  filter_upwards [heq, hbnd] with η h1 h2
  rw [h1, norm_mul]
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

-- ─── The integrand 1/β_η is not interval-integrable ─────────────────────

/-- On [η₁, η₁+ε] (with 0 < ε < η₂−η₁), the integrand 1/β_η is NOT
    interval-integrable. The singularity at η₁ is of type (η−η₁)⁻¹ which is
    not L¹ near 0. -/
theorem integrand_not_integrable_at_lower_zero (κ η₁ η₂ : ℝ)
    (hκ : κ ≠ 0) (hη : η₁ < η₂) (ε : ℝ) (hε : 0 < ε) (_hεη : ε < η₂ - η₁) :
    ¬ IntervalIntegrable (fun η => 1 / betaEta κ η₁ η₂ η) volume η₁ (η₁ + ε) :=
  not_intervalIntegrable_of_sub_inv_isBigO_punctured
    (sub_inv_isBigO_betaEta_inv κ η₁ η₂ hκ hη)
    (by linarith)
    left_mem_uIcc

-- ─── The full DT integral is not well-defined ─────────────────────────────

/-- The integrand 1/β_η is NOT interval-integrable on [η₁, η₂]:
    the DT integral I = ∫_{η₁}^{η₂} dη/β_η does not exist as an L¹ integral. -/
theorem dt_integral_diverges (κ η₁ η₂ : ℝ) (hκ : κ ≠ 0) (hη : η₁ < η₂) :
    ¬ IntervalIntegrable (fun η => 1 / betaEta κ η₁ η₂ η) volume η₁ η₂ :=
  not_intervalIntegrable_of_sub_inv_isBigO_punctured
    (sub_inv_isBigO_betaEta_inv κ η₁ η₂ hκ hη)
    hη.ne
    left_mem_uIcc

-- ─── Main no-go theorem ─────────────────────────────────────────────────────

/-- SRRG No-Go Theorem (machine-checked):
    With β_η = κ(η − η₁)(η − η₂) having simple zeros at both endpoints,
    the integrand 1/β_η is NOT in L¹[η₁, η₂].

    Physical reading: The SRRG η-flow cannot generate the EW scale v ≈ 246 GeV
    through dimensional transmutation. v remains a Category A/D anchor in UGP/PSC. -/
theorem srrg_no_dimensional_transmutation (κ η₁ η₂ : ℝ)
    (hκ : κ ≠ 0) (hη : η₁ < η₂) :
    ¬ IntervalIntegrable (fun η => 1 / betaEta κ η₁ η₂ η) volume η₁ η₂ :=
  dt_integral_diverges κ η₁ η₂ hκ hη

-- ─── Higgs quartic corollary ─────────────────────────────────────────────

/-- The Higgs quartic DT integrand 1/(b₀λ²) is NOT interval-integrable on [0,1].
    Stronger singularity (λ⁻² vs λ⁻¹), same conclusion: no finite DT scale.

    Proof: λ⁻¹ = b₀λ · (1/(b₀λ²)) and b₀λ → 0 near 0, so λ⁻¹ = O(1/(b₀λ²)).
    Apply not_intervalIntegrable_of_sub_inv_isBigO_punctured with c = 0. -/
theorem higgs_quartic_no_dt (b₀ : ℝ) (hb₀ : b₀ > 0) :
    ¬ IntervalIntegrable (fun lam => 1 / (b₀ * lam ^ 2)) volume 0 1 := by
  apply not_intervalIntegrable_of_sub_inv_isBigO_punctured
      _ (by norm_num : (0 : ℝ) ≠ 1) left_mem_uIcc
  simp only [sub_zero]
  -- Factorization: lam⁻¹ = b₀·lam · (1/(b₀·lam²)) for lam ≠ 0
  have heq : ∀ᶠ lam in 𝓝[≠] (0 : ℝ), lam⁻¹ = b₀ * lam * (1 / (b₀ * lam ^ 2)) := by
    filter_upwards [self_mem_nhdsWithin] with lam hlam
    field_simp [hb₀.ne', pow_ne_zero 2 hlam, hlam]
  -- b₀·lam is bounded near 0 (tends to 0, so eventually ‖b₀·lam‖ < 1)
  have hbnd : ∀ᶠ lam in 𝓝[≠] (0 : ℝ), ‖b₀ * lam‖ ≤ 1 := by
    have hcts : ContinuousAt (fun lam : ℝ => b₀ * lam) 0 := by fun_prop
    have htend : Filter.Tendsto (fun lam => b₀ * lam) (𝓝[≠] (0 : ℝ)) (𝓝 0) := by
      have h := hcts.tendsto
      simp only [mul_zero] at h
      exact tendsto_nhdsWithin_of_tendsto_nhds h
    have hlt : ∀ᶠ lam in 𝓝[≠] (0 : ℝ), ‖b₀ * lam‖ < 1 :=
      htend.norm.eventually (Iio_mem_nhds (by norm_num : ‖(0 : ℝ)‖ < 1))
    exact hlt.mono (fun _ h => le_of_lt h)
  -- ‖lam⁻¹‖ = ‖b₀·lam‖ · ‖1/(b₀·lam²)‖ ≤ 1 · ‖1/(b₀·lam²)‖
  apply IsBigO.of_bound 1
  filter_upwards [heq, hbnd] with lam h1 h2
  rw [h1, norm_mul]
  exact mul_le_mul_of_nonneg_right h2 (norm_nonneg _)

-- ─── Contrast remark ─────────────────────────────────────────────────────

/-- For contrast: QCD DT is possible via Λ_QCD = μ · exp(−1/(b₀αs(μ))),
    a closed-form that bypasses the integral obstruction. The Higgs has no
    such mechanism. -/
theorem qcd_contrast_remark : True := trivial

end

-- To import: import UgpLean.VEVNoGo.SRRGNoGo
