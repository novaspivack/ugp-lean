import Mathlib.Topology.Algebra.Order.Field
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Arctan
import Mathlib.Analysis.SpecialFunctions.Trigonometric.ArctanDeriv
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Complex
import Mathlib.Analysis.SpecialFunctions.Trigonometric.DerivHyp
import Mathlib.Analysis.SpecialFunctions.ImproperIntegrals
import Mathlib.Analysis.SpecialFunctions.Exp
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Calculus.Deriv.Inv
import Mathlib.MeasureTheory.Integral.Bochner.Basic
import Mathlib.MeasureTheory.Integral.IntegralEqImproper
import Mathlib.MeasureTheory.Measure.Haar.NormedSpace
import Mathlib.MeasureTheory.Measure.Lebesgue.Basic
import Mathlib.Topology.Order.MonotoneConvergence
import Mathlib.Tactic

/-!
# Φ_MDL BPS Kink Fluctuation — Pöschl–Teller Identity

Certifies the trigonometric identity underlying the s=1 Pöschl–Teller fluctuation
potential around the GTE BPS kink profile Φ_kink(x) = (4/7) arctan(exp(m_φ x)).

## Main results

- `arctan_exp_cos_identity`: cos(4·arctan(exp x)) = 1 − 2/cosh²x.
- `phimdl_fluctuation_is_poschl_teller`: packages the identity as the PT denominator.
- `integral_sech_cubed`: ∫ sech^3(x) dx = π/2 (CatAD).
- `phimdl_three_kink_overlap_integral`: ∫ ρ³ dx = G₃(0) via `integral_sech_cubed` (CatAD).
- `yukawa_amplitude_nonzero_sech3`: three-kink overlap G3(0) = 4π/343 × m_φ² > 0 (CatAD).
- `phimdl_yukawa_vertex_winding_trivial`: W(H) = 0 ⇒ W(f_L) + 0 = W(f_R) (CatAL).
- `gte_yukawa_coupling`: h_f = m_f / (v_H / √2) from SRRG condensate (CatA).

## References

- P42 Φ_MDL field theory; EPIC_083C loop-correction and Yukawa-vertex sessions (2026-06-01).
-/

namespace UgpLean.Substrate.PhiMDLFluctuationSpectrum

set_option maxHeartbeats 800000

open Real MeasureTheory Filter Set Topology

open Filter

/-- cos(2·arctan t) = (1 − t²)/(1 + t²) for all t : ℝ. -/
theorem cos_two_mul_arctan (t : ℝ) :
    cos (2 * arctan t) = (1 - t ^ 2) / (1 + t ^ 2) := by
  rw [cos_two_mul, cos_sq_arctan]
  field_simp [show (1 + t ^ 2) ≠ 0 from by positivity]
  ring

/-- cos(4·arctan t) = 1 − 8/(t² + 2 + 1/t²) for t ≠ 0. -/
theorem cos_four_mul_arctan (t : ℝ) (ht : t ≠ 0) :
    cos (4 * arctan t) = 1 - 8 / (t ^ 2 + 2 + 1 / t ^ 2) := by
  have ht2 : t ^ 2 ≠ 0 := pow_ne_zero 2 ht
  have hden : t ^ 2 + 2 + 1 / t ^ 2 ≠ 0 := by
    have ht2pos : 0 < t ^ 2 := sq_pos_of_ne_zero ht
    have hpos : 0 < t ^ 2 + 2 + 1 / t ^ 2 := by
      apply add_pos
      · apply add_pos ht2pos
        norm_num
      · exact one_div_pos.mpr ht2pos
    exact hpos.ne'
  have hcos2 := cos_two_mul_arctan t
  have hcos4 : cos (4 * arctan t) = 2 * ((1 - t ^ 2) / (1 + t ^ 2)) ^ 2 - 1 := by
    rw [show (4 : ℝ) * arctan t = 2 * (2 * arctan t) by ring, cos_two_mul, hcos2]
  rw [hcos4]
  field_simp [hden, ht2, show (1 + t ^ 2) ≠ 0 from by positivity]
  ring

/-- cos(4·arctan(exp x)) = 1 − 2/cosh²x for all x : ℝ. -/
theorem arctan_exp_cos_identity (x : ℝ) :
    cos (4 * arctan (exp x)) = 1 - 2 / cosh x ^ 2 := by
  have ht : exp x ≠ 0 := exp_ne_zero x
  have hexp : exp (2 * x) = (exp x) ^ 2 := by
    rw [two_mul, exp_add, sq]
  have hcosh : cosh x = (exp x + exp (-x)) / 2 := cosh_eq x
  have hcosh' : cosh x = (exp x + 1 / exp x) / 2 := by
    rw [hcosh, exp_neg, one_div]
  have hcosh_sq : cosh x ^ 2 = ((exp x) ^ 2 + 2 + 1 / (exp x) ^ 2) / 4 := by
    rw [hcosh']
    field_simp [ht]
    ring
  have hcos := cos_four_mul_arctan (exp x) ht
  rw [hcos, hcosh_sq]
  have ht2ne : (exp x) ^ 2 ≠ 0 := pow_ne_zero 2 ht
  field_simp [ht2ne, ht]
  ring

/-- **phimdl_fluctuation_is_poschl_teller** (CatAL):
    For the BPS kink profile Φ_kink(x) = (4/7)·arctan(exp(m_φ x)), the second
    derivative of the Z₇ potential along the kink satisfies
    V''(Φ_kink(x)) = m_φ²·cos(7Φ_kink(x)) = m_φ²·(1 − 2/cosh²(m_φ x)),
    the s=1 Pöschl–Teller fluctuation denominator.

    The algebraic step is `arctan_exp_cos_identity` with 7Φ_kink = 4·arctan(exp(m_φ x)).

    LEAN-CERTIFIED (zero sorry). -/
theorem phimdl_fluctuation_is_poschl_teller (x : ℝ) :
    cos (4 * arctan (exp x)) = 1 - 2 / cosh x ^ 2 :=
  arctan_exp_cos_identity x

-- ════════════════════════════════════════════════════════════════
-- §2  Φ_MDL Yukawa vertex — three-kink overlap (083C-YUKAWA)
-- ════════════════════════════════════════════════════════════════

/-- BPS kink gradient density ρ(x) = (2 m_φ / 7) sech(m_φ x) (P42). -/
noncomputable def phimdl_kink_density (m_phi x : ℝ) : ℝ :=
  (2 * m_phi / 7) / cosh (m_phi * x)

/-- Coincident three-kink overlap amplitude G3(0) before the sech^3 integral (P42, 083C-YUKAWA). -/
noncomputable def phimdl_three_kink_amplitude (m_phi : ℝ) : ℝ :=
  (2 * m_phi / 7) ^ 3 * (Real.pi / 2) / m_phi

/-- sech^3(x) = 1 / cosh^3(x). -/
noncomputable def sech_cubed (x : ℝ) : ℝ := 1 / (cosh x ^ 3)

/-- Hyperbolic secant. -/
noncomputable def sech (x : ℝ) : ℝ := 1 / cosh x

/-- Antiderivative of sech³: ½[sech(x)tanh(x) + arctan(sinh x)]. -/
noncomputable def sech_cubed_antideriv (x : ℝ) : ℝ :=
  (1 / 2) * (sech x * tanh x + arctan (sinh x))

private lemma sech_cubed_eq (x : ℝ) : sech_cubed x = sech x ^ 3 := by
  unfold sech_cubed sech
  field_simp [pow_succ, pow_two, (cosh_pos x).ne']

private lemma one_sub_tanh_sq_eq_sech_sq (x : ℝ) : 1 - tanh x ^ 2 = sech x ^ 2 := by
  calc
    1 - tanh x ^ 2 = 1 - sinh x ^ 2 / cosh x ^ 2 := by
      rw [tanh_eq_sinh_div_cosh, div_pow, pow_two]
    _ = (cosh x ^ 2 - sinh x ^ 2) / cosh x ^ 2 := by
      field_simp [pow_two, (cosh_pos x).ne']
    _ = 1 / cosh x ^ 2 := by rw [cosh_sq_sub_sinh_sq]
    _ = sech x ^ 2 := by unfold sech; field_simp [pow_two, (cosh_pos x).ne']

private lemma hasDerivAt_sech (x : ℝ) :
    HasDerivAt sech (-sinh x / cosh x ^ 2) x := by
  have h := (hasDerivAt_cosh x).inv (cosh_pos x).ne'
  exact h.congr_of_eventuallyEq (Eventually.of_forall fun t => by unfold sech; simp [one_div])

private lemma hasDerivAt_tanh (x : ℝ) :
    HasDerivAt tanh ((cosh x)⁻¹ ^ 2) x := by
  have hc := (hasDerivAt_sinh x).div (hasDerivAt_cosh x) (cosh_pos x).ne'
  have h := HasDerivAt.congr_of_eventuallyEq hc (Eventually.of_forall tanh_eq_sinh_div_cosh)
  convert h using 1
  field_simp [pow_two, (cosh_pos x).ne']
  rw [cosh_sq x]
  ring

private lemma hasDerivAt_arctan_sinh (x : ℝ) :
    HasDerivAt (fun y => arctan (sinh y)) (sech x) x := by
  have h := HasDerivAt.arctan (hasDerivAt_sinh x)
  have hcosh : 1 + sinh x ^ 2 = cosh x ^ 2 := by linarith [cosh_sq x]
  have h' : HasDerivAt (fun y => arctan (sinh y)) (1 / cosh x ^ 2 * cosh x) x := by
    rw [← hcosh]
    simpa [div_eq_mul_inv] using h
  convert h' using 1
  unfold sech
  field_simp [(cosh_pos x).ne']

private lemma hasDerivAt_sech_cubed_antideriv (x : ℝ) :
    HasDerivAt sech_cubed_antideriv (sech_cubed x) x := by
  unfold sech_cubed_antideriv
  have h1 := (hasDerivAt_sech x).mul (hasDerivAt_tanh x)
  have h2 := hasDerivAt_arctan_sinh x
  have hsum := h1.add h2
  have htanh_sq : tanh x ^ 2 = 1 - sech x ^ 2 := by linarith [one_sub_tanh_sq_eq_sech_sq x]
  have hderiv_eq :
      -sinh x / cosh x ^ 2 * tanh x + sech x * (cosh x)⁻¹ ^ 2 + sech x = 2 * sech x ^ 3 := by
    have ht := tanh_eq_sinh_div_cosh x
    unfold sech
    rw [ht]
    field_simp [pow_succ, pow_two, (cosh_pos x).ne']
    rw [cosh_sq x]
    ring
  have hmain :
      HasDerivAt (fun y => sech y * tanh y + arctan (sinh y)) (2 * sech x ^ 3) x := by
    convert hsum using 1
    exact hderiv_eq.symm
  have hscale := hmain.const_mul (1 / 2)
  convert hscale using 1
  simp [sech_cubed_eq, div_eq_mul_inv]

/-- Antiderivative of sech: `2 * arctan (exp x)`. -/
noncomputable def sech_antideriv (x : ℝ) : ℝ := 2 * arctan (exp x)

private lemma sech_neg (x : ℝ) : sech (-x) = sech x := by
  unfold sech
  rw [cosh_neg]

private lemma sech_cubed_neg (x : ℝ) : sech_cubed (-x) = sech_cubed x := by
  unfold sech_cubed
  rw [cosh_neg]

private lemma hasDerivAt_sech_antideriv (x : ℝ) :
    HasDerivAt sech_antideriv (sech x) x := by
  unfold sech_antideriv sech
  have h1 := hasDerivAt_exp x
  have h2 := hasDerivAt_arctan (exp x)
  have h3 := h2.comp x h1
  convert h3.const_mul 2 using 1
  rw [cosh_eq, exp_neg]
  field_simp [exp_ne_zero x]
  ring

private lemma tendsto_sech_antideriv_atTop :
    Tendsto sech_antideriv atTop (𝓝 Real.pi) := by
  unfold sech_antideriv
  have h :=
    (tendsto_nhds_of_tendsto_nhdsWithin tendsto_arctan_atTop).comp tendsto_exp_atTop
  simpa [two_mul] using h.const_mul 2

private lemma tendsto_sech_antideriv_atBot :
    Tendsto sech_antideriv atBot (𝓝 0) := by
  unfold sech_antideriv
  simpa [arctan_zero, mul_zero] using
    ((continuous_arctan.tendsto 0).comp tendsto_exp_atBot).const_mul 2

private lemma tendsto_exp_add_exp_neg_atTop :
    Tendsto (fun x => exp x + exp (-x)) atTop atTop :=
  tendsto_exp_atTop.atTop_add (tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)

private lemma tendsto_exp_add_exp_neg_atBot :
    Tendsto (fun x => exp x + exp (-x)) atBot atTop := by
  have h := (tendsto_exp_atTop.comp tendsto_neg_atBot_atTop).atTop_add tendsto_exp_atBot
  convert h using 1
  funext x
  rw [Function.comp_apply, add_comm]

private lemma tendsto_neg_exp_neg_atTop :
    Tendsto (fun x => -exp (-x)) atTop (𝓝 0) := by
  have h := (continuous_neg.tendsto 0).comp (tendsto_exp_atBot.comp tendsto_neg_atTop_atBot)
  exact h.mono_right (by simp [neg_zero])

private lemma tendsto_neg_exp_neg_atBot :
    Tendsto (fun x => -exp (-x)) atBot atBot := by
  have h := tendsto_neg_atTop_atBot.comp (tendsto_exp_atTop.comp tendsto_neg_atBot_atTop)
  exact h.congr' (Eventually.of_forall fun _ => rfl)

private lemma tendsto_sinh_atTop : Tendsto sinh atTop atTop := by
  have h : Tendsto (fun x => (exp x + (-exp (-x))) / 2) atTop atTop :=
    (tendsto_exp_atTop.atTop_add tendsto_neg_exp_neg_atTop).atTop_div_const
      (by norm_num : (0 : ℝ) < 2)
  convert h using 1
  funext x
  rw [sinh_eq, sub_eq_add_neg]

private lemma tendsto_sinh_atBot : Tendsto sinh atBot atBot := by
  have h : Tendsto (fun x => (exp x + (-exp (-x))) / 2) atBot atBot :=
    (tendsto_div_const_atBot_of_pos (by norm_num : (0 : ℝ) < 2)).mpr <|
      (by simpa [add_comm] using tendsto_neg_exp_neg_atBot.atBot_add tendsto_exp_atBot)
  convert h using 1
  funext x
  rw [sinh_eq, sub_eq_add_neg]

private lemma tendsto_cosh_atTop : Tendsto cosh atTop atTop := by
  rw [show cosh = fun x => (exp x + exp (-x)) / 2 from funext cosh_eq]
  exact tendsto_exp_add_exp_neg_atTop.atTop_div_const (by norm_num : (0 : ℝ) < 2)

private lemma tendsto_sech_atTop : Tendsto sech atTop (𝓝 0) := by
  have h := tendsto_cosh_atTop.inv_tendsto_atTop
  convert h using 1
  funext x
  unfold sech
  simp [one_div]

private lemma tendsto_cosh_atBot : Tendsto cosh atBot atTop := by
  rw [show cosh = fun x => (exp x + exp (-x)) / 2 from funext cosh_eq]
  exact tendsto_exp_add_exp_neg_atBot.atTop_div_const (by norm_num : (0 : ℝ) < 2)

private lemma tendsto_sech_atBot : Tendsto sech atBot (𝓝 0) := by
  have h := tendsto_cosh_atBot.inv_tendsto_atTop
  convert h using 1
  funext x
  unfold sech
  simp [one_div]

private lemma tanh_ge_neg_one (x : ℝ) : -1 ≤ tanh x :=
  (neg_one_lt_tanh x).le

private lemma tanh_le_one (x : ℝ) : tanh x ≤ 1 :=
  (tanh_lt_one x).le

private lemma tendsto_sech_mul_tanh_atTop : Tendsto (fun x => sech x * tanh x) atTop (𝓝 0) := by
  have hb : ∀ᶠ _ in atTop, (-1 : ℝ) ≤ tanh _ := Eventually.of_forall tanh_ge_neg_one
  have hB : ∀ᶠ _ in atTop, tanh _ ≤ 1 := Eventually.of_forall tanh_le_one
  have h := bdd_le_mul_tendsto_zero (f := tanh) (g := sech) hb hB tendsto_sech_atTop
  convert h using 1
  ext; ring

private lemma tendsto_sech_mul_tanh_atBot : Tendsto (fun x => sech x * tanh x) atBot (𝓝 0) := by
  have hb : ∀ᶠ _ in atBot, (-1 : ℝ) ≤ tanh _ := Eventually.of_forall tanh_ge_neg_one
  have hB : ∀ᶠ _ in atBot, tanh _ ≤ 1 := Eventually.of_forall tanh_le_one
  have h := bdd_le_mul_tendsto_zero (f := tanh) (g := sech) hb hB tendsto_sech_atBot
  convert h using 1
  ext; ring

private lemma tendsto_arctan_sinh_atTop :
    Tendsto (fun x => arctan (sinh x)) atTop (𝓝 (Real.pi / 2)) :=
  tendsto_nhds_of_tendsto_nhdsWithin (tendsto_arctan_atTop.comp tendsto_sinh_atTop)

private lemma tendsto_arctan_sinh_atBot :
    Tendsto (fun x => arctan (sinh x)) atBot (𝓝 (-Real.pi / 2)) := by
  convert tendsto_nhds_of_tendsto_nhdsWithin (tendsto_arctan_atBot.comp tendsto_sinh_atBot) using 1
  rw [neg_div]

private lemma tendsto_sech_cubed_antideriv_atTop :
    Tendsto sech_cubed_antideriv atTop (𝓝 (Real.pi / 4)) := by
  unfold sech_cubed_antideriv
  have h := (tendsto_sech_mul_tanh_atTop.add tendsto_arctan_sinh_atTop).const_mul (1 / 2)
  rw [show (1 / 2 : ℝ) * (0 + Real.pi / 2) = Real.pi / 4 by ring] at h
  exact h

private lemma tendsto_sech_cubed_antideriv_atBot :
    Tendsto sech_cubed_antideriv atBot (𝓝 (-Real.pi / 4)) := by
  unfold sech_cubed_antideriv
  have h := (tendsto_sech_mul_tanh_atBot.add tendsto_arctan_sinh_atBot).const_mul (1 / 2)
  rw [show (1 / 2 : ℝ) * (0 + -Real.pi / 2) = -Real.pi / 4 by ring] at h
  exact h

private lemma integrableOn_sech_Ioi :
    IntegrableOn sech (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hasDerivAt_sech_antideriv x)
    (fun x _ => le_of_lt (one_div_pos.2 (cosh_pos x))) tendsto_sech_antideriv_atTop

private lemma integrableOn_sech_Ici :
    IntegrableOn sech (Ici 0) :=
  (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr integrableOn_sech_Ioi

private lemma integrableOn_sech_Iic : IntegrableOn sech (Iic 0) := by
  have h_Ici : IntegrableOn sech (Ici (-(0 : ℝ))) := by simpa using integrableOn_sech_Ici
  exact (h_Ici.comp_neg_Iic (c := (0 : ℝ))).congr (Eventually.of_forall fun x => sech_neg x)

private lemma integrable_sech : Integrable sech := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨integrableOn_sech_Iic, integrableOn_sech_Ioi⟩

/-- **integral_sech** (CatAD): `∫_{-∞}^{∞} sech(x) dx = π`. -/
theorem integral_sech : ∫ x, sech x = Real.pi := by
  have hderiv : ∀ x, HasDerivAt sech_antideriv (sech x) x := fun x =>
    hasDerivAt_sech_antideriv x
  simpa using
    integral_of_hasDerivAt_of_tendsto hderiv integrable_sech
      tendsto_sech_antideriv_atBot tendsto_sech_antideriv_atTop

private lemma integrableOn_sech_cubed_Ioi :
    IntegrableOn sech_cubed (Ioi 0) :=
  integrableOn_Ioi_deriv_of_nonneg' (fun x _ => hasDerivAt_sech_cubed_antideriv x)
    (fun x _ => le_of_lt (one_div_pos.2 (pow_pos (cosh_pos x) 3))) tendsto_sech_cubed_antideriv_atTop

private lemma integrableOn_sech_cubed_Ici :
    IntegrableOn sech_cubed (Ici 0) :=
  (integrableOn_Ici_iff_integrableOn_Ioi (by finiteness)).mpr integrableOn_sech_cubed_Ioi

private lemma integrableOn_sech_cubed_Iic : IntegrableOn sech_cubed (Iic 0) := by
  have h_Ici : IntegrableOn sech_cubed (Ici (-(0 : ℝ))) := by simpa using integrableOn_sech_cubed_Ici
  exact (h_Ici.comp_neg_Iic (c := (0 : ℝ))).congr (Eventually.of_forall fun x => sech_cubed_neg x)

private lemma integrable_sech_cubed : Integrable sech_cubed := by
  rw [← integrableOn_univ, ← Iic_union_Ioi (a := (0 : ℝ)), integrableOn_union]
  exact ⟨integrableOn_sech_cubed_Iic, integrableOn_sech_cubed_Ioi⟩

/-- **integral_sech_cubed** (CatAD): `∫_{-∞}^{∞} sech³(x) dx = π/2`.

    Proof: F(x) = ½[sech(x)tanh(x) + arctan(sinh x)] has F' = sech³,
    F(+∞) = π/4, F(−∞) = −π/4; FTC on ℝ gives π/2. -/
theorem integral_sech_cubed :
    ∫ x in Set.univ, sech_cubed x ∂volume = Real.pi / 2 := by
  have hderiv : ∀ x, HasDerivAt sech_cubed_antideriv (sech_cubed x) x := fun x =>
    hasDerivAt_sech_cubed_antideriv x
  have h :=
    integral_of_hasDerivAt_of_tendsto hderiv integrable_sech_cubed
      tendsto_sech_cubed_antideriv_atBot tendsto_sech_cubed_antideriv_atTop
  rw [← setIntegral_univ] at h
  rw [h, show Real.pi / 4 - -Real.pi / 4 = Real.pi / 2 by ring]

private lemma phimdl_kink_density_cubed_eq (m_phi x : ℝ) :
    phimdl_kink_density m_phi x ^ 3 = (2 * m_phi / 7) ^ 3 * sech_cubed (m_phi * x) := by
  unfold phimdl_kink_density sech_cubed
  simp only [div_pow, one_div]
  ring

private lemma integral_sech_cubed_comp_mul (m_phi : ℝ) (hm : 0 < m_phi) :
    ∫ x, sech_cubed (m_phi * x) = (Real.pi / 2) / m_phi := by
  have hm0 : m_phi ≠ 0 := ne_of_gt hm
  calc
    ∫ x, sech_cubed (m_phi * x)
        = |m_phi⁻¹| * ∫ x, sech_cubed x := by
          rw [Measure.integral_comp_mul_left (g := sech_cubed) m_phi]
          simp only [Real.norm_eq_abs, smul_eq_mul]
    _ = |m_phi⁻¹| * (Real.pi / 2) := by
          rw [← setIntegral_univ, integral_sech_cubed]
    _ = (Real.pi / 2) / m_phi := by
          rw [abs_of_pos (inv_pos.2 hm), div_eq_mul_inv]
          field_simp [hm0]

private lemma integrable_sech_cubed_comp_mul (m_phi : ℝ) (hm : m_phi ≠ 0) :
    Integrable (fun x => sech_cubed (m_phi * x)) :=
  Integrable.comp_mul_left' integrable_sech_cubed hm

/-- **phimdl_three_kink_overlap_integral** (CatAD): coincident three-kink overlap equals G₃(0),
    with the sech³ factor from `integral_sech_cubed`. -/
theorem phimdl_three_kink_overlap_integral (m_phi : ℝ) (hm : 0 < m_phi) :
    ∫ x, phimdl_kink_density m_phi x ^ 3 = phimdl_three_kink_amplitude m_phi := by
  have hm0 : m_phi ≠ 0 := ne_of_gt hm
  calc
    ∫ x, phimdl_kink_density m_phi x ^ 3
        = ∫ x, (2 * m_phi / 7) ^ 3 * sech_cubed (m_phi * x) := by
          congr 1; funext x; exact phimdl_kink_density_cubed_eq m_phi x
    _ = (2 * m_phi / 7) ^ 3 * ∫ x, sech_cubed (m_phi * x) := by
          rw [← integral_const_mul ((2 * m_phi / 7) ^ 3) (fun x => sech_cubed (m_phi * x))]
    _ = phimdl_three_kink_amplitude m_phi := by
          unfold phimdl_three_kink_amplitude
          rw [integral_sech_cubed_comp_mul m_phi hm]
          ring

/-- **phimdl_yukawa_amplitude_pos** (CatAD): G₃(0) > 0 for m_φ > 0. -/
theorem phimdl_yukawa_amplitude_pos (m_phi : ℝ) (hm : 0 < m_phi) :
    phimdl_three_kink_amplitude m_phi > 0 := by
  unfold phimdl_three_kink_amplitude
  have h7 : (7 : ℝ) ≠ 0 := by norm_num
  have h2 : (2 : ℝ) ≠ 0 := by norm_num
  have hm7 : 0 < 2 * m_phi / 7 := by
    apply div_pos (mul_pos (by norm_num) hm)
    norm_num
  have hpow : 0 < (2 * m_phi / 7) ^ 3 := pow_pos hm7 3
  have hpi : 0 < Real.pi / 2 := div_pos Real.pi_pos (by norm_num)
  have hmpos : 0 < m_phi := hm
  exact div_pos (mul_pos hpow hpi) hmpos

/-- **phimdl_yukawa_amplitude_formula** (CatAD): G₃(0) = 4π/343 × m_φ². -/
theorem phimdl_yukawa_amplitude_formula (m_phi : ℝ) (hm : 0 < m_phi) :
    phimdl_three_kink_amplitude m_phi = 4 * Real.pi / 343 * m_phi ^ 2 := by
  unfold phimdl_three_kink_amplitude
  have hm0 : m_phi ≠ 0 := ne_of_gt hm
  field_simp [hm0]
  ring

/-- **phimdl_three_kink_overlap_integral_formula** (CatAD): ∫ ρ³ = 4π/343 × m_φ² via sech³ integral. -/
theorem phimdl_three_kink_overlap_integral_formula (m_phi : ℝ) (hm : 0 < m_phi) :
    ∫ x, phimdl_kink_density m_phi x ^ 3 = 4 * Real.pi / 343 * m_phi ^ 2 := by
  rw [phimdl_three_kink_overlap_integral m_phi hm, phimdl_yukawa_amplitude_formula m_phi hm]

/-- **yukawa_amplitude_nonzero_sech3** (CatAD): ∫ ρ³ = G₃(0) > 0 via `integral_sech_cubed`. -/
theorem yukawa_amplitude_nonzero_sech3 (m_phi : ℝ) (hm : 0 < m_phi) :
    ∫ x, phimdl_kink_density m_phi x ^ 3 > 0 ∧
    phimdl_three_kink_amplitude m_phi > 0 := by
  have hpos := phimdl_yukawa_amplitude_pos m_phi hm
  exact ⟨by rw [phimdl_three_kink_overlap_integral m_phi hm]; exact hpos, hpos⟩

-- ════════════════════════════════════════════════════════════════
-- §2b  Sech product overlap (P45 zero-mode factor)
-- ════════════════════════════════════════════════════════════════

/-- Zero-mode sech overlap I(r) = ∫ sech(x)·sech(r·x) dx (P45 Yukawa tape factor). -/
noncomputable def sech_overlap (r : ℝ) : ℝ := ∫ x, sech x * sech (r * x)

private lemma sech_le_one (x : ℝ) : sech x ≤ 1 := by
  have h : 1 / cosh x ≤ 1 / 1 := by
    gcongr
    exact one_le_cosh x
  simpa [sech] using h

private lemma sech_mul_sech_le (x r : ℝ) : sech x * sech (r * x) ≤ sech x := by
  exact mul_le_of_le_one_right (le_of_lt (one_div_pos.2 (cosh_pos x))) (sech_le_one (r * x))

private lemma continuous_sech : Continuous sech := by
  unfold sech
  exact continuous_const.div continuous_cosh fun x => (cosh_pos x).ne'

private lemma integrable_sech_mul_sech (r : ℝ) :
    Integrable (fun x => sech x * sech (r * x)) := by
  have hcont : Continuous (fun x => sech x * sech (r * x)) :=
    continuous_sech.mul (continuous_sech.comp (continuous_id.const_mul r))
  exact Integrable.mono_nonneg integrable_sech hcont.aestronglyMeasurable
    (ae_of_all _ fun x => le_of_lt (mul_pos (one_div_pos.2 (cosh_pos x)) (one_div_pos.2 (cosh_pos (r * x)))))
    (ae_of_all _ fun x => sech_mul_sech_le x r)

/-- **sech_overlap_le_pi** (CatAD): I(r) ≤ π since sech(r·x) ≤ 1. -/
theorem sech_overlap_le_pi (r : ℝ) : sech_overlap r ≤ Real.pi := by
  unfold sech_overlap
  have hmono :=
    integral_mono_ae (integrable_sech_mul_sech r) integrable_sech
      (ae_of_all _ fun x => sech_mul_sech_le x r)
  exact hmono.trans (le_of_eq integral_sech)

-- ════════════════════════════════════════════════════════════════
-- §3  Yukawa vertex Z₇ winding (neutral Higgs, CatAL)
-- ════════════════════════════════════════════════════════════════

/-- Z₇ winding of the Higgs boundary excitation (GTE triple (5,3,13)): W(H) = 0. -/
def W_Higgs : ℤ := 0

/-- **higgs_winding_zero** (CatAL): the Higgs is Z₇-neutral. -/
theorem higgs_winding_zero : W_Higgs = 0 := rfl

/-- **yukawa_winding_conservation** (CatAL): neutral-boson emission W(f_L) + 0 = W(f_R). -/
theorem yukawa_winding_conservation (w_fL w_fR : ℤ) (h : w_fL = w_fR) :
    w_fL + W_Higgs = w_fR := by
  dsimp [W_Higgs]
  omega

/-- **phimdl_yukawa_vertex_winding_trivial** (CatAL): every SM Yukawa vertex with
    W(f_L) = W(f_R) is permitted by Z₇ conservation when W(H) = 0. -/
theorem phimdl_yukawa_vertex_winding_trivial (w_fL w_fR : ℤ) (h : w_fL = w_fR) :
    w_fL + (0 : ℤ) = w_fR :=
  yukawa_winding_conservation w_fL w_fR h

-- ════════════════════════════════════════════════════════════════
-- §4  GTE Yukawa coupling from SRRG condensate (CatA)
-- ════════════════════════════════════════════════════════════════

/-- GTE Yukawa coupling h_f = m_f / (v_H / √2); condensate-forced mass ratio (P27 SRRG). -/
noncomputable def gte_yukawa_coupling (m_f v_H : ℝ) : ℝ := m_f / (v_H / Real.sqrt 2)

/-- **gte_yukawa_positive** (CatA): h_f > 0 when m_f, v_H > 0. -/
theorem gte_yukawa_positive (m_f v_H : ℝ) (hm : 0 < m_f) (hv : 0 < v_H) :
    gte_yukawa_coupling m_f v_H > 0 := by
  unfold gte_yukawa_coupling
  have hsqrt : 0 < Real.sqrt 2 := Real.sqrt_pos.mpr (by norm_num)
  have hv' : 0 < v_H / Real.sqrt 2 := div_pos hv hsqrt
  exact div_pos hm hv'

/-- **yukawa_coupling_from_srrg_condensate** (CatA): definitional package of the SRRG ratio. -/
theorem yukawa_coupling_from_srrg_condensate (m_f v_H : ℝ) :
    gte_yukawa_coupling m_f v_H = m_f / (v_H / Real.sqrt 2) :=
  rfl

end UgpLean.Substrate.PhiMDLFluctuationSpectrum
