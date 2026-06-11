import Mathlib.Tactic
import UgpLean.Spacetime.OrbitMassHierarchy
import UgpLean.Universality.LambdaGTEThreshold

/-!
# CMCA physical-point dictionary and tape saturation

Given the seven-kink threshold `Λ = 7·M`, the SCC kink mass `M = (8/49)·m_φ`
(`mkink_from_scc`), certifies the lattice-spacing corollaries `a·M = 1/7`,
`a·m_φ = 7/8`, and `ξ* = 1/(a·M) = 7 = |ℤ/7ℤ|`.

The **Tape Saturation Theorem** upgrades `MDLSaturationSpacingHypothesis` from a
bare assumption to a theorem-with-named-premise: under
`ComptonSupportCriterion` (Compton-support identification + tape discreteness
pinning κ = 1), strict MDL pricing monotonicity, and extremization at the
hosting boundary, the optimal spacing satisfies `a·Λ = 1`.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Physics.CMCAPhysicalPoint

open GTE.Spacetime.OrbitMassHierarchy
open UgpLean.Universality.LambdaGTEThreshold

/-- Seven-kink chain multiplier entering `Λ = 7·M`. -/
def kinkChainMultiplier : ℕ := z7ChainMultiplier

/-- **MDLSaturationSpacingHypothesis** (named CatB premise):
    The continuum lattice spacing `a > 0` saturates the MDL description length at
    the seven-kink threshold scale `Λ > 0` via `a·Λ = 1`.  Assumes only the
    spacing identity and positivity — the corollary web is derived, not assumed. -/
structure MDLSaturationSpacingHypothesis where
  a : ℚ
  Lambda : ℚ
  pos_a : 0 < a
  pos_Lambda : 0 < Lambda
  a_Lambda_eq_one : a * Lambda = 1

theorem kink_chain_multiplier_eq_seven : kinkChainMultiplier = 7 := rfl

theorem seven_kink_threshold (M : ℚ) :
    (7 : ℚ) * M = (kinkChainMultiplier : ℚ) * M := rfl

theorem a_times_M_eq_one_seventh
    (M : ℚ) (h : MDLSaturationSpacingHypothesis)
    (hThreshold : h.Lambda = (7 : ℚ) * M)
    (hMpos : 0 < M) :
    h.a * M = 1 / 7 := by
  have hprod : h.a * h.Lambda = 1 := h.a_Lambda_eq_one
  rw [hThreshold] at hprod
  have hMne : (M : ℚ) ≠ 0 := ne_of_gt hMpos
  field_simp at hprod ⊢
  linarith

theorem a_times_mphi_eq_seven_eighths
    (M mphi : ℚ) (hM : M = (8 / 49 : ℚ) * mphi)
    (h : MDLSaturationSpacingHypothesis)
    (hThreshold : h.Lambda = (7 : ℚ) * M)
    (hMpos : 0 < M) (hmpos : 0 < mphi) :
    h.a * mphi = 7 / 8 := by
  have hAM := a_times_M_eq_one_seventh M h hThreshold hMpos
  have hMne : (mphi : ℚ) ≠ 0 := ne_of_gt hmpos
  calc h.a * mphi
    _ = (h.a * M) * (mphi / M) := by field_simp [hMne]
    _ = (1 / 7) * (mphi / M) := by rw [hAM]
    _ = (1 / 7) * (49 / 8) := by
        rw [hM]
        field_simp
    _ = 7 / 8 := by norm_num

theorem xi_star_eq_seven
    (M : ℚ) (h : MDLSaturationSpacingHypothesis)
    (hThreshold : h.Lambda = (7 : ℚ) * M)
    (hMpos : 0 < M) :
    1 / (h.a * M) = 7 := by
  rw [a_times_M_eq_one_seventh M h hThreshold hMpos]
  norm_num

theorem xi_star_eq_z7_order
    (M : ℚ) (h : MDLSaturationSpacingHypothesis)
    (hThreshold : h.Lambda = (7 : ℚ) * M)
    (hMpos : 0 < M) :
    1 / (h.a * M) = (kinkChainMultiplier : ℚ) := by
  rw [xi_star_eq_seven M h hThreshold hMpos, kink_chain_multiplier_eq_seven]
  norm_num

/-- **cmca_physical_point_dictionary** (CatAL | MDLSaturationSpacingHypothesis):
    From `Λ = 7·M`, `M = (8/49)·m_φ`, and `a·Λ = 1`, the lattice-spacing web
    `a·M = 1/7`, `a·m_φ = 7/8`, and `ξ* = 7`. -/
theorem cmca_physical_point_dictionary
    (M : ℚ) (hM : M = mkink_scc)
    (h : MDLSaturationSpacingHypothesis)
    (hThreshold : h.Lambda = (7 : ℚ) * M)
    (hMpos : 0 < M) (hmpos : 0 < mphi_scc) :
    h.a * M = 1 / 7 ∧
      h.a * mphi_scc = 7 / 8 ∧
        1 / (h.a * M) = 7 ∧
          1 / (h.a * M) = (kinkChainMultiplier : ℚ) ∧
            h.a * mphi_scc = (49 / 8 : ℚ) * (1 / 7) := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩
  · exact a_times_M_eq_one_seventh M h hThreshold hMpos
  · exact a_times_mphi_eq_seven_eighths M mphi_scc (by rw [hM, mkink_scc]) h hThreshold hMpos hmpos
  · exact xi_star_eq_seven M h hThreshold hMpos
  · exact xi_star_eq_z7_order M h hThreshold hMpos
  · have hAm := a_times_mphi_eq_seven_eighths M mphi_scc (by rw [hM, mkink_scc]) h hThreshold hMpos hmpos
    calc h.a * mphi_scc
      _ = 7 / 8 := hAm
      _ = (49 / 8 : ℚ) * (1 / 7) := by norm_num

/-- Consistency witness: the tree-reading spacing `a = 1/Λ` with `Λ = 7·M`
    satisfies the MDL-saturation hypothesis and reproduces the dictionary. -/
def mdl_saturation_tree_reading (M : ℚ) (hMpos : 0 < M) : MDLSaturationSpacingHypothesis where
  a := 1 / ((7 : ℚ) * M)
  Lambda := (7 : ℚ) * M
  pos_a := by
    have h7 : (0 : ℚ) < 7 := by norm_num
    exact div_pos one_pos (mul_pos h7 hMpos)
  pos_Lambda := by
    have h7 : (0 : ℚ) < 7 := by norm_num
    exact mul_pos h7 hMpos
  a_Lambda_eq_one := by field_simp

theorem cmca_physical_point_tree_reading
    (hMpos : 0 < mkink_scc) (hmpos : 0 < mphi_scc) :
    let h := mdl_saturation_tree_reading mkink_scc hMpos
    h.a * mkink_scc = 1 / 7 ∧
      h.a * mphi_scc = 7 / 8 ∧
        1 / (h.a * mkink_scc) = 7 := by
  dsimp [mdl_saturation_tree_reading]
  have hThreshold : (mdl_saturation_tree_reading mkink_scc hMpos).Lambda = (7 : ℚ) * mkink_scc := rfl
  have hMain := cmca_physical_point_dictionary mkink_scc rfl
    (mdl_saturation_tree_reading mkink_scc hMpos) hThreshold hMpos hmpos
  exact ⟨hMain.1, hMain.2.1, hMain.2.2.1⟩

-- ─────────────────────────────────────────────────────────────────────────
-- Tape Saturation Theorem (LT-088-61): Compton-support criterion spine
-- ─────────────────────────────────────────────────────────────────────────

/-- Admissible supremum `a* = ℏc/Λ` of the κ = 1 hosting boundary. -/
noncomputable def admissibleSupremum (Lambda hbarc : ℚ) : ℚ := hbarc / Lambda

/-- **ComptonSupportCriterion** (named CatB premise):
    The localization-size = inverse-correlation-length identification together
    with tape discreteness (minimal defect occupies one lattice cell) enforces
    the κ = 1 hosting boundary `m·a ≤ ℏc`.  Fields:
    * `threshold_hosting` — faithfulness bound at the seven-kink scale `Λ`;
    * `kappa_one_units` — discreteness pins κ = 1 with `ℏc = 1` in natural units
      (no Brillouin-π ambiguity). -/
structure ComptonSupportCriterion where
  a : ℚ
  Lambda : ℚ
  hbarc : ℚ
  pos_a : 0 < a
  pos_Lambda : 0 < Lambda
  pos_hbarc : 0 < hbarc
  threshold_hosting : a * Lambda ≤ hbarc
  kappa_one_units : hbarc = 1

/-- **faithful_tape_admissibility** (b1): a faithful tape satisfies `a ≤ ℏc/Λ`. -/
theorem faithful_tape_admissibility (csc : ComptonSupportCriterion) :
    csc.a * csc.Lambda ≤ 1 := by
  simpa [csc.kappa_one_units] using csc.threshold_hosting

/-- **compton_support_hosting_general**: the threshold hosting bound propagates to
    every hosted mass `m ≤ Λ`. -/
theorem compton_support_hosting_general
    (csc : ComptonSupportCriterion) (m : ℚ) (_hm : 0 < m) (hle : m ≤ csc.Lambda) :
    m * csc.a ≤ csc.hbarc := by
  have hma : m * csc.a ≤ csc.Lambda * csc.a :=
    mul_le_mul_of_nonneg_right hle (le_of_lt csc.pos_a)
  linarith [csc.threshold_hosting, hma]

/-- **faithful_tape_spacing_bound**: admissible spacing is bounded by `a* = ℏc/Λ`. -/
theorem faithful_tape_spacing_bound (csc : ComptonSupportCriterion) :
    csc.a ≤ admissibleSupremum csc.Lambda csc.hbarc := by
  unfold admissibleSupremum
  have hΛ : (0 : ℚ) < csc.Lambda := csc.pos_Lambda
  field_simp
  exact csc.threshold_hosting

/-- **StrictTapePricingHypothesis** (b2): abstract strict monotone MDL pricing —
    coarser admissible tape spacing strictly lowers description length. -/
structure StrictTapePricingHypothesis where
  a_fine : ℚ
  a_coarse : ℚ
  cost_fine : ℚ
  cost_coarse : ℚ
  pos_fine : 0 < a_fine
  pos_coarse : 0 < a_coarse
  coarser : a_fine < a_coarse
  strict_decrease : cost_coarse < cost_fine

/-- **tape_pricing_monotonicity**: strict pricing prefers the coarser admissible spacing. -/
theorem tape_pricing_monotonicity (pr : StrictTapePricingHypothesis) :
    pr.cost_coarse < pr.cost_fine :=
  pr.strict_decrease

/-- **TapeSaturationExtremization** (b3 + b4): MDL extremization attains the hosting
    boundary `a·Λ = ℏc` (the omitted threshold state is admissible at the supremum). -/
structure TapeSaturationExtremization where
  csc : ComptonSupportCriterion
  attains_hosting_boundary : csc.a * csc.Lambda = csc.hbarc

/-- Boundary spacing saturates the admissible supremum. -/
theorem tape_saturation_attains_supremum (ext : TapeSaturationExtremization) :
    ext.csc.a = admissibleSupremum ext.csc.Lambda ext.csc.hbarc := by
  unfold admissibleSupremum
  have hΛ : (0 : ℚ) < ext.csc.Lambda := ext.csc.pos_Lambda
  have hb := ext.attains_hosting_boundary
  field_simp at hb ⊢
  linarith

/-- **tape_saturation_theorem** (CatAD | ComptonSupportCriterion):
    Extremization at the κ = 1 hosting boundary yields `a·Λ = 1`. -/
theorem tape_saturation_theorem (ext : TapeSaturationExtremization) :
    ext.csc.a * ext.csc.Lambda = 1 := by
  have hb := ext.attains_hosting_boundary
  rwa [ext.csc.kappa_one_units] at hb

/-- **mdl_supremum_from_strict_pricing**: if the current spacing is strictly inside
    the admissible bound, a coarser admissible spacing with lower cost exists — the
    order-theoretic content of MDL extremization. -/
theorem mdl_supremum_from_strict_pricing
    (csc : ComptonSupportCriterion) (pr : StrictTapePricingHypothesis)
    (_h_fine : pr.a_fine = csc.a)
    (h_coarse_sup : pr.a_coarse = admissibleSupremum csc.Lambda csc.hbarc)
    (h_strictly_inner : csc.a < admissibleSupremum csc.Lambda csc.hbarc)
    (_h_coarse_admiss : pr.a_coarse * csc.Lambda ≤ csc.hbarc) :
    pr.cost_coarse < pr.cost_fine ∧
      csc.a < pr.a_coarse ∧ pr.a_coarse ≤ admissibleSupremum csc.Lambda csc.hbarc := by
  refine ⟨pr.strict_decrease, ?_, ?_⟩
  · exact h_strictly_inner.trans_eq h_coarse_sup.symm
  · exact le_of_eq h_coarse_sup

/-- **compton_support_derives_mdl_saturation**: bridge from the named criterion to
    `MDLSaturationSpacingHypothesis`. -/
noncomputable def compton_support_derives_mdl_saturation
    (ext : TapeSaturationExtremization) : MDLSaturationSpacingHypothesis where
  a := ext.csc.a
  Lambda := ext.csc.Lambda
  pos_a := ext.csc.pos_a
  pos_Lambda := ext.csc.pos_Lambda
  a_Lambda_eq_one := tape_saturation_theorem ext

/-- Consistent instance: extremization at `a = 1/Λ` with `ℏc = 1`. -/
noncomputable def compton_support_saturation_witness
    (Lambda : ℚ) (hΛ : 0 < Lambda) : TapeSaturationExtremization where
  csc := {
    a := 1 / Lambda
    Lambda := Lambda
    hbarc := 1
    pos_a := div_pos one_pos hΛ
    pos_Lambda := hΛ
    pos_hbarc := one_pos
    threshold_hosting := by field_simp; norm_num
    kappa_one_units := rfl
  }
  attains_hosting_boundary := by field_simp

/-- **tape_saturation_physical_point_dictionary** (CatAD | ComptonSupportCriterion):
    From extremization at the hosting boundary, the full physical-point dictionary
    follows via the upgraded spacing identity. -/
theorem tape_saturation_physical_point_dictionary
    (M : ℚ) (hM : M = mkink_scc)
    (ext : TapeSaturationExtremization)
    (hThreshold : ext.csc.Lambda = (7 : ℚ) * M)
    (hMpos : 0 < M) (hmpos : 0 < mphi_scc) :
    ext.csc.a * ext.csc.Lambda = 1 ∧
      let h := compton_support_derives_mdl_saturation ext
      h.a * M = 1 / 7 ∧
        h.a * mphi_scc = 7 / 8 ∧
          1 / (h.a * M) = 7 := by
  dsimp only
  have hSat := tape_saturation_theorem ext
  have hDict := cmca_physical_point_dictionary M hM
    (compton_support_derives_mdl_saturation ext) hThreshold hMpos hmpos
  exact ⟨hSat, hDict.1, hDict.2.1, hDict.2.2.1⟩

/-- Tree-reading spacing as a Compton-support extremization witness at `Λ = 7·M`. -/
theorem compton_support_tree_reading_witness (M : ℚ) (hMpos : 0 < M) :
    (compton_support_saturation_witness ((7 : ℚ) * M) (mul_pos (by norm_num) hMpos)).csc.a *
        ((7 : ℚ) * M) = 1 ∧
      (compton_support_derives_mdl_saturation
        (compton_support_saturation_witness ((7 : ℚ) * M) (mul_pos (by norm_num) hMpos))).a *
        M = 1 / 7 := by
  let hex := compton_support_saturation_witness ((7 : ℚ) * M) (mul_pos (by norm_num) hMpos)
  have hSat := tape_saturation_theorem hex
  have hThreshold : (compton_support_derives_mdl_saturation hex).Lambda = (7 : ℚ) * M := by
    unfold compton_support_derives_mdl_saturation
    dsimp [hex, compton_support_saturation_witness]
  have hAM := a_times_M_eq_one_seventh M (compton_support_derives_mdl_saturation hex)
    hThreshold hMpos
  dsimp [compton_support_derives_mdl_saturation, hex, compton_support_saturation_witness]
  exact ⟨hSat, hAM⟩

end UgpLean.Physics.CMCAPhysicalPoint
