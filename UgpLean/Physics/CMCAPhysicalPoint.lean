import Mathlib.Tactic
import UgpLean.Spacetime.OrbitMassHierarchy
import UgpLean.Universality.LambdaGTEThreshold

/-!
# CMCA physical-point dictionary

Given the seven-kink threshold `Λ = 7·M`, the SCC kink mass `M = (8/49)·m_φ`
(`mkink_from_scc`), and the MDL-saturation spacing premise `a·Λ = 1`, certifies
the lattice-spacing corollaries `a·M = 1/7`, `a·m_φ = 7/8`, and
`ξ* = 1/(a·M) = 7 = |ℤ/7ℤ|`.

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

end UgpLean.Physics.CMCAPhysicalPoint
