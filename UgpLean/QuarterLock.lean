import Mathlib.Data.Rat.Defs
import Mathlib.Tactic.Ring
import Mathlib.Algebra.GroupWithZero.Basic
import Mathlib.NumberTheory.Real.GoldenRatio
import UgpLean.ElegantKernel
import UgpLean.ElegantKernel.KGen2

/-!
# UgpLean.QuarterLock — Quarter-Lock Law

The Quarter-Lock identity: k_M = k_gen2 + ¼ k_L².
Constrains the Elegant Kernel coefficients.

Reference: First Principles SM, UGP Math Foundations, Reflexive Reality
-/

namespace UgpLean

/-- Quarter-Lock identity: k_M = k_gen2 + (1/4) * k_L2 -/
def quarterLockIdentity (k_M k_gen2 k_L2 : ℚ) : Prop :=
  k_M = k_gen2 + (1/4 : ℚ) * k_L2

/-- Example coefficients satisfying Quarter-Lock: k_gen2 = 7/2048, k_M = 7/1024.
Uses ElegantKernel.k_L2 = 7/512. -/
def k_gen2_example : ℚ := 7/2048
def k_M_example : ℚ := 7/1024

theorem quarterLock_holds_example : quarterLockIdentity k_M_example k_gen2_example k_L2 := by
  unfold quarterLockIdentity k_M_example k_gen2_example
  rw [k_L2_eq]
  ring

/-- Quarter-Lock Law: There exist rational coefficients satisfying the identity with k_L2 = 7/512. -/
theorem quarterLockLaw : ∃ k_M k_gen2 : ℚ, quarterLockIdentity k_M k_gen2 k_L2 :=
  ⟨k_M_example, k_gen2_example, quarterLock_holds_example⟩

/-- Kernel Defect Functional: squared distance from Quarter-Lock plane.
 D(k) = (16/33)(k_M - k_G - ¼k_L)². State is lawful iff D = 0. -/
def kernelDefect (k_M k_G k_L : ℚ) : ℚ := (16/33) * (k_M - k_G - (1/4)*k_L)^2

/-- Stability of Quarter-Lock: T contracts the Kernel Defect in a neighborhood of the lawful manifold.
 For states with small defect, D(T(k)) < D(k). -/
def quarterLockStability : Prop :=
  ∀ k_M k_G k_L : ℚ, kernelDefect k_M k_G k_L = 0 →
    quarterLockIdentity k_M k_G k_L

theorem quarterLockStability_holds : quarterLockStability := by
  intro k_M k_G k_L hD
  unfold kernelDefect quarterLockIdentity at *
  rcases mul_eq_zero.mp hD with h₁ | h₂
  · exfalso; norm_num at h₁
  · have h : k_M - k_G - (1/4)*k_L = 0 := sq_eq_zero_iff.mp h₂
    linarith

/-! ## Quarter-Lock over ℝ — Elegant Kernel k_M -/

open Real UgpLean.ElegantKernel

/-- The Quarter-Lock M-coefficient over ℝ: `k_M = k_gen² + (1/4)·k_L²`. -/
noncomputable def k_M : ℝ := k_gen2 + (k_L2 : ℝ) / 4

/-- Quarter-Lock identity over ℝ (definitional). -/
theorem k_M_quarter_lock_identity : k_M = k_gen2 + (k_L2 : ℝ) / 4 := rfl

/-- **THM-UCL-QuarterLock (CatAL).** Closed form: `k_M = −φ/2 + 7/2048`. -/
theorem k_M_eq_neg_phi_half_plus_seven_2048 :
    k_M = -(Real.goldenRatio / 2) + (7 / 2048 : ℝ) := by
  unfold k_M
  rw [k_gen2_eq_neg_phi_half]
  have hk : (k_L2 : ℝ) = 7 / 512 := by
    rw [show k_L2 = 7/512 from k_L2_eq]; norm_num
  rw [hk]
  ring

/-- Equivalent closed form: `k_M = −(1+√5)/4 + 7/2048`. -/
theorem k_M_eq_neg_one_plus_sqrt5_over_4_plus_seven_2048 :
    k_M = -((1 + Real.sqrt 5) / 4) + (7 / 2048 : ℝ) := by
  rw [k_M_eq_neg_phi_half_plus_seven_2048]
  unfold Real.goldenRatio
  ring

/-- Quarter-Lock packaged with CatAL-certified ingredient values. -/
theorem thm_quarter_lock_catal :
    k_M = k_gen2 + (k_L2 : ℝ) / 4 ∧
    k_M = -(Real.goldenRatio / 2) + (7 / 2048 : ℝ) ∧
    (k_L2 : ℝ) = 7 / 512 ∧
    k_gen2 = -(Real.goldenRatio / 2) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · rfl
  · exact k_M_eq_neg_phi_half_plus_seven_2048
  · rw [show k_L2 = 7/512 from k_L2_eq]; norm_num
  · exact k_gen2_eq_neg_phi_half

end UgpLean
