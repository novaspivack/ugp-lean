import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fintype.Pi
import Mathlib.Data.Fintype.Prod
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Archimedean
import Mathlib.Topology.Instances.Nat

/-!
# Holographic Scaling of the Three-Tape CMCA

The three-tape CMCA has holographic information structure:
the state space of three 1D arrays of length L over Z₇ is much
smaller than a naive 3D lattice description.

Three-tape state: (ZMod 7)^L × (ZMod 7)^L × (ZMod 7)^L = (ZMod 7)^{3L}
Naive 3D lattice: (ZMod 7)^{L³}

Holographic ratio: log|State_3tape| / log|State_3D| = 3L / L³ = 3/L²
-/

namespace HolographicScaling

open Filter

/-- The three-tape CMCA state space for L cells has cardinality 7^{3L} -/
theorem three_tape_state_card (L : ℕ) :
    Fintype.card ((Fin L → ZMod 7) × (Fin L → ZMod 7) × (Fin L → ZMod 7))
    = 7 ^ (3 * L) := by
  simp [Fintype.card_prod, Fintype.card_pi, Fintype.card_fin, ZMod.card]
  ring

/-- The naive 3D lattice state space for L cells has cardinality 7^{L³} -/
theorem naive_3d_state_card (L : ℕ) :
    Fintype.card (Fin L × Fin L × Fin L → ZMod 7)
    = 7 ^ (L ^ 3) := by
  simp [Fintype.card_pi, Fintype.card_prod, Fintype.card_fin, ZMod.card]
  ring

/-- For L ≥ 2, the exponent 3L is strictly below L³. -/
private theorem threeL_lt_L_cubed (L : ℕ) (hL : 2 ≤ L) : 3 * L < L ^ 3 := by
  match L with
  | 0 | 1 => omega
  | 2 => decide
  | L + 3 =>
    have : 0 ≤ L := by omega
    nlinarith [sq_nonneg (L : ℤ), sq_nonneg (L + 1 : ℤ), sq_nonneg (L + 2 : ℤ), sq_nonneg (L + 3 : ℤ)]

/-- For L > 1, the three-tape state space is strictly smaller than the naive 3D lattice -/
theorem three_tape_smaller_than_3d (L : ℕ) (hL : 2 ≤ L) :
    7 ^ (3 * L) < 7 ^ (L ^ 3) := by
  apply Nat.pow_lt_pow_right (by norm_num : 1 < 7)
  exact threeL_lt_L_cubed L hL

/-- The log-cardinality ratio: 3L/L³ = 3/L² -/
theorem holographic_ratio_formula (L : ℕ) (hL : 0 < L) :
    (3 * L : ℝ) / (L ^ 3 : ℝ) = 3 / (L ^ 2 : ℝ) := by
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr hL.ne'
  field_simp [hLne, pow_ne_zero 2 hLne, pow_ne_zero 3 hLne]

/-- The holographic ratio vanishes: 3/L² → 0 as L → ∞ -/
theorem holographic_ratio_vanishes :
    Tendsto (fun L : ℕ => (3 : ℝ) / (L : ℝ) ^ 2) atTop (nhds 0) := by
  have hL : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
  have hLsq : Tendsto (fun L : ℕ => (L : ℝ) ^ 2) atTop atTop :=
    (tendsto_pow_atTop (by norm_num : (2 : ℕ) ≠ 0)).comp hL
  have hinv : Tendsto (fun L : ℕ => ((L : ℝ) ^ 2)⁻¹) atTop (nhds 0) :=
    tendsto_inv_atTop_zero.comp hLsq
  have hmul : Tendsto (fun L : ℕ => (3 : ℝ) * ((L : ℝ) ^ 2)⁻¹) atTop (nhds 0) := by
    simpa [mul_zero] using (tendsto_const_nhds (x := 3)).mul hinv
  have heq : (fun L : ℕ => (3 : ℝ) / (L : ℝ) ^ 2) = fun L : ℕ => (3 : ℝ) * ((L : ℝ) ^ 2)⁻¹ := by
    ext L
    rw [div_eq_mul_inv]
  rw [heq]
  exact hmul

/-- Master theorem: three-tape CMCA is holographic at small L (verified for L=7) -/
theorem three_tape_holographic_L7 :
    Fintype.card ((Fin 7 → ZMod 7) × (Fin 7 → ZMod 7) × (Fin 7 → ZMod 7))
    < Fintype.card (Fin 7 × Fin 7 × Fin 7 → ZMod 7) := by
  rw [three_tape_state_card, naive_3d_state_card]
  exact three_tape_smaller_than_3d 7 (by decide)

end HolographicScaling
