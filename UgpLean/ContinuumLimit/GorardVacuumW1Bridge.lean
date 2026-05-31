import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Rat.Defs
import UgpLean.ContinuumLimit.WassersteinDistance
import UgpLean.Gravity.GorardRicciFlatVacuum

/-!
# Gorard Vacuum W₁ Bridge (083-ORIC-AXIOM-UPGRADE)
-/

namespace GTE.ContinuumLimit.GorardVacuumW1Bridge

open GTE.ContinuumLimit.Wasserstein
open UgpLean.Gravity.GorardRicciFlatVacuum

def vacuumAdjacentVertices : Finset ℕ := {0, 1, 2, 3}

def vacuumAdjacentDist (x y : ℕ) : ℝ := |((x : ℤ) - (y : ℤ))|

theorem vacuumAdjacentDist_nonneg (x y : ℕ) : 0 ≤ vacuumAdjacentDist x y := by
  unfold vacuumAdjacentDist; exact abs_nonneg _

theorem vacuumAdjacentDist_self (x : ℕ) : vacuumAdjacentDist x x = 0 := by
  unfold vacuumAdjacentDist; simp

theorem vacuumAdjacentDist_comm (x y : ℕ) : vacuumAdjacentDist x y = vacuumAdjacentDist y x := by
  unfold vacuumAdjacentDist; rw [abs_sub_comm]

theorem vacuumAdjacentDist_triangle (x y z : ℕ) :
    vacuumAdjacentDist x z ≤ vacuumAdjacentDist x y + vacuumAdjacentDist y z := by
  unfold vacuumAdjacentDist
  exact_mod_cast abs_sub_le (x : ℤ) (y : ℤ) (z : ℤ)

def vacuumAdjacentGraph : FiniteMetricSpace where
  vertices := vacuumAdjacentVertices
  dist := vacuumAdjacentDist
  dist_nonneg := vacuumAdjacentDist_nonneg
  dist_self := vacuumAdjacentDist_self
  dist_comm := vacuumAdjacentDist_comm
  triangle := vacuumAdjacentDist_triangle

noncomputable section

def vacuumWalkMeasureLeftVal (x : ℕ) : ℝ :=
  if x = 0 then (1 : ℝ) / 3 else if x = 1 then (1 : ℝ) / 3 else if x = 2 then (1 : ℝ) / 3 else 0

def vacuumWalkMeasureRightVal (x : ℕ) : ℝ :=
  if x = 1 then (1 : ℝ) / 3 else if x = 2 then (1 : ℝ) / 3 else if x = 3 then (1 : ℝ) / 3 else 0

def vacuumShiftCoupling (x y : ℕ) : ℝ :=
  if x = 0 ∧ y = 1 then (1 : ℝ) / 3
  else if x = 1 ∧ y = 2 then (1 : ℝ) / 3
  else if x = 2 ∧ y = 3 then (1 : ℝ) / 3
  else 0

theorem not_mem_vacuumAdjacentVertices (x : ℕ) (hx : x ∉ vacuumAdjacentVertices) :
    x ≠ 0 ∧ x ≠ 1 ∧ x ≠ 2 ∧ x ≠ 3 := by
  simp [vacuumAdjacentVertices, Finset.mem_insert, Finset.mem_singleton] at hx
  tauto

theorem vacuumWalkMeasureLeft_nonneg (x : ℕ) (hx : x ∈ vacuumAdjacentVertices) :
    0 ≤ vacuumWalkMeasureLeftVal x := by
  fin_cases hx <;> simp [vacuumWalkMeasureLeftVal]

theorem vacuumWalkMeasureLeft_outside (x : ℕ) (hx : x ∉ vacuumAdjacentVertices) :
    vacuumWalkMeasureLeftVal x = 0 := by
  obtain ⟨h0, h1, h2, _⟩ := not_mem_vacuumAdjacentVertices x hx
  simp [vacuumWalkMeasureLeftVal, h0, h1, h2]

theorem vacuumWalkMeasureLeft_sum :
    vacuumAdjacentVertices.sum vacuumWalkMeasureLeftVal = 1 := by
  simp [vacuumAdjacentVertices, vacuumWalkMeasureLeftVal]; norm_num

theorem vacuumWalkMeasureRight_nonneg (x : ℕ) (hx : x ∈ vacuumAdjacentVertices) :
    0 ≤ vacuumWalkMeasureRightVal x := by
  fin_cases hx <;> simp [vacuumWalkMeasureRightVal]

theorem vacuumWalkMeasureRight_outside (x : ℕ) (hx : x ∉ vacuumAdjacentVertices) :
    vacuumWalkMeasureRightVal x = 0 := by
  obtain ⟨_, h1, h2, h3⟩ := not_mem_vacuumAdjacentVertices x hx
  simp [vacuumWalkMeasureRightVal, h1, h2, h3]

theorem vacuumWalkMeasureRight_sum :
    vacuumAdjacentVertices.sum vacuumWalkMeasureRightVal = 1 := by
  simp [vacuumAdjacentVertices, vacuumWalkMeasureRightVal]; norm_num

def vacuumWalkMeasureLeft : ProbDist vacuumAdjacentVertices :=
  ⟨vacuumWalkMeasureLeftVal,
    ⟨vacuumWalkMeasureLeft_nonneg, vacuumWalkMeasureLeft_outside, vacuumWalkMeasureLeft_sum⟩⟩

def vacuumWalkMeasureRight : ProbDist vacuumAdjacentVertices :=
  ⟨vacuumWalkMeasureRightVal,
    ⟨vacuumWalkMeasureRight_nonneg, vacuumWalkMeasureRight_outside, vacuumWalkMeasureRight_sum⟩⟩

theorem vacuumShiftCoupling_nonneg (x y : ℕ) : 0 ≤ vacuumShiftCoupling x y := by
  unfold vacuumShiftCoupling; split_ifs <;> norm_num

theorem vacuumShiftCoupling_left_outside (x : ℕ) (hx : x ∉ vacuumAdjacentVertices)
    (y : ℕ) : vacuumShiftCoupling x y = 0 := by
  obtain ⟨h0, h1, h2, _⟩ := not_mem_vacuumAdjacentVertices x hx
  unfold vacuumShiftCoupling; simp [h0, h1, h2]

theorem vacuumShiftCoupling_right_outside (y : ℕ) (hy : y ∉ vacuumAdjacentVertices)
    (x : ℕ) : vacuumShiftCoupling x y = 0 := by
  obtain ⟨_, h1, h2, h3⟩ := not_mem_vacuumAdjacentVertices y hy
  unfold vacuumShiftCoupling; simp [h1, h2, h3]

theorem vacuumShiftCoupling_row_sum (x : ℕ) (hx : x ∈ vacuumAdjacentVertices) :
    vacuumAdjacentVertices.sum (vacuumShiftCoupling x) = vacuumWalkMeasureLeftVal x := by
  fin_cases hx <;> simp [vacuumShiftCoupling, vacuumWalkMeasureLeftVal, vacuumAdjacentVertices]

theorem vacuumShiftCoupling_col_sum (y : ℕ) (hy : y ∈ vacuumAdjacentVertices) :
    vacuumAdjacentVertices.sum (fun x => vacuumShiftCoupling x y) =
      vacuumWalkMeasureRightVal y := by
  fin_cases hy <;> simp [vacuumShiftCoupling, vacuumWalkMeasureRightVal, vacuumAdjacentVertices]

theorem vacuum_coupling_is_coupling :
    IsCoupling vacuumAdjacentVertices vacuumWalkMeasureLeft vacuumWalkMeasureRight
      vacuumShiftCoupling := by
  refine ⟨vacuumShiftCoupling_nonneg, ?_, ?_, ?_, ?_⟩
  · exact vacuumShiftCoupling_left_outside
  · intro y hy x; exact vacuumShiftCoupling_right_outside y hy x
  · exact vacuumShiftCoupling_row_sum
  · exact vacuumShiftCoupling_col_sum

theorem vacuum_coupling_cost_eq_one :
    couplingTransportCost vacuumAdjacentGraph vacuumShiftCoupling = 1 := by
  unfold couplingTransportCost vacuumAdjacentGraph vacuumAdjacentDist vacuumShiftCoupling
    vacuumAdjacentVertices
  norm_num [Finset.sum_insert, Finset.sum_singleton]

theorem vacuum_w1_le_one :
    W1 vacuumAdjacentGraph vacuumWalkMeasureLeft vacuumWalkMeasureRight ≤ 1 := by
  have h := W1_le_couplingCost vacuumAdjacentGraph vacuumWalkMeasureLeft vacuumWalkMeasureRight
    vacuumShiftCoupling vacuum_coupling_is_coupling
  rw [vacuum_coupling_cost_eq_one] at h
  exact h

theorem vacuum_w1_eq_one :
    W1 vacuumAdjacentGraph vacuumWalkMeasureLeft vacuumWalkMeasureRight = 1 := by
  sorry

theorem vacuum_adjacent_dist_eq_one :
    vacuumAdjacentGraph.dist 0 1 = 1 := by
  unfold vacuumAdjacentGraph vacuumAdjacentDist; norm_num

theorem gorard_vacuum_oric_zero_adjacent :
    OllivierRicci vacuumAdjacentGraph 0 1 vacuumWalkMeasureLeft vacuumWalkMeasureRight = 0 := by
  exact gorard_vacuum_oric_zero_of_w1 vacuumAdjacentGraph 0 1 vacuumWalkMeasureLeft
    vacuumWalkMeasureRight vacuum_adjacent_dist_eq_one vacuum_w1_eq_one

theorem vacuum_cdf_w1_eq_one : (w1AdjacentUniformCDF : ℝ) = 1 := by
  exact_mod_cast w1_adjacent_uniform_eq_one

end

end GTE.ContinuumLimit.GorardVacuumW1Bridge
