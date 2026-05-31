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

theorem vacuumAdjacentDist_eq_zero_iff (x y : ℕ) :
    vacuumAdjacentDist x y = 0 ↔ x = y := by
  unfold vacuumAdjacentDist
  constructor
  · intro h
    have habs : |(x : ℤ) - (y : ℤ)| = 0 := h
    have heq : (x : ℤ) = (y : ℤ) := abs_eq_zero.mp habs
    exact_mod_cast heq
  · intro h; subst h; simp

def vacuumAdjacentGraph : FiniteMetricSpace where
  vertices := vacuumAdjacentVertices
  dist := vacuumAdjacentDist
  dist_nonneg := vacuumAdjacentDist_nonneg
  dist_self := vacuumAdjacentDist_self
  dist_comm := vacuumAdjacentDist_comm
  triangle := vacuumAdjacentDist_triangle
  dist_eq_zero_iff := vacuumAdjacentDist_eq_zero_iff

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

theorem vacuum_couplingCostSet_nonempty :
    (couplingCostSet vacuumAdjacentGraph vacuumWalkMeasureLeft vacuumWalkMeasureRight).Nonempty :=
  ⟨couplingTransportCost vacuumAdjacentGraph vacuumShiftCoupling, vacuumShiftCoupling,
    vacuum_coupling_is_coupling, rfl⟩

theorem vacuum_position_one_lipschitz (x y : ℕ) :
    |(x : ℝ) - (y : ℝ)| ≤ vacuumAdjacentGraph.dist x y := by
  unfold vacuumAdjacentGraph vacuumAdjacentDist
  simp

theorem vacuum_left_expectation_position :
    probExpectation vacuumAdjacentGraph vacuumWalkMeasureLeft (fun x => (x : ℝ)) = 1 := by
  unfold probExpectation vacuumAdjacentGraph vacuumAdjacentVertices vacuumWalkMeasureLeft
    vacuumWalkMeasureLeftVal
  simp [Finset.sum_insert, Finset.sum_singleton]
  norm_num

theorem vacuum_right_expectation_position :
    probExpectation vacuumAdjacentGraph vacuumWalkMeasureRight (fun x => (x : ℝ)) = 2 := by
  unfold probExpectation vacuumAdjacentGraph vacuumAdjacentVertices vacuumWalkMeasureRight
    vacuumWalkMeasureRightVal
  simp [Finset.sum_insert, Finset.sum_singleton]
  norm_num

theorem vacuum_w1_ge_one :
    1 ≤ W1 vacuumAdjacentGraph vacuumWalkMeasureLeft vacuumWalkMeasureRight := by
  have h := W1_ge_of_lipschitz vacuumAdjacentGraph vacuumWalkMeasureLeft vacuumWalkMeasureRight
    (fun x => (x : ℝ)) vacuum_position_one_lipschitz vacuum_couplingCostSet_nonempty
  rw [vacuum_left_expectation_position, vacuum_right_expectation_position] at h
  have habs : |(1 : ℝ) - 2| = 1 := by norm_num
  rw [habs] at h
  exact h

theorem vacuum_w1_eq_one :
    W1 vacuumAdjacentGraph vacuumWalkMeasureLeft vacuumWalkMeasureRight = 1 :=
  le_antisymm vacuum_w1_le_one vacuum_w1_ge_one

theorem vacuum_adjacent_dist_eq_one :
    vacuumAdjacentGraph.dist 0 1 = 1 := by
  unfold vacuumAdjacentGraph vacuumAdjacentDist; norm_num

theorem gorard_vacuum_oric_zero_adjacent :
    OllivierRicci vacuumAdjacentGraph 0 1 vacuumWalkMeasureLeft vacuumWalkMeasureRight = 0 := by
  exact gorard_vacuum_oric_zero_of_w1 vacuumAdjacentGraph 0 1 vacuumWalkMeasureLeft
    vacuumWalkMeasureRight vacuum_adjacent_dist_eq_one vacuum_w1_eq_one

theorem vacuum_cdf_w1_eq_one : (w1AdjacentUniformCDF : ℝ) = 1 := by
  exact_mod_cast w1_adjacent_uniform_eq_one

/-!
## Translation-invariant vacuum tape windows

The adjacent-patch computation at `(0,1)` applies to every edge `(n, n+1)` on the
Rule 110 vacuum tape by translation invariance: the ether pattern and uniform
1-step walk measures are identical at every position.
-/

/-- Four-cell vacuum window `{n, n+1, n+2, n+3}` centered at adjacent edge `(n, n+1)`. -/
def vacuumAdjacentVerticesAt (n : ℕ) : Finset ℕ := {n, n + 1, n + 2, n + 3}

def vacuumAdjacentDistAt (n : ℕ) (x y : ℕ) : ℝ := |((x : ℤ) - (y : ℤ))|

theorem vacuumAdjacentDistAt_nonneg (n : ℕ) (x y : ℕ) : 0 ≤ vacuumAdjacentDistAt n x y := by
  unfold vacuumAdjacentDistAt; exact abs_nonneg _

theorem vacuumAdjacentDistAt_self (n : ℕ) (x : ℕ) : vacuumAdjacentDistAt n x x = 0 := by
  unfold vacuumAdjacentDistAt; simp

theorem vacuumAdjacentDistAt_comm (n : ℕ) (x y : ℕ) :
    vacuumAdjacentDistAt n x y = vacuumAdjacentDistAt n y x := by
  unfold vacuumAdjacentDistAt; rw [abs_sub_comm]

theorem vacuumAdjacentDistAt_triangle (n : ℕ) (x y z : ℕ) :
    vacuumAdjacentDistAt n x z ≤ vacuumAdjacentDistAt n x y + vacuumAdjacentDistAt n y z := by
  unfold vacuumAdjacentDistAt
  exact_mod_cast abs_sub_le (x : ℤ) (y : ℤ) (z : ℤ)

theorem vacuumAdjacentDistAt_eq_zero_iff (n : ℕ) (x y : ℕ) :
    vacuumAdjacentDistAt n x y = 0 ↔ x = y := by
  unfold vacuumAdjacentDistAt
  constructor
  · intro h
    have habs : |(x : ℤ) - (y : ℤ)| = 0 := h
    have heq : (x : ℤ) = (y : ℤ) := abs_eq_zero.mp habs
    exact_mod_cast heq
  · intro h; subst h; simp

def vacuumAdjacentGraphAt (n : ℕ) : FiniteMetricSpace where
  vertices := vacuumAdjacentVerticesAt n
  dist := vacuumAdjacentDistAt n
  dist_nonneg := vacuumAdjacentDistAt_nonneg n
  dist_self := vacuumAdjacentDistAt_self n
  dist_comm := vacuumAdjacentDistAt_comm n
  triangle := vacuumAdjacentDistAt_triangle n
  dist_eq_zero_iff := vacuumAdjacentDistAt_eq_zero_iff n

/-- The vacuum tape window predicate: a four-cell patch with integer-line metric. -/
def IsVacuumTapeWindow (M : FiniteMetricSpace) (n : ℕ) : Prop :=
  M.vertices = vacuumAdjacentVerticesAt n ∧
  ∀ x y, x ∈ M.vertices → y ∈ M.vertices → M.dist x y = vacuumAdjacentDistAt n x y

theorem isVacuumTapeWindow_at (n : ℕ) : IsVacuumTapeWindow (vacuumAdjacentGraphAt n) n := by
  refine ⟨rfl, fun x y hx hy => ?_⟩
  rfl

def vacuumWalkMeasureLeftValAt (n : ℕ) (x : ℕ) : ℝ :=
  if x = n then (1 : ℝ) / 3
  else if x = n + 1 then (1 : ℝ) / 3
  else if x = n + 2 then (1 : ℝ) / 3
  else 0

def vacuumWalkMeasureRightValAt (n : ℕ) (x : ℕ) : ℝ :=
  if x = n + 1 then (1 : ℝ) / 3
  else if x = n + 2 then (1 : ℝ) / 3
  else if x = n + 3 then (1 : ℝ) / 3
  else 0

theorem not_mem_vacuumAdjacentVerticesAt (n x : ℕ) (hx : x ∉ vacuumAdjacentVerticesAt n) :
    x ≠ n ∧ x ≠ n + 1 ∧ x ≠ n + 2 ∧ x ≠ n + 3 := by
  simp [vacuumAdjacentVerticesAt, Finset.mem_insert, Finset.mem_singleton] at hx
  tauto

theorem vacuumWalkMeasureLeftValAt_nonneg (n x : ℕ) (hx : x ∈ vacuumAdjacentVerticesAt n) :
    0 ≤ vacuumWalkMeasureLeftValAt n x := by
  simp only [vacuumAdjacentVerticesAt, vacuumWalkMeasureLeftValAt,
    Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with hx | hx | hx | hx <;> subst hx <;> norm_num

theorem vacuumWalkMeasureLeftValAt_outside (n x : ℕ) (hx : x ∉ vacuumAdjacentVerticesAt n) :
    vacuumWalkMeasureLeftValAt n x = 0 := by
  obtain ⟨hn, hn1, hn2, _⟩ := not_mem_vacuumAdjacentVerticesAt n x hx
  simp [vacuumWalkMeasureLeftValAt, hn, hn1, hn2]

theorem vacuumWalkMeasureLeftValAt_sum (n : ℕ) :
    (vacuumAdjacentVerticesAt n).sum (vacuumWalkMeasureLeftValAt n) = 1 := by
  simp [vacuumAdjacentVerticesAt, vacuumWalkMeasureLeftValAt]; norm_num

theorem vacuumWalkMeasureRightValAt_nonneg (n x : ℕ) (hx : x ∈ vacuumAdjacentVerticesAt n) :
    0 ≤ vacuumWalkMeasureRightValAt n x := by
  simp only [vacuumAdjacentVerticesAt, vacuumWalkMeasureRightValAt,
    Finset.mem_insert, Finset.mem_singleton] at hx ⊢
  rcases hx with hx | hx | hx | hx <;> subst hx <;> norm_num

theorem vacuumWalkMeasureRightValAt_outside (n x : ℕ) (hx : x ∉ vacuumAdjacentVerticesAt n) :
    vacuumWalkMeasureRightValAt n x = 0 := by
  obtain ⟨_, hn1, hn2, hn3⟩ := not_mem_vacuumAdjacentVerticesAt n x hx
  simp [vacuumWalkMeasureRightValAt, hn1, hn2, hn3]

theorem vacuumWalkMeasureRightValAt_sum (n : ℕ) :
    (vacuumAdjacentVerticesAt n).sum (vacuumWalkMeasureRightValAt n) = 1 := by
  simp [vacuumAdjacentVerticesAt, vacuumWalkMeasureRightValAt]; norm_num

def vacuumWalkMeasureLeftAt (n : ℕ) : ProbDist (vacuumAdjacentVerticesAt n) :=
  ⟨vacuumWalkMeasureLeftValAt n,
    ⟨vacuumWalkMeasureLeftValAt_nonneg n,
      vacuumWalkMeasureLeftValAt_outside n,
      vacuumWalkMeasureLeftValAt_sum n⟩⟩

def vacuumWalkMeasureRightAt (n : ℕ) : ProbDist (vacuumAdjacentVerticesAt n) :=
  ⟨vacuumWalkMeasureRightValAt n,
    ⟨vacuumWalkMeasureRightValAt_nonneg n,
      vacuumWalkMeasureRightValAt_outside n,
      vacuumWalkMeasureRightValAt_sum n⟩⟩

/-- Uniform 1-step random walk measure at tape position `n` (left endpoint). -/
def IsVacuumWalkMeasureLeftAt (n : ℕ) (μ : ProbDist (vacuumAdjacentVerticesAt n)) : Prop :=
  μ = vacuumWalkMeasureLeftAt n

/-- Uniform 1-step random walk measure at tape position `n + 1` (right endpoint). -/
def IsVacuumWalkMeasureRightAt (n : ℕ) (μ : ProbDist (vacuumAdjacentVerticesAt n)) : Prop :=
  μ = vacuumWalkMeasureRightAt n

def vacuumShiftCouplingAt (n : ℕ) (x y : ℕ) : ℝ :=
  if x = n ∧ y = n + 1 then (1 : ℝ) / 3
  else if x = n + 1 ∧ y = n + 2 then (1 : ℝ) / 3
  else if x = n + 2 ∧ y = n + 3 then (1 : ℝ) / 3
  else 0

theorem vacuumShiftCouplingAt_nonneg (n x y : ℕ) : 0 ≤ vacuumShiftCouplingAt n x y := by
  unfold vacuumShiftCouplingAt; split_ifs <;> norm_num

theorem vacuumShiftCouplingAt_left_outside (n x : ℕ) (hx : x ∉ vacuumAdjacentVerticesAt n)
    (y : ℕ) : vacuumShiftCouplingAt n x y = 0 := by
  obtain ⟨hn, hn1, hn2, _⟩ := not_mem_vacuumAdjacentVerticesAt n x hx
  unfold vacuumShiftCouplingAt; simp [hn, hn1, hn2]

theorem vacuumShiftCouplingAt_right_outside (n y : ℕ) (hy : y ∉ vacuumAdjacentVerticesAt n)
    (x : ℕ) : vacuumShiftCouplingAt n x y = 0 := by
  obtain ⟨_, hn1, hn2, hn3⟩ := not_mem_vacuumAdjacentVerticesAt n y hy
  unfold vacuumShiftCouplingAt; simp [hn1, hn2, hn3]

theorem vacuumShiftCouplingAt_row_sum (n x : ℕ) (hx : x ∈ vacuumAdjacentVerticesAt n) :
    (vacuumAdjacentVerticesAt n).sum (vacuumShiftCouplingAt n x) =
      vacuumWalkMeasureLeftValAt n x := by
  simp only [vacuumAdjacentVerticesAt, Finset.mem_insert, Finset.mem_singleton] at hx
  rcases hx with hx | hx | hx | hx <;>
    subst hx <;>
    simp [vacuumShiftCouplingAt, vacuumWalkMeasureLeftValAt, vacuumAdjacentVerticesAt,
      Finset.sum_insert, Finset.sum_singleton]

theorem vacuumShiftCouplingAt_col_sum (n y : ℕ) (hy : y ∈ vacuumAdjacentVerticesAt n) :
    (vacuumAdjacentVerticesAt n).sum (fun x => vacuumShiftCouplingAt n x y) =
      vacuumWalkMeasureRightValAt n y := by
  simp only [vacuumAdjacentVerticesAt, Finset.mem_insert, Finset.mem_singleton] at hy
  rcases hy with hy | hy | hy | hy <;>
    subst hy <;>
    simp [vacuumShiftCouplingAt, vacuumWalkMeasureRightValAt, vacuumAdjacentVerticesAt,
      Finset.sum_insert, Finset.sum_singleton]

theorem vacuum_coupling_is_coupling_at (n : ℕ) :
    IsCoupling (vacuumAdjacentVerticesAt n) (vacuumWalkMeasureLeftAt n)
      (vacuumWalkMeasureRightAt n) (vacuumShiftCouplingAt n) := by
  refine ⟨vacuumShiftCouplingAt_nonneg n, ?_, ?_, ?_, ?_⟩
  · exact vacuumShiftCouplingAt_left_outside n
  · intro y hy x; exact vacuumShiftCouplingAt_right_outside n y hy x
  · exact vacuumShiftCouplingAt_row_sum n
  · exact vacuumShiftCouplingAt_col_sum n

theorem vacuum_coupling_cost_eq_one_at (n : ℕ) :
    couplingTransportCost (vacuumAdjacentGraphAt n) (vacuumShiftCouplingAt n) = 1 := by
  unfold couplingTransportCost vacuumAdjacentGraphAt vacuumAdjacentDistAt vacuumShiftCouplingAt
    vacuumAdjacentVerticesAt
  norm_num [Finset.sum_insert, Finset.sum_singleton]

theorem vacuum_w1_le_one_at (n : ℕ) :
    W1 (vacuumAdjacentGraphAt n) (vacuumWalkMeasureLeftAt n) (vacuumWalkMeasureRightAt n) ≤ 1 := by
  have h := W1_le_couplingCost (vacuumAdjacentGraphAt n) (vacuumWalkMeasureLeftAt n)
    (vacuumWalkMeasureRightAt n) (vacuumShiftCouplingAt n) (vacuum_coupling_is_coupling_at n)
  rw [vacuum_coupling_cost_eq_one_at n] at h
  exact h

theorem vacuum_couplingCostSet_nonempty_at (n : ℕ) :
    (couplingCostSet (vacuumAdjacentGraphAt n) (vacuumWalkMeasureLeftAt n)
      (vacuumWalkMeasureRightAt n)).Nonempty :=
  ⟨couplingTransportCost (vacuumAdjacentGraphAt n) (vacuumShiftCouplingAt n),
    vacuumShiftCouplingAt n, vacuum_coupling_is_coupling_at n, rfl⟩

theorem vacuum_position_one_lipschitz_at (n : ℕ) (x y : ℕ) :
    |(x : ℝ) - (y : ℝ)| ≤ (vacuumAdjacentGraphAt n).dist x y := by
  unfold vacuumAdjacentGraphAt vacuumAdjacentDistAt
  simp

theorem vacuum_left_expectation_position_at (n : ℕ) :
    probExpectation (vacuumAdjacentGraphAt n) (vacuumWalkMeasureLeftAt n) (fun x => (x : ℝ)) =
      (n : ℝ) + 1 := by
  unfold probExpectation vacuumAdjacentGraphAt vacuumAdjacentVerticesAt vacuumWalkMeasureLeftAt
    vacuumWalkMeasureLeftValAt
  simp [Finset.sum_insert, Finset.sum_singleton]
  ring

theorem vacuum_right_expectation_position_at (n : ℕ) :
    probExpectation (vacuumAdjacentGraphAt n) (vacuumWalkMeasureRightAt n) (fun x => (x : ℝ)) =
      (n : ℝ) + 2 := by
  unfold probExpectation vacuumAdjacentGraphAt vacuumAdjacentVerticesAt vacuumWalkMeasureRightAt
    vacuumWalkMeasureRightValAt
  simp [Finset.sum_insert, Finset.sum_singleton]
  ring

theorem vacuum_w1_ge_one_at (n : ℕ) :
    1 ≤ W1 (vacuumAdjacentGraphAt n) (vacuumWalkMeasureLeftAt n) (vacuumWalkMeasureRightAt n) := by
  have h := W1_ge_of_lipschitz (vacuumAdjacentGraphAt n) (vacuumWalkMeasureLeftAt n)
    (vacuumWalkMeasureRightAt n) (fun x => (x : ℝ)) (vacuum_position_one_lipschitz_at n)
    (vacuum_couplingCostSet_nonempty_at n)
  rw [vacuum_left_expectation_position_at n, vacuum_right_expectation_position_at n] at h
  have habs : |((n : ℝ) + 1) - ((n : ℝ) + 2)| = 1 := by ring_nf; norm_num
  rw [habs] at h
  exact h

theorem vacuum_w1_eq_one_at (n : ℕ) :
    W1 (vacuumAdjacentGraphAt n) (vacuumWalkMeasureLeftAt n) (vacuumWalkMeasureRightAt n) = 1 :=
  le_antisymm (vacuum_w1_le_one_at n) (vacuum_w1_ge_one_at n)

theorem vacuum_adjacent_dist_eq_one_at (n : ℕ) :
    (vacuumAdjacentGraphAt n).dist n (n + 1) = 1 := by
  unfold vacuumAdjacentGraphAt vacuumAdjacentDistAt; norm_num

/-- Translation invariance: Ollivier-Ricci curvature vanishes at every adjacent vacuum edge. -/
theorem gorard_vacuum_oric_zero_at (n : ℕ) :
    OllivierRicci (vacuumAdjacentGraphAt n) n (n + 1) (vacuumWalkMeasureLeftAt n)
      (vacuumWalkMeasureRightAt n) = 0 :=
  gorard_vacuum_oric_zero_of_w1 (vacuumAdjacentGraphAt n) n (n + 1)
    (vacuumWalkMeasureLeftAt n) (vacuumWalkMeasureRightAt n)
    (vacuum_adjacent_dist_eq_one_at n) (vacuum_w1_eq_one_at n)

/--
Scoped replacement for the overly general `gorard_vacuum_oric_zero` axiom:
Ollivier-Ricci curvature vanishes on adjacent vacuum cells with 1-step uniform walk measures.
-/
theorem gorard_vacuum_oric_zero_scoped (n : ℕ) :
    OllivierRicci (vacuumAdjacentGraphAt n) n (n + 1) (vacuumWalkMeasureLeftAt n)
      (vacuumWalkMeasureRightAt n) = 0 :=
  gorard_vacuum_oric_zero_at n

/-- Vacuum walk-measure predicates imply κ_OR = 0 on the canonical window graph. -/
theorem gorard_vacuum_oric_zero_scoped_pred (n : ℕ)
    (μ_n : ProbDist (vacuumAdjacentVerticesAt n))
    (μ_np1 : ProbDist (vacuumAdjacentVerticesAt n))
    (hμ_n : IsVacuumWalkMeasureLeftAt n μ_n)
    (hμ_np1 : IsVacuumWalkMeasureRightAt n μ_np1) :
    OllivierRicci (vacuumAdjacentGraphAt n) n (n + 1) μ_n μ_np1 = 0 := by
  rw [hμ_n, hμ_np1]
  exact gorard_vacuum_oric_zero_scoped n

end

end GTE.ContinuumLimit.GorardVacuumW1Bridge
