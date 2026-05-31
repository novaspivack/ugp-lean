import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field

/-!
# W₁ Wasserstein Distance for OQ-QG-1

This module provides the W₁ (1-Wasserstein / Earth Mover's Distance) framework
needed for OQ-QG-1 Step 2: proving that the Rule 110 causal graph
converges to a smooth Lorentzian manifold in the Gromov-Wasserstein sense.

Mathlib does not yet have an optimal transport / Wasserstein library (as of 2026).
This scaffold provides:
- Self-contained definitions of finite metric spaces and probability distributions
- A declared (sorry) definition of W₁ with the correct type signature
- The Ollivier-Ricci curvature formula via W₁
- A named axiom for the Gorard vacuum Ricci-flat condition
- A named axiom for Gromov-Wasserstein convergence (long-range target)

## OQ-QG-1 dependency chain

Step 1 (DONE): GF(7) vacuum uniqueness — `GF7VacuumFixedPoint.lean`
Step 2 (THIS FILE): W₁ distance scaffold + Ollivier-Ricci formulation
Step 3 (FUTURE): Gorard chain — discrete Ricci flatness of vacuum causal graph
Step 4 (FUTURE): Gromov-Wasserstein limit → smooth Lorentzian metric

## Status
- `W1`: noncomputable, defined as `sInf` of coupling transport costs
- `W1_le_couplingCost`: CatAL upper bound for any admissible coupling
- `W1_nonneg`, `W1_comm`: CatAL basic properties
- `OllivierRicci`: noncomputable, defined in terms of `W1`
- `gorard_vacuum_oric_zero`: **axiom** (overly general; use `GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped`)
- `rule110_gromov_wasserstein_limit`: **axiom** — GW convergence (long-range, gated on OQ-QG-1)

## Key references
- Sturm (2006): metric measure spaces and Ricci curvature bounds via W₂
- Lott-Villani (2009): synthetic Ricci curvature via optimal transport
- Gorard (2020): Ollivier-Ricci curvature on causal graphs
- Ollivier (2009): Ricci curvature of Markov chains on metric spaces
-/

namespace GTE.ContinuumLimit.Wasserstein

/-!
## Finite metric spaces

We work with finite metric spaces throughout — sufficient for CA causal graphs at
any fixed resolution. The continuum limit is captured by the Gromov-Wasserstein
convergence axiom below.
-/

/-- A finite metric space: a finite vertex set with a proper metric. -/
structure FiniteMetricSpace where
  /-- The vertex set (represented as a Finset of ℕ for simplicity). -/
  vertices : Finset ℕ
  /-- The distance function. -/
  dist : ℕ → ℕ → ℝ
  dist_nonneg : ∀ x y, 0 ≤ dist x y
  dist_self   : ∀ x, dist x x = 0
  dist_comm   : ∀ x y, dist x y = dist y x
  triangle    : ∀ x y z, dist x z ≤ dist x y + dist y z
  dist_eq_zero_iff : ∀ x y, dist x y = 0 ↔ x = y

/-!
## Probability distributions on finite sets
-/

/--
A probability distribution on a finite vertex set `S`:
a non-negative function supported on `S` that sums to 1.
-/
def ProbDist (S : Finset ℕ) : Type :=
  { f : ℕ → ℝ // (∀ x ∈ S, 0 ≤ f x) ∧ (∀ x ∉ S, f x = 0) ∧ S.sum f = 1 }


private theorem probDist_vertex_mass_balance (S : Finset ℕ) (μ ν : ProbDist S) :
    S.sum (fun x => μ.val x - ν.val x) = 0 := by
  rw [Finset.sum_sub_distrib, μ.2.2.2, ν.2.2.2, sub_self]

/--
A coupling of two distributions `μ` and `ν` on `S`:
a joint distribution `γ : ℕ → ℕ → ℝ` with the correct marginals.
-/
def IsCoupling (S : Finset ℕ) (μ ν : ProbDist S) (γ : ℕ → ℕ → ℝ) : Prop :=
  (∀ x y, 0 ≤ γ x y) ∧
  (∀ x ∉ S, ∀ y, γ x y = 0) ∧
  (∀ y ∉ S, ∀ x, γ x y = 0) ∧
  (∀ x ∈ S, S.sum (γ x) = μ.val x) ∧
  (∀ y ∈ S, S.sum (fun x => γ x y) = ν.val y)

/-- Transport cost of a coupling on a finite metric space. -/
def couplingTransportCost (M : FiniteMetricSpace) (γ : ℕ → ℕ → ℝ) : ℝ :=
  M.vertices.sum fun x => M.vertices.sum fun y => γ x y * M.dist x y

/-- Set of transport costs over all admissible couplings. -/
def couplingCostSet (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) : Set ℝ :=
  { c | ∃ γ, IsCoupling M.vertices μ ν γ ∧ c = couplingTransportCost M γ }

/-!
## W₁ Wasserstein distance

W₁ is the infimum of the transport cost over all couplings:
  W₁(μ, ν) = inf_{γ ∈ Γ(μ,ν)} ∑_{x,y} γ(x,y) · d(x,y)

On finite spaces this infimum is attained (LP duality). The Lean proof of
general properties (symmetry, triangle inequality, CDF identification) remains
open pending a dedicated optimal transport library in Mathlib (2026).
-/

/--
W₁ (1-Wasserstein / Earth Mover's Distance) between two probability
distributions on a finite metric space.
-/
noncomputable def W1 (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) : ℝ :=
  sInf (couplingCostSet M μ ν)

theorem couplingTransportCost_nonneg (M : FiniteMetricSpace) (γ : ℕ → ℕ → ℝ)
    (hγ : ∀ x y, 0 ≤ γ x y) :
    0 ≤ couplingTransportCost M γ := by
  unfold couplingTransportCost
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (hγ x y) (M.dist_nonneg x y)

/-- Any admissible coupling gives an upper bound on W₁. -/
theorem W1_le_couplingCost (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (γ : ℕ → ℕ → ℝ) (hγ : IsCoupling M.vertices μ ν γ) :
    W1 M μ ν ≤ couplingTransportCost M γ := by
  unfold W1 couplingCostSet
  apply csInf_le
  · refine ⟨0, ?_⟩
    intro c hc
    obtain ⟨γ', hγ', hc'⟩ := hc
    rw [hc']
    exact couplingTransportCost_nonneg M γ' hγ'.1
  · exact ⟨γ, hγ, rfl⟩

/-- Expectation of `f` under a probability distribution on `M.vertices`. -/
def probExpectation (M : FiniteMetricSpace) (μ : ProbDist M.vertices) (f : ℕ → ℝ) : ℝ :=
  M.vertices.sum fun x => f x * μ.val x

private theorem probExpectation_diff_eq_coupling_sum
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) (γ : ℕ → ℕ → ℝ)
    (hγ : IsCoupling M.vertices μ ν γ) (f : ℕ → ℝ) :
    probExpectation M μ f - probExpectation M ν f =
      M.vertices.sum fun x =>
        M.vertices.sum fun y => γ x y * (f x - f y) := by
  unfold probExpectation
  have hμ :
      M.vertices.sum (fun x => f x * μ.val x) =
        M.vertices.sum fun x =>
          M.vertices.sum fun y => f x * γ x y := by
    apply Finset.sum_congr rfl
    intro x hx
    rw [← hγ.2.2.2.1 x hx, Finset.mul_sum]
  have hν :
      M.vertices.sum (fun y => f y * ν.val y) =
        M.vertices.sum fun y =>
          M.vertices.sum fun x => f y * γ x y := by
    apply Finset.sum_congr rfl
    intro y hy
    rw [← hγ.2.2.2.2 y hy, Finset.mul_sum]
  rw [hμ, hν]
  rw [show M.vertices.sum (fun y => M.vertices.sum (fun x => f y * γ x y)) =
      M.vertices.sum (fun x => M.vertices.sum (fun y => f y * γ x y)) from Finset.sum_comm]
  rw [← Finset.sum_sub_distrib]
  congr 1
  ext x
  rw [← Finset.sum_sub_distrib]
  refine Finset.sum_congr rfl ?_
  intro y _
  ring

private theorem abs_probExpectation_diff_le_couplingTransportCost
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) (γ : ℕ → ℕ → ℝ)
    (hγ : IsCoupling M.vertices μ ν γ) (f : ℕ → ℝ)
    (hf : ∀ x y, |f x - f y| ≤ M.dist x y) :
    |probExpectation M μ f - probExpectation M ν f| ≤ couplingTransportCost M γ := by
  rw [probExpectation_diff_eq_coupling_sum M μ ν γ hγ f]
  have habs_inner :
      ∀ x ∈ M.vertices,
        |M.vertices.sum fun y => γ x y * (f x - f y)| ≤
          M.vertices.sum fun y => |γ x y * (f x - f y)| :=
    fun x _ => Finset.abs_sum_le_sum_abs (s := M.vertices) (f := fun y => γ x y * (f x - f y))
  have habs :
      |M.vertices.sum fun x =>
          M.vertices.sum fun y => γ x y * (f x - f y)| ≤
        M.vertices.sum fun x =>
          M.vertices.sum fun y => |γ x y * (f x - f y)| := by
    calc
      |M.vertices.sum fun x =>
          M.vertices.sum fun y => γ x y * (f x - f y)| ≤
        M.vertices.sum fun x =>
          |M.vertices.sum fun y => γ x y * (f x - f y)| :=
        Finset.abs_sum_le_sum_abs (s := M.vertices)
          (f := fun x => M.vertices.sum fun y => γ x y * (f x - f y))
      _ ≤ M.vertices.sum fun x =>
            M.vertices.sum fun y => |γ x y * (f x - f y)| :=
        Finset.sum_le_sum habs_inner
  have hterm :
      ∀ x y,
        |γ x y * (f x - f y)| ≤ γ x y * M.dist x y := by
    intro x y
    have hγnn := hγ.1 x y
    rw [abs_mul, abs_of_nonneg hγnn]
    exact mul_le_mul_of_nonneg_left (hf x y) hγnn
  have hinner :
      M.vertices.sum (fun x => M.vertices.sum (fun y => |γ x y * (f x - f y)|)) ≤
        couplingTransportCost M γ := by
    unfold couplingTransportCost
    refine Finset.sum_le_sum fun x _ => ?_
    exact Finset.sum_le_sum fun y _ => hterm x y
  exact habs.trans hinner

/--
Kantorovich–Rubinstein weak duality: any 1-Lipschitz test function gives a lower
bound on W₁ via the expectation gap.
-/
theorem W1_ge_of_lipschitz (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (f : ℕ → ℝ) (hf : ∀ x y, |f x - f y| ≤ M.dist x y)
    (hne : (couplingCostSet M μ ν).Nonempty) :
    |probExpectation M μ f - probExpectation M ν f| ≤ W1 M μ ν := by
  have hle : ∀ c ∈ couplingCostSet M μ ν,
      |probExpectation M μ f - probExpectation M ν f| ≤ c := by
    intro c hc
    obtain ⟨γ, hγ, hc'⟩ := hc
    rw [hc']
    exact abs_probExpectation_diff_le_couplingTransportCost M μ ν γ hγ f hf
  unfold W1
  exact le_csInf hne hle

/-!
## Basic properties of W₁
-/

/-- Independent (product) coupling of `μ` and `ν`. -/
def productCoupling (S : Finset ℕ) (μ ν : ProbDist S) (x y : ℕ) : ℝ :=
  μ.val x * ν.val y

theorem productCoupling_nonneg (S : Finset ℕ) (μ ν : ProbDist S) :
    ∀ x y, 0 ≤ productCoupling S μ ν x y := by
  intro x y
  unfold productCoupling
  by_cases hx : x ∈ S
  · by_cases hy : y ∈ S
    · exact mul_nonneg (μ.2.1 x hx) (ν.2.1 y hy)
    · simp [productCoupling, hx, hy, ν.2.2.1 y hy]
  · simp [productCoupling, hx, μ.2.2.1 x hx]

theorem productCoupling_left_outside (S : Finset ℕ) (μ ν : ProbDist S)
    (x : ℕ) (hx : x ∉ S) (y : ℕ) :
    productCoupling S μ ν x y = 0 := by
  unfold productCoupling
  simp [hx, μ.2.2.1 x hx]

theorem productCoupling_right_outside (S : Finset ℕ) (μ ν : ProbDist S)
    (y : ℕ) (hy : y ∉ S) (x : ℕ) :
    productCoupling S μ ν x y = 0 := by
  unfold productCoupling
  simp [hy, ν.2.2.1 y hy]

theorem productCoupling_row_sum (S : Finset ℕ) (μ ν : ProbDist S)
    (x : ℕ) (hx : x ∈ S) :
    S.sum (productCoupling S μ ν x) = μ.val x := by
  unfold productCoupling
  rw [← Finset.mul_sum, ν.2.2.2, mul_one]

theorem productCoupling_col_sum (S : Finset ℕ) (μ ν : ProbDist S)
    (y : ℕ) (hy : y ∈ S) :
    S.sum (fun x => productCoupling S μ ν x y) = ν.val y := by
  unfold productCoupling
  rw [← Finset.sum_mul, μ.2.2.2, one_mul]

theorem productCoupling_is_coupling (S : Finset ℕ) (μ ν : ProbDist S) :
    IsCoupling S μ ν (productCoupling S μ ν) := by
  refine ⟨productCoupling_nonneg S μ ν, ?_, ?_, ?_, ?_⟩
  · exact productCoupling_left_outside S μ ν
  · intro y hy x; exact productCoupling_right_outside S μ ν y hy x
  · exact productCoupling_row_sum S μ ν
  · exact productCoupling_col_sum S μ ν

theorem couplingCostSet_nonempty (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    (couplingCostSet M μ ν).Nonempty :=
  ⟨couplingTransportCost M (productCoupling M.vertices μ ν),
    productCoupling M.vertices μ ν,
    productCoupling_is_coupling M.vertices μ ν, rfl⟩

/-- W₁ is non-negative. -/
theorem W1_nonneg (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    0 ≤ W1 M μ ν := by
  unfold W1
  apply le_csInf (couplingCostSet_nonempty M μ ν)
  intro c hc
  obtain ⟨γ, hγ, hc'⟩ := hc
  rw [hc']
  exact couplingTransportCost_nonneg M γ hγ.1

/-- Transpose of a coupling, swapping marginals. -/
def transposeCoupling (S : Finset ℕ) (γ : ℕ → ℕ → ℝ) (x y : ℕ) : ℝ :=
  γ y x

theorem transposeCoupling_is_coupling (S : Finset ℕ) (μ ν : ProbDist S) (γ : ℕ → ℕ → ℝ)
    (hγ : IsCoupling S μ ν γ) :
    IsCoupling S ν μ (transposeCoupling S γ) := by
  refine ⟨fun x y => hγ.1 y x, ?_, ?_, ?_, ?_⟩
  · intro x hx y; exact hγ.2.2.1 x hx y
  · intro y hy x; exact hγ.2.1 y hy x
  · intro x hx; simpa [transposeCoupling] using hγ.2.2.2.2 x hx
  · intro y hy; simpa [transposeCoupling] using hγ.2.2.2.1 y hy

theorem couplingTransportCost_transpose (M : FiniteMetricSpace) (γ : ℕ → ℕ → ℝ) :
    couplingTransportCost M (transposeCoupling M.vertices γ) =
      couplingTransportCost M γ := by
  unfold couplingTransportCost transposeCoupling
  rw [Finset.sum_comm]
  congr 1; ext y
  apply Finset.sum_congr rfl
  intro x _
  rw [M.dist_comm y x]

theorem couplingCostSet_comm (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    couplingCostSet M μ ν = couplingCostSet M ν μ := by
  ext c
  constructor
  · intro hc
    obtain ⟨γ, hγ, hc'⟩ := hc
    refine ⟨transposeCoupling M.vertices γ, transposeCoupling_is_coupling M.vertices μ ν γ hγ, ?_⟩
    rw [couplingTransportCost_transpose M γ, hc']
  · intro hc
    obtain ⟨γ, hγ, hc'⟩ := hc
    refine ⟨transposeCoupling M.vertices γ, transposeCoupling_is_coupling M.vertices ν μ γ hγ, ?_⟩
    rw [couplingTransportCost_transpose M γ, hc']

/-- W₁ is symmetric. -/
theorem W1_comm (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = W1 M ν μ := by
  unfold W1
  rw [couplingCostSet_comm M μ ν]

theorem dist_pos_of_ne (M : FiniteMetricSpace) {x y : ℕ} (hne : x ≠ y) : 0 < M.dist x y := by
  by_contra h
  push_neg at h
  exact hne ((M.dist_eq_zero_iff x y).mp (le_antisymm h (M.dist_nonneg x y)))

theorem dist_lipschitz (M : FiniteMetricSpace) (xAnchor : ℕ) :
    ∀ x y, |M.dist x xAnchor - M.dist y xAnchor| ≤ M.dist x y := by
  intro x y
  have h1 : M.dist x xAnchor ≤ M.dist x y + M.dist y xAnchor := M.triangle x y xAnchor
  have h2 : M.dist y xAnchor ≤ M.dist x y + M.dist x xAnchor := by
    rw [M.dist_comm x y]; exact M.triangle y x xAnchor
  rw [abs_le]; constructor <;> linarith

def diagonalCoupling (S : Finset ℕ) (μ : ProbDist S) (x y : ℕ) : ℝ :=
  if x = y then μ.val x else 0

theorem diagonalCoupling_nonneg (S : Finset ℕ) (μ : ProbDist S) :
    ∀ x y, 0 ≤ diagonalCoupling S μ x y := by
  intro x y; unfold diagonalCoupling; split_ifs with h
  · subst h; by_cases hx : x ∈ S
    · exact μ.2.1 x hx
    · simp [μ.2.2.1 x hx]
  · simp

theorem diagonalCoupling_left_outside (S : Finset ℕ) (μ : ProbDist S)
    (x : ℕ) (hx : x ∉ S) (y : ℕ) :
    diagonalCoupling S μ x y = 0 := by
  unfold diagonalCoupling; split_ifs with h
  · subst h; simp [μ.2.2.1 x hx]
  · simp

theorem diagonalCoupling_right_outside (S : Finset ℕ) (μ : ProbDist S)
    (y : ℕ) (hy : y ∉ S) (x : ℕ) :
    diagonalCoupling S μ x y = 0 := by
  unfold diagonalCoupling; split_ifs with h
  · simp [h, μ.2.2.1 y hy]
  · simp

theorem diagonalCoupling_row_sum (S : Finset ℕ) (μ : ProbDist S)
    (x : ℕ) (hx : x ∈ S) :
    S.sum (diagonalCoupling S μ x) = μ.val x := by
  classical
  simp [diagonalCoupling, Finset.sum_ite_eq', hx]

theorem diagonalCoupling_col_sum (S : Finset ℕ) (μ : ProbDist S)
    (y : ℕ) (hy : y ∈ S) :
    S.sum (fun x => diagonalCoupling S μ x y) = μ.val y := by
  classical
  simp [diagonalCoupling, Finset.sum_ite_eq', hy]

theorem diagonalCoupling_is_coupling (S : Finset ℕ) (μ : ProbDist S) :
    IsCoupling S μ μ (diagonalCoupling S μ) := by
  refine ⟨diagonalCoupling_nonneg S μ, ?_, ?_, ?_, ?_⟩
  · exact diagonalCoupling_left_outside S μ
  · intro y hy x; exact diagonalCoupling_right_outside S μ y hy x
  · exact diagonalCoupling_row_sum S μ
  · exact diagonalCoupling_col_sum S μ

theorem diagonalCoupling_cost_zero (M : FiniteMetricSpace) (μ : ProbDist M.vertices) :
    couplingTransportCost M (diagonalCoupling M.vertices μ) = 0 := by
  unfold couplingTransportCost diagonalCoupling
  apply Finset.sum_eq_zero; intro x _
  apply Finset.sum_eq_zero; intro y _
  split_ifs with h <;> simp [M.dist_self, h]

theorem probDist_eq_of_vertex_weights_eq {S : Finset ℕ} {μ ν : ProbDist S}
    (h : ∀ x ∈ S, μ.val x = ν.val x) : μ = ν := by
  apply Subtype.ext; funext x
  by_cases hx : x ∈ S
  · exact h x hx
  · rw [μ.2.2.1 x hx, ν.2.2.1 x hx]

private theorem exists_mass_imbalance_neg (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (x : ℕ) (hgt : μ.val x > ν.val x) (hx : x ∈ M.vertices) :
    ∃ y ∈ M.vertices, μ.val y < ν.val y := by
  by_contra hall; push_neg at hall
  have hall' : ∀ t ∈ M.vertices, ν.val t ≤ μ.val t := fun t ht => hall t ht
  have hsum : M.vertices.sum (fun t => μ.val t - ν.val t) = 0 :=
    probDist_vertex_mass_balance M.vertices μ ν
  have hnonneg : ∀ t ∈ M.vertices, 0 ≤ μ.val t - ν.val t :=
    fun t ht => sub_nonneg.mpr (hall' t ht)
  have hpos : 0 < μ.val x - ν.val x := sub_pos.mpr hgt
  have hsumpos : 0 < M.vertices.sum (fun t => μ.val t - ν.val t) :=
    lt_of_lt_of_le hpos (Finset.single_le_sum hnonneg hx)
  linarith

private theorem exists_mass_imbalance_pos (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (x : ℕ) (hlt : μ.val x < ν.val x) (hx : x ∈ M.vertices) :
    ∃ y ∈ M.vertices, μ.val y > ν.val y := by
  by_contra hall; push_neg at hall
  have hall' : ∀ t ∈ M.vertices, μ.val t ≤ ν.val t := fun t ht => hall t ht
  have hsum : M.vertices.sum (fun t => ν.val t - μ.val t) = 0 := by
    simpa using probDist_vertex_mass_balance M.vertices ν μ
  have hnonneg : ∀ t ∈ M.vertices, 0 ≤ ν.val t - μ.val t :=
    fun t ht => sub_nonneg.mpr (hall' t ht)
  have hpos : 0 < ν.val x - μ.val x := sub_pos.mpr hlt
  have hsumpos : 0 < M.vertices.sum (fun t => ν.val t - μ.val t) :=
    lt_of_lt_of_le hpos (Finset.single_le_sum hnonneg hx)
  linarith

theorem exists_mass_imbalance_pair (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) :
    ∃ xPlus ∈ M.vertices, ∃ xMinus ∈ M.vertices,
      μ.val xPlus > ν.val xPlus ∧ μ.val xMinus < ν.val xMinus := by
  obtain ⟨x, hx, hdiff⟩ := hne
  by_cases hgt : μ.val x > ν.val x
  · obtain ⟨xMinus, hxMinus, hlt⟩ := exists_mass_imbalance_neg M μ ν x hgt hx
    exact ⟨x, hx, xMinus, hxMinus, hgt, hlt⟩
  · push_neg at hgt
    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff
    obtain ⟨xPlus, hxPlus, hgt'⟩ := exists_mass_imbalance_pos M μ ν x hlt hx
    exact ⟨xPlus, hxPlus, x, hx, hgt', hlt⟩

theorem productCoupling_cost_pos (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    {x y : ℕ} (hx : x ∈ M.vertices) (hy : y ∈ M.vertices) (hne : x ≠ y)
    (hμ : 0 < μ.val x) (hν : 0 < ν.val y) :
    0 < couplingTransportCost M (productCoupling M.vertices μ ν) := by
  unfold couplingTransportCost productCoupling
  have hwitness : 0 < productCoupling M.vertices μ ν x y * M.dist x y := by
    simp [productCoupling, hx, hy]
    exact mul_pos (mul_pos hμ hν) (dist_pos_of_ne M hne)
  have hnn : ∀ a ∈ M.vertices, ∀ b ∈ M.vertices,
      0 ≤ productCoupling M.vertices μ ν a b * M.dist a b := by
    intro a ha b hb
    simp [productCoupling, ha, hb]
    exact mul_nonneg (mul_nonneg (μ.2.1 a ha) (ν.2.1 b hb)) (M.dist_nonneg a b)
  refine lt_of_lt_of_le hwitness ?_
  calc productCoupling M.vertices μ ν x y * M.dist x y
      ≤ M.vertices.sum (fun b => productCoupling M.vertices μ ν x b * M.dist x b) :=
        Finset.single_le_sum (fun b hb => hnn x hx b hb) hy
    _ ≤ M.vertices.sum (fun a => M.vertices.sum (fun b =>
          productCoupling M.vertices μ ν a b * M.dist a b)) :=
        Finset.single_le_sum (fun a ha => Finset.sum_nonneg (fun b hb => hnn a ha b hb)) hx

private theorem couplingTransportCost_eq_zero_of_eq
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) (γ : ℕ → ℕ → ℝ)
    (hγ : IsCoupling M.vertices μ ν γ) (hc : couplingTransportCost M γ = 0) :
    ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  intro x hx
  have hrow_nonneg (a : ℕ) :
      0 ≤ M.vertices.sum (fun b => γ a b * M.dist a b) := by
    apply Finset.sum_nonneg; intro b _; exact mul_nonneg (hγ.1 a b) (M.dist_nonneg a b)
  have hrow_zero (a : ℕ) (ha : a ∈ M.vertices) :
      M.vertices.sum (fun b => γ a b * M.dist a b) = 0 := by
    unfold couplingTransportCost at hc
    exact (Finset.sum_eq_zero_iff_of_nonneg (fun t ht => hrow_nonneg t)).mp hc a ha
  have hoff (a b : ℕ) (ha : a ∈ M.vertices) (hb : b ∈ M.vertices) (hne : a ≠ b) :
      γ a b = 0 := by
    have hnn : 0 ≤ γ a b * M.dist a b := mul_nonneg (hγ.1 a b) (M.dist_nonneg a b)
    have hzero : γ a b * M.dist a b = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hnn)).mp (hrow_zero a ha) b hb
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (dist_pos_of_ne M hne))
  have hdiag : γ x x = μ.val x := by
    calc γ x x = M.vertices.sum (γ x) := by
        rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun hne => absurd hx hne)]
        simp
      _ = μ.val x := hγ.2.2.2.1 x hx
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    calc M.vertices.sum (fun z => γ z x) = γ x x := by
      rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]
      simp
  have hnu : ν.val x = γ x x := by rw [← hcol, hγ.2.2.2.2 x hx]
  linarith [hdiag, hnu]

theorem couplingTransportCost_eq_zero_implies_vertex_eq (M : FiniteMetricSpace)
    (μ ν : ProbDist M.vertices) (γ : ℕ → ℕ → ℝ) (hγ : IsCoupling M.vertices μ ν γ)
    (hc : couplingTransportCost M γ = 0) :
    ∀ x ∈ M.vertices, μ.val x = ν.val x :=
  couplingTransportCost_eq_zero_of_eq M μ ν γ hγ hc

theorem couplingTransportCost_pos_of_vertex_ne (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) :
    0 < couplingTransportCost M (productCoupling M.vertices μ ν) := by
  obtain ⟨x, hx, hdiff⟩ := hne
  by_cases hgt : μ.val x > ν.val x
  · obtain ⟨y, hy, hlt⟩ := exists_mass_imbalance_neg M μ ν x hgt hx
    have hμpos : 0 < μ.val x := lt_of_le_of_ne (μ.2.1 x hx) (Ne.symm (sub_ne_zero.mpr hgt))
    have hνpos : 0 < ν.val y := lt_of_le_of_ne (ν.2.1 y hy) (Ne.symm (sub_ne_zero.mpr hlt))
    exact productCoupling_cost_pos M μ ν hx hy (by intro heq; subst heq; linarith) hμpos hνpos
  · push_neg at hgt
    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff
    obtain ⟨y, hy, hgt'⟩ := exists_mass_imbalance_pos M μ ν x hlt hx
    have hμpos : 0 < μ.val y := lt_of_le_of_ne (μ.2.1 y hy) (Ne.symm (sub_ne_zero.mpr hgt'))
    have hνpos : 0 < ν.val x := lt_of_le_of_ne (ν.2.1 x hx) (Ne.symm hdiff)
    exact productCoupling_cost_pos M μ ν hy hx (by intro heq; subst heq; linarith) hμpos hνpos

private theorem probExpectation_dist_sub (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (xAnchor : ℕ) :
    probExpectation M μ (M.dist · xAnchor) - probExpectation M ν (M.dist · xAnchor) =
      M.vertices.sum fun t => (μ.val t - ν.val t) * M.dist t xAnchor := by
  unfold probExpectation; rw [← Finset.sum_sub_distrib]; congr 1; funext t; ring

private theorem exists_delta_neg_of_sum_zero (S : Finset ℕ) (δ : ℕ → ℝ)
    (hsum : S.sum δ = 0) {tPlus : ℕ} (htPlus : tPlus ∈ S.filter (fun t => 0 < δ t)) (htPluspos : 0 < δ tPlus) :
    ∃ tMinus ∈ S, δ tMinus < 0 := by
  by_contra hall; push_neg at hall
  have hnonneg : ∀ t ∈ S, 0 ≤ δ t := hall
  have hsumpos : 0 < S.sum δ :=
    lt_of_lt_of_le htPluspos (Finset.single_le_sum hnonneg (Finset.mem_filter.mp htPlus).1)
  linarith [hsum, hsumpos]

private theorem exists_delta_pos_of_sum_zero (S : Finset ℕ) (δ : ℕ → ℝ)
    (hsum : S.sum δ = 0) {tMinus : ℕ} (htMinus : tMinus ∈ S.filter (fun t => δ t < 0))
    (htMinusNeg : δ tMinus < 0) :
    ∃ tPlus ∈ S, 0 < δ tPlus := by
  by_contra hall; push_neg at hall
  have hnonpos : ∀ t ∈ S, δ t ≤ 0 := hall
  have hall0 : ∀ t ∈ S, δ t = 0 := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum
  linarith [htMinusNeg, hall0 tMinus (Finset.mem_filter.mp htMinus).1]

set_option maxHeartbeats 800000 in
private theorem delta_three_anchor_contradiction
    (d01 d0u d1u : ℝ) (h01 : 0 < d01) (h0u : 0 < d0u) (h1u : 0 < d1u)
    (δ0 δ1 δu : ℝ) (h0 : 0 < δ0) (h1 : δ1 < 0) (hu : δu ≠ 0)
    (hsum3 : δ0 + δ1 + δu = 0)
    (e0 : δ1 * d01 + δu * d0u = 0)
    (e1 : δ0 * d01 + δu * d1u = 0)
    (e2 : δ0 * d0u + δ1 * d1u = 0) : False := by
  nlinarith [sq_nonneg (δ0 * d01 - δu * d1u), sq_nonneg (δ1 * d01 - δu * d0u),
    sq_nonneg (δ0 * d0u - δ1 * d1u), h0, h1, hu, hsum3, e0, e1, e2, h01, h0u, h1u]

/-- If all distance expectations agree, vertex masses agree. -/
private theorem probExpectation_dist_eq_all_imp_vertex_eq (M : FiniteMetricSpace)
    (μ ν : ProbDist M.vertices)
    (h : ∀ a ∈ M.vertices, probExpectation M μ (M.dist · a) = probExpectation M ν (M.dist · a)) :
    ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  intro x hx
  set δ : ℕ → ℝ := fun t => μ.val t - ν.val t
  have hsum : M.vertices.sum δ = 0 := by
    simpa [δ] using probDist_vertex_mass_balance M.vertices μ ν
  have hdist (a : ℕ) (ha : a ∈ M.vertices) :
      M.vertices.sum (fun t => δ t * M.dist t a) = 0 := by
    rw [← probExpectation_dist_sub M μ ν a, h a ha, sub_self]
  by_contra hne
  have ht0ne : μ.val x ≠ ν.val x := hne
  set t0 := x
  have ht0 : t0 ∈ M.vertices := hx
  by_cases ht0pos : 0 < δ t0
  · have htPlus : t0 ∈ M.vertices.filter (fun t => 0 < δ t) :=
      Finset.mem_filter.mpr ⟨ht0, ht0pos⟩
    obtain ⟨tMinus, htMinusMem, htMinusNeg⟩ :=
      exists_delta_neg_of_sum_zero M.vertices δ hsum htPlus ht0pos
    have hnePM : t0 ≠ tMinus := by intro heq; subst heq; linarith [ht0pos, htMinusNeg]
    have hdistPM : 0 < M.dist t0 tMinus := dist_pos_of_ne M hnePM
    have htMinusInErase : tMinus ∈ M.vertices.erase t0 :=
      Finset.mem_erase.mpr ⟨hnePM.symm, htMinusMem⟩
    have hdist0 := hdist t0 ht0
    have hdistM := hdist tMinus htMinusMem
    have hdistM0 : 0 < M.dist tMinus t0 := by rwa [M.dist_comm]
    have hheadPlus : δ tMinus * M.dist tMinus t0 < 0 :=
      mul_neg_of_neg_of_pos htMinusNeg hdistM0
    by_cases hthird : ∃ u ∈ M.vertices, u ≠ t0 ∧ u ≠ tMinus ∧ δ u ≠ 0
    · have hthirdEx := hthird
      obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthirdEx
      have hut0ne : u ≠ t0 := hut0
      have hutMne : u ≠ tMinus := hutM
      have hδ0 (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) (hu' : t ≠ u) :
          δ t = 0 := by
        by_cases htu : t = u
        · subst htu; exfalso; exact hudne rfl
        · by_contra hδ
          exact hthirdEx ⟨t, ht, ht0', htM', hδ⟩
      have hsum3 : δ t0 + δ tMinus + δ u = 0 := by
        have hrest : (((M.vertices.erase t0).erase tMinus).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδ0 t (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht) (Finset.ne_of_mem_erase ht)
        have hdecomp : M.vertices.sum δ =
            δ t0 + δ tMinus + δ u + (((M.vertices.erase t0).erase tMinus).erase u).sum δ := by
          rw [← Finset.sum_eq_add_sum_diff_singleton_of_mem ht0,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem htMinusInErase,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hut0ne, hu⟩)]
        linarith [hsum, hrest, hdecomp]
      have hdist0' := hdist0
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0] at hdist0'
      simp only [M.dist_self t0, mul_zero, add_zero] at hdist0'
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htMinusInErase] at hdist0'
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hut0ne, hu⟩)] at hdist0'
      simp only [Finset.sdiff_singleton_eq_erase] at hdist0'
      have hdistM' := hdistM
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htMinusMem] at hdistM'
      simp only [M.dist_self tMinus, mul_zero, add_zero] at hdistM'
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hutMne.symm, ht0⟩)] at hdistM'
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hutMne, hu⟩)] at hdistM'
      simp only [Finset.sdiff_singleton_eq_erase] at hdistM'
      have hdistU' := hdist u hu
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hu] at hdistU'
      simp only [M.dist_self u, mul_zero, add_zero] at hdistU'
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hut0ne.symm, ht0⟩)] at hdistU'
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hutMne.symm, htMinusMem⟩)] at hdistU'
      simp only [Finset.sdiff_singleton_eq_erase] at hdistU'
      exact delta_three_anchor_contradiction
        (M.dist t0 tMinus) (M.dist t0 u) (M.dist tMinus u)
        hdistPM (dist_pos_of_ne M hut0ne) (dist_pos_of_ne M hutMne)
        (δ t0) (δ tMinus) (δ u) ht0pos htMinusNeg hudne hsum3 hdist0' hdistM' hdistU'
    · push_neg at hthird
      have hδ0 (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) : δ t = 0 :=
        hthird t ht ht0' htM'
      have hdistPlus := hdist0
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0] at hdistPlus
      simp only [M.dist_self t0, mul_zero, add_zero] at hdistPlus
      simp only [Finset.sdiff_singleton_eq_erase] at hdistPlus
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htMinusInErase] at hdistPlus
      have hrest0 :
          ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) = 0 :=
        Finset.sum_eq_zero fun t ht => by
          have htErase0 : t ∈ M.vertices.erase t0 := Finset.mem_of_mem_erase ht
          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase htErase0
          simp [hδ0 t htVert (Finset.ne_of_mem_erase htErase0) (Finset.ne_of_mem_erase ht), zero_mul]
      have hsplit :
          (M.vertices.erase t0).sum (fun t => δ t * M.dist t t0) =
            δ tMinus * M.dist tMinus t0 +
              ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) := by
        rw [← Finset.add_sum_erase (M.vertices.erase t0) (fun t => δ t * M.dist t t0) tMinus htMinusInErase]
      have hplus0 : δ tMinus * M.dist tMinus t0 = 0 := by
        linarith [hdistPlus, hsplit, hrest0]
      linarith [hheadPlus, hplus0]
  · push_neg at ht0pos
    have ht0δne : δ t0 ≠ 0 := sub_ne_zero.mpr ht0ne
    have ht0neg : δ t0 < 0 := lt_of_le_of_ne ht0pos ht0δne
    have htMinus : t0 ∈ M.vertices.filter (fun t => δ t < 0) :=
      Finset.mem_filter.mpr ⟨ht0, ht0neg⟩
    obtain ⟨tPlus, htPlusMem, htPlusPos⟩ :=
      exists_delta_pos_of_sum_zero M.vertices δ hsum htMinus ht0neg
    have hnePM : tPlus ≠ t0 := by intro heq; subst heq; linarith [htPlusPos, ht0neg]
    have hdistPM : 0 < M.dist tPlus t0 := dist_pos_of_ne M hnePM
    have ht0InErase : t0 ∈ M.vertices.erase tPlus :=
      Finset.mem_erase.mpr ⟨hnePM.symm, ht0⟩
    have hdistP := hdist tPlus htPlusMem
    have hdist0 := hdist t0 ht0
    have hdistP0 : 0 < M.dist t0 tPlus := by rwa [M.dist_comm]
    have hheadPlus : δ t0 * M.dist t0 tPlus < 0 :=
      mul_neg_of_neg_of_pos ht0neg hdistP0
    by_cases hthird : ∃ u ∈ M.vertices, u ≠ tPlus ∧ u ≠ t0 ∧ δ u ≠ 0
    · have hthirdEx := hthird
      obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthirdEx
      have hutPne : u ≠ tPlus := hutP
      have hut0ne : u ≠ t0 := hut0
      have hδ0 (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) (hu' : t ≠ u) :
          δ t = 0 := by
        by_cases htu : t = u
        · subst htu; exfalso; exact hudne rfl
        · by_contra hδ
          exact hthirdEx ⟨t, ht, htP', ht0', hδ⟩
      have hsum3 : δ tPlus + δ t0 + δ u = 0 := by
        have hrest : (((M.vertices.erase tPlus).erase t0).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδ0 t (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht) (Finset.ne_of_mem_erase ht)
        have hdecomp : M.vertices.sum δ =
            δ tPlus + δ t0 + δ u + (((M.vertices.erase tPlus).erase t0).erase u).sum δ := by
          rw [← Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hut0ne, hu⟩)]
        linarith [hsum, hrest, hdecomp]
      have hdistP' := hdistP
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem] at hdistP'
      simp only [M.dist_self tPlus, mul_zero, add_zero] at hdistP'
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase] at hdistP'
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hut0ne, hu⟩)] at hdistP'
      simp only [Finset.sdiff_singleton_eq_erase] at hdistP'
      have hdist0' := hdist0
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0] at hdist0'
      simp only [M.dist_self t0, mul_zero, add_zero] at hdist0'
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hutPne, ht0⟩)] at hdist0'
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hutPne.symm, hu⟩)] at hdist0'
      simp only [Finset.sdiff_singleton_eq_erase] at hdist0'
      have hdistU' := hdist u hu
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem hu] at hdistU'
      simp only [M.dist_self u, mul_zero, add_zero] at hdistU'
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hutPne.symm, htPlusMem⟩)] at hdistU'
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hut0ne.symm, ht0⟩)] at hdistU'
      simp only [Finset.sdiff_singleton_eq_erase] at hdistU'
      exact delta_three_anchor_contradiction
        (M.dist tPlus t0) (M.dist tPlus u) (M.dist t0 u)
        hdistPM (dist_pos_of_ne M hutPne) (dist_pos_of_ne M hut0ne)
        (δ tPlus) (δ t0) (δ u) htPlusPos ht0neg hudne hsum3 hdistP' hdist0' hdistU'
    · push_neg at hthird
      have hδ0 (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) : δ t = 0 :=
        hthird t ht htP' ht0'
      have hdistPlus := hdistP
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem] at hdistPlus
      simp only [M.dist_self tPlus, mul_zero, add_zero] at hdistPlus
      simp only [Finset.sdiff_singleton_eq_erase] at hdistPlus
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase] at hdistPlus
      have hrest0 :
          ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) = 0 :=
        Finset.sum_eq_zero fun t ht => by
          have htErasePlus : t ∈ M.vertices.erase tPlus := Finset.mem_of_mem_erase ht
          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase htErasePlus
          simp [hδ0 t htVert (Finset.ne_of_mem_erase htErasePlus) (Finset.ne_of_mem_erase ht), zero_mul]
      have hsplit :
          (M.vertices.erase tPlus).sum (fun t => δ t * M.dist t tPlus) =
            δ t0 * M.dist t0 tPlus +
              ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) := by
        rw [← Finset.add_sum_erase (M.vertices.erase tPlus) (fun t => δ t * M.dist t tPlus) t0 ht0InErase]
      have hplus0 : δ t0 * M.dist t0 tPlus = 0 := by
        linarith [hdistPlus, hsplit, hrest0]
      linarith [hheadPlus, hplus0]

private theorem exists_probExpectation_dist_gap (M : FiniteMetricSpace)
    (μ ν : ProbDist M.vertices) (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) :
    ((∃ a ∈ M.vertices, 0 < probExpectation M μ (M.dist · a) - probExpectation M ν (M.dist · a)) ∨
      ∃ a ∈ M.vertices, 0 < probExpectation M ν (M.dist · a) - probExpectation M μ (M.dist · a)) := by
  by_contra hnot; push_neg at hnot
  rcases hnot with ⟨hμ, hν⟩
  have heq : ∀ a ∈ M.vertices, probExpectation M μ (M.dist · a) = probExpectation M ν (M.dist · a) := by
    intro a ha; have hleμ := hμ a ha; have hleν := sub_nonpos.mp (hν a ha); linarith
  rcases hne with ⟨x, hx, hdiff⟩
  exact hdiff (probExpectation_dist_eq_all_imp_vertex_eq M μ ν heq x hx)

private theorem W1_pos_of_vertex_ne (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) : 0 < W1 M μ ν := by
  rcases exists_probExpectation_dist_gap M μ ν hne with h | h
  · rcases h with ⟨a, _, hpos⟩
    have hW1ge := W1_ge_of_lipschitz M μ ν (M.dist · a) (dist_lipschitz M a)
      (couplingCostSet_nonempty M μ ν)
    exact hpos.trans_le (le_trans (le_abs_self _) hW1ge)
  · rcases h with ⟨a, _, hpos⟩
    have hW1ge := W1_ge_of_lipschitz M μ ν (M.dist · a) (dist_lipschitz M a)
      (couplingCostSet_nonempty M μ ν)
    have hge : probExpectation M ν (M.dist · a) - probExpectation M μ (M.dist · a) ≤ W1 M μ ν := by
      calc probExpectation M ν (M.dist · a) - probExpectation M μ (M.dist · a) ≤
          |probExpectation M μ (M.dist · a) - probExpectation M ν (M.dist · a)| := by
            rw [abs_sub_comm]; exact le_abs_self _
        _ ≤ W1 M μ ν := hW1ge
    exact hpos.trans_le hge

/-- Glued coupling of `γ₁ : μ ↝ ν` and `γ₂ : ν ↝ ρ` via disintegration at `ν`. -/
noncomputable def gluedCoupling (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ) (x z : ℕ) : ℝ :=
  S.sum fun y =>
    if ν.val y = 0 then 0 else γ₁ x y * γ₂ y z / ν.val y

private theorem gluedCoupling_nonneg (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : ∀ x y, 0 ≤ γ₁ x y) (hγ₂ : ∀ x y, 0 ≤ γ₂ x y) :
    ∀ x z, 0 ≤ gluedCoupling S ν γ₁ γ₂ x z := by
  intro x z
  unfold gluedCoupling
  apply Finset.sum_nonneg
  intro y hy
  split_ifs with h
  · simp
  · exact div_nonneg (mul_nonneg (hγ₁ x y) (hγ₂ y z)) (le_of_lt (lt_of_le_of_ne (ν.2.1 y hy) (Ne.symm h)))

private theorem gluedCoupling_left_outside (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : ∀ x y, x ∉ S → γ₁ x y = 0) (x : ℕ) (hx : x ∉ S) (z : ℕ) :
    gluedCoupling S ν γ₁ γ₂ x z = 0 := by
  unfold gluedCoupling
  apply Finset.sum_eq_zero
  intro y _
  split_ifs <;> simp [hγ₁ x _ hx]

private theorem gluedCoupling_right_outside (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₂ : ∀ w x, w ∉ S → γ₂ x w = 0) (z : ℕ) (hz : z ∉ S) (x : ℕ) :
    gluedCoupling S ν γ₁ γ₂ x z = 0 := by
  unfold gluedCoupling
  apply Finset.sum_eq_zero
  intro y _
  split_ifs <;> simp [hγ₂ y hz]

private theorem coupling_col_zero_of_mass_zero {S : Finset ℕ} {μ ν : ProbDist S} {γ : ℕ → ℕ → ℝ}
    (hγ : IsCoupling S μ ν γ) (w : ℕ) (hw : w ∈ S) (hν : ν.val w = 0) :
    ∀ x, γ x w = 0 := by
  intro x
  have hcol := hγ.2.2.2.2 w hw; rw [hν] at hcol
  by_cases hx : x ∈ S
  · exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hγ.1 z w)).mp hcol x hx
  · exact hγ.2.1 x hx w

private theorem gluedCoupling_row_sum (S : Finset ℕ) (μ ν ρ : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : IsCoupling S μ ν γ₁) (hγ₂ : IsCoupling S ν ρ γ₂) (x : ℕ) (hx : x ∈ S) :
    S.sum (gluedCoupling S ν γ₁ γ₂ x) = μ.val x := by
  classical
  unfold gluedCoupling
  rw [Finset.sum_comm]
  trans S.sum fun w => γ₁ x w
  · apply Finset.sum_congr rfl
    intro w hw
    by_cases hν : ν.val w = 0
    · simp [hν, coupling_col_zero_of_mass_zero hγ₁ w hw hν x]
    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        rw [← Finset.mul_sum, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simpa [hν] using hinner
  · exact hγ₁.2.2.2.1 x hx

private theorem gluedCoupling_col_sum (S : Finset ℕ) (μ ν ρ : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : IsCoupling S μ ν γ₁) (hγ₂ : IsCoupling S ν ρ γ₂) (z : ℕ) (hz : z ∈ S) :
    S.sum (fun x => gluedCoupling S ν γ₁ γ₂ x z) = ρ.val z := by
  classical
  unfold gluedCoupling
  trans S.sum fun w => γ₂ w z
  · apply Finset.sum_congr rfl
    intro w hw
    by_cases hν : ν.val w = 0
    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'
      simp [hν, Finset.sum_eq_zero fun x' _ => by simp [hcol x']]
    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by
        rw [← Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]
      simpa [hν] using hinner
  · exact hγ₂.2.2.2.2 z hz

theorem gluedCoupling_is_coupling (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling M.vertices μ ν γ₁)
    (hγ₂ : IsCoupling M.vertices ν ρ γ₂) :
    IsCoupling M.vertices μ ρ (gluedCoupling M.vertices ν γ₁ γ₂) := by
  refine ⟨gluedCoupling_nonneg M.vertices ν γ₁ γ₂ hγ₁.1 hγ₂.1, ?_, ?_, ?_, ?_⟩
  · intro x hx y; exact gluedCoupling_left_outside M.vertices ν γ₁ γ₂ (fun a ha b => hγ₁.2.1 ha b) x hx y
  · intro y hy x; exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂ (fun w z hz => hγ₂.2.2.1 hz w) y hy x
  · intro x hx; exact gluedCoupling_row_sum M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂ x hx
  · intro y hy; exact gluedCoupling_col_sum M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂ y hy

theorem gluedCoupling_cost_le (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling M.vertices μ ν γ₁)
    (hγ₂ : IsCoupling M.vertices ν ρ γ₂) :
    couplingTransportCost M (gluedCoupling M.vertices ν γ₁ γ₂) ≤
      couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
  classical
  set γ₃ := gluedCoupling M.vertices ν γ₁ γ₂
  unfold couplingTransportCost at *
  have hterm :
      ∀ x z,
        M.dist x z * γ₃ x z ≤
          M.vertices.sum fun w =>
            if ν.val w = (0 : ℝ) then (0 : ℝ) else γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) := by
    intro x z; unfold γ₃ gluedCoupling; rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    split_ifs with hν
    · simp
    · have hpos : 0 < ν.val w := lt_of_le_of_ne (ν.2.1 w (by simpa using hw)) (Ne.symm hν)
      have hdiv : 0 ≤ γ₁ x w * γ₂ w z / ν.val w :=
        div_nonneg (mul_nonneg (hγ₁.1 x w) (hγ₂.1 w z)) hpos.le
      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv
  have hsplit :
      M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = 0 then 0 else γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) =
        M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w =>
            if ν.val w = 0 then 0 else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := by
    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    refine Finset.sum_congr rfl fun w hw => ?_
    by_cases hν : ν.val w = 0
    · have hγxw := coupling_col_zero_of_mass_zero hγ₁ w hw hν x
      simp [hν, hγxw, zero_mul, mul_zero, add_zero]
    · have hν' : ν.val w ≠ 0 := hν
      have hcol : M.vertices.sum (fun z => γ₂ w z) = ν.val w := hγ₂.2.2.2.1 w hw
      calc
        M.vertices.sum fun z => γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) =
            γ₁ x w / ν.val w *
              M.vertices.sum fun z => γ₂ w z * (M.dist x w + M.dist w z) := by
          rw [Finset.mul_sum, mul_div_assoc, mul_assoc]
        _ = γ₁ x w / ν.val w * (M.vertices.sum fun z => γ₂ w z * M.dist x w +
              M.vertices.sum fun z => γ₂ w z * M.dist w z) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, mul_comm (M.dist x w)]
        _ = γ₁ x w * M.dist x w +
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := by
          rw [hcol, mul_div_cancel₀ _ hν']; ring
  have hbound :
      M.vertices.sum fun w =>
          if ν.val w = 0 then 0 else
            M.vertices.sum fun x => γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z ≤
        M.vertices.sum fun w => M.vertices.sum fun z => γ₂ w z * M.dist w z := by
    refine Finset.sum_le_sum fun w hw => ?_
    split_ifs with hν
    · simp
    · rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_comm, mul_div_cancel₀ _ (Ne.symm hν)]
  calc
    M.vertices.sum fun x => M.vertices.sum fun z => M.dist x z * γ₃ x z ≤
        M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = (0 : ℝ) then (0 : ℝ) else γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => hterm x z
    _ = M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w =>
            if ν.val w = 0 then 0 else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := hsplit
    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      unfold couplingTransportCost
      rw [← Finset.sum_add_distrib]
      apply add_le_add le_rfl
      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
      exact hbound

/-- W₁ vanishes iff the distributions are identical on vertices. -/
theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  constructor
  · intro hW1
    by_contra hne
    push_neg at hne
    have hpos := W1_pos_of_vertex_ne M μ ν hne
    linarith [W1_nonneg M μ ν, hW1]
  · intro h
    have hμν : μ = ν := probDist_eq_of_vertex_weights_eq h
    subst hμν
    apply le_antisymm
    · have := W1_le_couplingCost M μ μ (diagonalCoupling M.vertices μ)
        (diagonalCoupling_is_coupling M.vertices μ)
      rw [diagonalCoupling_cost_zero M μ] at this
      exact this
    · exact W1_nonneg M μ μ

/-- Triangle inequality for W₁. -/
theorem W1_triangle (M : FiniteMetricSpace)
    (μ ν ρ : ProbDist M.vertices) :
    W1 M μ ρ ≤ W1 M μ ν + W1 M ν ρ := by
  rw [le_iff_forall_pos_lt_add]
  intro ε hε
  obtain ⟨c₁, hc₁mem, hc₁lt⟩ :=
    Real.lt_sInf_add_pos (couplingCostSet_nonempty M μ ν) (half_pos hε)
  obtain ⟨c₂, hc₂mem, hc₂lt⟩ :=
    Real.lt_sInf_add_pos (couplingCostSet_nonempty M ν ρ) (half_pos hε)
  obtain ⟨γ₁, hγ₁, hc₁eq⟩ := hc₁mem
  obtain ⟨γ₂, hγ₂, hc₂eq⟩ := hc₂mem
  have hglued := gluedCoupling_is_coupling M μ ν ρ γ₁ γ₂ hγ₁ hγ₂
  have hcost := gluedCoupling_cost_le M μ ν ρ γ₁ γ₂ hγ₁ hγ₂
  have hle := W1_le_couplingCost M μ ρ (gluedCoupling M.vertices ν γ₁ γ₂) hglued
  have hW1μν : W1 M μ ν ≤ c₁ := by
    unfold W1; apply csInf_le
    · refine ⟨0, ?_⟩; intro c hc; obtain ⟨γ', hγ', hc'⟩ := hc; rw [hc']; exact couplingTransportCost_nonneg M γ' hγ'.1
    · exact ⟨γ₁, hγ₁, hc₁eq⟩
  have hW1νρ : W1 M ν ρ ≤ c₂ := by
    unfold W1; apply csInf_le
    · refine ⟨0, ?_⟩; intro c hc; obtain ⟨γ', hγ', hc'⟩ := hc; rw [hc']; exact couplingTransportCost_nonneg M γ' hγ'.1
    · exact ⟨γ₂, hγ₂, hc₂eq⟩
  unfold W1 at hle hW1μν hW1νρ ⊢
  linarith [hle, hcost, hc₁lt, hc₂lt, hW1μν, hW1νρ]

/-!
## Ollivier-Ricci curvature

For an edge (x, y) in the causal graph, let μ_x and μ_y be the
1-step random walk distributions from x and y respectively.
The Ollivier-Ricci curvature is:
  κ_OR(x, y) = 1 − W₁(μ_x, μ_y) / d(x, y)

This measures how much balls around x and y "attract" each other
relative to the distance d(x, y).
-/

/--
Ollivier-Ricci curvature of an edge (x, y) with respect to
1-step random walk measures μ_x and μ_y centered at x and y.
-/
noncomputable def OllivierRicci (M : FiniteMetricSpace) (x y : ℕ)
    (μ_x μ_y : ProbDist M.vertices) : ℝ :=
  1 - W1 M μ_x μ_y / M.dist x y

/-!
## Gorard vacuum condition: discrete Ricci flatness

For the Rule 110 vacuum ether background (winding w = 0), the
Ollivier-Ricci curvature vanishes on every edge of the causal graph.
This is the discrete analogue of Ricci flatness (Einstein vacuum equation
R_μν = 0) and is consistent with Minkowski spacetime as the continuum limit.

Status: AXIOM (CatD-STRONG). Evidence:
- GF(7) uniqueness of w=0 vacuum (GF7VacuumFixedPoint.lean)
- Gorard (2020): numerical Ricci flatness of Rule 110 causal graphs
- Requires: formal derivation of the 1-step random walk on Rule 110 graph
-/

/--
For the vacuum Rule 110 causal graph, the Ollivier-Ricci curvature
κ_OR(x, y) = 0 for all edges (x, y).
This is the discrete Ricci-flat condition: the ether background is
geometrically flat at the level of Ollivier curvature.

**Axiom (overly general)** — quantifies over all `ProbDist` values, not only
the vacuum 1-step random walk. The scoped CatAL replacement is
`GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped`, proved for every
adjacent edge `(n, n+1)` via translation invariance of the uniform walk.

Pending: remove this axiom once all downstream references migrate to the scoped theorem.
-/
@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]
axiom gorard_vacuum_oric_zero
    (M : FiniteMetricSpace) (x y : ℕ)
    (hx : x ∈ M.vertices) (hy : y ∈ M.vertices)
    (hxy : M.dist x y > 0)
    (μ_vac_x μ_vac_y : ProbDist M.vertices) :
    OllivierRicci M x y μ_vac_x μ_vac_y = 0

/--
If W₁ equals the graph distance on a unit causal edge, Ollivier-Ricci
curvature vanishes. This is the abstract form of the CatAL CDF argument.
-/
theorem gorard_vacuum_oric_zero_of_w1
    (M : FiniteMetricSpace) (x y : ℕ)
    (μ_x μ_y : ProbDist M.vertices)
    (hd : M.dist x y = 1)
    (hw : W1 M μ_x μ_y = 1) :
    OllivierRicci M x y μ_x μ_y = 0 := by
  unfold OllivierRicci
  rw [hw, hd]
  norm_num

/-!
## OQ-QG-1 Step 2: Gromov-Wasserstein convergence (long-range target)

The target theorem: the sequence of Rule 110 causal graph metric measure spaces
  (M_n, a_n · d_graph, μ_n)
converges to (ℝ^{1,3}, η, vol) in the Gromov-Wasserstein sense as a_n → 0,
where η is the Minkowski metric and vol is the Lorentzian volume form.

This is a major open problem (OQ-QG-1). Blocking dependencies:
1. Mathlib optimal transport library (currently upstream work-in-progress)
2. Lorentzian geometry in Mathlib (not yet available)
3. Formal connection between Ollivier-Ricci flat ⟹ GW limit is flat

Current formalization: named axiom capturing the expected conclusion.
-/

/--
The Gromov-Wasserstein convergence of the Rule 110 causal graph
metric measure spaces to 4D Minkowski spacetime.

**Axiom** — long-range target for OQ-QG-1. Blocked on:
- Mathlib optimal transport / GW distance
- Lorentzian geometry library
- Formal Rule 110 graph construction at scale n

The `True` placeholder in the conclusion stands for:
  GW-distance((M_n, a_n · d_n, μ_n), (ℝ^{1,3}, η, vol)) < ε
-/
axiom rule110_gromov_wasserstein_limit :
    ∀ (ε : ℝ), ε > 0 →
    ∃ (n₀ : ℕ), ∀ (n : ℕ), n ≥ n₀ →
    True  -- GW-distance(Rule110_n, Minkowski) < ε

end GTE.ContinuumLimit.Wasserstein
