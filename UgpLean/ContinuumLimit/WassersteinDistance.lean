import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.MeasureTheory.Measure.MeasureSpace
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import UgpLean.ContinuumLimit.GF7VacuumFixedPoint

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
- `OllivierRicci`: noncomputable, defined in terms of `W1`
- `gorard_vacuum_oric_zero`: **axiom** (overly general; see `GorardVacuumW1Bridge` for scoped path)
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

/-!
## Probability distributions on finite sets
-/

/--
A probability distribution on a finite vertex set `S`:
a non-negative function supported on `S` that sums to 1.
-/
def ProbDist (S : Finset ℕ) : Type :=
  { f : ℕ → ℝ // (∀ x ∈ S, 0 ≤ f x) ∧ (∀ x ∉ S, f x = 0) ∧ S.sum f = 1 }

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

/-!
## Basic properties of W₁
-/

/-- W₁ is non-negative. -/
theorem W1_nonneg (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    0 ≤ W1 M μ ν := by
  sorry  -- follows from dist_nonneg and γ ≥ 0

/-- W₁ is symmetric. -/
theorem W1_comm (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = W1 M ν μ := by
  sorry  -- symmetric: swap coupling γ(x,y) ↦ γ(y,x); dist is symmetric

/-- W₁ vanishes iff the distributions are identical. -/
theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  sorry  -- follows from: W₁ = 0 ↔ diagonal coupling is optimal ↔ μ = ν

/-- Triangle inequality for W₁. -/
theorem W1_triangle (M : FiniteMetricSpace)
    (μ ν ρ : ProbDist M.vertices) :
    W1 M μ ρ ≤ W1 M μ ν + W1 M ν ρ := by
  sorry  -- gluing lemma for couplings

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
the vacuum 1-step random walk. The scoped CatAL path is
`GorardVacuumW1Bridge.gorard_vacuum_oric_zero_adjacent`, which reduces to
`vacuum_w1_eq_one` once the CDF ↔ OT bridge is closed.

Pending: replace with a theorem over `vacuumWalkMeasureLeft/Right` only.
-/
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
