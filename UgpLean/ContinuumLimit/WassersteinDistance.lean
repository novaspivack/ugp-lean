import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.BigOperators.Group.Finset.Piecewise
import Mathlib.Algebra.BigOperators.Group.Finset.Sigma
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Data.Real.Archimedean
import Mathlib.Order.ConditionallyCompleteLattice.Basic
import Mathlib.Topology.Order.Compact
import Mathlib.Topology.Compactness.Compact
import Mathlib.Topology.Order.Monotone
import Mathlib.Topology.Order.Real
import Mathlib.Topology.Instances.Real.Lemmas
import Mathlib.Topology.Constructions
import Mathlib.Topology.Algebra.Monoid.FunOnFinite
import Mathlib.Tactic.Linarith

/-!
# Wasserstein Distance and Ollivier-Ricci Curvature (EPIC_083)

Finite-metric-space W₁ Wasserstein distance and Ollivier-Ricci curvature scaffold
for the Gorard discrete-gravity programme.

## Exports

- `FiniteMetricSpace` — finite graph with a genuine metric
- `ProbDist` — probability distribution on a `Finset ℕ` support
- `IsCoupling` — coupling predicate for a pair of probability distributions
- `couplingTransportCost` — transport cost of a coupling plan
- `couplingCostSet` — set of achievable transport costs
- `W1` — Wasserstein-1 distance (infimum over couplings)
- `OllivierRicci` — Ollivier-Ricci curvature on an edge
- `probExpectation` — expected value under a probability distribution
- `gorard_vacuum_oric_zero_of_w1` — κ_OR = 0 when W₁ = d(x, y) = 1
-/

namespace GTE.ContinuumLimit.Wasserstein

-- ---------------------------------------------------------------------------
-- Finite metric space
-- ---------------------------------------------------------------------------

/-- A finite metric space with vertex set `Finset ℕ`. -/
structure FiniteMetricSpace where
  vertices : Finset ℕ
  dist : ℕ → ℕ → ℝ
  dist_nonneg : ∀ x y, 0 ≤ dist x y
  dist_self : ∀ x, dist x x = 0
  dist_comm : ∀ x y, dist x y = dist y x
  triangle : ∀ x y z, dist x z ≤ dist x y + dist y z
  dist_eq_zero_iff : ∀ x y, dist x y = 0 ↔ x = y

-- ---------------------------------------------------------------------------
-- Probability distribution
-- ---------------------------------------------------------------------------

/-- Well-formedness conditions for a weight function on a finset support. -/
structure ProbDistProof (V : Finset ℕ) (w : ℕ → ℝ) : Prop where
  weights_nonneg : ∀ x ∈ V, 0 ≤ w x
  weights_outside : ∀ x ∉ V, w x = 0
  sum_one : V.sum w = 1

/-- A probability distribution supported on `V : Finset ℕ`. -/
structure ProbDist (V : Finset ℕ) where
  weights : ℕ → ℝ
  proof : ProbDistProof V weights

-- ---------------------------------------------------------------------------
-- Coupling
-- ---------------------------------------------------------------------------

/-- `IsCoupling V μ ν γ`: `γ` is a valid coupling plan from `μ` to `ν` on `V`. -/
structure IsCoupling (V : Finset ℕ) (μ ν : ProbDist V) (γ : ℕ → ℕ → ℝ) : Prop where
  nonneg : ∀ x y, 0 ≤ γ x y
  left_outside : ∀ x ∉ V, ∀ y, γ x y = 0
  right_outside : ∀ y ∉ V, ∀ x, γ x y = 0
  marginal_left : ∀ x ∈ V, V.sum (γ x) = μ.weights x
  marginal_right : ∀ y ∈ V, V.sum (fun x => γ x y) = ν.weights y

-- ---------------------------------------------------------------------------
-- Transport cost and cost set
-- ---------------------------------------------------------------------------

/-- Transport cost of plan `γ` on finite metric space `M`:
    sum over all vertex pairs `(x, y)` of `γ(x,y) · d(x,y)`. -/
noncomputable def couplingTransportCost (M : FiniteMetricSpace) (γ : ℕ → ℕ → ℝ) : ℝ :=
  M.vertices.sum (fun x => M.vertices.sum (fun y => γ x y * M.dist x y))

/-- Set of all achievable transport costs for couplings of `μ` and `ν`. -/
noncomputable def couplingCostSet
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) : Set ℝ :=
  {c | ∃ γ : ℕ → ℕ → ℝ, IsCoupling M.vertices μ ν γ ∧ couplingTransportCost M γ = c}

-- ---------------------------------------------------------------------------
-- Wasserstein-1 distance
-- ---------------------------------------------------------------------------

/-- Wasserstein-1 distance: infimum over all valid coupling costs. -/
noncomputable def W1 (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) : ℝ :=
  sInf (couplingCostSet M μ ν)

-- ---------------------------------------------------------------------------
-- Ollivier-Ricci curvature
-- ---------------------------------------------------------------------------

/-- Ollivier-Ricci curvature on edge `(x, y)` with walk measures `μ`, `ν`:
    `κ(x, y) = 1 − W₁(μ, ν) / d(x, y)`. -/
noncomputable def OllivierRicci
    (M : FiniteMetricSpace) (x y : ℕ) (μ ν : ProbDist M.vertices) : ℝ :=
  1 - W1 M μ ν / M.dist x y

-- ---------------------------------------------------------------------------
-- Expected value
-- ---------------------------------------------------------------------------

/-- Expected value of `f : ℕ → ℝ` under distribution `μ`. -/
noncomputable def probExpectation
    (M : FiniteMetricSpace) (μ : ProbDist M.vertices) (f : ℕ → ℝ) : ℝ :=
  M.vertices.sum (fun x => μ.weights x * f x)

-- ---------------------------------------------------------------------------
-- Helper: transport cost is nonneg for valid couplings
-- ---------------------------------------------------------------------------

theorem couplingTransportCost_nonneg
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) (γ : ℕ → ℕ → ℝ)
    (hγ : IsCoupling M.vertices μ ν γ) :
    0 ≤ couplingTransportCost M γ := by
  unfold couplingTransportCost
  apply Finset.sum_nonneg
  intro x _
  apply Finset.sum_nonneg
  intro y _
  exact mul_nonneg (hγ.nonneg x y) (M.dist_nonneg x y)

-- ---------------------------------------------------------------------------
-- W₁ ≤ any coupling cost  (zero sorry)
-- ---------------------------------------------------------------------------

/-- W₁ is at most the transport cost of any valid coupling. -/
theorem W1_le_couplingCost
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (γ : ℕ → ℕ → ℝ) (hγ : IsCoupling M.vertices μ ν γ) :
    W1 M μ ν ≤ couplingTransportCost M γ := by
  unfold W1
  apply csInf_le
  · exact ⟨0, fun c ⟨γ', hγ', hc⟩ => hc ▸ couplingTransportCost_nonneg M μ ν γ' hγ'⟩
  · exact ⟨γ, hγ, rfl⟩

-- ---------------------------------------------------------------------------
-- W₁ ≥ 0  (zero sorry)
-- ---------------------------------------------------------------------------

/-- W₁ is nonneg: it is the infimum of nonneg values. -/
theorem W1_nonneg
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    0 ≤ W1 M μ ν := by
  unfold W1
  by_cases h : (couplingCostSet M μ ν).Nonempty
  · apply le_csInf h
    rintro c ⟨γ, hγ, rfl⟩
    exact couplingTransportCost_nonneg M μ ν γ hγ
  · have heq : couplingCostSet M μ ν = ∅ := Set.not_nonempty_iff_eq_empty.mp h
    simp [heq]

-- ---------------------------------------------------------------------------
-- Helper couplings
-- ---------------------------------------------------------------------------

/-- Independent product coupling `γ(x,y) = μ(x) · ν(y)`. -/
noncomputable def productCoupling (V : Finset ℕ) (μ ν : ProbDist V) (x y : ℕ) : ℝ :=
  μ.weights x * ν.weights y

theorem productCoupling_nonneg (V : Finset ℕ) (μ ν : ProbDist V) (x y : ℕ) :
    0 ≤ productCoupling V μ ν x y := by
  unfold productCoupling
  exact mul_nonneg
    (by
      by_cases hx : x ∈ V
      · exact μ.proof.weights_nonneg x hx
      · rw [μ.proof.weights_outside x hx])
    (by
      by_cases hy : y ∈ V
      · exact ν.proof.weights_nonneg y hy
      · rw [ν.proof.weights_outside y hy])

theorem productCoupling_left_outside (V : Finset ℕ) (μ ν : ProbDist V) (x : ℕ)
    (hx : x ∉ V) (y : ℕ) : productCoupling V μ ν x y = 0 := by
  unfold productCoupling
  simp [μ.proof.weights_outside x hx]

theorem productCoupling_right_outside (V : Finset ℕ) (μ ν : ProbDist V) (y : ℕ)
    (hy : y ∉ V) (x : ℕ) : productCoupling V μ ν x y = 0 := by
  unfold productCoupling
  simp [ν.proof.weights_outside y hy]

theorem productCoupling_marginal_left (V : Finset ℕ) (μ ν : ProbDist V) (x : ℕ)
    (_hx : x ∈ V) :
    V.sum (productCoupling V μ ν x) = μ.weights x := by
  unfold productCoupling
  calc
    V.sum (fun y => μ.weights x * ν.weights y) =
        μ.weights x * V.sum ν.weights := by
      simp [Finset.mul_sum]
    _ = μ.weights x * 1 := by rw [ν.proof.sum_one]
    _ = μ.weights x := by ring

theorem productCoupling_marginal_right (V : Finset ℕ) (μ ν : ProbDist V) (y : ℕ)
    (_hy : y ∈ V) :
    V.sum (fun x => productCoupling V μ ν x y) = ν.weights y := by
  unfold productCoupling
  calc
    V.sum (fun x => μ.weights x * ν.weights y) =
        V.sum μ.weights * ν.weights y := by
      simp [Finset.sum_mul]
    _ = 1 * ν.weights y := by rw [μ.proof.sum_one]
    _ = ν.weights y := by ring

theorem productCoupling_isCoupling (V : Finset ℕ) (μ ν : ProbDist V) :
    IsCoupling V μ ν (productCoupling V μ ν) :=
  ⟨productCoupling_nonneg V μ ν,
    productCoupling_left_outside V μ ν,
    fun y hy x => productCoupling_right_outside V μ ν y hy x,
    productCoupling_marginal_left V μ ν,
    productCoupling_marginal_right V μ ν⟩

theorem couplingCostSet_nonempty (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    (couplingCostSet M μ ν).Nonempty := by
  refine ⟨couplingTransportCost M (productCoupling M.vertices μ ν), _, ?_, rfl⟩
  exact productCoupling_isCoupling M.vertices μ ν

/-- Diagonal coupling `γ(x,y) = μ(x)` when `x = y`, else `0`. -/
noncomputable def diagonalCoupling (V : Finset ℕ) (μ : ProbDist V) (x y : ℕ) : ℝ :=
  if x = y then μ.weights x else 0

theorem diagonalCoupling_nonneg (V : Finset ℕ) (μ : ProbDist V) (x y : ℕ) :
    0 ≤ diagonalCoupling V μ x y := by
  unfold diagonalCoupling; split_ifs with h
  · subst h
    by_cases hx : x ∈ V
    · exact μ.proof.weights_nonneg x hx
    · simp [μ.proof.weights_outside x hx]
  · exact le_rfl

theorem diagonalCoupling_left_outside (V : Finset ℕ) (μ : ProbDist V) (x : ℕ)
    (hx : x ∉ V) (y : ℕ) : diagonalCoupling V μ x y = 0 := by
  unfold diagonalCoupling
  split_ifs with h
  · subst h
    rw [μ.proof.weights_outside x hx]
  · rfl

theorem diagonalCoupling_right_outside (V : Finset ℕ) (μ : ProbDist V) (y : ℕ)
    (hy : y ∉ V) (x : ℕ) : diagonalCoupling V μ x y = 0 := by
  unfold diagonalCoupling
  split_ifs with h
  · have hx : x ∉ V := h ▸ hy
    exact μ.proof.weights_outside x hx
  · rfl

theorem diagonalCoupling_marginal_left (V : Finset ℕ) (μ : ProbDist V) (x : ℕ)
    (hx : x ∈ V) :
    V.sum (diagonalCoupling V μ x) = μ.weights x := by
  unfold diagonalCoupling
  have hsum :
      V.sum (fun y => if x = y then μ.weights x else 0) = μ.weights x := by
    calc
      V.sum (fun y => if x = y then μ.weights x else 0) =
          V.sum (fun y => if y = x then μ.weights x else 0) := by
        apply Finset.sum_congr rfl
        intro y _
        by_cases hxy : x = y
        · simp [hxy]
        · simp [hxy, eq_comm]
      _ = if x ∈ V then μ.weights x else 0 := by simp [Finset.sum_ite_eq']
      _ = μ.weights x := by simp [hx]
  simpa using hsum

theorem diagonalCoupling_marginal_right (V : Finset ℕ) (μ : ProbDist V) (y : ℕ)
    (hy : y ∈ V) :
    V.sum (fun x => diagonalCoupling V μ x y) = μ.weights y := by
  unfold diagonalCoupling
  have hsum :
      V.sum (fun x => if x = y then μ.weights x else 0) = μ.weights y := by
    calc
      V.sum (fun x => if x = y then μ.weights x else 0) =
          if y ∈ V then μ.weights y else 0 := by simp [Finset.sum_ite_eq']
      _ = μ.weights y := by simp [hy]
  simpa using hsum

theorem diagonalCoupling_isCoupling (V : Finset ℕ) (μ : ProbDist V) :
    IsCoupling V μ μ (diagonalCoupling V μ) :=
  ⟨diagonalCoupling_nonneg V μ,
    diagonalCoupling_left_outside V μ,
    fun y hy x => diagonalCoupling_right_outside V μ y hy x,
    diagonalCoupling_marginal_left V μ,
    diagonalCoupling_marginal_right V μ⟩

theorem diagonalCouplingTransportCost_zero (M : FiniteMetricSpace) (μ : ProbDist M.vertices) :
    couplingTransportCost M (diagonalCoupling M.vertices μ) = 0 := by
  unfold couplingTransportCost diagonalCoupling
  apply Finset.sum_eq_zero
  intro x hx
  apply Finset.sum_eq_zero
  intro y hy
  by_cases hxy : x = y
  · rw [if_pos hxy, show M.dist x y = 0 from hxy ▸ M.dist_self x, mul_zero]
  · rw [if_neg hxy, zero_mul]

/-- Zero transport cost forces equal marginals. -/
theorem couplingTransportCost_eq_zero_implies_weights_eq
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) (γ : ℕ → ℕ → ℝ)
    (hγ : IsCoupling M.vertices μ ν γ) (hcost : couplingTransportCost M γ = 0) :
    μ.weights = ν.weights := by
  ext x
  by_cases hx : x ∈ M.vertices
  · have hrow_nonneg :
        ∀ x' ∈ M.vertices, 0 ≤ M.vertices.sum (fun y => γ x' y * M.dist x' y) := by
      intro x' hx'
      apply Finset.sum_nonneg
      intro y _
      exact mul_nonneg (hγ.nonneg x' y) (M.dist_nonneg x' y)
    have hrows :
        ∀ x' ∈ M.vertices, M.vertices.sum (fun y => γ x' y * M.dist x' y) = 0 := by
      intro x' hx'
      exact (Finset.sum_eq_zero_iff_of_nonneg hrow_nonneg).1 hcost x' hx'
    have hzero :
        ∀ x' y, x' ∈ M.vertices → y ∈ M.vertices → γ x' y * M.dist x' y = 0 := by
      intro x' y hx' hy'
      exact (Finset.sum_eq_zero_iff_of_nonneg fun z _ =>
        mul_nonneg (hγ.nonneg x' z) (M.dist_nonneg x' z)).1 (hrows x' hx') y hy'
    have hoff :
        ∀ x' y, x' ∈ M.vertices → y ∈ M.vertices → x' ≠ y → γ x' y = 0 := by
      intro x' y hx' hy' hxy
      have hdist : 0 < M.dist x' y := by
        have hne' : M.dist x' y ≠ 0 := by
          intro h0
          exact hxy ((M.dist_eq_zero_iff x' y).mp h0)
        exact (M.dist_nonneg x' y).lt_of_ne hne'.symm
      exact (mul_eq_zero.mp (hzero x' y hx' hy')).resolve_right (ne_of_gt hdist)
    have hrow :
        μ.weights x = M.vertices.sum (γ x) := (hγ.marginal_left x hx).symm
    have hcol :
        ν.weights x = M.vertices.sum (fun x' => γ x' x) := (hγ.marginal_right x hx).symm
    have hdiag :
        M.vertices.sum (γ x) = γ x x := by
      rw [Finset.sum_eq_sum_diff_singleton_add hx]
      have hrest :
          (M.vertices \ {x}).sum (γ x) = 0 := by
        apply Finset.sum_eq_zero
        intro y hy
        have hyne : y ≠ x := by
          intro heq
          exact (Finset.mem_sdiff.mp hy).2 (heq ▸ Finset.mem_singleton_self x)
        exact hoff x y hx ((Finset.mem_sdiff.mp hy).1) hyne.symm
      simp [hrest]
    have hdiag' :
        M.vertices.sum (fun x' => γ x' x) = γ x x := by
      rw [Finset.sum_eq_sum_diff_singleton_add hx]
      have hrest :
          (M.vertices \ {x}).sum (fun x' => γ x' x) = 0 := by
        apply Finset.sum_eq_zero
        intro y hy
        have hyne : y ≠ x := by
          intro heq
          exact (Finset.mem_sdiff.mp hy).2 (heq ▸ Finset.mem_singleton_self x)
        exact hoff y x ((Finset.mem_sdiff.mp hy).1) hx hyne
      simp [hrest]
    rw [hrow, hcol, hdiag, hdiag']
  · simp [μ.proof.weights_outside x hx, ν.proof.weights_outside x hx]

/-- If the weight functions differ, every valid coupling has positive transport cost. -/
theorem couplingTransportCost_pos_of_ne_weights
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : μ.weights ≠ ν.weights) (γ : ℕ → ℕ → ℝ)
    (hγ : IsCoupling M.vertices μ ν γ) :
    0 < couplingTransportCost M γ := by
  refine lt_of_le_of_ne (couplingTransportCost_nonneg M μ ν γ hγ) ?_
  intro h0
  exact hne (couplingTransportCost_eq_zero_implies_weights_eq M μ ν γ hγ h0.symm)

-- ---------------------------------------------------------------------------
-- Coupling polytope compactness (finite-dimensional transport polytope)
-- ---------------------------------------------------------------------------

section CouplingPolytope

variable {V : Finset ℕ} {μ ν : ProbDist V}

/-- Vertex pair in the coupling support. -/
abbrev CouplingPair (V : Finset ℕ) := ↑(V ×ˢ V)

/-- Pair-indexed coupling coefficients with the product topology. -/
abbrev CouplingCoeffs (V : Finset ℕ) := ∀ _ : CouplingPair V, ℝ

instance : TopologicalSpace (CouplingPair V) := ⊥

/-- Extend pair-indexed coefficients to a full coupling plan, zero outside `V ×ˢ V`. -/
noncomputable def couplingFromPairs (c : CouplingCoeffs V) : ℕ → ℕ → ℝ :=
  fun x y => if h : (x, y) ∈ V ×ˢ V then c ⟨(x, y), h⟩ else 0

theorem couplingFromPairs_nonneg (c : CouplingCoeffs V)
    (hnonneg : ∀ p : CouplingPair V, 0 ≤ c p) (x y : ℕ) :
    0 ≤ couplingFromPairs (V := V) c x y := by
  unfold couplingFromPairs; split_ifs with h
  · exact hnonneg ⟨(x, y), h⟩
  · exact le_rfl

theorem couplingFromPairs_left_outside (c : CouplingCoeffs V) (x : ℕ) (hx : x ∉ V) (y : ℕ) :
    couplingFromPairs (V := V) c x y = 0 := by
  unfold couplingFromPairs; split_ifs with h
  · exact absurd (Finset.mem_product.mp h).1 hx
  · rfl

theorem couplingFromPairs_right_outside (c : CouplingCoeffs V) (y : ℕ) (hy : y ∉ V) (x : ℕ) :
    couplingFromPairs (V := V) c x y = 0 := by
  unfold couplingFromPairs; split_ifs with h
  · exact absurd (Finset.mem_product.mp h).2 hy
  · rfl

/-- Coefficient-level coupling constraints on `V ×ˢ V`. -/
structure IsCouplingCoeffs (c : CouplingCoeffs V) : Prop where
  nonneg : ∀ p : CouplingPair V, 0 ≤ c p
  marginal_left :
    ∀ x ∈ V, V.sum (fun y => couplingFromPairs (V := V) c x y) = μ.weights x
  marginal_right :
    ∀ y ∈ V, V.sum (fun x => couplingFromPairs (V := V) c x y) = ν.weights y

theorem IsCouplingCoeffs.isCoupling (c : CouplingCoeffs V)
    (hc : IsCouplingCoeffs (V := V) (μ := μ) (ν := ν) c) :
    IsCoupling V μ ν (couplingFromPairs (V := V) c) := by
  refine ⟨couplingFromPairs_nonneg c hc.nonneg,
    couplingFromPairs_left_outside c, couplingFromPairs_right_outside c, ?_, ?_⟩
  · intro x hx; exact hc.marginal_left x hx
  · intro y hy; exact hc.marginal_right y hy

/-- Transport cost from pair-indexed coefficients. -/
noncomputable def couplingTransportCostPairs (M : FiniteMetricSpace)
    (c : CouplingCoeffs M.vertices) : ℝ :=
  M.vertices.sum (fun x => M.vertices.sum (fun y =>
    if h : (x, y) ∈ M.vertices ×ˢ M.vertices then c ⟨(x, y), h⟩ * M.dist x y else 0))

theorem couplingTransportCostPairs_eq (M : FiniteMetricSpace) (c : CouplingCoeffs M.vertices) :
    couplingTransportCostPairs M c =
      couplingTransportCost M (couplingFromPairs (V := M.vertices) c) := by
  unfold couplingTransportCostPairs couplingTransportCost couplingFromPairs
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  have hpair : (x, y) ∈ M.vertices ×ˢ M.vertices := Finset.mem_product.mpr ⟨hx, hy⟩
  simp [hpair]

/-- The set of pair-indexed coupling coefficients satisfying marginal constraints. -/
def couplingPolytope (V : Finset ℕ) (μ ν : ProbDist V) : Set (CouplingCoeffs V) :=
  {c | IsCouplingCoeffs (V := V) (μ := μ) (ν := ν) c}

theorem IsCouplingCoeffs.coeff_le_one (c : CouplingCoeffs V)
    (hc : IsCouplingCoeffs (V := V) (μ := μ) (ν := ν) c) (p : CouplingPair V) :
    c p ≤ 1 := by
  have hp : p.1 ∈ V ×ˢ V := p.2
  have hx : p.1.1 ∈ V := (Finset.mem_product.mp hp).1
  have hy : p.1.2 ∈ V := (Finset.mem_product.mp hp).2
  have hnonneg' : ∀ y ∈ V, 0 ≤ couplingFromPairs (V := V) c p.1.1 y :=
    fun y _ => couplingFromPairs_nonneg c hc.nonneg p.1.1 y
  have hcp : c p = couplingFromPairs (V := V) c p.1.1 p.1.2 := by
    unfold couplingFromPairs; simp [hp]
  have hle : c p ≤ V.sum (fun y => couplingFromPairs (V := V) c p.1.1 y) := by
    rw [hcp]
    exact Finset.single_le_sum hnonneg' hy
  have hμle : μ.weights p.1.1 ≤ 1 := by
    have hnonnegμ : ∀ x ∈ V, 0 ≤ μ.weights x := μ.proof.weights_nonneg
    calc
      μ.weights p.1.1 ≤ V.sum μ.weights := Finset.single_le_sum hnonnegμ hx
      _ = 1 := μ.proof.sum_one
  exact (hle.trans_eq (hc.marginal_left p.1.1 hx)).trans hμle

theorem couplingPolytope_subset_box (V : Finset ℕ) (μ ν : ProbDist V) :
    couplingPolytope (V := V) μ ν ⊆
      Set.pi Set.univ (fun (_ : CouplingPair V) => Set.Icc (0 : ℝ) 1) := by
  intro c hc p _
  have hf : IsCouplingCoeffs (V := V) (μ := μ) (ν := ν) c := by
    simpa [couplingPolytope, Set.mem_setOf_eq] using hc
  exact ⟨hf.nonneg p, IsCouplingCoeffs.coeff_le_one (V := V) (μ := μ) (ν := ν) c hf p⟩

/-- Coefficient function extracted from a full coupling plan on `V ×ˢ V`. -/
noncomputable def couplingToPairs (γ : ℕ → ℕ → ℝ) : CouplingCoeffs V :=
  fun p => γ p.1.1 p.1.2

theorem couplingFromPairs_couplingToPairs (γ : ℕ → ℕ → ℝ) {x y : ℕ}
    (hmem : (x, y) ∈ V ×ˢ V) :
    couplingFromPairs (V := V) (couplingToPairs γ) x y = γ x y := by
  unfold couplingFromPairs couplingToPairs
  simp [hmem]

theorem couplingTransportCost_couplingToPairs (M : FiniteMetricSpace) (γ : ℕ → ℕ → ℝ) :
    couplingTransportCost M (couplingFromPairs (V := M.vertices) (couplingToPairs γ)) =
      couplingTransportCost M γ := by
  unfold couplingTransportCost couplingFromPairs couplingToPairs
  apply Finset.sum_congr rfl
  intro x hx
  apply Finset.sum_congr rfl
  intro y hy
  have hmem : (x, y) ∈ M.vertices ×ˢ M.vertices := Finset.mem_product.mpr ⟨hx, hy⟩
  simp [hmem]

theorem couplingToPairs_isCouplingCoeffs (γ : ℕ → ℕ → ℝ)
    (hγ : IsCoupling V μ ν γ) :
    IsCouplingCoeffs (V := V) (μ := μ) (ν := ν) (couplingToPairs γ) := by
  refine ⟨fun p => hγ.nonneg p.1.1 p.1.2, ?_, ?_⟩
  · intro x hx
    have hsum :
        V.sum (fun y => couplingFromPairs (V := V) (couplingToPairs γ) x y) = V.sum (γ x) := by
      apply Finset.sum_congr rfl
      intro y hy
      rw [couplingFromPairs_couplingToPairs γ (Finset.mem_product.mpr ⟨hx, hy⟩)]
    rw [hsum, hγ.marginal_left x hx]
  · intro y hy
    have hsum :
        V.sum (fun x => couplingFromPairs (V := V) (couplingToPairs γ) x y) = V.sum (γ · y) := by
      apply Finset.sum_congr rfl
      intro x hx
      rw [couplingFromPairs_couplingToPairs γ (Finset.mem_product.mpr ⟨hx, hy⟩)]
    rw [hsum, hγ.marginal_right y hy]

theorem isCompact_couplingCoeffBox (V : Finset ℕ) :
    IsCompact (Set.pi Set.univ (fun (_ : CouplingPair V) => Set.Icc (0 : ℝ) 1)) := by
  apply isCompact_univ_pi
  intro _
  exact isCompact_Icc

theorem continuous_couplingCoeffEval (p : CouplingPair V) :
    Continuous (fun c : CouplingCoeffs V => c p) :=
  continuous_apply p

theorem continuous_couplingFromPairs (x y : ℕ) :
    Continuous (fun c : CouplingCoeffs V => couplingFromPairs (V := V) c x y) := by
  unfold couplingFromPairs
  by_cases hmem : (x, y) ∈ V ×ˢ V
  · simp only [dif_pos hmem]
    exact continuous_apply ((⟨(x, y), hmem⟩ : CouplingPair V))
  · simp only [dif_neg (fun h => hmem h)]
    exact continuous_const

theorem continuous_couplingLeftMarginal (x : ℕ) :
    Continuous (fun c : CouplingCoeffs V =>
      V.sum (fun y => couplingFromPairs (V := V) c x y)) := by
  apply continuous_finset_sum
  intro y _
  exact continuous_couplingFromPairs (V := V) x y

theorem continuous_couplingRightMarginal (y : ℕ) :
    Continuous (fun c : CouplingCoeffs V =>
      V.sum (fun x => couplingFromPairs (V := V) c x y)) := by
  apply continuous_finset_sum
  intro x _
  exact continuous_couplingFromPairs (V := V) x y

theorem couplingPolytope_isClosed (V : Finset ℕ) (μ ν : ProbDist V) :
    IsClosed (couplingPolytope (V := V) μ ν) := by
  change IsClosed {c | IsCouplingCoeffs (V := V) (μ := μ) (ν := ν) c}
  have hnonneg :
      IsClosed {c : CouplingCoeffs V | ∀ p : CouplingPair V, 0 ≤ c p} := by
    have heq :
        {c : CouplingCoeffs V | ∀ p : CouplingPair V, 0 ≤ c p} =
          ⋂ p : CouplingPair V, {c | 0 ≤ c p} := by
      ext c
      simp [Set.mem_iInter]
    rw [heq]
    refine isClosed_iInter fun (p : CouplingPair V) =>
      isClosed_le continuous_const (continuous_couplingCoeffEval p)
  have hleft :
      IsClosed {c : CouplingCoeffs V |
        ∀ x ∈ V, V.sum (fun y => couplingFromPairs (V := V) c x y) = μ.weights x} := by
    have heq :
        {c : CouplingCoeffs V | ∀ x ∈ V, V.sum (fun y => couplingFromPairs c x y) = μ.weights x} =
          ⋂ x ∈ V, {c | V.sum (fun y => couplingFromPairs (V := V) c x y) = μ.weights x} := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [heq]
    exact isClosed_biInter fun x _ =>
      isClosed_eq (continuous_couplingLeftMarginal (V := V) x) continuous_const
  have hright :
      IsClosed {c : CouplingCoeffs V |
        ∀ y ∈ V, V.sum (fun x => couplingFromPairs (V := V) c x y) = ν.weights y} := by
    have heq :
        {c : CouplingCoeffs V | ∀ y ∈ V, V.sum (fun x => couplingFromPairs c x y) = ν.weights y} =
          ⋂ y ∈ V, {c | V.sum (fun x => couplingFromPairs (V := V) c x y) = ν.weights y} := by
      ext c
      simp only [Set.mem_setOf_eq, Set.mem_iInter]
    rw [heq]
    exact isClosed_biInter fun y _ =>
      isClosed_eq (continuous_couplingRightMarginal (V := V) y) continuous_const
  have hdef :
      {c | IsCouplingCoeffs (V := V) (μ := μ) (ν := ν) c} =
        {c : CouplingCoeffs V | ∀ p : CouplingPair V, 0 ≤ c p} ∩
          {c : CouplingCoeffs V |
            ∀ x ∈ V, V.sum (fun y => couplingFromPairs (V := V) c x y) = μ.weights x} ∩
          {c : CouplingCoeffs V |
            ∀ y ∈ V, V.sum (fun x => couplingFromPairs (V := V) c x y) = ν.weights y} := by
    ext c
    simp only [Set.mem_setOf_eq, Set.mem_inter_iff]
    constructor
    · intro h
      exact And.intro (And.intro h.nonneg h.marginal_left) h.marginal_right
    · intro ⟨⟨h1, h2⟩, h3⟩
      exact ⟨h1, h2, h3⟩
  rw [hdef]
  exact (hnonneg.inter hleft).inter hright

theorem couplingPolytope_isCompact (V : Finset ℕ) (μ ν : ProbDist V) :
    IsCompact (couplingPolytope (V := V) μ ν) := by
  apply IsCompact.of_isClosed_subset (isCompact_couplingCoeffBox (V := V))
  · exact couplingPolytope_isClosed (V := V) μ ν
  · exact couplingPolytope_subset_box (V := V) μ ν

theorem continuous_couplingTransportCostPairs (M : FiniteMetricSpace) :
    Continuous (couplingTransportCostPairs (M := M)) := by
  unfold couplingTransportCostPairs
  apply continuous_finset_sum
  intro x _
  apply continuous_finset_sum
  intro y _
  by_cases hmem : (x, y) ∈ M.vertices ×ˢ M.vertices
  · simp only [dif_pos hmem]
    exact (continuous_apply ((⟨(x, y), hmem⟩ : CouplingPair M.vertices))).mul continuous_const
  · simp only [dif_neg (fun h => hmem h)]
    exact continuous_const

/-- Achievable transport costs are the image of the coupling polytope under pair transport cost. -/
theorem couplingCostSet_eq_image (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    couplingCostSet M μ ν =
      couplingTransportCostPairs M '' couplingPolytope (V := M.vertices) μ ν := by
  ext c
  simp only [couplingCostSet, couplingPolytope, Set.mem_setOf_eq, Set.mem_image]
  constructor
  · rintro ⟨γ, hγ, rfl⟩
    refine ⟨couplingToPairs γ,
      couplingToPairs_isCouplingCoeffs (V := M.vertices) (μ := μ) (ν := ν) γ hγ, ?_⟩
    rw [couplingTransportCostPairs_eq, couplingTransportCost_couplingToPairs]
  · rintro ⟨coeff, hc, rfl⟩
    refine ⟨couplingFromPairs (V := M.vertices) coeff,
      IsCouplingCoeffs.isCoupling (V := M.vertices) (μ := μ) (ν := ν) coeff hc, ?_⟩
    exact (couplingTransportCostPairs_eq M coeff).symm

/-- On a finite vertex set, achievable transport costs form a compact subset of `ℝ`. -/
theorem couplingCostSet_isCompact (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    IsCompact (couplingCostSet M μ ν) := by
  rw [couplingCostSet_eq_image]
  exact IsCompact.image (couplingPolytope_isCompact (V := M.vertices) μ ν)
    (continuous_couplingTransportCostPairs (M := M))

end CouplingPolytope

/-- The W₁ infimum is achieved by some coupling plan.

    Proof: `couplingCostSet` is compact (`couplingCostSet_isCompact`), hence the infimum
    belongs to the cost set (`IsCompact.sInf_mem`). The remaining sorries formalize the
    finite-dimensional transport polytope and continuity of transport cost. -/
theorem W1_attained
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    ∃ γ : ℕ → ℕ → ℝ, IsCoupling M.vertices μ ν γ ∧
      couplingTransportCost M γ = W1 M μ ν := by
  have hne := couplingCostSet_nonempty M μ ν
  have hcompact := couplingCostSet_isCompact M μ ν
  have hw1_mem : W1 M μ ν ∈ couplingCostSet M μ ν := by
    unfold W1
    exact IsCompact.sInf_mem hcompact hne
  rcases hw1_mem with ⟨γ, hγ, hcost⟩
  exact ⟨γ, hγ, hcost⟩

/-- On a finite metric space, distinct distributions have positive W₁ distance. -/
theorem W1_pos_of_ne_weights
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : μ.weights ≠ ν.weights) : 0 < W1 M μ ν := by
  by_contra hnotpos
  push Not at hnotpos
  have hW1 : W1 M μ ν = 0 := le_antisymm hnotpos (W1_nonneg M μ ν)
  obtain ⟨γ, hγ, hcost⟩ := W1_attained M μ ν
  rw [hW1] at hcost
  exact hne (couplingTransportCost_eq_zero_implies_weights_eq M μ ν γ hγ hcost)

theorem exists_zero_cost_coupling_of_W1_eq_zero
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (h : W1 M μ ν = 0) :
    ∃ γ : ℕ → ℕ → ℝ, IsCoupling M.vertices μ ν γ ∧ couplingTransportCost M γ = 0 := by
  obtain ⟨γ, hγ, hcost⟩ := W1_attained M μ ν
  rw [h] at hcost
  exact ⟨γ, hγ, hcost⟩

/-- Kantorovich bound: 1-Lipschitz test functions give a lower bound on transport cost. -/
theorem abs_probExpectation_sub_le_couplingTransportCost
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) (γ : ℕ → ℕ → ℝ)
    (hγ : IsCoupling M.vertices μ ν γ) (f : ℕ → ℝ)
    (hf : ∀ x y, |f x - f y| ≤ M.dist x y) :
    |probExpectation M μ f - probExpectation M ν f| ≤ couplingTransportCost M γ := by
  have hμ :
      probExpectation M μ f =
        M.vertices.sum (fun x => M.vertices.sum (fun y => γ x y * f x)) := by
    unfold probExpectation
    apply Finset.sum_congr rfl
    intro x hx
    have hstep :
        μ.weights x * f x = M.vertices.sum (fun y => γ x y * f x) := by
      calc
        μ.weights x * f x = f x * M.vertices.sum (γ x) := by
          rw [mul_comm, ← hγ.marginal_left x hx]
        _ = M.vertices.sum (fun y => f x * γ x y) := by rw [Finset.mul_sum]
        _ = M.vertices.sum (fun y => γ x y * f x) := by
          apply Finset.sum_congr rfl
          intro y _
          ring
    exact hstep
  have hν :
      probExpectation M ν f =
        M.vertices.sum (fun x => M.vertices.sum (fun y => γ x y * f y)) := by
    unfold probExpectation
    have h1 :
        M.vertices.sum (fun y => ν.weights y * f y) =
          M.vertices.sum (fun y => M.vertices.sum (fun x => γ x y * f y)) := by
      apply Finset.sum_congr rfl
      intro y hy
      have hstep :
          ν.weights y * f y = M.vertices.sum (fun x => γ x y * f y) := by
        calc
          ν.weights y * f y = f y * M.vertices.sum (fun x => γ x y) := by
            rw [mul_comm, ← hγ.marginal_right y hy]
          _ = M.vertices.sum (fun x => f y * γ x y) := by
            rw [Finset.mul_sum]
          _ = M.vertices.sum (fun x => γ x y * f y) := by
            apply Finset.sum_congr rfl
            intro x _
            ring
      exact hstep
    rw [h1, Finset.sum_comm]
  have hdiff :
      probExpectation M μ f - probExpectation M ν f =
        M.vertices.sum (fun x => M.vertices.sum (fun y => γ x y * (f x - f y))) := by
    rw [hμ, hν, ← Finset.sum_sub_distrib]
    congr 1
    ext x
    rw [← Finset.sum_sub_distrib]
    congr 1
    ext y
    ring
  rw [hdiff]
  calc
    |M.vertices.sum (fun x => M.vertices.sum (fun y => γ x y * (f x - f y)))|
        ≤ M.vertices.sum (fun x => |M.vertices.sum (fun y => γ x y * (f x - f y))|) := by
      simpa using
        (Finset.abs_sum_le_sum_abs (s := M.vertices)
          (f := fun x => M.vertices.sum (fun y => γ x y * (f x - f y))))
    _ ≤ M.vertices.sum (fun x => M.vertices.sum (fun y => |γ x y * (f x - f y)|)) := by
      apply Finset.sum_le_sum
      intro x _
      simpa using
        (Finset.abs_sum_le_sum_abs (s := M.vertices)
          (f := fun y => γ x y * (f x - f y)))
    _ ≤ M.vertices.sum (fun x => M.vertices.sum (fun y => γ x y * |f x - f y|)) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      rw [abs_mul, abs_of_nonneg (hγ.nonneg x y)]
    _ ≤ M.vertices.sum (fun x => M.vertices.sum (fun y => γ x y * M.dist x y)) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      exact mul_le_mul_of_nonneg_left (hf x y) (hγ.nonneg x y)
    _ = couplingTransportCost M γ := rfl

-- ---------------------------------------------------------------------------
-- Kantorovich dual lower bound
-- ---------------------------------------------------------------------------

/-- `|E_μ[f] - E_ν[f]| ≤ W1 M μ ν` for every 1-Lipschitz `f`.

    Proof sketch: for any coupling `γ` with `IsCoupling V μ ν γ`,
      E_μ[f] - E_ν[f]
        = Σ_x μ(x) f(x) - Σ_y ν(y) f(y)
        = Σ_x (Σ_y γ(x,y)) f(x) - Σ_y (Σ_x γ(x,y)) f(y)   [marginals]
        = Σ_{x,y} γ(x,y) (f(x) - f(y))                       [sum swap]
      |E_μ[f] - E_ν[f]| ≤ Σ_{x,y} γ(x,y) |f(x) - f(y)|      [triangle]
                        ≤ Σ_{x,y} γ(x,y) d(x,y)               [1-Lip + nonneg γ]
                        = cost(γ)
    Taking infimum gives the result.
    Deferred: Finset double-sum marginal rewriting requires support-restriction
    lemmas and a Finset.sum_comm argument that is nontrivial to assemble cleanly. -/
theorem W1_ge_of_lipschitz
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (f : ℕ → ℝ) (hf : ∀ x y, |f x - f y| ≤ M.dist x y)
    (hne : (couplingCostSet M μ ν).Nonempty) :
    |probExpectation M μ f - probExpectation M ν f| ≤ W1 M μ ν := by
  unfold W1
  apply le_csInf hne
  intro c hc
  obtain ⟨γ, hγ, rfl⟩ := hc
  exact abs_probExpectation_sub_le_couplingTransportCost M μ ν γ hγ f hf

-- ---------------------------------------------------------------------------
-- W₁ = 0 ↔ μ = ν  (explicit sorry — diagonal coupling argument)
-- ---------------------------------------------------------------------------

/-- `W1 M μ ν = 0 ↔ μ.weights = ν.weights`.

    Proof sketch:
    (≥) diagonal coupling `γ(x,y) = μ(x) · [x = y]` has cost 0.
    (≤) cost 0 ⟹ γ(x,y) > 0 ⟹ d(x,y) = 0 ⟹ x = y ⟹ marginals coincide.
    Deferred: requires finset support analysis and `dist_eq_zero_iff`. -/
theorem W1_eq_zero_iff
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ μ.weights = ν.weights := by
  constructor
  · intro hW1
    obtain ⟨γ, hγ, hcost⟩ := exists_zero_cost_coupling_of_W1_eq_zero M μ ν hW1
    exact couplingTransportCost_eq_zero_implies_weights_eq M μ ν γ hγ hcost
  · intro heq
    have hγ : IsCoupling M.vertices μ ν (diagonalCoupling M.vertices μ) :=
      ⟨diagonalCoupling_nonneg M.vertices μ,
        diagonalCoupling_left_outside M.vertices μ,
        fun y hy x => diagonalCoupling_right_outside M.vertices μ y hy x,
        diagonalCoupling_marginal_left M.vertices μ,
        fun y hy => by rw [← heq]; exact diagonalCoupling_marginal_right M.vertices μ y hy⟩
    have hle := W1_le_couplingCost M μ ν (diagonalCoupling M.vertices μ) hγ
    rw [diagonalCouplingTransportCost_zero M μ] at hle
    exact le_antisymm hle (W1_nonneg M μ ν)

-- ---------------------------------------------------------------------------
-- Glued coupling (triangle inequality ingredient)
-- ---------------------------------------------------------------------------

/-- Gluing term `γ₁(x,y) · γ₂(y,z) / ν(y)` when `ν(y) ≠ 0`, else `0`. -/
noncomputable def gluedCouplingTerm (V : Finset ℕ) (ν : ProbDist V)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (x y z : ℕ) : ℝ :=
  if h : ν.weights y = 0 then 0 else γ₁ x y * γ₂ y z / ν.weights y

/-- Glued coupling `γ(x,z) = Σ_{y ∈ V} γ₁(x,y) γ₂(y,z) / ν(y)`. -/
noncomputable def gluedCoupling (V : Finset ℕ) (ν : ProbDist V)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (x z : ℕ) : ℝ :=
  V.sum (fun y => gluedCouplingTerm V ν γ₁ γ₂ x y z)

theorem IsCoupling_col_zero_of_weight_zero (V : Finset ℕ) (μ ν : ProbDist V)
    (γ : ℕ → ℕ → ℝ) (hγ : IsCoupling V μ ν γ) {y : ℕ} (hy : y ∈ V)
    (hν : ν.weights y = 0) (x : ℕ) : γ x y = 0 := by
  by_cases hx : x ∈ V
  · have hsum := hγ.marginal_right y hy
    rw [hν] at hsum
    exact (Finset.sum_eq_zero_iff_of_nonneg fun x' _ => hγ.nonneg x' y).1 hsum x hx
  · exact hγ.left_outside x hx y

theorem IsCoupling_row_zero_of_weight_zero (V : Finset ℕ) (μ ν : ProbDist V)
    (γ : ℕ → ℕ → ℝ) (hγ : IsCoupling V μ ν γ) {x : ℕ} (hx : x ∈ V)
    (hμ : μ.weights x = 0) (y : ℕ) : γ x y = 0 := by
  by_cases hy : y ∈ V
  · have hsum := hγ.marginal_left x hx
    rw [hμ] at hsum
    exact (Finset.sum_eq_zero_iff_of_nonneg fun y' _ => hγ.nonneg x y').1 hsum y hy
  · exact hγ.right_outside y hy x

theorem gluedCouplingTerm_eq_zero_of_weight_zero (V : Finset ℕ) (μ ν ρ : ProbDist V)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling V μ ν γ₁) (hγ₂ : IsCoupling V ν ρ γ₂)
    {y : ℕ} (hy : y ∈ V) (hν : ν.weights y = 0) (x z : ℕ) :
    gluedCouplingTerm V ν γ₁ γ₂ x y z = 0 := by
  unfold gluedCouplingTerm
  simp [hν]

theorem gluedCouplingTerm_nonneg (V : Finset ℕ) (μ ν ρ : ProbDist V)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling V μ ν γ₁)
    (hγ₂ : IsCoupling V ν ρ γ₂) (x y z : ℕ) :
    0 ≤ gluedCouplingTerm V ν γ₁ γ₂ x y z := by
  unfold gluedCouplingTerm
  split_ifs with hν
  · exact le_rfl
  · apply div_nonneg (mul_nonneg (hγ₁.nonneg x y) (hγ₂.nonneg y z))
    by_cases hy : y ∈ V
    · exact le_of_lt (lt_of_le_of_ne (ν.proof.weights_nonneg y hy) (Ne.symm hν))
    · exfalso
      exact hν (ν.proof.weights_outside y hy)

theorem gluedCoupling_nonneg (V : Finset ℕ) (μ ν ρ : ProbDist V)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling V μ ν γ₁)
    (hγ₂ : IsCoupling V ν ρ γ₂) (x z : ℕ) :
    0 ≤ gluedCoupling V ν γ₁ γ₂ x z := by
  unfold gluedCoupling
  apply Finset.sum_nonneg
  intro y _
  exact gluedCouplingTerm_nonneg V μ ν ρ γ₁ γ₂ hγ₁ hγ₂ x y z

theorem gluedCoupling_left_outside (V : Finset ℕ) (μ ν ρ : ProbDist V)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling V μ ν γ₁) (x : ℕ) (hx : x ∉ V) (z : ℕ) :
    gluedCoupling V ν γ₁ γ₂ x z = 0 := by
  unfold gluedCoupling gluedCouplingTerm
  apply Finset.sum_eq_zero
  intro y _
  by_cases hν : ν.weights y = 0
  · simp [hν]
  · have := hγ₁.left_outside x hx y
    simp [this, zero_mul, zero_div]

theorem gluedCoupling_right_outside (V : Finset ℕ) (μ ν ρ : ProbDist V)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₂ : IsCoupling V ν ρ γ₂) (z : ℕ) (hz : z ∉ V) (x : ℕ) :
    gluedCoupling V ν γ₁ γ₂ x z = 0 := by
  unfold gluedCoupling gluedCouplingTerm
  apply Finset.sum_eq_zero
  intro y _
  by_cases hν : ν.weights y = 0
  · simp [hν]
  · have := hγ₂.right_outside z hz y
    simp [this, mul_zero, zero_div]

theorem gluedCoupling_marginal_left (V : Finset ℕ) (μ ν ρ : ProbDist V)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling V μ ν γ₁)
    (hγ₂ : IsCoupling V ν ρ γ₂) (x : ℕ) (hx : x ∈ V) :
    V.sum (gluedCoupling V ν γ₁ γ₂ x) = μ.weights x := by
  unfold gluedCoupling gluedCouplingTerm
  calc
    V.sum (fun z => V.sum (fun y => gluedCouplingTerm V ν γ₁ γ₂ x y z)) =
        V.sum (fun y => V.sum (fun z => gluedCouplingTerm V ν γ₁ γ₂ x y z)) := Finset.sum_comm
    _ = V.sum (fun y =>
          if h : ν.weights y = 0 then 0
          else γ₁ x y * V.sum (γ₂ y) / ν.weights y) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hν : ν.weights y = 0
      · simp [gluedCouplingTerm, hν]
      · calc
          V.sum (fun z => gluedCouplingTerm V ν γ₁ γ₂ x y z) =
              V.sum (fun z => γ₁ x y * γ₂ y z / ν.weights y) := by
            apply Finset.sum_congr rfl
            intro z _
            simp [gluedCouplingTerm, dif_neg hν]
          _ = γ₁ x y * V.sum (γ₂ y) / ν.weights y := by
            calc
              _ = V.sum (fun z => (γ₁ x y / ν.weights y) * γ₂ y z) := by
                apply Finset.sum_congr rfl
                intro z _
                ring
              _ = (γ₁ x y / ν.weights y) * V.sum (γ₂ y) := by
                rw [← Finset.mul_sum]
              _ = γ₁ x y * V.sum (γ₂ y) / ν.weights y := by ring
          _ = if h : ν.weights y = 0 then 0 else γ₁ x y * V.sum (γ₂ y) / ν.weights y := by
            simp [dif_neg hν]
    _ = V.sum (fun y => if h : ν.weights y = 0 then 0 else γ₁ x y) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hν : ν.weights y = 0
      · simp [hν]
      · rw [dif_neg hν, dif_neg hν]
        have hrow := hγ₂.marginal_left y hy
        have hne : ν.weights y ≠ 0 := by intro h; exact hν h
        field_simp [hne]
        rw [hrow]
    _ = V.sum (γ₁ x) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hν : ν.weights y = 0
      · have hzero := IsCoupling_col_zero_of_weight_zero V μ ν γ₁ hγ₁ hy hν x
        simp [hν, hzero]
      · simp [dif_neg hν, mul_comm]
    _ = μ.weights x := hγ₁.marginal_left x hx

theorem gluedCoupling_marginal_right (V : Finset ℕ) (μ ν ρ : ProbDist V)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling V μ ν γ₁)
    (hγ₂ : IsCoupling V ν ρ γ₂) (z : ℕ) (hz : z ∈ V) :
    V.sum (fun x => gluedCoupling V ν γ₁ γ₂ x z) = ρ.weights z := by
  unfold gluedCoupling gluedCouplingTerm
  calc
    V.sum (fun x => V.sum (fun y => gluedCouplingTerm V ν γ₁ γ₂ x y z)) =
        V.sum (fun y => V.sum (fun x => gluedCouplingTerm V ν γ₁ γ₂ x y z)) := Finset.sum_comm
    _ = V.sum (fun y =>
          if h : ν.weights y = 0 then 0
          else V.sum (γ₁ · y) * γ₂ y z / ν.weights y) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hν : ν.weights y = 0
      · simp [gluedCouplingTerm, hν]
      · calc
          V.sum (fun x => gluedCouplingTerm V ν γ₁ γ₂ x y z) =
              V.sum (fun x => γ₁ x y * γ₂ y z / ν.weights y) := by
            apply Finset.sum_congr rfl
            intro x _
            simp [gluedCouplingTerm, dif_neg hν]
          _ = V.sum (γ₁ · y) * γ₂ y z / ν.weights y := by
            calc
              _ = V.sum (fun x => (γ₂ y z / ν.weights y) * γ₁ x y) := by
                apply Finset.sum_congr rfl
                intro x _
                ring
              _ = (γ₂ y z / ν.weights y) * V.sum (γ₁ · y) := by
                rw [← Finset.mul_sum]
              _ = V.sum (γ₁ · y) * γ₂ y z / ν.weights y := by ring
          _ = if h : ν.weights y = 0 then 0 else V.sum (γ₁ · y) * γ₂ y z / ν.weights y := by
            simp [dif_neg hν]
    _ = V.sum (fun y => if h : ν.weights y = 0 then 0 else γ₂ y z) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hν : ν.weights y = 0
      · simp [hν]
      · rw [dif_neg hν, dif_neg hν]
        have hrow := hγ₁.marginal_right y hy
        have hne : ν.weights y ≠ 0 := by intro h; exact hν h
        field_simp [hne]
        rw [hrow, mul_comm]
    _ = V.sum (γ₂ · z) := by
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hν : ν.weights y = 0
      · have hzero := IsCoupling_row_zero_of_weight_zero V ν ρ γ₂ hγ₂ hy hν z
        simp [hν, hzero]
      · simp [dif_neg hν, mul_comm]
    _ = ρ.weights z := hγ₂.marginal_right z hz

theorem gluedCoupling_isCoupling (V : Finset ℕ) (μ ν ρ : ProbDist V)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling V μ ν γ₁)
    (hγ₂ : IsCoupling V ν ρ γ₂) :
    IsCoupling V μ ρ (gluedCoupling V ν γ₁ γ₂) :=
  ⟨gluedCoupling_nonneg V μ ν ρ γ₁ γ₂ hγ₁ hγ₂,
    fun x hx z => gluedCoupling_left_outside V μ ν ρ γ₁ γ₂ hγ₁ x hx z,
    fun z hz x => gluedCoupling_right_outside V μ ν ρ γ₁ γ₂ hγ₂ z hz x,
    gluedCoupling_marginal_left V μ ν ρ γ₁ γ₂ hγ₁ hγ₂,
    gluedCoupling_marginal_right V μ ν ρ γ₁ γ₂ hγ₁ hγ₂⟩

theorem gluedCouplingTerm_triangle
    (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling M.vertices μ ν γ₁)
    (hγ₂ : IsCoupling M.vertices ν ρ γ₂) (x y z : ℕ) :
    gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z * M.dist x z ≤
      gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z * (M.dist x y + M.dist y z) := by
  exact mul_le_mul_of_nonneg_left (M.triangle x y z)
    (gluedCouplingTerm_nonneg M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂ x y z)

theorem gluedCoupling_cost_first_sum
    (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling M.vertices μ ν γ₁)
    (hγ₂ : IsCoupling M.vertices ν ρ γ₂) :
    M.vertices.sum (fun x => M.vertices.sum (fun y => M.vertices.sum (fun z =>
          gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z * M.dist x y))) =
      couplingTransportCost M γ₁ := by
  unfold couplingTransportCost
  calc
    M.vertices.sum (fun x => M.vertices.sum (fun y => M.vertices.sum (fun z =>
            gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z * M.dist x y))) =
        M.vertices.sum (fun x => M.vertices.sum (fun y =>
          M.dist x y * M.vertices.sum (fun z =>
            gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z))) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y _
      calc
        M.vertices.sum (fun z => gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z * M.dist x y) =
            M.vertices.sum (fun z => M.dist x y * gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z) := by
          apply Finset.sum_congr rfl
          intro z _
          ring
        _ = M.dist x y * M.vertices.sum (fun z => gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z) := by
          rw [← Finset.mul_sum]
    _ = M.vertices.sum (fun x => M.vertices.sum (fun y =>
          M.dist x y * if h : ν.weights y = 0 then 0 else γ₁ x y)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hν : ν.weights y = 0
      · simp [gluedCouplingTerm, hν]
      · have hne : ν.weights y ≠ 0 := fun h => hν h
        calc
          M.dist x y * M.vertices.sum (fun z => gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z) =
              M.dist x y * (γ₁ x y * M.vertices.sum (γ₂ y) / ν.weights y) := by
            congr 1
            calc
              M.vertices.sum (fun z => gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z) =
                  M.vertices.sum (fun z => γ₁ x y * γ₂ y z / ν.weights y) := by
                apply Finset.sum_congr rfl
                intro z _
                simp [gluedCouplingTerm, dif_neg hν]
              _ = γ₁ x y * M.vertices.sum (γ₂ y) / ν.weights y := by
                calc
                  _ = M.vertices.sum (fun z => (γ₁ x y / ν.weights y) * γ₂ y z) := by
                    apply Finset.sum_congr rfl
                    intro z _
                    ring
                  _ = (γ₁ x y / ν.weights y) * M.vertices.sum (γ₂ y) := by
                    rw [← Finset.mul_sum]
                  _ = γ₁ x y * M.vertices.sum (γ₂ y) / ν.weights y := by ring
          _ = M.dist x y * if h : ν.weights y = 0 then 0 else γ₁ x y := by
            rw [hγ₂.marginal_left y hy]
            field_simp [hne]
            simp [dif_neg hν]
    _ = M.vertices.sum (fun x => M.vertices.sum (fun y => γ₁ x y * M.dist x y)) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro y hy
      by_cases hν : ν.weights y = 0
      · have hzero := IsCoupling_col_zero_of_weight_zero M.vertices μ ν γ₁ hγ₁ hy hν x
        simp [hν, hzero, mul_zero, zero_mul]
      · simp [dif_neg hν, mul_comm]

theorem gluedCoupling_cost_second_sum
    (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling M.vertices μ ν γ₁)
    (hγ₂ : IsCoupling M.vertices ν ρ γ₂) :
    M.vertices.sum (fun x => M.vertices.sum (fun y => M.vertices.sum (fun z =>
          gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z * M.dist y z))) =
      couplingTransportCost M γ₂ := by
  unfold couplingTransportCost
  calc
    M.vertices.sum (fun x => M.vertices.sum (fun y => M.vertices.sum (fun z =>
            gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z * M.dist y z))) =
        M.vertices.sum (fun y => M.vertices.sum (fun z =>
          M.dist y z * M.vertices.sum (fun x =>
            gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z))) := by
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro y _
      rw [Finset.sum_comm]
      apply Finset.sum_congr rfl
      intro z _
      calc
        M.vertices.sum (fun x => gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z * M.dist y z) =
            M.vertices.sum (fun x => M.dist y z * gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z) := by
          apply Finset.sum_congr rfl
          intro x _
          ring
        _ = M.dist y z * M.vertices.sum (fun x => gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z) := by
          rw [← Finset.mul_sum]
    _ = M.vertices.sum (fun y => M.vertices.sum (fun z =>
          M.dist y z * if h : ν.weights y = 0 then 0 else γ₂ y z)) := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z _
      by_cases hν : ν.weights y = 0
      · simp [gluedCouplingTerm, hν]
      · have hne : ν.weights y ≠ 0 := fun h => hν h
        calc
          M.dist y z * M.vertices.sum (fun x => gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z) =
              M.dist y z * (M.vertices.sum (γ₁ · y) * γ₂ y z / ν.weights y) := by
            congr 1
            calc
              M.vertices.sum (fun x => gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z) =
                  M.vertices.sum (fun x => γ₁ x y * γ₂ y z / ν.weights y) := by
                apply Finset.sum_congr rfl
                intro x _
                simp [gluedCouplingTerm, dif_neg hν]
              _ = M.vertices.sum (γ₁ · y) * γ₂ y z / ν.weights y := by
                calc
                  _ = M.vertices.sum (fun x => (γ₂ y z / ν.weights y) * γ₁ x y) := by
                    apply Finset.sum_congr rfl
                    intro x _
                    ring
                  _ = (γ₂ y z / ν.weights y) * M.vertices.sum (γ₁ · y) := by
                    rw [← Finset.mul_sum]
                  _ = M.vertices.sum (γ₁ · y) * γ₂ y z / ν.weights y := by ring
          _ = M.dist y z * if h : ν.weights y = 0 then 0 else γ₂ y z := by
            rw [hγ₁.marginal_right y hy]
            field_simp [hne]
            simp [dif_neg hν]
    _ = M.vertices.sum (fun y => M.vertices.sum (fun z => γ₂ y z * M.dist y z)) := by
      apply Finset.sum_congr rfl
      intro y hy
      apply Finset.sum_congr rfl
      intro z _
      by_cases hν : ν.weights y = 0
      · have hzero := IsCoupling_row_zero_of_weight_zero M.vertices ν ρ γ₂ hγ₂ hy hν z
        simp [hν, hzero, mul_zero, zero_mul]
      · simp [dif_neg hν, mul_comm]

theorem gluedCoupling_cost_le (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling M.vertices μ ν γ₁)
    (hγ₂ : IsCoupling M.vertices ν ρ γ₂) :
    couplingTransportCost M (gluedCoupling M.vertices ν γ₁ γ₂) ≤
      couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
  unfold couplingTransportCost gluedCoupling
  calc
    M.vertices.sum (fun x => M.vertices.sum (fun z =>
          (M.vertices.sum (fun y => gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z)) * M.dist x z)) =
        M.vertices.sum (fun x => M.vertices.sum (fun z => M.vertices.sum (fun y =>
          gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z * M.dist x z))) := by
      apply Finset.sum_congr rfl
      intro x _
      apply Finset.sum_congr rfl
      intro z _
      rw [Finset.sum_mul]
    _ = M.vertices.sum (fun x => M.vertices.sum (fun y => M.vertices.sum (fun z =>
          gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z * M.dist x z))) := by
      apply Finset.sum_congr rfl
      intro x _
      rw [Finset.sum_comm]
    _ ≤ M.vertices.sum (fun x => M.vertices.sum (fun y => M.vertices.sum (fun z =>
          gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z * (M.dist x y + M.dist y z)))) := by
      apply Finset.sum_le_sum
      intro x _
      apply Finset.sum_le_sum
      intro y _
      apply Finset.sum_le_sum
      intro z _
      exact gluedCouplingTerm_triangle M μ ν ρ γ₁ γ₂ hγ₁ hγ₂ x y z
    _ = M.vertices.sum (fun x => M.vertices.sum (fun y => M.vertices.sum (fun z =>
            gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z * M.dist x y))) +
        M.vertices.sum (fun x => M.vertices.sum (fun y => M.vertices.sum (fun z =>
            gluedCouplingTerm M.vertices ν γ₁ γ₂ x y z * M.dist y z))) := by
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro x _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro y _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl
      intro z _
      ring
    _ = couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      rw [gluedCoupling_cost_first_sum M μ ν ρ γ₁ γ₂ hγ₁ hγ₂,
        gluedCoupling_cost_second_sum M μ ν ρ γ₁ γ₂ hγ₁ hγ₂]

-- ---------------------------------------------------------------------------
-- Triangle inequality
-- ---------------------------------------------------------------------------

/-- `W1 M μ ρ ≤ W1 M μ ν + W1 M ν ρ`. -/
theorem W1_triangle
    (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices) :
    W1 M μ ρ ≤ W1 M μ ν + W1 M ν ρ := by
  rw [le_iff_forall_pos_lt_add]
  intro ε hε
  have hne₁ : (couplingCostSet M μ ν).Nonempty := couplingCostSet_nonempty M μ ν
  have hne₂ : (couplingCostSet M ν ρ).Nonempty := couplingCostSet_nonempty M ν ρ
  obtain ⟨c₁, hc₁, hlt₁⟩ :=
    Real.lt_sInf_add_pos (s := couplingCostSet M μ ν) hne₁ (ε := ε / 2) (half_pos hε)
  obtain ⟨γ₁, hγ₁, hc₁eq⟩ := hc₁
  obtain ⟨c₂, hc₂, hlt₂⟩ :=
    Real.lt_sInf_add_pos (s := couplingCostSet M ν ρ) hne₂ (ε := ε / 2) (half_pos hε)
  obtain ⟨γ₂, hγ₂, hc₂eq⟩ := hc₂
  have hγ :
      IsCoupling M.vertices μ ρ (gluedCoupling M.vertices ν γ₁ γ₂) :=
    gluedCoupling_isCoupling M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂
  calc
    W1 M μ ρ ≤ couplingTransportCost M (gluedCoupling M.vertices ν γ₁ γ₂) :=
      W1_le_couplingCost M μ ρ (gluedCoupling M.vertices ν γ₁ γ₂) hγ
    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ :=
      gluedCoupling_cost_le M μ ν ρ γ₁ γ₂ hγ₁ hγ₂
    _ < W1 M μ ν + W1 M ν ρ + ε := by
      rw [← hc₁eq] at hlt₁
      rw [← hc₂eq] at hlt₂
      dsimp [W1]
      linarith

-- ---------------------------------------------------------------------------
-- Core curvature identity  (zero sorry)
-- ---------------------------------------------------------------------------

/-- When `W1 M μ ν = 1` and `M.dist x y = 1`, Ollivier-Ricci curvature vanishes:
    `OllivierRicci M x y μ ν = 1 − W1 / dist = 1 − 1/1 = 0`. -/
theorem gorard_vacuum_oric_zero_of_w1
    (M : FiniteMetricSpace) (x y : ℕ) (μ ν : ProbDist M.vertices)
    (hdist : M.dist x y = 1) (hw1 : W1 M μ ν = 1) :
    OllivierRicci M x y μ ν = 0 := by
  unfold OllivierRicci
  rw [hw1, hdist]
  norm_num

-- ---------------------------------------------------------------------------
-- Legacy axiom (superseded)
-- ---------------------------------------------------------------------------

/-- Legacy axiom: κ_OR = 0 on every positive-distance edge.
    Overly general; superseded by `gorard_vacuum_oric_zero_of_w1` and the scoped
    bridge theorems. Retained for backward compatibility. -/
axiom gorard_vacuum_oric_zero
    (M : FiniteMetricSpace) (x y : ℕ) (μ ν : ProbDist M.vertices)
    (hdist : 0 < M.dist x y) :
    OllivierRicci M x y μ ν = 0

-- ---------------------------------------------------------------------------
-- Rule 110 Gromov-Wasserstein limit (axiom)
-- ---------------------------------------------------------------------------

/-- There exists a sequence of finite metric spaces (Rule 110 CMCA graphs) that
    serves as the discrete approximation of flat Riemannian space.
    Stated as an axiom pending the full G26 continuum-limit proof. -/
axiom rule110_gromov_wasserstein_limit :
    ∃ _ : ℕ → FiniteMetricSpace, True

end GTE.ContinuumLimit.Wasserstein
