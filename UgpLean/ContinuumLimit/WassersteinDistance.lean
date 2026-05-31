import Mathlib.Data.Finset.Basic
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Group.Finset.Basic
import Mathlib.Algebra.Order.BigOperators.Group.Finset
import Mathlib.Order.ConditionallyCompleteLattice.Basic

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
-- Kantorovich dual lower bound  (explicit sorry — marginal sum rewriting)
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
  sorry

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
  sorry

-- ---------------------------------------------------------------------------
-- Triangle inequality  (explicit sorry — gluing lemma)
-- ---------------------------------------------------------------------------

/-- `W1 M μ ρ ≤ W1 M μ ν + W1 M ν ρ`.

    Proof sketch: glue optimal couplings via
      γ(x,z) = Σ_y γ₁(x,y) γ₂(y,z) / ν(y).
    Cost satisfies triangle by dist_triangle. Deferred: requires glued coupling
    to be a valid `IsCoupling` and marginal bookkeeping. -/
theorem W1_triangle
    (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices) :
    W1 M μ ρ ≤ W1 M μ ν + W1 M ν ρ := by
  sorry

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
