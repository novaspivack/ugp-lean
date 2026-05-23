import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Real.Basic

namespace GTE.Spacetime.Spectral

/-!
# Degree-Normalized Random-Walk Heat Kernel

The companion `UgpLean.Spacetime.SpectralDimension` introduces an alternative
normalization `P := A / |V|` for didactic purposes. That normalization does not
match the physics convention for a random walk on a regular graph: the standard
random-walk operator on a `d`-regular graph is `P := A / d`, which is row-stochastic
(every row sums to 1) and produces the diffusive heat-kernel scaling
`K_n ~ C · n^{-d_s/2}` in the thermodynamic limit.

This module supplies the physics-standard degree-normalized definitions used in
the thermodynamic-limit spectral-dimension theorem. They are deliberately kept
in a separate namespace from the existing `spectralDimension` so neither
definition is silently overwritten by the other.

## Outline

* `degreeNormalizedAdjacencyStep G d` — the row-stochastic operator `(1/d) · A` for a
  `d`-regular simple graph `G`.
* `physicalHeatKernelReturn G d n v` — diagonal entry `((1/d)·A)^n` at `v`.
* `physicalHeatKernelReturnAvg G d n` — graph-averaged diagonal heat-kernel.
* `physicalSpectralDimensionLogRatio G d n` — the scaling-law sequence
  `log K_n / log n`.

These objects compute the physical heat-kernel return probability for the standard
random walk and feed the thermodynamic-limit spectral-dimension proof in
`HeatKernelLaplace.lean` and `SpectralDimensionFromAsymptotic.lean`.
-/

section
variable {V : Type*} [Fintype V] [DecidableEq V]

/-- `P := (1/d) · A`: the row-stochastic random-walk operator on a `d`-regular
    simple graph, where `d` is the (common) vertex degree.

    For a `d`-regular graph this is the canonical Markov chain associated with
    the simple random walk: from any vertex, jump uniformly to one of the `d`
    neighbours. -/
noncomputable def degreeNormalizedAdjacencyStep
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) : Matrix V V ℝ :=
  d⁻¹ • G.adjMatrix ℝ

/-- Diagonal heat-kernel return amplitude `((1/d)·A)^n` at vertex `v`.

    Equivalently, the probability that the `d`-regular random walk starting at
    `v` returns to `v` after exactly `n` steps. -/
noncomputable def physicalHeatKernelReturn
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (n : ℕ) (v : V) : ℝ :=
  (degreeNormalizedAdjacencyStep G d ^ n) v v

/-- Vertex-averaged diagonal heat-kernel:
    `(1/|V|) · Σ_v ((1/d)·A)^n vv = (1/|V|) · tr(((1/d)·A)^n)`.

    For a vertex-transitive (e.g. Cayley) graph this equals the diagonal
    `physicalHeatKernelReturn` at any fixed vertex. -/
noncomputable def physicalHeatKernelReturnAvg
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (n : ℕ) : ℝ :=
  (∑ v, physicalHeatKernelReturn G d n v) / Fintype.card V

/-- Scaling-law log ratio `log K_n / log n` for the physical (degree-normalized)
    heat kernel.

    The `if 1 < n` guard mirrors the existing
    `GTE.Spacetime.spectralDimensionLogRatio` and avoids `log 1 = 0` and
    `log 0` corner cases at the start of the sequence. -/
noncomputable def physicalSpectralDimensionLogRatio
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (n : ℕ) : ℝ :=
  if 1 < n then Real.log (physicalHeatKernelReturnAvg G d n) / Real.log n else 0

end

end GTE.Spacetime.Spectral
