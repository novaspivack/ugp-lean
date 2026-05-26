import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import UgpLean.Spacetime.SpectralDimension
import UgpLean.Spacetime.Spectral.DegreeNormalized
import UgpLean.Spacetime.Spectral.HeatKernelFourier

namespace GTE.Spacetime.Spectral

open Filter Topology
open GTE.Spacetime

/-!
# Heat-Kernel Laplace Asymptotic for the Periodic 3D f_MDL Causal Graph

This module records the **single analytical statement** required to upgrade the
periodic 3D f_MDL causal graph's spectral dimension from a structural (algebraic
Cayley-ℤ⁴) result to a thermodynamic-limit theorem of the form
`log K_n / log n → −2`.

## The statement

For the sequence of periodic causal graphs `CausalGraphPeriodic L L` (a Cayley
graph of `(ℤ/Lℤ)³ × (ℤ/(L+1)ℤ)` — asymptotically `(ℤ/Lℤ)⁴` — with the standard
twenty-element generating set `S₄`), the diagonal heat kernel of the
degree-normalized simple random walk satisfies the diffusive scaling

```
L⁴ · K_{L²}(G_L) → C  > 0  as L → ∞.
```

Equivalently: in the joint thermodynamic limit `L → ∞`, `n = L²`, the heat-kernel
return amplitude obeys `K_n ~ C · L⁻⁴ = C · n⁻²`, the universal four-dimensional
diffusive heat-kernel asymptotic.

## Why this is the right (and only) analytical input

Spectral dimension is fundamentally an asymptotic statement about the heat kernel
of an infinite or thermodynamically growing graph. For any *fixed* finite Cayley
graph the heat kernel decays exponentially (degree-normalized random walks mix
to the uniform distribution in `O(L²)` steps and stay there). The polynomial
scaling `K_n ~ const · n^{-d_s/2}` only emerges in the joint limit, where the
discrete Fourier sum

```
K_n = |G|⁻¹ Σ_k (λ_k / d)ⁿ  ,    λ_k = Σ_{s ∈ S} χ_k(s)
```

is well-approximated by a continuum Gaussian integral over the Brillouin zone.
Near `k = 0` the eigenvalues satisfy `λ_k / d = 1 − c · ‖k_phys‖² + O(‖k_phys‖⁴)`
with `c > 0`; the Laplace method on `ℝ⁴` then yields the four-dimensional
Gaussian integral and the asserted polynomial scaling.

## Mathlib status

Mathlib 4.29.1 does **not** yet contain:

* a finite-abelian-group discrete-Fourier framework with character orthogonality
  packaged for Cayley graph adjacency matrices;
* a Laplace-method / heat-kernel asymptotic on the discrete torus `(ℤ/Lℤ)ᵈ`;
* a Riemann-sum-to-integral convergence theorem at the level of generality needed
  to bridge the discrete Fourier sum to the continuous Gaussian integral.

These are well-defined, independent analytical statements about real sequences
and oscillatory sums; none of them depends on the framework's spectral
dimension definition. The proof of
`causal_graph_heat_kernel_diffusive_asymptotic` is therefore a genuine open
analytical gap relative to Mathlib's current state, **not** a circular
restatement of the spectral dimension theorem.

When Mathlib gains either:

  (a) discrete Fourier analysis on `(ZMod n)ᵈ` with the eigenvalue formula for
      finite abelian Cayley adjacency operators, or
  (b) a heat-kernel-asymptotic theorem on the discrete torus,

this lemma will close to zero sorry by a direct DFT + Laplace argument.

## Scope of the sorry

The sorry below stands for the entire analytical chain:

1. *Eigenvalue formula* — the periodic causal Cayley adjacency operator is
   diagonalized by the dual characters of the abelian group
   `(ℤ/(L+1)ℤ) × (ℤ/Lℤ)³`. Eigenvalues
   `λ_k = 2 Σⱼ cos(2π k_j / L) + 2 cos(2π k_t / (L+1))
         + 4 cos(2π k_t / (L+1)) · Σⱼ cos(2π k_j / L)`
   with `λ_0 = 20`.
2. *Quadratic expansion* — near `k = 0`,
   `λ_k = 20 − (28π² k_t² / (L+1)² + 12π² ‖k_{xyz}‖² / L²) + O(‖k‖⁴)`.
   The quadratic form is positive-definite with explicit coefficients.
3. *Riemann-sum / Laplace* — the discrete sum
   `(1/|V|) Σ_k (λ_k / 20)^{L²}`
   converges in the limit `L → ∞` to the 4-dimensional Gaussian integral
   `(2π)⁻⁴ · ∫_{ℝ⁴} exp(−Q(u)/20) d⁴u · L⁻⁴`
   where `Q(u) = 28π² u_t² + 12π² (u_x² + u_y² + u_z²)`.
4. The constant `C > 0` is the explicit Gaussian factor.

Each step is a standard real-analysis result with a textbook proof. Their joint
formalization is a substantial Mathlib contribution and is the *only* gap
between the upstream algebraic machinery (`SpectralDimension`,
`DegreeNormalized`) and the thermodynamic-limit theorem.

## Independence from the goal

This asymptotic is not a restatement of `causal_graph_spectral_dim_thermodynamic_limit`:
the former is a positive-real-valued limit
`Tendsto (L⁴ · K_{L²}(G_L)) atTop (nhds C)` with `C > 0`, the latter is a
log-ratio limit
`Tendsto (log K_{L²}(G_L) / log (L²)) atTop (nhds (-2))`. The bridge between the
two is a purely real-analytic logarithm identity, supplied (zero sorry) by
`spectral_dim_log_ratio_tendsto_of_diffusive_asymptotic` in
`SpectralDimensionFromAsymptotic.lean`.
-/

/-- **The single analytical hypothesis**: the periodic 3D f_MDL causal graph
    obeys the four-dimensional diffusive heat-kernel asymptotic
    `L⁴ · K_{L²}(G_L) → C  > 0` as `L → ∞`, where `K_n(G_L)` is the
    vertex-averaged diagonal entry of the degree-normalized random-walk operator
    `(1/20) · A_{G_L}` raised to power `n`.

    This is the genuine analytical content of "spectral dimension equals 4"; see
    the file header for the mathematical reduction (DFT eigenvalues + Laplace
    method) and the precise Mathlib gap.

    The graph `CausalGraphPeriodic (L + 2) (L + 2)` is used to avoid the small-`L`
    edge cases (`L ≥ 2`, `T ≥ 1` are automatic). The asymptotic statement is
    independent of any finite-`L` shift in the indexing. -/
theorem causal_graph_heat_kernel_diffusive_asymptotic :
    ∃ C : ℝ, 0 < C ∧
      Tendsto
        (fun L : ℕ =>
          ((L : ℝ) + 2)^4 *
            physicalHeatKernelReturnAvg
              (CausalGraphPeriodic (L + 2) (L + 2)
                (by omega : 2 ≤ L + 2) (by omega : 1 ≤ L + 2))
              20 ((L + 2)^2))
        atTop (nhds C) :=
  causal_graph_heat_kernel_diffusive_asymptotic_fourier

/-- Convenience corollary: the positive heat-kernel value is eventually positive
    (a trivial consequence of the asymptotic limit `C > 0`). Used to feed the
    bridge theorem's positivity hypothesis. -/
theorem causal_graph_heat_kernel_diffusive_asymptotic_eventually_pos :
    ∃ C : ℝ, 0 < C ∧
      Tendsto
        (fun L : ℕ =>
          ((L : ℝ) + 2)^4 *
            physicalHeatKernelReturnAvg
              (CausalGraphPeriodic (L + 2) (L + 2)
                (by omega : 2 ≤ L + 2) (by omega : 1 ≤ L + 2))
              20 ((L + 2)^2))
        atTop (nhds C) ∧
      ∀ᶠ L : ℕ in atTop,
        0 < ((L : ℝ) + 2)^4 *
            physicalHeatKernelReturnAvg
              (CausalGraphPeriodic (L + 2) (L + 2)
                (by omega : 2 ≤ L + 2) (by omega : 1 ≤ L + 2))
              20 ((L + 2)^2) := by
  obtain ⟨C, hC, hLim⟩ := causal_graph_heat_kernel_diffusive_asymptotic
  refine ⟨C, hC, hLim, ?_⟩
  exact hLim.eventually (eventually_gt_nhds hC)

end GTE.Spacetime.Spectral
