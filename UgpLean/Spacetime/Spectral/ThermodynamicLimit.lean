import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import UgpLean.Spacetime.SpectralDimension
import UgpLean.Spacetime.Spectral.DegreeNormalized
import UgpLean.Spacetime.Spectral.HeatKernelLaplace
import UgpLean.Spacetime.Spectral.SpectralDimensionFromAsymptotic

namespace GTE.Spacetime.Spectral

open Filter Topology
open GTE.Spacetime

/-!
# Thermodynamic-Limit Spectral Dimension of the 3D f_MDL Causal Graph

This module combines the bridge (`SpectralDimensionFromAsymptotic.lean`, pure
real analysis, zero sorry) with the analytical Laplace asymptotic
(`HeatKernelLaplace.lean`, one documented sorry capturing the discrete-Fourier
/ Gaussian-integral content) to produce the **thermodynamic-limit spectral
dimension theorem** for the periodic 3D f_MDL causal graph.

## What this proves

For the sequence of periodic causal graphs `CausalGraphPeriodic (L+2) (L+2)`
(a Cayley graph of `(ℤ/(L+3)ℤ) × (ℤ/(L+2)ℤ)³`, asymptotically the 4-torus
`(ℤ/Lℤ)⁴` as `L → ∞`) equipped with the *physical* degree-normalized random walk
`P = (1/20)·A`, the scaling-law sequence

```
log K_{(L+2)²}(G_{L+2}) / log ((L+2)²)
```

converges to `−2` as `L → ∞`, where `K_n` is the vertex-averaged diagonal heat
kernel. By the spectral-dimension convention `d_s = −2 · lim (log K_n / log n)`,
this is the statement that the periodic 3D f_MDL causal graph has spectral
dimension **exactly 4** in the joint thermodynamic limit.

## Why this is the right statement

`d_s = 4` is intrinsically a thermodynamic-limit claim: heat-kernel diffusion
on the lattice exhibits the asymptotic `K_n ~ C · n^{-d_s/2}` only when both the
graph size `L → ∞` and the walk length `n = n(L)` grow at the diffusive scale
(here `n = L²`). For fixed finite `(L, T)`, the heat kernel of the
degree-normalized random walk decays exponentially after the mixing time
`τ ≈ L²`, so no real-valued limit of `log K_n / log n` exists at fixed graph
size. The thermodynamic-limit reformulation captures the genuine physical
content.

## Naming

The theorem is `causal_graph_spectral_dim_thermodynamic_limit` — role-based,
no spec / round / rank IDs in any identifier.

## Relationship to the historical algebraic theorem

The historical zero-sorry algebraic structure (`causal_graph_is_Z4_cayley`,
`causal_graph_periodic_translation_invariant` in
`UgpLean.Spacetime.SpectralDimension`) establishes that the periodic causal
graph is a Cayley graph of a finite abelian group of rank 4. The
thermodynamic-limit theorem is the analytical complement: the spectral
dimension extracted from heat-kernel diffusion equals the Cayley rank, in the
joint limit.

The historical `spectral_dim_cayley_Z4_eq_4 = 4` claim at *fixed* `(L, T)` is
mathematically false (the heat kernel decays exponentially, not polynomially,
at fixed graph size). That sorry is retained in
`UgpLean.Spacetime.SpectralDimension` as a documented honest mathematical-content
mismatch; `causal_graph_spectral_dim_thermodynamic_limit` below is the active
statement of "spectral dimension = 4 for the periodic 3D f_MDL causal graph".
-/

/-- **Spectral dimension of the 3D f_MDL causal graph in the thermodynamic limit
    equals 4.**

    Statement: for the sequence of periodic causal graphs
    `G_M = CausalGraphPeriodic M M` indexed by `M = L + 2 → ∞`, the physical
    (degree-normalized) heat-kernel return amplitude satisfies the scaling law

    ```
    log K_{M²}(G_M) / log (M²)  →  -2
    ```

    so the spectral dimension `d_s = -2 · lim (log K / log n)` equals `4`.

    Proof:
    * `causal_graph_heat_kernel_diffusive_asymptotic` (in `HeatKernelLaplace.lean`)
      supplies the diffusive heat-kernel asymptotic
      `(L+2)⁴ · K_{(L+2)²}(G_{L+2}) → C > 0` (single documented sorry — the genuine
      Mathlib-gap, see that file).
    * `spectral_dim_log_ratio_tendsto_of_diffusive_asymptotic` (in
      `SpectralDimensionFromAsymptotic.lean`) bridges that asymptotic to the
      logarithmic scaling-law limit `−2` (pure real-analysis, zero sorry).
    * The body below assembles those two pieces and unfolds
      `physicalSpectralDimensionLogRatio` for the relevant range.

    The eventual positivity of the amplified heat kernel (required as input to
    the bridge) is delivered by
    `causal_graph_heat_kernel_diffusive_asymptotic_eventually_pos`.

    The body of `causal_graph_spectral_dim_thermodynamic_limit` itself is
    sorry-free; the only `sorry` in the dependency graph is the documented
    Laplace-method asymptotic, which is the genuine analytical content of the
    physics statement. -/
theorem causal_graph_spectral_dim_thermodynamic_limit :
    Tendsto
      (fun L : ℕ =>
        physicalSpectralDimensionLogRatio
          (CausalGraphPeriodic (L + 2) (L + 2)
            (by omega : 2 ≤ L + 2) (by omega : 1 ≤ L + 2))
          20 ((L + 2)^2))
      atTop (nhds (-2)) := by
  obtain ⟨C, hC, hLim, hPos⟩ :=
    causal_graph_heat_kernel_diffusive_asymptotic_eventually_pos
  -- Apply the bridge with `M L = (L : ℝ) + 2` and `f L = (L+2)^4 * K_{(L+2)²}`.
  have hM_lim : Tendsto (fun L : ℕ => (L : ℝ) + 2) atTop atTop := by
    have h₁ : Tendsto (fun L : ℕ => (L : ℝ)) atTop atTop := tendsto_natCast_atTop_atTop
    simpa using h₁.atTop_add tendsto_const_nhds
  have hM_gt_one : ∀ᶠ L : ℕ in atTop, (1 : ℝ) < (L : ℝ) + 2 := by
    filter_upwards [eventually_ge_atTop (0 : ℕ)] with L hL
    have : (0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast hL
    linarith
  have hBridge :
      Tendsto
        (fun L : ℕ =>
          Real.log
              (((L : ℝ) + 2)^4 *
                  physicalHeatKernelReturnAvg
                    (CausalGraphPeriodic (L + 2) (L + 2)
                      (by omega : 2 ≤ L + 2) (by omega : 1 ≤ L + 2))
                    20 ((L + 2)^2)
                / ((L : ℝ) + 2)^4)
            / Real.log (((L : ℝ) + 2)^2))
        atTop (nhds (-2)) :=
    spectral_dim_log_ratio_tendsto_of_diffusive_asymptotic
      hC hM_lim hM_gt_one hPos hLim
  -- Now massage the bridge's conclusion into the form of
  -- `physicalSpectralDimensionLogRatio`.
  -- Step 1: `(((L+2)^4 * K) / (L+2)^4) = K`.
  have hSimp :
      (fun L : ℕ =>
          Real.log
              (((L : ℝ) + 2)^4 *
                  physicalHeatKernelReturnAvg
                    (CausalGraphPeriodic (L + 2) (L + 2)
                      (by omega : 2 ≤ L + 2) (by omega : 1 ≤ L + 2))
                    20 ((L + 2)^2)
                / ((L : ℝ) + 2)^4)
            / Real.log (((L : ℝ) + 2)^2))
        =ᶠ[atTop]
      (fun L : ℕ =>
          physicalSpectralDimensionLogRatio
            (CausalGraphPeriodic (L + 2) (L + 2)
              (by omega : 2 ≤ L + 2) (by omega : 1 ≤ L + 2))
            20 ((L + 2)^2)) := by
    filter_upwards [eventually_ge_atTop (0 : ℕ)] with L _
    -- ((L+2):ℝ)^4 ≠ 0
    have hLR : (0 : ℝ) < (L : ℝ) + 2 := by
      have : (0 : ℝ) ≤ (L : ℝ) := by exact_mod_cast Nat.zero_le L
      linarith
    have hLR4_ne : ((L : ℝ) + 2)^4 ≠ 0 := (pow_pos hLR 4).ne'
    have hCancel :
        ((L : ℝ) + 2)^4 *
            physicalHeatKernelReturnAvg
              (CausalGraphPeriodic (L + 2) (L + 2)
                (by omega : 2 ≤ L + 2) (by omega : 1 ≤ L + 2))
              20 ((L + 2)^2)
          / ((L : ℝ) + 2)^4
        = physicalHeatKernelReturnAvg
            (CausalGraphPeriodic (L + 2) (L + 2)
              (by omega : 2 ≤ L + 2) (by omega : 1 ≤ L + 2))
            20 ((L + 2)^2) := by
      field_simp
    -- (((L+2):ℝ)^2) equals ((L+2)^2 : ℕ → ℝ)
    have hCastPow : (((L : ℝ) + 2)^2) = (((L + 2)^2 : ℕ) : ℝ) := by push_cast; ring
    -- ((L+2)^2 : ℕ) > 1
    have hN_gt : 1 < ((L + 2)^2 : ℕ) := by
      have : 2 ≤ L + 2 := by omega
      have h4 : 4 ≤ (L + 2)^2 := by
        calc (L + 2)^2 ≥ 2^2 := Nat.pow_le_pow_left this 2
          _ = 4 := by norm_num
      omega
    -- Conclude: the bridge expression equals `physicalSpectralDimensionLogRatio …`
    -- on the right.
    unfold physicalSpectralDimensionLogRatio
    rw [if_pos hN_gt]
    rw [hCancel, hCastPow]
  exact hBridge.congr' hSimp

end GTE.Spacetime.Spectral
