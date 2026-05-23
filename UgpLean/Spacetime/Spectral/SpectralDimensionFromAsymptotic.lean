import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Algebra.Order.LiminfLimsup
import Mathlib.Topology.Instances.Real.Lemmas

namespace GTE.Spacetime.Spectral

open Filter Topology

/-!
# Spectral Dimension from Diffusive Heat-Kernel Asymptotic

Bridge from a diffusive heat-kernel asymptotic
`M⁴ · K_n(M) → C  > 0  as M → ∞ with n = M^β`
to the spectral-dimension scaling-law statement
`log K_n(M) / log n → -α/β`.

This module proves the bridge as a pure real-analysis fact about positive real
sequences and their logarithms. No graph theory is used; the input is an arbitrary
positive sequence `f : α → ℝ` with limit `C > 0` and a positive "size" sequence
`M : α → ℝ` tending to infinity. Specializing `α = 4`, `β = 2` recovers the
four-dimensional diffusive scaling that gives spectral dimension 4.

The size sequence `M` is parametric in the index `α` (with filter `l`) so the
result composes cleanly with shifted indexings such as `M = L + 2` (used in the
graph application to avoid `L ≥ 2` edge cases).

## Main result

* `spectral_dim_log_ratio_tendsto_of_diffusive_asymptotic` —
  if `f → C > 0`, `M → ∞`, and the obvious positivity conditions hold, then
    `log (f / M^4) / log (M^2) → -2`.
-/

/-- The algebraic identity (eventually): when `M > 1` and `f > 0`,
    `log (f / M^4) / log (M^2) = log f / (2 · log M) - 2`. -/
private lemma log_ratio_rewrite
    {α : Type*} {l : Filter α} {f M : α → ℝ}
    (hf_pos : ∀ᶠ x in l, 0 < f x)
    (hM_gt_one : ∀ᶠ x in l, (1 : ℝ) < M x) :
    ∀ᶠ x in l,
      Real.log (f x / (M x)^4) / Real.log ((M x)^2) =
        Real.log (f x) / (2 * Real.log (M x)) - 2 := by
  filter_upwards [hf_pos, hM_gt_one] with x hfx hMx
  have hMx_pos : 0 < M x := lt_trans zero_lt_one hMx
  have hMx2_pos : 0 < (M x)^2 := pow_pos hMx_pos 2
  have hMx4_pos : 0 < (M x)^4 := pow_pos hMx_pos 4
  have hlogMx_pos : 0 < Real.log (M x) := Real.log_pos hMx
  have hlogMx_ne : Real.log (M x) ≠ 0 := ne_of_gt hlogMx_pos
  have h2logMx_ne : 2 * Real.log (M x) ≠ 0 := mul_ne_zero (by norm_num) hlogMx_ne
  -- log(f / M^4) = log f - log(M^4) = log f - 4 log M
  -- log(M^2) = 2 log M
  rw [Real.log_div hfx.ne' hMx4_pos.ne',
      show ((M x)^2 : ℝ) = (M x)^(2 : ℕ) from rfl,
      show ((M x)^4 : ℝ) = (M x)^(4 : ℕ) from rfl,
      Real.log_pow, Real.log_pow]
  field_simp
  ring

/-- **Bridge theorem.**

    Given:

    * a positive sequence `f → C > 0` (representing the *amplified* heat kernel
      `M⁴ · K_{M^β}(G_M)`),
    * a size sequence `M → ∞` eventually exceeding 1,

    the scaling-law sequence
    `log (f / M⁴) / log (M²)`
    converges to `−2`.

    Equivalently: a diffusive heat-kernel asymptotic `K_n ~ C · M⁻⁴` with `n = M²`
    gives spectral dimension `4` in the convention `d_s = −2 · lim log K_n / log n`.

    Pure real-analysis argument; zero sorry. -/
theorem spectral_dim_log_ratio_tendsto_of_diffusive_asymptotic
    {α : Type*} {l : Filter α}
    {f M : α → ℝ} {C : ℝ} (hC : 0 < C)
    (hM_lim : Tendsto M l atTop)
    (hM_gt_one : ∀ᶠ x in l, (1 : ℝ) < M x)
    (hf_pos : ∀ᶠ x in l, 0 < f x)
    (hf_lim : Tendsto f l (nhds C)) :
    Tendsto
      (fun x => Real.log (f x / (M x)^4) / Real.log ((M x)^2))
      l (nhds (-2)) := by
  -- (1) `log (f x) → log C` (finite), via continuity of `log` away from 0.
  have h_log_f : Tendsto (fun x => Real.log (f x)) l (nhds (Real.log C)) :=
    (Real.continuousAt_log (ne_of_gt hC)).tendsto.comp hf_lim
  -- (2) `log (M x) → ∞`, then `2 · log (M x) → ∞`.
  have h_log_M : Tendsto (fun x => Real.log (M x)) l atTop :=
    Real.tendsto_log_atTop.comp hM_lim
  have h_2log_M : Tendsto (fun x => 2 * Real.log (M x)) l atTop :=
    Tendsto.const_mul_atTop (by norm_num : (0 : ℝ) < 2) h_log_M
  -- (3) finite / ∞ → 0.
  have h_frac_zero :
      Tendsto (fun x => Real.log (f x) / (2 * Real.log (M x))) l (nhds 0) :=
    h_log_f.div_atTop h_2log_M
  -- (4) `0 - 2 = -2`.
  have h_minus :
      Tendsto (fun x => Real.log (f x) / (2 * Real.log (M x)) - 2)
        l (nhds (0 - 2 : ℝ)) :=
    h_frac_zero.sub_const 2
  have h_target :
      Tendsto (fun x => Real.log (f x) / (2 * Real.log (M x)) - 2)
        l (nhds (-2 : ℝ)) := by
    simpa using h_minus
  -- (5) The original expression is eventually equal to the rewritten one.
  have hEq :
      (fun x => Real.log (f x / (M x)^4) / Real.log ((M x)^2))
        =ᶠ[l]
      (fun x => Real.log (f x) / (2 * Real.log (M x)) - 2) :=
    log_ratio_rewrite hf_pos hM_gt_one
  exact h_target.congr' hEq.symm

end GTE.Spacetime.Spectral
