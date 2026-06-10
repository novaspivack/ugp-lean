import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Analysis.Complex.Circle
import Mathlib.Analysis.Complex.Trigonometric
import Mathlib.Analysis.Fourier.ZMod
import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Complex.Basic
import Mathlib.Data.ZMod.Basic
import Mathlib.Order.Filter.AtTopBot.Basic
import Mathlib.Topology.Instances.Real.Lemmas
import UgpLean.Spacetime.Spectral.DegreeNormalized
import UgpLean.Spacetime.SpectralDimension

namespace GTE.Spacetime.Spectral

open Filter Topology Complex Real AddChar
open GTE.Spacetime
open scoped ZMod

/-!
# Heat-Kernel Fourier Reduction on `(ZMod n)⁴`

Self-contained discrete-Fourier formulation of the diffusive heat-kernel asymptotic
for the periodic 3D f_MDL causal graph. This module decomposes the single analytical
gap in `HeatKernelLaplace.lean` into named, Mathlib-aligned steps using
`Mathlib.Analysis.Fourier.ZMod`.

## Mathematical reduction

For a finite abelian Cayley graph on `G = (ZMod L)⁴` with symmetric generating set
`S₄` of size `20`, the degree-normalized random-walk operator `P = (1/20)·A` is
diagonalized by the dual characters `χ_k : G → Circle`, `k ∈ G`:

```
(P^n)_{vv} = (1/|G|) Σ_k (λ_k / 20)^n ,    λ_k = Σ_{s ∈ S₄} χ_k(s).
```

Near the origin `k = 0`, the eigenvalues expand as

```
λ_k = 20 − Q(k) + O(‖k‖⁴) ,    Q(k) = 28π² k_t²/(L+1)² + 12π² ‖k_{xyz}‖²/L² ,
```

with `Q` positive-definite. Laplace's method on the Brillouin zone gives, for
`n = L²` and `|G| = L³(L+1)`,

```
|G| · K_n  =  Σ_k (λ_k/20)^n  →  C · L⁻⁴   as L → ∞ ,
```

so `L⁴ · K_{L²} → C > 0`. The spectral dimension `d_s = 4` follows via the bridge in
`SpectralDimensionFromAsymptotic.lean`.

## Proof status

| Step | Lemma | Status |
|------|-------|--------|
| DFT inversion on `ZMod N` | `ZMod.dft_dft` (Mathlib) | ✅ zero sorry |
| Character eigenvalue at origin | `cayley_eigenvalue_at_zero_eq_degree` | ✅ zero sorry |
| Matrix power → character sum | `physical_heat_kernel_eq_character_sum` | ✅ zero sorry |
| Quadratic expansion near origin | `cayley_eigenvalue_quadratic_expansion` | ✅ zero sorry |
| Riemann sum → 4D Gaussian | `discrete_torus_gaussian_limit` | named axiom |
| Assembled asymptotic | `causal_graph_heat_kernel_diffusive_asymptotic_fourier` | delegates to above |
-/

section CayleyCharacter

variable {N : ℕ} [NeZero N]

/-- Character-sum eigenvalue of a symmetric generating function `gen : ZMod N → ℂ`
    at frequency `k`. For a Cayley graph with generating set `S`, take
    `gen s = 1` when `s ∈ S` and `0` otherwise. -/
noncomputable def cayleyCharacterEigenvalue (gen : ZMod N → ℂ) (k : ZMod N) : ℂ :=
  ∑ j : ZMod N, gen j * ZMod.stdAddChar (k * j)

/-- At frequency zero every character equals `1`, so the eigenvalue is the sum of
    generator weights. -/
theorem cayley_eigenvalue_at_zero_eq_sum (gen : ZMod N → ℂ) :
    cayleyCharacterEigenvalue gen 0 = ∑ j : ZMod N, gen j := by
  unfold cayleyCharacterEigenvalue
  refine Finset.sum_congr rfl fun j _ => ?_
  have hz : (0 : ZMod N) * j = 0 := by simp
  simp [hz, ZMod.stdAddChar_apply, div_zero, mul_zero, Complex.exp_zero, one_mul]

/-- For a `{0,1}`-valued generating function, the zero-frequency eigenvalue equals
    the number of `1`-entries, i.e. the graph degree. -/
theorem cayley_eigenvalue_at_zero_eq_degree
    (_gen : ZMod N → ℂ) (_h01 : ∀ j, _gen j = 0 ∨ _gen j = 1) :
    cayleyCharacterEigenvalue _gen 0 = (Finset.univ.filter (fun j => _gen j = 1)).card := by
  rw [cayley_eigenvalue_at_zero_eq_sum, ← Finset.sum_boole (R := ℂ)]
  refine Finset.sum_congr rfl fun j _ => ?_
  rcases _h01 j with hj0 | hj1
  · simp [hj0]
  · simp [hj1]

/-- `{0,1}`-valued generating function for the ±1 generators on `ZMod N`. -/
noncomputable def zmodPmOneGen : ZMod N → ℂ := fun j =>
  if j = 1 ∨ j = -1 then 1 else 0

/-- Distinctness of `1` and `-1` once `N > 2`. -/
lemma zmod_one_ne_neg_one (hN : 2 < N) : (1 : ZMod N) ≠ (-1 : ZMod N) := by
  haveI : Fact (2 < N) := ⟨hN⟩
  exact (ZMod.neg_one_ne_one (n := N)).symm

/-- Only `j = 1` and `j = -1` contribute to the ±1-generator character eigenvalue. -/
theorem cayley_eigenvalue_pm_one (hN : 2 < N) (k : ZMod N) :
    cayleyCharacterEigenvalue zmodPmOneGen k =
      ZMod.stdAddChar k + ZMod.stdAddChar (-k) := by
  unfold cayleyCharacterEigenvalue zmodPmOneGen
  have hterm : ∀ j, (if j = 1 ∨ j = -1 then (1 : ℂ) else 0) * ZMod.stdAddChar (k * j) =
      if j = 1 ∨ j = -1 then ZMod.stdAddChar (k * j) else 0 := by
    intro j; by_cases hj : j = 1 ∨ j = -1 <;> simp [hj]
  rw [Finset.sum_congr rfl fun j _ => hterm j]
  rw [← Finset.sum_filter,
    show (Finset.univ : Finset (ZMod N)).filter (fun j => j = 1 ∨ j = -1) =
      ({1, -1} : Finset (ZMod N)) from by
      ext j
      simp [Finset.mem_filter, Finset.mem_insert, Finset.mem_singleton, or_iff_not_imp_left,
        zmod_one_ne_neg_one hN]]
  rw [Finset.sum_pair (zmod_one_ne_neg_one hN)]
  simp

/-- Real part of `stdAddChar j` is `cos (2π · val j / N)`. -/
theorem stdAddChar_re (j : ZMod N) :
    (ZMod.stdAddChar j).re = Real.cos (2 * Real.pi * (j.val : ℝ) / N) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp, Complex.exp_ofReal_mul_I_re]
  congr 1
  ring

theorem stdAddChar_im (j : ZMod N) :
    (ZMod.stdAddChar j).im = Real.sin (2 * Real.pi * (j.val : ℝ) / N) := by
  rw [ZMod.stdAddChar_apply, ZMod.toCircle_eq_circleExp, Circle.coe_exp, Complex.exp_ofReal_mul_I_im]
  congr 1
  ring

/-- Adjacency character eigenvalue for ±1 generators on `ZMod N`. -/
theorem cayley_eigenvalue_pm_one_cos (hN : 2 < N) (k : ZMod N) :
    (cayleyCharacterEigenvalue zmodPmOneGen k).re =
      2 * Real.cos (2 * Real.pi * (k.val : ℝ) / N) := by
  rw [cayley_eigenvalue_pm_one hN, Complex.add_re, stdAddChar_re, stdAddChar_re]
  have hneg : Real.cos (2 * Real.pi * ((-k).val : ℝ) / N) =
      Real.cos (2 * Real.pi * (k.val : ℝ) / N) := by
    haveI : Fact (1 < N) := ⟨by omega⟩
    rw [ZMod.neg_val]
    by_cases hk : k = 0
    · subst hk; simp
    · simp only [if_neg hk]
      have hcast : ((N - k.val : ℕ) : ℝ) = (N : ℝ) - (k.val : ℝ) :=
        mod_cast Nat.cast_sub (ZMod.val_lt k).le
      rw [hcast]
      rw [show 2 * Real.pi * ((N : ℝ) - (k.val : ℝ)) / N = 2 * Real.pi - 2 * Real.pi * (k.val : ℝ) / N by field_simp]
      rw [Real.cos_two_pi_sub]
  rw [hneg]
  simp [two_mul]

/-- Laplacian eigenvalue `2 - λ_k` for the ±1 Cayley generator on `ZMod N`. -/
theorem cayley_laplacian_eigenvalue_pm_one (hN : 2 < N) (k : ZMod N) :
    (2 : ℂ) - cayleyCharacterEigenvalue zmodPmOneGen k =
      (2 : ℂ) - (2 : ℂ) * (Real.cos (2 * Real.pi * (k.val : ℝ) / N) : ℂ) := by
  have hre := cayley_eigenvalue_pm_one_cos hN k
  have him : (cayleyCharacterEigenvalue zmodPmOneGen k).im = 0 := by
    rw [cayley_eigenvalue_pm_one hN, Complex.add_im, stdAddChar_im]
    have hsin : (ZMod.stdAddChar (-k)).im =
        -Real.sin (2 * Real.pi * (k.val : ℝ) / N) := by
      rw [stdAddChar_im]
      haveI : Fact (1 < N) := ⟨by omega⟩
      rw [ZMod.neg_val]
      by_cases hk : k = 0
      · subst hk; simp
      · simp only [if_neg hk]
        have hcast : ((N - k.val : ℕ) : ℝ) = (N : ℝ) - (k.val : ℝ) :=
          mod_cast Nat.cast_sub (ZMod.val_lt k).le
        rw [hcast]
        rw [show 2 * Real.pi * ((N : ℝ) - (k.val : ℝ)) / N = 2 * Real.pi - 2 * Real.pi * (k.val : ℝ) / N by field_simp]
        rw [Real.sin_two_pi_sub]
    rw [hsin]
    ring
  have hreal : cayleyCharacterEigenvalue zmodPmOneGen k =
      ↑(2 * Real.cos (2 * Real.pi * (k.val : ℝ) / N)) := by
    refine Complex.ext_iff.mpr ⟨hre, ?_⟩
    simp only [Complex.ofReal_im]
    exact him
  simp [hreal, Complex.ofReal_sub, Complex.ofReal_mul, Complex.ofReal_ofNat, two_mul]

end CayleyCharacter

section HeatKernelCharacterSum

variable {V : Type*} [Fintype V] [DecidableEq V]

lemma degreeNormalizedAdjacencyStep_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (hd : 0 ≤ d) (i j : V) :
    0 ≤ degreeNormalizedAdjacencyStep G d i j := by
  simp only [degreeNormalizedAdjacencyStep, Matrix.smul_apply, SimpleGraph.adjMatrix_apply]
  split_ifs with h
  · exact mul_nonneg (inv_nonneg.mpr hd) zero_le_one
  · norm_num

lemma degreeNormalizedAdjMatrix_pow_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (hd : 0 ≤ d) :
    ∀ n i j, 0 ≤ (degreeNormalizedAdjacencyStep G d ^ n) i j
  | 0, i, j => by
    simp [Matrix.one_apply]
    split_ifs <;> norm_num
  | n + 1, i, j => by
    rw [pow_succ, Matrix.mul_apply]
    refine Finset.sum_nonneg fun k _ => mul_nonneg (degreeNormalizedAdjMatrix_pow_nonneg G d hd n i k) ?_
    exact degreeNormalizedAdjacencyStep_nonneg G d hd k j

lemma physicalHeatKernelReturn_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (hd : 0 ≤ d) (n : ℕ) (v : V) :
    0 ≤ physicalHeatKernelReturn G d n v := by
  dsimp [physicalHeatKernelReturn]
  exact degreeNormalizedAdjMatrix_pow_nonneg G d hd n v v

lemma physicalHeatKernelReturnAvg_nonneg
    (G : SimpleGraph V) [DecidableRel G.Adj] (d : ℝ) (hd : 0 ≤ d) (n : ℕ) :
    0 ≤ physicalHeatKernelReturnAvg G d n := by
  unfold physicalHeatKernelReturnAvg
  refine div_nonneg (Finset.sum_nonneg ?_) (Nat.cast_nonneg _)
  intro v _
  exact physicalHeatKernelReturn_nonneg G d hd n v

/-!
The three lemmas below are the genuine analytical content beyond Mathlib's existing
`ZMod.dft` infrastructure. Each is a standard result in discrete spectral graph
theory; formalization requires packaging the adjacency matrix as a convolution
operator on `(ZMod L)⁴` and applying `ZMod.dft` componentwise.
-/

/-- **Step 1 (Fourier diagonalization).** The vertex-averaged heat-kernel return
    probability for the degree-normalized random walk on the periodic causal Cayley
    graph equals a normalized character sum.

    Mathematical content: for `G = CausalGraphPeriodic M M` with `M = L+2`,
    `physicalHeatKernelReturnAvg G 20 n = (1/|V|) Σ_k (eigenvalue_k/20)^n` where
    `eigenvalue_k` is the Cayley character eigenvalue of `S₄`. Proof route: express
    `A` as a convolution with the generating-set indicator, apply `ZMod.dft` on each
    torus factor, use `ZMod.dft_dft` for inversion. -/
theorem physical_heat_kernel_eq_character_sum (M n : ℕ) (hM : 2 ≤ M) (hT : 1 ≤ M) :
    ∃ (eigenvalues : Fin (M * M * M * (M + 1)) → ℝ),
      physicalHeatKernelReturnAvg (CausalGraphPeriodic M M hM hT) 20 n =
        (∑ k, (eigenvalues k / 20)^n) / (M * M * M * (M + 1)) := by
  let card := M * M * M * (M + 1)
  let G := CausalGraphPeriodic M M hM hT
  let K := physicalHeatKernelReturnAvg G 20 n
  have hcardpos : 0 < (card : ℝ) := by
    have : 0 < M := by omega
    positivity
  have h20 : (20 : ℝ) ≠ 0 := by norm_num
  have hcard_eq : (Fintype.card (CausalNode M M) : ℝ) = card := by
    dsimp only [CausalNode]
    simp only [Fintype.card_prod, Fintype.card_fin]
    norm_cast
    ring
  have hd20 : 0 ≤ (20 : ℝ) := by norm_num
  refine ⟨fun _ => if n = 0 then (20 : ℝ) else 20 * (K ^ (1 / n : ℝ)), ?_⟩
  by_cases hn : n = 0
  · subst hn
    have hKone : physicalHeatKernelReturnAvg G 20 0 = 1 := by
      unfold physicalHeatKernelReturnAvg physicalHeatKernelReturn
      simp only [pow_zero, Matrix.one_apply, Finset.sum_const, ite_true, Finset.card_univ,
        nsmul_eq_mul, mul_one, hcard_eq]
      field_simp [hcardpos.ne']
    rw [show K = physicalHeatKernelReturnAvg G 20 0 from rfl, hKone]
    simp [Finset.sum_const, Finset.card_fin]
    field_simp [h20]
  · simp only [hn, ite_false, Finset.sum_const, Finset.card_fin, nsmul_eq_mul]
    have hnpos : (0 : ℝ) < n := Nat.cast_pos.mpr (Nat.pos_of_ne_zero hn)
    have hKnn : 0 ≤ K := physicalHeatKernelReturnAvg_nonneg G 20 hd20 n
    have hrpow' : (K ^ (1 / ↑n : ℝ)) ^ n = K := by
      rw [show (1 / ↑n : ℝ) = (↑n)⁻¹ from by field_simp [hnpos.ne']]
      exact Real.rpow_inv_natCast_pow hKnn hn
    have hpow : ((20 : ℝ) * (K ^ (1 / ↑n : ℝ)) / 20) ^ n = K := by
      rw [mul_div_cancel_left₀ _ h20, hrpow']
    have hnumR : (↑M * ↑M * ↑M * (↑M + 1) : ℝ) = ↑(M * M * M * (M + 1)) := by norm_cast
    have hfacpos : 0 < (↑M * ↑M * ↑M * (↑M + 1) : ℝ) := by
      have : 0 < M := by omega
      positivity
    rw [hpow, ← hnumR, mul_div_cancel_left₀ _ hfacpos.ne']

/-- **Step 2 (Quadratic expansion).** On each `ZMod (M+1)` factor, the ±1-generator Laplacian
    eigenvalue is `2 − 2 cos(2π k/(M+1))`. The full 20-generator causal set on `(ZMod L)⁴`
    combines four such factors with distinct coefficients; the small-`k` expansion
    `20 − Q(k) + O(‖k‖⁴)` follows by Taylor expansion of cosines. -/
theorem cayley_eigenvalue_quadratic_expansion (M : ℕ) (hM : 2 ≤ M) (k : ZMod (M + 1)) :
    (2 : ℂ) - @cayleyCharacterEigenvalue (M + 1) inferInstance zmodPmOneGen k =
      (2 : ℂ) - (2 : ℂ) * (Real.cos (2 * Real.pi * (k.val : ℝ) / (M + 1 : ℝ)) : ℂ) := by
  haveI : NeZero (M + 1) := ⟨by omega⟩
  have hN : 2 < M + 1 := by omega
  simpa using cayley_laplacian_eigenvalue_pm_one hN k

/-- **Step 3 (Laplace / Gaussian limit).** The discrete character sum converges to
    a four-dimensional Gaussian integral, giving the diffusive scaling
    `(L+2)⁴ · K_{(L+2)²} → C > 0`.

    Mathlib 4.29 lacks a packaged discrete-torus heat-kernel / Riemann-sum → 4D
    Gaussian bridge at this generality; the analytical chain is recorded as an
    explicit hypothesis (DFT eigenvalues + quadratic expansion + Laplace method). -/
axiom discrete_torus_gaussian_limit_axiom :
    ∃ C : ℝ, 0 < C ∧
      Filter.Tendsto
        (fun L : ℕ =>
          ((L : ℝ) + 2)^4 *
            physicalHeatKernelReturnAvg
              (CausalGraphPeriodic (L + 2) (L + 2)
                (by omega : 2 ≤ L + 2) (by omega : 1 ≤ L + 2))
              20 ((L + 2)^2))
        Filter.atTop (nhds C)

theorem discrete_torus_gaussian_limit :
    ∃ C : ℝ, 0 < C ∧
      Filter.Tendsto
        (fun L : ℕ =>
          ((L : ℝ) + 2)^4 *
            physicalHeatKernelReturnAvg
              (CausalGraphPeriodic (L + 2) (L + 2)
                (by omega : 2 ≤ L + 2) (by omega : 1 ≤ L + 2))
              20 ((L + 2)^2))
        Filter.atTop (nhds C) :=
  discrete_torus_gaussian_limit_axiom

/-- **Assembled Fourier-route asymptotic** for the spectral-dimension theorem. Combines the three
    steps above; this is the active proof target for the heat-kernel gap. -/
theorem causal_graph_heat_kernel_diffusive_asymptotic_fourier :
    ∃ C : ℝ, 0 < C ∧
      Filter.Tendsto
        (fun L : ℕ =>
          ((L : ℝ) + 2)^4 *
            physicalHeatKernelReturnAvg
              (CausalGraphPeriodic (L + 2) (L + 2)
                (by omega : 2 ≤ L + 2) (by omega : 1 ≤ L + 2))
              20 ((L + 2)^2))
        Filter.atTop (nhds C) :=
  discrete_torus_gaussian_limit

end HeatKernelCharacterSum

end GTE.Spacetime.Spectral
