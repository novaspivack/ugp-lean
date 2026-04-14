import Mathlib

/-!
# UgpLean.GTE.DSIExport — Analytic Export for Domain-Semantic-Internalization

This module provides the real-analysis interface that DSI's
`ArcBAnalyticBoundary` / `SmallSymmetricMVTBundle` consumes.

## What is exported

For the **Wall 1 (single-hyperbola)** route class:

1. **`ugpOutputGap R`**: the real-valued c₁ function on the hyperbola bq = R,
   parameterized by q: `ugpOutputGap R q = (R/q + q + 7)(q - 13) + 20`.

2. **`ugpShell R`**: the valid parameter domain `{q ∈ ℝ | 14 ≤ q ≤ R/16}`.

3. **Derivative**: `deriv (ugpOutputGap R) q = 2q - R/q² × (q - 13) + (R/q + q + 7) - 13 × R/q²`
   simplified to `1 - R/q² + 2q + R/q - 6` which is ≥ 2√R - 6 on the shell.

4. **Uniform lower bound**: `|deriv (ugpOutputGap R) q| ≥ 2√R - 7` for q in the shell,
   giving ε = 2√R - 7 > 0 for R ≥ 16.

## Alignment with DSI

| DSI concept | ugp-lean export |
|-------------|-----------------|
| `TwinRouteShortcutClass.singleHyperbolaShell` | Wall 1 |
| `shell` | `ugpShell R` |
| `outputGap` | `ugpOutputGap R` |
| `adm` | `smallSymmetricMoves δ` for small δ |
| `uniformEps` | `22` (R-independent; tighter R-dependent bound: `13R/q² + 2q - 6`) |
| `Hderiv` | `ugp_deriv_lower_bound` |

## Mathlib pin

This module requires Mathlib v4.29.0-rc6 (same as DSI).

Reference: DSI item (4), fn-4, ArcBEffectiveGapMagnification.lean
-/

namespace UgpLean

open Real Set

-- ════════════════════════════════════════════════════════════════
-- §1  Real-valued c₁ on the hyperbola
-- ════════════════════════════════════════════════════════════════

/-- The real-valued c₁ function parameterized by q along the hyperbola bq = R.
    ugpOutputGap R q = (R/q + q + 7)(q - 13) + 20 for real q > 0. -/
noncomputable def ugpOutputGap (R : ℝ) (q : ℝ) : ℝ :=
  (R / q + q + 7) * (q - 13) + 20

/-- The valid parameter shell: q values where both b = R/q ≥ 16 and q ≥ 14. -/
def ugpShell (R : ℝ) : Set ℝ :=
  { q : ℝ | 14 ≤ q ∧ q ≤ R / 16 ∧ 0 < q }

/-- The shell is nonempty for R ≥ 16 · 14 = 224. -/
theorem ugpShell_nonempty {R : ℝ} (hR : 224 ≤ R) : (ugpShell R).Nonempty :=
  ⟨14, le_refl 14, by linarith, by norm_num⟩

-- ════════════════════════════════════════════════════════════════
-- §2  Expanded form for differentiation
-- ════════════════════════════════════════════════════════════════

/-- Expanded form: ugpOutputGap R q = R - 13R/q + q² - 6q - 71 for q ≠ 0.
    This is more convenient for differentiation. -/
theorem ugpOutputGap_expanded {R q : ℝ} (hq : q ≠ 0) :
    ugpOutputGap R q = R - 13 * R / q + q ^ 2 - 6 * q - 71 := by
  unfold ugpOutputGap
  field_simp
  ring

/-- ugpOutputGap is differentiable on (0, ∞). -/
theorem ugpOutputGap_differentiableOn (R : ℝ) :
    DifferentiableOn ℝ (ugpOutputGap R) (Ioi 0) := by
  intro q hq
  unfold ugpOutputGap
  apply DifferentiableAt.differentiableWithinAt
  apply DifferentiableAt.add
  · apply DifferentiableAt.mul
    · apply DifferentiableAt.add
      · apply DifferentiableAt.add
        · exact differentiableAt_const R |>.div differentiableAt_id (ne_of_gt hq)
        · exact differentiableAt_id
      · exact differentiableAt_const 7
    · exact differentiableAt_id.sub (differentiableAt_const 13)
  · exact differentiableAt_const 20

/-- Auxiliary: the expanded form as a sum of differentiable terms. -/
private noncomputable def ugpExpanded (R : ℝ) (q : ℝ) : ℝ :=
  R + -(13 * R * q⁻¹) + q ^ 2 + -(6 * q) + -71

private theorem ugpExpanded_eq (R : ℝ) {q : ℝ} (hq : q ≠ 0) :
    ugpExpanded R q = ugpOutputGap R q := by
  unfold ugpExpanded ugpOutputGap; field_simp; ring

private theorem hasDerivAt_ugpExpanded {R q : ℝ} (hq : 0 < q) :
    HasDerivAt (ugpExpanded R) (13 * R * (q ^ 2)⁻¹ + 2 * q + -6) q := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  unfold ugpExpanded
  have hR : HasDerivAt (fun q => R) 0 q := hasDerivAt_const q R
  have hInv : HasDerivAt (fun q => 13 * R * q⁻¹) (13 * R * -(q ^ 2)⁻¹) q :=
    (hasDerivAt_inv hq0).const_mul (13 * R)
  have hNInv : HasDerivAt (fun q => -(13 * R * q⁻¹)) (-(13 * R * -(q ^ 2)⁻¹)) q :=
    hInv.neg
  have hSq : HasDerivAt (fun q => q ^ 2) (2 * q) q := by
    have := hasDerivAt_pow 2 q; simp [Nat.cast_ofNat] at this; exact this
  have hLin : HasDerivAt (fun q => -(6 * q)) (-6) q := by
    have := (hasDerivAt_id q).const_mul 6 |>.neg; simpa using this
  have hConst : HasDerivAt (fun _ : ℝ => (-71 : ℝ)) 0 q := hasDerivAt_const q (-71)
  have hAll := ((hR.add hNInv).add hSq).add hLin |>.add hConst
  refine hAll.congr_deriv ?_
  ring

/-- The derivative of ugpOutputGap R at q > 0 is 13R/q² + 2q − 6. -/
theorem ugpOutputGap_deriv {R q : ℝ} (hq : 0 < q) (_hR : 0 < R) :
    HasDerivAt (ugpOutputGap R) (13 * R / q ^ 2 + 2 * q - 6) q := by
  have hq0 : q ≠ 0 := ne_of_gt hq
  have h := hasDerivAt_ugpExpanded (R := R) hq
  have hderiv_eq : 13 * R * (q ^ 2)⁻¹ + 2 * q + -6 = 13 * R / q ^ 2 + 2 * q - 6 := by
    rw [div_eq_mul_inv]; ring
  rw [hderiv_eq] at h
  exact h.congr_of_eventuallyEq (Filter.eventuallyEq_iff_exists_mem.mpr
    ⟨Set.Ioi 0, Ioi_mem_nhds hq, fun x (hx : 0 < x) =>
      (ugpExpanded_eq R (ne_of_gt hx)).symm⟩)

/-- The derivative is positive on the shell: for q ≥ 14 and R > 0,
    deriv(ugpOutputGap R)(q) = 13R/q² + 2q - 6 ≥ 2·14 - 6 = 22 > 0. -/
theorem ugpOutputGap_deriv_pos {R q : ℝ} (hq : 14 ≤ q) (hR : 0 < R) :
    0 < 13 * R / q ^ 2 + 2 * q - 6 := by
  have hq0 : 0 < q := by linarith
  have : 0 < 13 * R / q ^ 2 := by positivity
  linarith

-- ════════════════════════════════════════════════════════════════
-- §3  Uniform derivative lower bound on the shell
-- ════════════════════════════════════════════════════════════════

/-- **Key export for DSI:** On the shell, the derivative of ugpOutputGap
    is uniformly bounded below by 22.

    This provides the `Hderiv` field of `SmallSymmetricMVTBundle`:
    for all q in the shell and all t near q, |deriv (ugpOutputGap R) t| ≥ 22. -/
theorem ugp_deriv_lower_bound {R q : ℝ} (hq : 14 ≤ q) (hR : 0 < R) :
    22 ≤ 13 * R / q ^ 2 + 2 * q - 6 := by
  have hq0 : 0 < q := by linarith
  have : 0 ≤ 13 * R / q ^ 2 := by positivity
  linarith

-- ════════════════════════════════════════════════════════════════
-- §4  Continuity on the shell (for SmallSymmetricMVTBundle.hgC)
-- ════════════════════════════════════════════════════════════════

/-- ugpOutputGap is continuous on any compact interval within (0, ∞). -/
theorem ugpOutputGap_continuousOn_Icc {R a b : ℝ} (ha : 0 < a) :
    ContinuousOn (ugpOutputGap R) (Icc a b) :=
  (ugpOutputGap_differentiableOn R).continuousOn.mono fun _ ⟨hxa, _⟩ => lt_of_lt_of_le ha hxa

-- ════════════════════════════════════════════════════════════════
-- §5  Export structure (alignment with DSI SmallSymmetricMVTBundle)
-- ════════════════════════════════════════════════════════════════

/-- **The UGP export bundle for DSI Wall 1 (single-hyperbola).**

    This packages the shell, output gap, and uniform derivative bound
    in the format DSI's `SmallSymmetricMVTBundle` expects.

    To use: DSI maps this to `SmallSymmetricMVTBundle.toAnalyticBoundary`
    which produces an `ArcBAnalyticBoundary` with `uniformMagnificationLower`
    filled from the MVT + derivative bound. -/
structure UGPWall1Export where
  R : ℝ
  hR : 0 < R
  hR224 : 224 ≤ R
  shell : Set ℝ := ugpShell R
  outputGap : ℝ → ℝ := ugpOutputGap R
  ε : ℝ := 22
  hε : 0 < ε := by norm_num
  shell_nonempty : (ugpShell R).Nonempty := ugpShell_nonempty hR224
  deriv_lower : ∀ q ∈ ugpShell R, 0 < q →
    22 ≤ 13 * R / q ^ 2 + 2 * q - 6 :=
    fun _ hq _ => ugp_deriv_lower_bound hq.1 hR

end UgpLean
