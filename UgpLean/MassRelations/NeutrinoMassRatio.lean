import Mathlib
import UgpLean.MassRelations.SeesawIndex

/-!
# UgpLean.MassRelations.NeutrinoMassRatio

Lean formalization of the neutrino mass-squared ratio prediction from the UGP
seesaw exponent α = 29/9 applied to Braid Atlas b-values {5, 11, 19}.

## Phase 1 Theorems (EPIC_052_NLS, 2026-05-16)

Three theorems targeting zero sorry:

1. **`fn_texture_gives_seesaw_exponent`** — Arithmetic closure.
   The FN charge pair (q₁,q₂) = (N_c, strand) = (3,2), selected by the UGP MDL
   criterion as the unique singleton-atomic solution to 9q₁+q₂=29, gives:
   q₁ + q₂/N_c² = 3 + 2/9 = 29/9 = nuSeesawExponent.

2. **`seesaw_ratio_independent_of_MR`** — Algebraic closure.
   In a Type-I seesaw where m_i = C·x_i (common prefactor C = E_D²/M_R),
   the mass-squared ratio (m₂²−m₁²)/(m₃²−m₁²) = (x₂²−x₁²)/(x₃²−x₁²)
   is independent of C, hence independent of M_R.

3. **`neutrino_mass_ratio_coarse_bound`** — Certified numerical bound.
   R = (11^{58/9} − 5^{58/9}) / (19^{58/9} − 5^{58/9}) satisfies 0.029 < R < 0.030.
   Proved via monotone integer bounds: each b^{58/9} is sandwiched by checking
   that (lower)⁹ < b⁵⁸ < (upper)⁹ using `norm_num`.

## The formula (from P21 §3)

  R = Δm²₂₁/Δm²₃₁ = (11^{58/9} − 5^{58/9}) / (19^{58/9} − 5^{58/9}) ≈ 0.02936
  NuFIT 6.0 central value: 0.02951 ± 0.00098 (0.16σ agreement, 0.52%)

## Dependencies

- `UgpLean.MassRelations.SeesawIndex` → `KoideAngle` (provides `nuSeesawExponent`)
- The b-values {5, 11, 19} are the Braid Atlas RH-neutrino composites
  certified in `BraidAtlas/CompositeTriples.lean`

## Status

Zero `sorry` for Theorems 1–3.
-/

namespace UgpLean.MassRelations.NeutrinoMassRatio

open UgpLean.MassRelations.KoideAngle

-- ════════════════════════════════════════════════════════════════
-- §0  Helper: reduce b^(p/q : ℝ) bound to integer 9th-power check
-- ════════════════════════════════════════════════════════════════

/-!
### Key helper lemmas

For `b, c > 0` and natural `p, q` with `q > 0`:

  `c < b^(p/q : ℝ)   ↔   c^q < b^p`
  `b^(p/q : ℝ) < c   ↔   b^p < c^q`

Both follow from: `(b^(p/q))^q = b^p` (by `rpow_mul` + `rpow_natCast`),
combined with monotonicity of `t ↦ t^q` on positives.
-/

/-- `c < b^(p/q)` follows from the integer 9th-power check `c^q < b^p`. -/
private lemma rpow_gt_of_pow_gt {b c : ℝ} (hb : 0 < b) (_hc : 0 < c)
    (p q : ℕ) (hq : 0 < q) (h : c ^ q < b ^ p) :
    c < b ^ ((p : ℝ) / (q : ℝ)) := by
  have hq' : (q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hq).ne'
  -- Prove (b^(p/q))^q = b^p via rpow_mul + rpow_natCast
  have key : (b ^ ((p : ℝ) / (q : ℝ))) ^ q = b ^ p := by
    conv_lhs => rw [← Real.rpow_natCast (b ^ ((p : ℝ) / (q : ℝ))) q]
    rw [← Real.rpow_mul (le_of_lt hb), div_mul_cancel₀ _ hq', Real.rpow_natCast]
  -- Apply: c^q < (b^(p/q))^q  →  c < b^(p/q)
  rw [← key] at h
  exact lt_of_pow_lt_pow_left₀ q (Real.rpow_nonneg (le_of_lt hb) _) h

/-- `b^(p/q) < c` follows from the integer 9th-power check `b^p < c^q`. -/
private lemma rpow_lt_of_pow_lt {b c : ℝ} (hb : 0 < b) (hc : 0 < c)
    (p q : ℕ) (hq : 0 < q) (h : b ^ p < c ^ q) :
    b ^ ((p : ℝ) / (q : ℝ)) < c := by
  have hq' : (q : ℝ) ≠ 0 := (Nat.cast_pos.mpr hq).ne'
  have key : (b ^ ((p : ℝ) / (q : ℝ))) ^ q = b ^ p := by
    conv_lhs => rw [← Real.rpow_natCast (b ^ ((p : ℝ) / (q : ℝ))) q]
    rw [← Real.rpow_mul (le_of_lt hb), div_mul_cancel₀ _ hq', Real.rpow_natCast]
  -- Apply: (b^(p/q))^q < c^q  →  b^(p/q) < c
  apply lt_of_pow_lt_pow_left₀ q (le_of_lt hc)
  rw [key]
  exact h

-- ════════════════════════════════════════════════════════════════
-- §1  Theorem 1 — FN Texture Arithmetic
-- ════════════════════════════════════════════════════════════════

/-- **Theorem 1 — FN texture arithmetic (zero sorry).**

    The unique singleton-atomic Froggatt-Nielsen charge pair
    (q₁, q₂) = (N_c, strand) = (3, 2) satisfies the seesaw exponent equation:

      q₁ + q₂/N_c² = 3 + 2/9 = 29/9 = nuSeesawExponent.

    Combined with `fn_texture_3_2_is_unique_singleton_atomic` (NeutrinoFroggattNielsen.lean),
    this closes the "FN texture selects exponent 29/9" claim in Lean.

    Note: `nuSeesawExponent : ℚ := 29/9` is defined in KoideAngle.lean. -/
theorem fn_texture_gives_seesaw_exponent :
    (3 : ℚ) + (2 : ℚ) / (3 : ℚ) ^ 2 = nuSeesawExponent := by
  unfold nuSeesawExponent; norm_num

-- ════════════════════════════════════════════════════════════════
-- §2  Theorem 2 — M_R Independence (Algebraic)
-- ════════════════════════════════════════════════════════════════

/-- **Theorem 2 — M_R independence of the mass-squared ratio (zero sorry).**

    Abstract form: if all three neutrino masses scale by the same factor C
    (i.e., m_i = C · x_i), then the mass-squared ratio is independent of C:

      (m₂² − m₁²) / (m₃² − m₁²) = (x₂² − x₁²) / (x₃² − x₁²).

    Physical interpretation: in the Type-I seesaw with diagonal couplings,
    m_i = (E_D² / M_R) · b_i^α, so C = E_D²/M_R and x_i = b_i^α.
    The ratio depends only on b-values and the exponent α — not on E_D or M_R.
    This confirms Category A (parameter-free) status.

    Proof: pure ring algebra after clearing denominators. -/
theorem seesaw_ratio_independent_of_MR
    (C x₁ x₂ x₃ : ℝ) (hC : C ≠ 0)
    (hx₁ : 0 < x₁) (hx₃ : 0 < x₃) (hne : x₁ ≠ x₃) :
    ((C * x₂) ^ 2 - (C * x₁) ^ 2) / ((C * x₃) ^ 2 - (C * x₁) ^ 2) =
    (x₂ ^ 2 - x₁ ^ 2) / (x₃ ^ 2 - x₁ ^ 2) := by
  have h_sq_ne : x₃ ^ 2 - x₁ ^ 2 ≠ 0 := by
    intro h
    have heq : (x₃ - x₁) * (x₃ + x₁) = 0 := by nlinarith [sq_nonneg x₁, sq_nonneg x₃]
    rcases mul_eq_zero.mp heq with h1 | h2
    · exact hne (by linarith)
    · linarith
  field_simp [hC, h_sq_ne]

-- ════════════════════════════════════════════════════════════════
-- §3  Theorem 3 — Coarse Numerical Bound (Certified Real Interval)
-- ════════════════════════════════════════════════════════════════

/-!
### Integer bounds used (all checked by `norm_num`)

Bounds of the form `c < b^(58/9)` reduce (via `rpow_gt_of_pow_gt`) to
`c^9 < b^58` — a comparison of exact integers that `norm_num` evaluates.

| b  | lower | lower^9 < b^58? | upper  | b^58 < upper^9? |
|----|-------|-----------------|--------|-----------------|
|  5 | 31250 | 512·5⁵⁴ < 625·5⁵⁴ ↔ 512<625 ✓ | 32000 | 2⁷²·5²⁷ > 5³¹ ✓ |
| 11 | 5130000 | ≈10^60.39 < 10^60.40 ✓ | 5200000 | > 11^58 ✓ |
| 19 | 173000000 | ≈1.38×10⁷⁴ < 1.47×10⁷⁴ ✓ | 175000000 | 1.54×10⁷⁴ > 1.47×10⁷⁴ ✓ |

### Ratio bound arithmetic (verified)

For R > 0.029 = 29/1000: need 1000·(11^{58/9} − 5^{58/9}) > 29·(19^{58/9} − 5^{58/9}).
  Using lower(11)=5130000, upper(5)=32000, upper(19)=175000000:
  1000·(5130000 − 32000) = 5098000000 > 29·(175000000 − 32000) = 5073072000 ✓

For R < 0.030 = 30/1000: need 1000·(11^{58/9} − 5^{58/9}) < 30·(19^{58/9} − 5^{58/9}).
  Using upper(11)=5200000, lower(5)=31250, lower(19)=173000000:
  1000·(5200000 − 31250) = 5168750000 < 30·(173000000 − 32000) = 5189040000 ✓
-/

/-- **Theorem 3 — Coarse numerical bound (zero sorry).**

    The UGP neutrino mass-squared ratio satisfies:

      0.029 < R < 0.030,  where R = (11^{58/9} − 5^{58/9}) / (19^{58/9} − 5^{58/9}).

    The true value is R ≈ 0.02936 (NuFIT 6.0 central value: 0.02951 ± 0.00098).
    This is certified by bounding each b^{58/9} via monotone integer 9th-power
    comparisons, reducing to `norm_num` evaluations of exact integers. -/
theorem neutrino_mass_ratio_coarse_bound :
    let R := ((11 : ℝ) ^ ((58 : ℝ) / 9) - (5 : ℝ) ^ ((58 : ℝ) / 9)) /
             ((19 : ℝ) ^ ((58 : ℝ) / 9) - (5 : ℝ) ^ ((58 : ℝ) / 9))
    (29 : ℝ) / 1000 < R ∧ R < (30 : ℝ) / 1000 := by
  simp only
  -- ── Integer bounds on each b^{58/9} ──────────────────────────
  -- 5^{58/9}: 31250 < · < 32000
  -- Lower: 31250^9 = 2^9·5^54 = 512·5^54 < 625·5^54 = 5^58  (norm_num: 512 < 625)
  have h5_lo : (31250 : ℝ) < (5 : ℝ) ^ ((58 : ℝ) / 9) :=
    rpow_gt_of_pow_gt (by norm_num) (by norm_num) 58 9 (by norm_num) (by norm_num)
  -- Upper: 32000^9 = 2^72·5^27 > 5^31·5^27 = 5^58  (norm_num: 2^72 > 5^31)
  have h5_hi : (5 : ℝ) ^ ((58 : ℝ) / 9) < (32000 : ℝ) :=
    rpow_lt_of_pow_lt (by norm_num) (by norm_num) 58 9 (by norm_num) (by norm_num)
  -- 11^{58/9}: 5130000 < · < 5200000
  have h11_lo : (5130000 : ℝ) < (11 : ℝ) ^ ((58 : ℝ) / 9) :=
    rpow_gt_of_pow_gt (by norm_num) (by norm_num) 58 9 (by norm_num) (by norm_num)
  have h11_hi : (11 : ℝ) ^ ((58 : ℝ) / 9) < (5200000 : ℝ) :=
    rpow_lt_of_pow_lt (by norm_num) (by norm_num) 58 9 (by norm_num) (by norm_num)
  -- 19^{58/9}: 173000000 < · < 175000000
  have h19_lo : (173000000 : ℝ) < (19 : ℝ) ^ ((58 : ℝ) / 9) :=
    rpow_gt_of_pow_gt (by norm_num) (by norm_num) 58 9 (by norm_num) (by norm_num)
  have h19_hi : (19 : ℝ) ^ ((58 : ℝ) / 9) < (175000000 : ℝ) :=
    rpow_lt_of_pow_lt (by norm_num) (by norm_num) 58 9 (by norm_num) (by norm_num)
  -- ── Denominator positivity ────────────────────────────────────
  have h_denom_pos : (0 : ℝ) < (19 : ℝ) ^ ((58 : ℝ) / 9) - (5 : ℝ) ^ ((58 : ℝ) / 9) := by
    linarith
  -- ── Lower bound: R > 29/1000 ─────────────────────────────────
  constructor
  · rw [lt_div_iff₀ h_denom_pos]
    -- Need: 29/1000 · denom < numer
    -- i.e., 29 · (19^{58/9} − 5^{58/9}) < 1000 · (11^{58/9} − 5^{58/9})
    -- Using: numer > 5130000−32000=5098000; denom < 175000000−31250=174968750
    -- 29 · 174968750 = 5073993750 < 5098000 · 1000 = 5098000000 ✓
    nlinarith
  -- ── Upper bound: R < 30/1000 ─────────────────────────────────
  · rw [div_lt_iff₀ h_denom_pos]
    -- Need: numer < 30/1000 · denom
    -- i.e., 1000 · (11^{58/9} − 5^{58/9}) < 30 · (19^{58/9} − 5^{58/9})
    -- Using: numer < 5200000−31250=5168750; denom > 173000000−32000=172968000
    -- 1000 · 5168750 = 5168750000 < 30 · 172968000 = 5189040000 ✓
    nlinarith

-- Phase 2 (tight bound |R − 0.02936| < 0.0001): deferred pending Mathlib Real.rpow
-- norm_num extension. Mathematical argument documented in EPIC_052_NLS_SPEC.md.

end UgpLean.MassRelations.NeutrinoMassRatio
