#!/usr/bin/env python3
"""Write finalized WassersteinDistance.lean from canonical template."""
from pathlib import Path

ROOT = Path("/Users/nova/ugp-lean-exp")
SRC = ROOT / "scripts/WassersteinDistance_canonical.lean"
TARGET = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"

text = SRC.read_text()

text = text.replace(
    "  · exact diagonalCoupling_row_sum S μ\n  · exact diagonalCoupling_col_sum S μ",
    "  · intro x hx; exact diagonalCoupling_row_sum S μ x hx\n  · intro y hy; exact diagonalCoupling_col_sum S μ y hy",
)

HSPLIT_OLD = """    by_cases hν : ν.val w = (0 : ℝ)
    · simp [hν]
    · rw [if_neg hν, if_neg hν]
      have hν' : ν.val w ≠ 0 := Ne.symm hν
      have hcol : M.vertices.sum (fun z => γ₂ w z) = ν.val w := hγ₂.2.2.2.1 w hw
      rw [Finset.mul_sum, ← Finset.sum_mul, mul_add]
      have hleft : (γ₁ x w / ν.val w) * M.vertices.sum (fun z => γ₂ w z * M.dist x w) =
          γ₁ x w * M.dist x w := by rw [Finset.sum_mul, hcol, mul_div_cancel₀ _ hν']
      rw [hleft]; ring"""

HSPLIT_NEW = """    by_cases hν : ν.val w = (0 : ℝ)
    · have hγxw := coupling_col_zero_of_mass_zero hγ₁ w hw hν x
      simp [hν, hγxw, zero_mul, mul_zero, add_zero]
    · rw [if_neg hν, if_neg hν]
      have hν' : ν.val w ≠ 0 := Ne.symm hν
      have hcol : M.vertices.sum (fun z => γ₂ w z) = ν.val w := hγ₂.2.2.2.1 w hw
      rw [Finset.mul_sum, ← Finset.sum_mul, mul_add]
      have hleft : (γ₁ x w / ν.val w) * M.vertices.sum (fun z => γ₂ w z * M.dist x w) =
          γ₁ x w * M.dist x w := by rw [Finset.sum_mul, hcol, mul_div_cancel₀ _ hν']
      rw [hleft]; ring"""

if HSPLIT_OLD not in text:
    raise SystemExit("hsplit patch anchor not found")
text = text.replace(HSPLIT_OLD, HSPLIT_NEW)

W1_OLD = """theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ μ = ν := by
  constructor
  · intro hW1
    by_contra hμν
    have hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x := by
      intro hall; push_neg at hall
      exact absurd hμν (probDist_eq_of_vertex_weights_eq hall)
    have hpos := W1_pos_of_vertex_ne M μ ν hne
    linarith [W1_nonneg M μ ν, hW1]
  · intro hμν; subst hμν
    apply le_antisymm
    · have hle := W1_le_couplingCost M μ μ (diagonalCoupling M.vertices μ)
        (diagonalCoupling_is_coupling M.vertices μ)
      rw [diagonalCoupling_cost_zero M μ] at hle
      exact hle
    · exact W1_nonneg M μ μ"""

W1_NEW = """theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  constructor
  · intro hW1
    by_contra hne
    push_neg at hne
    have hpos := W1_pos_of_vertex_ne M μ ν hne
    linarith [W1_nonneg M μ ν, hW1]
  · intro h
    have hμν : μ = ν := probDist_eq_of_vertex_weights_eq h
    subst hμν
    apply le_antisymm
    · have hle := W1_le_couplingCost M μ μ (diagonalCoupling M.vertices μ)
        (diagonalCoupling_is_coupling M.vertices μ)
      rw [diagonalCoupling_cost_zero M μ] at hle
      exact hle
    · exact W1_nonneg M μ μ"""

if W1_OLD not in text:
    raise SystemExit("W1_eq_zero_iff patch anchor not found")
text = text.replace(W1_OLD, W1_NEW)

TRI_OLD = """  have hc₁lt' : c₁ < W1 M μ ν + ε / 2 := by simpa [W1] using hc₁lt
  have hc₂lt' : c₂ < W1 M ν ρ + ε / 2 := by simpa [W1] using hc₂lt
  linarith [hle, hcost, hc₁lt', hc₂lt', hW1μν, hW1νρ]"""

TRI_NEW = """  unfold W1 at hle hW1μν hW1νρ ⊢
  linarith [hle, hcost, hc₁lt, hc₂lt, hW1μν, hW1νρ]"""

if TRI_OLD not in text:
    raise SystemExit("W1_triangle patch anchor not found")
text = text.replace(TRI_OLD, TRI_NEW)

text = text.replace(
    "axiom gorard_vacuum_oric_zero",
    '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\naxiom gorard_vacuum_oric_zero',
)

TARGET.write_text(text)
print(f"Wrote {TARGET} ({len(text.splitlines())} lines)")
