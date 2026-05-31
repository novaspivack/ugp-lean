#!/usr/bin/env python3
"""Assemble zero-sorry WassersteinDistance.lean."""
import re
import subprocess
from pathlib import Path

ROOT = Path("/Users/nova/ugp-lean-exp")
CANON = ROOT / "scripts/WassersteinDistance_canonical.lean"
GAP = ROOT / "UgpLean/ContinuumLimit/_gap_insert.lean"
TARGET = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"

canon = CANON.read_text()
gap = GAP.read_text()

start = canon.index("set_option maxHeartbeats 800000 in\nprivate theorem delta_three_anchor_contradiction")
end = canon.index("private theorem exists_probExpectation_dist_gap")

# gap file: delta_three + probExpectation proof (drop leading set_option; keep canonical exists_delta)
gap_body = gap.split("set_option maxHeartbeats 800000 in\n", 1)[1]

text = canon[:start] + "set_option maxHeartbeats 800000 in\n" + gap_body + canon[end:]

# couplingTransportCost_eq_zero apply pattern
OLD_EQ = """  have hdiag : γ x x = μ.val x := by
    have hsumx : γ x x = M.vertices.sum (γ x) := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun hne => absurd hx hne)]
      simp
    rw [hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]
    simp"""

NEW_EQ = """  have hdiag : γ x x = μ.val x := by
    have hsumx : γ x x = M.vertices.sum (γ x) := by
      apply Finset.sum_eq_single x
      · intro y hy hne; exact hoff x y hx hy hne
      · intro h; exact absurd hx h
    rw [hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    apply Finset.sum_eq_single x
    · intro z hz hne; exact hoff z x hz hx hne
    · intro h; exact absurd hx h"""

text = text.replace(OLD_EQ, NEW_EQ)

text = text.replace(
    "  · exact diagonalCoupling_row_sum S μ\n  · exact diagonalCoupling_col_sum S μ",
    "  · intro x hx; exact diagonalCoupling_row_sum S μ x hx\n  · intro y hy; exact diagonalCoupling_col_sum S μ y hy",
)

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

text = text.replace(W1_OLD, W1_NEW)

TRI_OLD = """  have hc₁lt' : c₁ < W1 M μ ν + ε / 2 := by simpa [W1] using hc₁lt
  have hc₂lt' : c₂ < W1 M ν ρ + ε / 2 := by simpa [W1] using hc₂lt
  linarith [hle, hcost, hc₁lt', hc₂lt', hW1μν, hW1νρ]"""

TRI_NEW = """  unfold W1 at hle hW1μν hW1νρ ⊢
  linarith [hle, hcost, hc₁lt, hc₂lt, hW1μν, hW1νρ]"""

text = text.replace(TRI_OLD, TRI_NEW)

text = re.sub(
    r'(@\[deprecated[^\n]+\]\n)+axiom gorard_vacuum_oric_zero',
    '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\naxiom gorard_vacuum_oric_zero',
    text,
)

TMP = Path("/tmp/WassersteinDistance_final.lean")
TMP.write_text(text)
TARGET.write_text(text)
print(f"Wrote {len(text.splitlines())} lines")
print("hγxw:", "hγxw" in text)
print("W1 vertex:", "∀ x ∈ M.vertices, μ.val x = ν.val x" in text.split("theorem W1_eq_zero_iff")[1][:200])
