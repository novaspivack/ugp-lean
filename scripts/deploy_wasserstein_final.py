#!/usr/bin/env python3
"""Deploy fixed WassersteinDistance.lean from canonical source."""
from pathlib import Path

src = Path("/Users/nova/ugp-lean-exp/scripts/WassersteinDistance_canonical.lean")
dst = Path("/Users/nova/ugp-lean-exp/UgpLean/ContinuumLimit/WassersteinDistance.lean")

text = src.read_text()

text = text.replace("push_neg", "push Not")
text = text.replace(
    "have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt (Ne.symm hdiff)",
    "have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff",
)
text = text.replace(
    "      apply add_le_add le_rfl\n      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]\n      exact hbound",
    "      apply add_le_add_left le_rfl\n      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]\n      exact hbound",
)
text = text.replace(
    """theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ μ = ν := by
  constructor
  · intro hW1
    apply probDist_eq_of_vertex_weights_eq
    intro x hx
    by_contra hne
    have hpos := W1_pos_of_vertex_ne M μ ν ⟨x, hx, hne⟩
    linarith [W1_nonneg M μ ν, hW1]
  · intro hμν; subst hμν
    apply le_antisymm
    · have hle := W1_le_couplingCost M μ μ (diagonalCoupling M.vertices μ)
        (diagonalCoupling_is_coupling M.vertices μ)
      rw [diagonalCoupling_cost_zero M μ] at hle
      exact hle
    · exact W1_nonneg M μ μ""",
    """theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  constructor
  · intro hW1 hne
    by_contra hall
    push Not at hall
    have hpos := W1_pos_of_vertex_ne M μ ν hall
    linarith [W1_nonneg M μ ν, hW1]
  · intro h
    have hμν : μ = ν := probDist_eq_of_vertex_weights_eq h
    subst hμν
    apply le_antisymm
    · have hle := W1_le_couplingCost M μ μ (diagonalCoupling M.vertices μ)
        (diagonalCoupling_is_coupling M.vertices μ)
      rw [diagonalCoupling_cost_zero M μ] at hle
      exact hle
    · exact W1_nonneg M μ μ""",
)
text = text.replace(
    "axiom gorard_vacuum_oric_zero",
    '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\naxiom gorard_vacuum_oric_zero',
    1,
)

if "sorry" in text.replace("- A declared (sorry)", ""):
    raise SystemExit("sorry found in deployed text")

dst.write_text(text)
print(f"Wrote {len(text.splitlines())} lines to {dst}")
