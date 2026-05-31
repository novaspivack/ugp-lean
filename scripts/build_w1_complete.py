#!/usr/bin/env python3
"""Assemble complete WassersteinDistance.lean with zero sorry."""
from pathlib import Path

ROOT = Path("/Users/nova/ugp-lean-exp")
SRC = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"
GAP = ROOT / "UgpLean/ContinuumLimit/_gap_v2.lean"
OUT = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean.complete"

lines = SRC.read_text().splitlines(keepends=True)

# Part 1: through exists_delta_pos (line 480, 0-indexed 479)
part1 = lines[:480]

# Patch part1 strings
text1 = "".join(part1)
text1 = text1.replace(
    "  · simp [h, μ.2.2.1 y hy]",
    "  · subst h; exact μ.2.2.1 y hy",
)
text1 = text1.replace(
    "  split_ifs with h <;> simp [M.dist_self x, h]",
    "  split_ifs with h\n  · subst h; simp [M.dist_self x]\n  · simp",
)
text1 = text1.replace(
    """  have hdiag : γ x x = μ.val x := by
    have hsumx : γ x x = M.vertices.sum (γ x) := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy (Ne.symm hne)) (fun hne => absurd hx hne)]
      simp
    rw [hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]
    simp""",
    """  have hdiag : γ x x = μ.val x := by
    have hsumx : γ x x = M.vertices.sum (γ x) := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy (Ne.symm hne)) (fun hne => absurd hx hne)]
    rw [hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]""",
)

gap = GAP.read_text()
if not gap.endswith("\n"):
    gap += "\n"

# Part 2: from exists_probExpectation_dist_gap onward (line 680, index 679)
part2 = "".join(lines[679:])

part2 = part2.replace(
    """private theorem gluedCoupling_left_outside (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : ∀ x y, x ∉ S → γ₁ x y = 0) (x : ℕ) (hx : x ∉ S) (z : ℕ) :
    gluedCoupling S ν γ₁ γ₂ x z = 0 := by
  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _
  by_cases hν : ν.val y = 0 <;> simp [hν, hγ₁ x y hx]""",
    """private theorem gluedCoupling_left_outside (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : ∀ x y, x ∉ S → γ₁ x y = 0) (x : ℕ) (hx : x ∉ S) (z : ℕ) :
    gluedCoupling S ν γ₁ γ₂ x z = 0 := by
  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _
  split_ifs with hν <;> simp [hγ₁ x hx]""",
)

part2 = part2.replace(
    "      apply add_le_add_left le_rfl",
    "      apply add_le_add le_rfl",
)

part2 = part2.replace(
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
    """theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  constructor
  · intro hW1 x hx
    by_contra hne
    have hpos := W1_pos_of_vertex_ne M μ ν ⟨x, hx, hne⟩
    linarith [W1_nonneg M μ ν, hW1]
  · intro h
    apply le_antisymm
    · have hle := W1_le_couplingCost M μ μ (diagonalCoupling M.vertices μ)
        (diagonalCoupling_is_coupling M.vertices μ)
      rw [diagonalCoupling_cost_zero M μ] at hle
      exact hle
    · exact W1_nonneg M μ μ""",
)

OUT.write_text(text1 + gap + part2)
print(f"Wrote {OUT} ({len(OUT.read_text().splitlines())} lines)")
