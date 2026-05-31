#!/usr/bin/env python3
"""Deploy green WassersteinDistance.lean: canonical + _gap_clean + mechanical fixes."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"
text = (ROOT / "scripts/WassersteinDistance_canonical.lean").read_text()
text = text.replace("push Not", "push_neg")
gap = (ROOT / "UgpLean/ContinuumLimit/_gap_clean.lean").read_text().rstrip() + "\n\n"

# Replace broken gap proof with clean version
j0 = text.index("private theorem probExpectation_dist_eq_all_imp_vertex_eq")
j1 = text.index("private theorem exists_probExpectation_dist_gap")
text = text[:j0] + gap + text[j1:]

# diagonalCoupling_right_outside
text = text.replace(
    "  · subst h; simp [μ.2.2.1 y hy]",
    "  · rw [if_pos h]\n    have hx : x ∉ S := by simpa [h] using hy\n    simp [μ.2.2.1 x hx]",
)

# diagonalCoupling_cost_zero
text = text.replace(
    """  split_ifs with h <;> simp [M.dist_self x, h]""",
    """  split_ifs with h
  · subst h; simp [M.dist_self x]
  · simp""",
)

text = text.replace(
    "theorem probExpectation_dist_sub",
    "private theorem probExpectation_dist_sub",
    1,
)

text = text.replace(
    """  have hall0 : ∀ t ∈ S, δ t = 0 := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum
  linarith [htMinusNeg, hall0 tMinus (Finset.mem_filter.mp htMinus).1]""",
    """  have hsumpos : 0 < S.sum δ :=
    lt_of_lt_of_le htMinusNeg (Finset.single_le_sum hnonpos (Finset.mem_filter.mp htMinus).1)
  linarith [hsum, hsumpos]""",
)

text = text.replace(
    "rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy (Ne.symm hne)) (fun hne => absurd hx hne)]\n      simp",
    "rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun hne => absurd hx hne)]\n      simp",
)

text = text.replace("  · exact hγ.2.2.1 x hx w", "  · exact hγ.2.1 x hx w")

text = text.replace(
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _; split_ifs <;> simp [hγ₁ x hx]",
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _; by_cases hν : ν.val y = 0 <;> simp [hγ₁ x hx y, *]",
)

text = text.replace(
    """    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        rw [← Finset.mul_sum, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
    """    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        have hconst : ∀ z, γ₁ x w * γ₂ w z / ν.val w = (γ₁ x w / ν.val w) * γ₂ w z := fun z => by ring
        rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
)

text = text.replace(
    """    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'
      simp [hν, Finset.sum_eq_zero fun x' _ => by simp [hcol x']]""",
    """    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'
      simp [hν, hcol, Finset.sum_const_zero]""",
)

text = text.replace(
    """    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by
        rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
    """    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by
        have hconst : ∀ x', γ₁ x' w * γ₂ w z / ν.val w = (γ₂ w z / ν.val w) * γ₁ x' w := fun x' => by ring
        rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
)

text = text.replace(
    """theorem gluedCoupling_cost_le (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling M.vertices μ ν γ₁)
    (hγ₂ : IsCoupling M.vertices ν ρ γ₂) :
    couplingTransportCost M (gluedCoupling M.vertices ν γ₁ γ₂) ≤
      couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
  classical
  set γ₃ := gluedCoupling M.vertices ν γ₁ γ₂""",
    """theorem gluedCoupling_cost_le (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling M.vertices μ ν γ₁)
    (hγ₂ : IsCoupling M.vertices ν ρ γ₂) :
    couplingTransportCost M (gluedCoupling M.vertices ν γ₁ γ₂) ≤
      couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
  classical
  haveI : ∀ w : ℕ, Decidable (ν.val w = 0) := fun _ => Classical.dec _
  set γ₃ := gluedCoupling M.vertices ν γ₁ γ₂""",
)

text = text.replace(
    """      rw [mul_comm (M.dist x z), mul_comm (M.dist x w + M.dist w z)]
      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv""",
    """      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv""",
)

text = text.replace(
    """    congr 1; ext w hw
    by_cases hν : ν.val w = (0 : ℝ)
    · have hγxw := coupling_col_zero_of_mass_zero hγ₁ w hw hν x
      rw [if_pos hν, if_pos hν]
      simp [hγxw, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
    · rw [if_neg hν, if_neg hν]
      have hν' : ν.val w ≠ 0 := Ne.symm hν
      have hcol : M.vertices.sum (fun z => γ₂ w z) = ν.val w := hγ₂.2.2.2.1 w hw
      calc
        M.vertices.sum fun z => γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) =
            γ₁ x w / ν.val w *
              M.vertices.sum fun z => γ₂ w z * (M.dist x w + M.dist w z) := by
          rw [Finset.mul_sum, mul_div_assoc, mul_assoc]
        _ = γ₁ x w / ν.val w * (M.vertices.sum fun z => γ₂ w z * M.dist x w +
              M.vertices.sum fun z => γ₂ w z * M.dist w z) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, mul_comm (M.dist x w)]
        _ = γ₁ x w * M.dist x w +
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := by
          rw [hcol, mul_div_cancel₀ _ hν']; ring""",
    """    congr 1; ext w
    intro hw
    by_cases hν : ν.val w = (0 : ℝ)
    · have hγxw := coupling_col_zero_of_mass_zero hγ₁ w hw hν x
      rw [if_pos hν, if_pos hν]
      simp [hγxw, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
    · rw [if_neg hν, if_neg hν]
      have hν' : ν.val w ≠ 0 := Ne.symm hν
      have hcol : M.vertices.sum (fun z => γ₂ w z) = ν.val w := hγ₂.2.2.2.1 w hw
      calc
        M.vertices.sum fun z => γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) =
            γ₁ x w / ν.val w *
              M.vertices.sum fun z => γ₂ w z * (M.dist x w + M.dist w z) := by
          rw [Finset.mul_sum, mul_div_assoc, mul_assoc]
        _ = γ₁ x w / ν.val w * (M.vertices.sum fun z => γ₂ w z * M.dist x w +
              M.vertices.sum fun z => γ₂ w z * M.dist w z) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, mul_comm (M.dist x w)]
        _ = γ₁ x w * M.dist x w +
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := by
          rw [hcol, mul_div_cancel₀ _ hν']; ring""",
)

text = text.replace("      apply add_le_add le_rfl", "      apply add_le_add le_rfl")

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
  · intro hμν; subst hμν""",
    """theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  constructor
  · intro hW1
    by_contra hne
    push_neg at hne
    have hpos := W1_pos_of_vertex_ne M μ ν hne
    linarith [W1_nonneg M μ ν, hW1]
  · intro h
    have hμν : μ = ν := probDist_eq_of_vertex_weights_eq h
    subst hμν""",
)

text = text.replace(
    "axiom gorard_vacuum_oric_zero",
    '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\naxiom gorard_vacuum_oric_zero',
)

text = text.replace(
    "  · exact diagonalCoupling_row_sum S μ\n  · exact diagonalCoupling_col_sum S μ",
    "  · intro x hx; exact diagonalCoupling_row_sum S μ x hx\n  · intro y hy; exact diagonalCoupling_col_sum S μ y hy",
)

text = text.replace(
    """    have hsumx : γ x x = M.vertices.sum (γ x) := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun hne => absurd hx hne)]
      simp
    rw [hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]
    simp""",
    """    have hsumx : γ x x = M.vertices.sum (γ x) := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun hne => absurd hx hne)]
    rw [hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]""",
)

text = text.replace(
    """  split_ifs with h
  · subst h; simp [M.dist_self x]
  · simp""",
    """  split_ifs with hxy
  · subst hxy; simp [M.dist_self]
  · simp""",
)

tmp = Path("/tmp/w1_green.lean")
tmp.write_text(text)
OUT.write_text(text)
print(f"Wrote {len(text.splitlines())} lines to {OUT} and {tmp}")
