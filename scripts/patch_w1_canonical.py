#!/usr/bin/env python3
"""Patch WassersteinDistance_canonical.lean into a buildable complete file."""
import re
from pathlib import Path

ROOT = Path("/Users/nova/ugp-lean-exp")
CANON = ROOT / "scripts/WassersteinDistance_canonical.lean"
GAP = ROOT / "UgpLean/ContinuumLimit/_gap_v2.lean"
OUT = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean.complete"

text = CANON.read_text()
gap = GAP.read_text().rstrip() + "\n"

# diagonalCoupling_right_outside
text = text.replace(
    "  · simp [h, μ.2.2.1 y hy]",
    "  · subst h; exact μ.2.2.1 y hy",
)

# diagonalCoupling_cost_zero
text = text.replace(
    "  split_ifs with h <;> simp [M.dist_self x, h]",
    "  split_ifs with h\n  · subst h; simp [M.dist_self x]\n  · simp",
)

# couplingTransportCost_eq_zero_of_eq: drop trailing simp after sum_eq_single
text = text.replace(
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

# exists_mass_imbalance_pair branch
text = text.replace(
    "    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt (Ne.symm hdiff)",
    "    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff",
)

# gluedCoupling outside
text = text.replace(
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _; split_ifs <;> simp [hγ₁ x hx]",
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _\n  split_ifs with hν <;> simp [hγ₁ x hx]",
)
text = text.replace(
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _; split_ifs <;> simp [hγ₂ y hz]",
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _\n  split_ifs with hν <;> simp [hγ₂ y hz]",
)

# gluedCoupling_cost_le final step
text = text.replace(
    "      apply add_le_add le_rfl",
    "      apply add_le_add_left le_rfl",
)

# W1_eq_zero_iff: vertex-weight statement
text = text.replace(
    """theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ μ = ν := by
  constructor
  · intro hW1
    apply probDist_eq_of_vertex_weights_eq
    intro x hx
    by_contra hne
    have hpos := W1_pos_of_vertex_ne M μ ν ⟨x, hx, hne⟩
    linarith
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

# Replace delta_three_anchor + old gap proof with _gap_v2
pattern = re.compile(
    r"set_option maxHeartbeats 800000 in\nprivate theorem delta_three_anchor_contradiction.*?"
    r"private theorem exists_probExpectation_dist_gap",
    re.DOTALL,
)
if not pattern.search(text):
    raise SystemExit("Could not find gap proof block to replace")
text = pattern.sub(gap + "\nprivate theorem exists_probExpectation_dist_gap", text, count=1)

# Fix gap proof three-point branch: push_neg before obtain
text = text.replace(
    """    · obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthird
      push_neg at hthird
      rcases hthird u hu with hut0eq | hutMeq | hδzero""",
    """    · obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthird
      have hneg := hthird
      push_neg at hneg
      rcases hneg u hu with hut0eq | hutMeq | hδzero""",
)
text = text.replace(
    """    · obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthird
      push_neg at hthird
      rcases hthird u hu with hutPeq | hut0eq | hδzero""",
    """    · obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthird
      have hneg := hthird
      push_neg at hneg
      rcases hneg u hu with hutPeq | hut0eq | hδzero""",
)

# exists_delta_pos_of_sum_zero - fix neg sum proof
text = text.replace(
    """  by_contra hall; push_neg at hall
  have hnonpos : ∀ t ∈ S, δ t ≤ 0 := hall
  have hpos : 0 < S.sum (fun t => -δ t) :=
    Finset.sum_pos' (fun t ht => sub_nonneg.mpr (hnonpos t ht))
      ⟨tMinus, (Finset.mem_filter.mp htMinus).1, neg_pos.mpr htMinusNeg⟩
  have heq : S.sum (fun t => -δ t) = -S.sum δ := Finset.sum_neg_distrib
  linarith [hsum, heq, hpos]""",
    """  by_contra hall; push_neg at hall
  have hnonpos : ∀ t ∈ S, δ t ≤ 0 := hall
  have hall0 : ∀ t ∈ S, δ t = 0 := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum
  linarith [htMinusNeg, hall0 tMinus (Finset.mem_filter.mp htMinus).1]""",
)

# gap proof two-point rewrites
text = text.replace(
    """      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0, M.dist_self t0, mul_zero, add_zero] at hdistPlus
      have hsumErase0 : (M.vertices.erase t0).sum (fun t => δ t * M.dist t t0) = 0 := by
        linarith [hdistPlus]""",
    """      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0] at hdistPlus
      simp only [M.dist_self t0, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus
      have hsumErase0 : (M.vertices.erase t0).sum (fun t => δ t * M.dist t t0) = 0 := by
        linarith [hdistPlus]""",
)

text = text.replace(
    """      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem, M.dist_self tPlus, mul_zero,
        add_zero] at hdistPlus
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase] at hdistPlus
      have hsumErase0 : (M.vertices.erase tPlus).sum (fun t => δ t * M.dist t tPlus) = 0 := by
        linarith [hdistPlus]""",
    """      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem] at hdistPlus
      simp only [M.dist_self tPlus, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase] at hdistPlus
      have hsumErase0 : (M.vertices.erase tPlus).sum (fun t => δ t * M.dist t tPlus) = 0 := by
        linarith [hdistPlus]""",
)

# coupling mass zero lemmas
text = text.replace(
    "  · exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hγ.1 z w)).1 hcol x hx",
    "  · exact ((Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hγ.1 z w)).mp hcol) x hx",
)
text = text.replace(
    "  · exact (Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hγ.1 w a)).1 hrow z hz",
    "  · exact ((Finset.sum_eq_zero_iff_of_nonneg (fun a _ => hγ.1 w a)).mp hrow) z hz",
)

# glued outside
text = text.replace(
    "  by_cases hν : ν.val y = 0 <;> simp [hν, hγ₁ x y hx]",
    "  split_ifs with hν <;> simp [hγ₁ x hx]",
)

# glued row inner sum
text = text.replace(
    """    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        have hconst : ∀ z, γ₁ x w * γ₂ w z / ν.val w = (γ₁ x w / ν.val w) * γ₂ w z := fun z => by ring
        rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
    """    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        calc S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) =
            (γ₁ x w / ν.val w) * S.sum (γ₂ w) := by
              rw [← Finset.sum_mul, mul_div_assoc]
          _ = γ₁ x w := by rw [hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
)

# glued col zero branch
text = text.replace(
    """    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'
      simp [hν, hcol, Finset.sum_const_zero]""",
    """    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'
      simp [hν, hcol, zero_mul, Finset.sum_const_zero]""",
)

# gluedCoupling_cost_le final
text = text.replace(
    """    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      unfold couplingTransportCost
      rw [← Finset.sum_add_distrib]
      apply add_le_add_left le_rfl
      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
      exact hbound""",
    """    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      unfold couplingTransportCost
      rw [← Finset.sum_add_distrib]
      apply add_le_add le_rfl
      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
      exact hbound""",
)

# W1_eq_zero_iff (actual text in patched output)
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

OUT.write_text(text)
print(f"Wrote {OUT} ({len(text.splitlines())} lines)")
