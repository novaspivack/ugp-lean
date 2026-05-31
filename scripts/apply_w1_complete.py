#!/usr/bin/env python3
"""Write complete WassersteinDistance.lean from canonical + all known proof fixes."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "scripts/WassersteinDistance_canonical.lean"
OUT = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"

text = SRC.read_text()

# diagonalCoupling_right_outside
text = text.replace(
    "  · simp [h, μ.2.2.1 y hy]",
    "  · subst h; simp [μ.2.2.1 y hy]",
)

# diagonalCoupling_cost_zero
text = text.replace(
    """theorem diagonalCoupling_cost_zero (M : FiniteMetricSpace) (μ : ProbDist M.vertices) :
    couplingTransportCost M (diagonalCoupling M.vertices μ) = 0 := by
  unfold couplingTransportCost diagonalCoupling
  apply Finset.sum_eq_zero; intro x _
  apply Finset.sum_eq_zero; intro y _
  split_ifs with h <;> simp [M.dist_self, h]""",
    """theorem diagonalCoupling_cost_zero (M : FiniteMetricSpace) (μ : ProbDist M.vertices) :
    couplingTransportCost M (diagonalCoupling M.vertices μ) = 0 := by
  unfold couplingTransportCost diagonalCoupling
  apply Finset.sum_eq_zero; intro x _
  apply Finset.sum_eq_zero; intro y _
  split_ifs with h
  · subst h; simp [M.dist_self x]
  · simp""",
)

# probExpectation_dist_sub visibility
text = text.replace(
    "private theorem probExpectation_dist_sub",
    "private theorem probExpectation_dist_sub",
)
text = text.replace(
    "theorem probExpectation_dist_sub",
    "private theorem probExpectation_dist_sub",
    1,
)

# couplingTransportCost_eq_zero_of_eq hdiag/hcol
text = text.replace(
    """  have hdiag : γ x x = μ.val x := by
    have hsumx : γ x x = M.vertices.sum (γ x) := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy (Ne.symm hne)) (fun hne => absurd hx hne)]
      simp
    rw [hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]
    simp
  have hnu : ν.val x = γ x x := by rw [← hcol, hγ.2.2.2.2 x hx]
  linarith [hdiag, hnu]""",
    """  have hdiag : γ x x = μ.val x := by
    have hsumx : γ x x = M.vertices.sum (γ x) := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun hne => absurd hx hne)]
      simp
    rw [hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]
    simp
  have hnu : ν.val x = γ x x := by rw [← hcol, hγ.2.2.2.2 x hx]
  linarith [hdiag, hnu]""",
)

# gap proof: first three-point branch
text = text.replace(
    """    · have hthirdEx := hthird
      obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthirdEx
      have hut0ne : u ≠ t0 := hut0
      have hutMne : u ≠ tMinus := hutM
      have hΔ : M.dist t0 tMinus < M.dist t0 u + M.dist tMinus u := by
        have htri' : M.dist t0 tMinus ≤ M.dist t0 u + M.dist u tMinus := M.triangle t0 u tMinus
        have htri : M.dist t0 tMinus ≤ M.dist t0 u + M.dist tMinus u := by
          rw [M.dist_comm u tMinus]; exact htri'
        refine lt_of_le_of_ne htri ?_
        intro h_eq
        nlinarith [M.dist_nonneg, hut0ne, hutMne, hdistPM, dist_pos_of_ne M hut0ne,
          dist_pos_of_ne M hutMne]
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) (hu' : t ≠ u) :
          δ t = 0 := by
        by_contra hδne
        exact absurd ⟨t, ht, ht0', htM', hδne⟩ hthirdEx
      have hsum3 : δ t0 + δ tMinus + δ u = 0 := by
        have hrest : (((M.vertices.erase t0).erase tMinus).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδrest t
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht) (Finset.ne_of_mem_erase ht)""",
    """    · obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthird
      have hδvanish (v : ℕ) (hv : v ∈ M.vertices) : v = t0 ∨ v = tMinus ∨ δ v = 0 := by
        rcases em (v = t0) with ht0eq | ht0ne'
        · exact Or.inl ht0eq
        rcases em (v = tMinus) with htMeq | htMne'
        · exact Or.inr (Or.inl htMeq)
        rcases em (δ v = 0) with hδeq | hδne
        · exact Or.inr (Or.inr hδeq)
        · exact absurd ⟨v, hv, ht0ne', htMne', hδne⟩ hthird
      have hut0ne : u ≠ t0 := hut0
      have hutMne : u ≠ tMinus := hutM
      have hΔ : M.dist t0 tMinus < M.dist t0 u + M.dist tMinus u := by
        refine lt_of_le_of_ne (M.triangle t0 u tMinus) ?_
        intro h_eq
        nlinarith [M.dist_nonneg, M.dist_comm, M.triangle t0 tMinus u, hut0ne, hutMne, hdistPM,
          dist_pos_of_ne M hut0ne, dist_pos_of_ne M hutMne]
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) :
          δ t = 0 := by
        rcases hδvanish t ht with ht0eq | htMeq | hδeq
        · exact absurd ht0eq ht0'
        · exact absurd htMeq htM'
        · exact hδeq
      have hsum3 : δ t0 + δ tMinus + δ u = 0 := by
        have hrest : (((M.vertices.erase t0).erase tMinus).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδrest t
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht)""",
)

# gap proof: second three-point branch
text = text.replace(
    """    · have hthirdEx := hthird
      obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthirdEx
      have hutPne : u ≠ tPlus := hutP
      have hut0ne : u ≠ t0 := hut0
      have hΔ : M.dist tPlus t0 < M.dist tPlus u + M.dist t0 u := by
        have htri' : M.dist tPlus t0 ≤ M.dist tPlus u + M.dist u t0 := M.triangle tPlus u t0
        have htri : M.dist tPlus t0 ≤ M.dist tPlus u + M.dist t0 u := by
          rw [M.dist_comm u t0]; exact htri'
        refine lt_of_le_of_ne htri ?_
        intro h_eq
        nlinarith [M.dist_nonneg, hutPne, hut0ne, hdistPM, dist_pos_of_ne M hutPne,
          dist_pos_of_ne M hut0ne]
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) (hu' : t ≠ u) :
          δ t = 0 := by
        by_contra hδne
        exact absurd ⟨t, ht, htP', ht0', hδne⟩ hthirdEx
      have hsum3 : δ tPlus + δ t0 + δ u = 0 := by
        have hrest : (((M.vertices.erase tPlus).erase t0).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδrest t
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht) (Finset.ne_of_mem_erase ht)""",
    """    · obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthird
      have hδvanish (v : ℕ) (hv : v ∈ M.vertices) : v = tPlus ∨ v = t0 ∨ δ v = 0 := by
        rcases em (v = tPlus) with htPeq | htPne'
        · exact Or.inl htPeq
        rcases em (v = t0) with ht0eq | ht0ne'
        · exact Or.inr (Or.inl ht0eq)
        rcases em (δ v = 0) with hδeq | hδne
        · exact Or.inr (Or.inr hδeq)
        · exact absurd ⟨v, hv, htPne', ht0ne', hδne⟩ hthird
      have hutPne : u ≠ tPlus := hutP
      have hut0ne : u ≠ t0 := hut0
      have hΔ : M.dist tPlus t0 < M.dist tPlus u + M.dist t0 u := by
        refine lt_of_le_of_ne (M.triangle tPlus u t0) ?_
        intro h_eq
        nlinarith [M.dist_nonneg, M.dist_comm, M.triangle tPlus t0 u, hutPne, hut0ne, hdistPM,
          dist_pos_of_ne M hutPne, dist_pos_of_ne M hut0ne]
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) :
          δ t = 0 := by
        rcases hδvanish t ht with htPeq | ht0eq | hδeq
        · exact absurd htPeq htP'
        · exact absurd ht0eq ht0'
        · exact hδeq
      have hsum3 : δ tPlus + δ t0 + δ u = 0 := by
        have hrest : (((M.vertices.erase tPlus).erase t0).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδrest t
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht)""",
)

# two-point branches: add dist_self rewrite before split
text = text.replace(
    """      have hdistPlus := hdist0
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0] at hdistPlus
      simp only [M.dist_self t0, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htMinusInErase] at hdistPlus""",
    """      have hdistPlus := hdist0
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0, M.dist_self t0, mul_zero, add_zero] at hdistPlus
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htMinusInErase] at hdistPlus""",
)

text = text.replace(
    """      have hdistPlus := hdistP
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem] at hdistPlus
      simp only [M.dist_self tPlus, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase] at hdistPlus""",
    """      have hdistPlus := hdistP
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem, M.dist_self tPlus, mul_zero, add_zero] at hdistPlus
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase] at hdistPlus""",
)

# gluedCoupling_cost_le hbound zero branch
text = text.replace(
    """    split_ifs with hν
    · simp
    · rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_comm, mul_div_cancel₀ _ (Ne.symm hν)]
  calc
    M.vertices.sum fun x => M.vertices.sum fun z => M.dist x z * γ₃ x z ≤""",
    """    split_ifs with hν
    · exact le_rfl
    · rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_comm, mul_div_cancel₀ _ (Ne.symm hν)]
  calc
    M.vertices.sum fun x => M.vertices.sum fun z => M.dist x z * γ₃ x z ≤""",
)

# W1_eq_zero_iff statement
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

OUT.write_text(text)
print(f"Wrote {len(text.splitlines())} lines to {OUT}")
