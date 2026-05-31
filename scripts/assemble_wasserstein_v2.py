#!/usr/bin/env python3
"""Assemble zero-sorry WassersteinDistance.lean from canonical + fixes."""
from pathlib import Path

ROOT = Path("/Users/nova/ugp-lean-exp")
text = (ROOT / "scripts/WassersteinDistance_canonical.lean").read_text()

text = text.replace("private theorem probDist_vertex_mass_balance", "theorem probDist_vertex_mass_balance", 1)
text = text.replace("private theorem probExpectation_dist_sub", "theorem probExpectation_dist_sub", 1)
text = text.replace(
    "rw [← probExpectation_dist_sub, h a ha, sub_self]",
    "rw [← probExpectation_dist_sub M μ ν a, h a ha, sub_self]",
)

# exists_mass_imbalance strict sum positivity
text = text.replace(
    "  have hsumpos : 0 < M.vertices.sum (fun t => μ.val t - ν.val t) :=\n    lt_of_lt_of_le hpos (Finset.single_le_sum hnonneg hx)",
    "  have hsumpos : 0 < M.vertices.sum (fun t => μ.val t - ν.val t) :=\n    Finset.sum_pos' hnonneg ⟨x, hx, hpos⟩",
)
text = text.replace(
    "  have hsumneg : M.vertices.sum (fun t => μ.val t - ν.val t) < 0 :=\n    lt_of_lt_of_le hneg (Finset.single_le_sum hnonpos hx)",
    "  have hsumneg : M.vertices.sum (fun t => μ.val t - ν.val t) < 0 :=\n    Finset.sum_neg' hnonpos ⟨x, hx, hneg⟩",
)

# couplingTransportCost_eq_zero_of_eq
OLD_ZERO = """private theorem couplingTransportCost_eq_zero_of_eq
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) (γ : ℕ → ℕ → ℝ)
    (hγ : IsCoupling M.vertices μ ν γ) (hc : couplingTransportCost M γ = 0) :
    ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  intro x hx
  have hrow_nonneg (a : ℕ) :
      0 ≤ M.vertices.sum (fun b => γ a b * M.dist a b) := by
    apply Finset.sum_nonneg; intro b _; exact mul_nonneg (hγ.1 a b) (M.dist_nonneg a b)
  have hrow_zero (a : ℕ) (ha : a ∈ M.vertices) :
      M.vertices.sum (fun b => γ a b * M.dist a b) = 0 := by
    unfold couplingTransportCost at hc
    have hle : M.vertices.sum (fun b => γ a b * M.dist a b) ≤ 0 := by
      have hle_total :
          M.vertices.sum (fun b => γ a b * M.dist a b) ≤
            M.vertices.sum (fun a' => M.vertices.sum (fun b => γ a' b * M.dist a' b)) :=
        Finset.single_le_sum (fun a' _ => hrow_nonneg a') ha
      linarith [hle_total, hc]
    exact le_antisymm hle (hrow_nonneg a)
  have hoff (a b : ℕ) (ha : a ∈ M.vertices) (hb : b ∈ M.vertices) (hne : a ≠ b) :
      γ a b = 0 := by
    have hnn : 0 ≤ γ a b * M.dist a b := mul_nonneg (hγ.1 a b) (M.dist_nonneg a b)
    have hzero : γ a b * M.dist a b = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => mul_nonneg (hγ.1 a c) (M.dist_nonneg a c))).1
        (hrow_zero a ha) b hb
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (dist_pos_of_ne M hne))
  have hdiag : γ x x = μ.val x := by
    have hsumx : γ x x = M.vertices.sum (γ x) := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy (Ne.symm hne)) (fun hne => absurd hx hne)]
      simp
    rw [hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]
    simp
  have hnu : ν.val x = γ x x := by rw [← hcol, hγ.2.2.2.2 x hx]
  linarith [hdiag, hnu]"""

NEW_ZERO = """private theorem couplingTransportCost_eq_zero_of_eq
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) (γ : ℕ → ℕ → ℝ)
    (hγ : IsCoupling M.vertices μ ν γ) (hc : couplingTransportCost M γ = 0) :
    ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  intro x hx
  have hrow_nonneg (a : ℕ) :
      0 ≤ M.vertices.sum (fun b => γ a b * M.dist a b) := by
    apply Finset.sum_nonneg; intro b _; exact mul_nonneg (hγ.1 a b) (M.dist_nonneg a b)
  have hrow_zero (a : ℕ) (ha : a ∈ M.vertices) :
      M.vertices.sum (fun b => γ a b * M.dist a b) = 0 := by
    unfold couplingTransportCost at hc
    have hle : M.vertices.sum (fun b => γ a b * M.dist a b) ≤ 0 := by
      have hle_total :
          M.vertices.sum (fun b => γ a b * M.dist a b) ≤
            M.vertices.sum (fun a' => M.vertices.sum (fun b => γ a' b * M.dist a' b)) :=
        Finset.single_le_sum (fun a' _ => hrow_nonneg a') ha
      linarith [hle_total, hc]
    exact le_antisymm hle (hrow_nonneg a)
  have hoff (a b : ℕ) (ha : a ∈ M.vertices) (hb : b ∈ M.vertices) (hne : a ≠ b) :
      γ a b = 0 := by
    have hnn : 0 ≤ γ a b * M.dist a b := mul_nonneg (hγ.1 a b) (M.dist_nonneg a b)
    have hzero : γ a b * M.dist a b = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => mul_nonneg (hγ.1 a c) (M.dist_nonneg a c))).1
        (hrow_zero a ha) b hb
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (dist_pos_of_ne M hne))
  have hdiag : γ x x = μ.val x := by
    calc γ x x = M.vertices.sum (γ x) := by
          rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun h => absurd hx h)]
      _ = μ.val x := hγ.2.2.2.1 x hx
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun h => absurd hx h)]
  linarith [hdiag, hγ.2.2.2.2 x hx]"""

text = text.replace(OLD_ZERO, NEW_ZERO)

# prob-gap true branch (t0 positive): let hex + push Not + 4-way hδrest
OLD_THIRD1 = """    · have hthirdEx := hthird
      obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthirdEx
      have hut0ne : u ≠ t0 := hut0
      have hutMne : u ≠ tMinus := hutM
      have hΔ : M.dist t0 tMinus < M.dist t0 u + M.dist tMinus u := by
        refine lt_of_le_of_ne (M.triangle t0 u tMinus) ?_
        intro h_eq
        nlinarith [M.dist_nonneg, M.dist_comm, M.triangle t0 tMinus u, hut0ne, hutMne, hdistPM,
          dist_pos_of_ne M hut0ne, dist_pos_of_ne M hutMne]
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) :
          δ t = 0 := by
        by_contra hδne
        exact absurd ⟨t, ht, ht0', htM', hδne⟩ hthirdEx
      have hsum3 : δ t0 + δ tMinus + δ u = 0 := by
        have hrest : (((M.vertices.erase t0).erase tMinus).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδrest t
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht)"""

NEW_THIRD1 = """    · let hex := hthird
      obtain ⟨u, hu, hut0, hutM, hudne⟩ := hex
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
        by_cases htu : t = u
        · exact absurd htu hu'
        · rcases hex t ht with h | h | hδ | hut
          · exact absurd h ht0'
          · exact absurd h htM'
          · exact hδ
          · exact absurd hut htu
      have hsum3 : δ t0 + δ tMinus + δ u = 0 := by
        have hrest : (((M.vertices.erase t0).erase tMinus).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδrest t
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht) (Finset.ne_of_mem_erase ht)"""

text = text.replace(OLD_THIRD1, NEW_THIRD1)

OLD_THIRD2 = """    · have hthirdEx := hthird
      obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthirdEx
      have hutPne : u ≠ tPlus := hutP
      have hut0ne : u ≠ t0 := hut0
      have hΔ : M.dist tPlus t0 < M.dist tPlus u + M.dist t0 u := by
        refine lt_of_le_of_ne (M.triangle tPlus u t0) ?_
        intro h_eq
        nlinarith [M.dist_nonneg, M.dist_comm, M.triangle tPlus t0 u, hutPne, hut0ne, hdistPM,
          dist_pos_of_ne M hutPne, dist_pos_of_ne M hut0ne]
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) :
          δ t = 0 := by
        by_contra hδne
        exact absurd ⟨t, ht, htP', ht0', hδne⟩ hthirdEx
      have hsum3 : δ tPlus + δ t0 + δ u = 0 := by
        have hrest : (((M.vertices.erase tPlus).erase t0).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδrest t
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht)"""

NEW_THIRD2 = """    · let hex := hthird
      obtain ⟨u, hu, hutP, hut0, hudne⟩ := hex
      push Not at hex
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
        by_cases htu : t = u
        · exact absurd htu hu'
        · rcases hex t ht with h | h | hδ | hut
          · exact absurd h htP'
          · exact absurd h ht0'
          · exact hδ
          · exact absurd hut htu
      have hsum3 : δ tPlus + δ t0 + δ u = 0 := by
        have hrest : (((M.vertices.erase tPlus).erase t0).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδrest t
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht) (Finset.ne_of_mem_erase ht)"""

text = text.replace(OLD_THIRD2, NEW_THIRD2)

# false branches: dist_self anchor + hplus0
text = text.replace(
    "simp only [M.dist_self, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus",
    "simp only [M.dist_self t0, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus",
    1,
)
text = text.replace(
    "simp only [M.dist_self, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus",
    "simp only [M.dist_self tPlus, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus",
    1,
)
text = text.replace(
    "      linarith [hdistPlus, hsplit, hrest0, hheadPlus]",
    "      have hplus0 : δ tMinus * M.dist tMinus t0 = 0 := by linarith [hdistPlus, hsplit, hrest0]\n      linarith [hheadPlus, hplus0]",
    1,
)
text = text.replace(
    "      linarith [hdistPlus, hsplit, hrest0, hheadPlus]",
    "      have hplus0 : δ t0 * M.dist t0 tPlus = 0 := by linarith [hdistPlus, hsplit, hrest0]\n      linarith [hheadPlus, hplus0]",
    1,
)

text = text.replace(
    "        rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]",
    "        rw [Finset.sum_mul_comm, hγ₁.2.2.2.2 w hw, mul_div_cancel₀ _ (Ne.symm hν)]",
)

text = text.replace(
    "  split_ifs with h <;> simp [M.dist_self, h]",
    "  split_ifs with h <;> simp [M.dist_self x, h]",
)

OUT = Path("/tmp/WassersteinDistance_final.lean")
OUT.write_text(text)
(ROOT / "scripts/WassersteinDistance_canonical.lean").write_text(text)
print(f"Wrote {len(text.splitlines())} lines to {OUT}")
