#!/usr/bin/env python3
"""Apply all known fixes to cbabcc7 WassersteinDistance.lean."""
from pathlib import Path

src = Path("/tmp/w1_cbabcc7.lean").read_text()
text = src

# imports
if "Mathlib.Data.Real.Archimedean" not in text:
    text = text.replace(
        "import Mathlib.Data.Real.Basic\n",
        "import Mathlib.Data.Real.Basic\nimport Mathlib.Data.Real.Archimedean\n",
    )
if "Mathlib.Algebra.BigOperators.Ring.Finset" not in text:
    text = text.replace(
        "import Mathlib.Algebra.Order.BigOperators.Group.Finset\n",
        "import Mathlib.Algebra.Order.BigOperators.Group.Finset\n"
        "import Mathlib.Algebra.BigOperators.Ring.Finset\n"
        "import Mathlib.Algebra.BigOperators.Field\n",
    )

text = text.replace(
    "  · rw [if_pos h]; exact μ.2.2.1 y hy",
    "  · subst h; simp [μ.2.2.1 y hy]",
)

text = text.replace(
    "  split_ifs with h <;> simp [M.dist_self, h]",
    "  split_ifs with h <;> simp [M.dist_self x, h]",
)

text = text.replace(
    "    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt (Ne.symm hdiff)",
    "    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff",
)

old_zero = """private theorem couplingTransportCost_eq_zero_of_eq
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) (γ : ℕ → ℕ → ℝ)
    (hγ : IsCoupling M.vertices μ ν γ) (hc : couplingTransportCost M γ = 0) :
    ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  intro x hx
  have hrow_zero (a : ℕ) (ha : a ∈ M.vertices) :
      M.vertices.sum (fun b => γ a b * M.dist a b) = 0 := by
    unfold couplingTransportCost at hc
    have houter :
        ∀ t ∈ M.vertices, 0 ≤ M.vertices.sum (fun b => γ t b * M.dist t b) := by
      intro t _; apply Finset.sum_nonneg; intro b _; exact mul_nonneg (hγ.1 t b) (M.dist_nonneg t b)
    exact (Finset.sum_eq_zero_iff_of_nonneg houter).1 hc a ha
  have hoff (a b : ℕ) (ha : a ∈ M.vertices) (hb : b ∈ M.vertices) (hne : a ≠ b) :
      γ a b = 0 := by
    have hnn : 0 ≤ γ a b * M.dist a b := mul_nonneg (hγ.1 a b) (M.dist_nonneg a b)
    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hnn)).1 (hrow_zero a ha) b hb
    exact (mul_eq_zero.mp hterm).resolve_right (ne_of_gt (dist_pos_of_ne M hne))
  calc
    μ.val x = M.vertices.sum (γ x) := hγ.2.2.2.1 x hx
    _ = γ x x := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun hne => absurd hx hne)]
      simp
    _ = M.vertices.sum (fun z => γ z x) := by
      rw [Finset.sum_eq_single x]
      · simp
      · intro z hz hne; exact hoff z x hz hx hne
      · intro hne; exact absurd hx hne
    _ = ν.val x := hγ.2.2.2.2 x hx"""

new_zero = """private theorem couplingTransportCost_eq_zero_of_eq
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
    have hzero : γ a b * M.dist a b = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => mul_nonneg (hγ.1 a c) (M.dist_nonneg a c))).1
        (hrow_zero a ha) b hb
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (dist_pos_of_ne M hne))
  have hdiag : γ x x = μ.val x := by
    have hsumx : M.vertices.sum (γ x) = γ x x := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun h => absurd hx h)]
      simp
    rw [← hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun h => absurd hx h)]
    simp
  have hnu : ν.val x = γ x x := by rw [← hcol, hγ.2.2.2.2 x hx]
  linarith [hdiag, hnu]"""

if old_zero not in text:
    raise SystemExit("couplingTransportCost_eq_zero_of_eq block not found")
text = text.replace(old_zero, new_zero)

old_pos = """  · obtain ⟨y, hy, hlt⟩ := exists_mass_imbalance_neg M μ ν x hgt hx
    refine productCoupling_cost_pos M μ ν hx hy (by intro heq; subst heq; linarith) hgt ?_
    exact lt_of_le_of_ne (ν.2.1 y hy) (Ne.symm (sub_ne_zero.mpr hlt))
  · push Not at hgt
    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt (Ne.symm hdiff)
    obtain ⟨y, hy, hgt'⟩ := exists_mass_imbalance_pos M μ ν x hlt hx
    refine productCoupling_cost_pos M μ ν hy hx (by intro heq; subst heq; linarith) hgt' ?_
    exact lt_of_le_of_ne (μ.2.1 x hx) (Ne.symm (sub_ne_zero.mpr hdiff))"""

new_pos = """  · obtain ⟨y, hy, hlt⟩ := exists_mass_imbalance_neg M μ ν x hgt hx
    have hμpos : 0 < μ.val x := by linarith [μ.2.1 x hx, ν.2.1 x hx, hgt]
    have hνpos : 0 < ν.val y := by linarith [ν.2.1 y hy, μ.2.1 y hy, hlt]
    exact productCoupling_cost_pos M μ ν hx hy (by intro heq; subst heq; linarith) hμpos hνpos
  · push Not at hgt
    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff
    obtain ⟨y, hy, hgt'⟩ := exists_mass_imbalance_pos M μ ν x hlt hx
    have hμpos : 0 < μ.val y := by linarith [μ.2.1 y hy, ν.2.1 y hy, hgt']
    have hνpos : 0 < ν.val x := by linarith [ν.2.1 x hx, μ.2.1 x hx, hlt]
    exact productCoupling_cost_pos M μ ν hy hx (by intro heq; subst heq; linarith) hμpos hνpos"""

text = text.replace(old_pos, new_pos)

text = text.replace(
    "    field_simp [ne_of_gt h01]; linarith [hsum3, hδ0, hδ1]",
    "    field_simp [ne_of_gt h01]; nlinarith [hsum3, hδ0, hδ1, e2]",
)

# probExpectation true branch 1
text = text.replace(
    """    by_cases hthird : ∃ u ∈ M.vertices, u ≠ t0 ∧ u ≠ tMinus ∧ δ u ≠ 0
    · obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthird
      push Not at hthird
      have hut0ne : u ≠ t0 := hut0
      have hutMne : u ≠ tMinus := hutM
      have hΔ : M.dist t0 tMinus < M.dist t0 u + M.dist tMinus u := by
        have htri : M.dist t0 tMinus ≤ M.dist t0 u + M.dist tMinus u := by
          calc M.dist t0 tMinus ≤ M.dist t0 u + M.dist u tMinus := M.triangle t0 u tMinus
            _ = M.dist t0 u + M.dist tMinus u := by rw [M.dist_comm u tMinus]
        refine lt_of_le_of_ne htri ?_
        intro h_eq
        nlinarith [M.dist_nonneg, M.dist_comm, M.triangle t0 tMinus u, hut0ne, hutMne, hdistPM,
          dist_pos_of_ne M hut0ne, dist_pos_of_ne M hutMne]
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) (hu' : t ≠ u) :
          δ t = 0 := hthird t ht ht0' htM' hu'""",
    """    by_cases hthird : ∃ u ∈ M.vertices, u ≠ t0 ∧ u ≠ tMinus ∧ δ u ≠ 0
    · have hthirdEx := hthird
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
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) :
          δ t = 0 := by
        by_contra hδne
        exact absurd ⟨t, ht, ht0', htM', hδne⟩ hthirdEx""",
)

# probExpectation true branch 2
text = text.replace(
    """    by_cases hthird : ∃ u ∈ M.vertices, u ≠ tPlus ∧ u ≠ t0 ∧ δ u ≠ 0
    · obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthird
      push Not at hthird
      have hutPne : u ≠ tPlus := hutP
      have hut0ne : u ≠ t0 := hut0
      have hΔ : M.dist tPlus t0 < M.dist tPlus u + M.dist t0 u := by
        have htri : M.dist tPlus t0 ≤ M.dist tPlus u + M.dist t0 u := by
          calc M.dist tPlus t0 ≤ M.dist tPlus u + M.dist u t0 := M.triangle tPlus u t0
            _ = M.dist tPlus u + M.dist t0 u := by rw [M.dist_comm u t0]
        refine lt_of_le_of_ne htri ?_
        intro h_eq
        nlinarith [M.dist_nonneg, M.dist_comm, M.triangle tPlus t0 u, hutPne, hut0ne, hdistPM,
          dist_pos_of_ne M hutPne, dist_pos_of_ne M hut0ne]
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) (hu' : t ≠ u) :
          δ t = 0 := hthird t ht htP' ht0' hu'""",
    """    by_cases hthird : ∃ u ∈ M.vertices, u ≠ tPlus ∧ u ≠ t0 ∧ δ u ≠ 0
    · have hthirdEx := hthird
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
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) :
          δ t = 0 := by
        by_contra hδne
        exact absurd ⟨t, ht, htP', ht0', hδne⟩ hthirdEx""",
)

# false branches push_neg + hplus0
text = text.replace(
    """    · push Not at hthird
      have hδ0 (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) : δ t = 0 :=
        hthird t ht ht0' htM'
      have hdistPlus := hdist0
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0] at hdistPlus
      simp only [M.dist_self, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htMinusInErase] at hdistPlus
      have hrest0 : ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) = 0 :=
        Finset.sum_eq_zero fun t ht => by
          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)
          simp [hδ0 t htVert (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht), zero_mul]
      have hsplit :
          (M.vertices.erase t0).sum (fun t => δ t * M.dist t t0) =
            δ tMinus * M.dist tMinus t0 +
              ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) := by
        rw [← Finset.add_sum_erase (M.vertices.erase t0) (fun t => δ t * M.dist t t0) tMinus htMinusInErase]
      linarith [hdistPlus, hsplit, hrest0, hheadPlus]""",
    """    · push_neg at hthird
      have hδ0 (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) : δ t = 0 :=
        hthird t ht ht0' htM'
      have hdistPlus := hdist0
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0, M.dist_self t0, mul_zero, add_zero] at hdistPlus
      have hsumErase0 : (M.vertices.erase t0).sum (fun t => δ t * M.dist t t0) = 0 := by
        linarith [hdistPlus]
      have hrest0 : ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) = 0 :=
        Finset.sum_eq_zero fun t ht => by
          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)
          simp [hδ0 t htVert (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht), zero_mul]
      have hsplit :
          (M.vertices.erase t0).sum (fun t => δ t * M.dist t t0) =
            δ tMinus * M.dist tMinus t0 +
              ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) := by
        rw [← Finset.add_sum_erase (s := M.vertices.erase t0) (f := fun t => δ t * M.dist t t0)
          htMinusInErase]
      have hplus0 : δ tMinus * M.dist tMinus t0 = 0 := by linarith [hsumErase0, hsplit, hrest0]
      linarith [hheadPlus, hplus0]""",
)

text = text.replace(
    """    · push Not at hthird
      have hδ0 (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) : δ t = 0 :=
        hthird t ht htP' ht0'
      have hdistPlus := hdistP
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem] at hdistPlus
      simp only [M.dist_self, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase] at hdistPlus
      have hrest0 : ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) = 0 :=
        Finset.sum_eq_zero fun t ht => by
          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)
          simp [hδ0 t htVert (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht), zero_mul]
      have hsplit :
          (M.vertices.erase tPlus).sum (fun t => δ t * M.dist t tPlus) =
            δ t0 * M.dist t0 tPlus +
              ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) := by
        rw [← Finset.add_sum_erase (M.vertices.erase tPlus) (fun t => δ t * M.dist t tPlus) t0 ht0InErase]
      linarith [hdistPlus, hsplit, hrest0, hheadPlus]""",
    """    · push_neg at hthird
      have hδ0 (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) : δ t = 0 :=
        hthird t ht htP' ht0'
      have hdistPlus := hdistP
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem, M.dist_self tPlus, mul_zero,
        add_zero] at hdistPlus
      have hsumErase0 : (M.vertices.erase tPlus).sum (fun t => δ t * M.dist t tPlus) = 0 := by
        linarith [hdistPlus]
      have hrest0 : ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) = 0 :=
        Finset.sum_eq_zero fun t ht => by
          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)
          simp [hδ0 t htVert (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht), zero_mul]
      have hsplit :
          (M.vertices.erase tPlus).sum (fun t => δ t * M.dist t tPlus) =
            δ t0 * M.dist t0 tPlus +
              ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) := by
        rw [← Finset.add_sum_erase (s := M.vertices.erase tPlus) (f := fun t => δ t * M.dist t tPlus)
          ht0InErase]
      have hplus0 : δ t0 * M.dist t0 tPlus = 0 := by linarith [hsumErase0, hsplit, hrest0]
      linarith [hheadPlus, hplus0]""",
)

# glued coupling fixes
text = text.replace(
    """private theorem gluedCoupling_left_outside (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : ∀ x hx y, x ∉ S → γ₁ x y = 0) (x : ℕ) (hx : x ∉ S) (z : ℕ) :
    gluedCoupling S ν γ₁ γ₂ x z = 0 := by
  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _; split_ifs <;> simp [hγ₁ x hx]""",
    """private theorem gluedCoupling_left_outside (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : ∀ x y, x ∉ S → γ₁ x y = 0) (x : ℕ) (hx : x ∉ S) (z : ℕ) :
    gluedCoupling S ν γ₁ γ₂ x z = 0 := by
  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _; by_cases hν : ν.val y = 0 <;> simp [hγ₁ x hx y, *]""",
)

text = text.replace(
    """  · exact hγ.2.2.1 x hx w""",
    """  · exact hγ.2.1 x hx w""",
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
      simp [hν, Finset.sum_eq_zero fun x' _ => by simp [hcol x']]
    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by
        rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
    """    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'
      simp [hν, hcol, Finset.sum_const_zero]
    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by
        have hconst : ∀ x', γ₁ x' w * γ₂ w z / ν.val w = (γ₂ w z / ν.val w) * γ₁ x' w := fun x' => by ring
        rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
)

text = text.replace(
    """  · intro x hx y; exact gluedCoupling_left_outside M.vertices ν γ₁ γ₂ (fun a ha b => hγ₁.2.1 a ha b) x hx y
  · intro y hy x; exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂ (fun w z hz => hγ₂.2.2.1 w hz z) y hy x""",
    """  · intro x hx y; exact gluedCoupling_left_outside M.vertices ν γ₁ γ₂ (fun a ha b => hγ₁.2.1 a ha b) x hx y
  · intro y hy x; exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂ (fun w z hz => hγ₂.2.2.1 z hz w) y hy x""",
)

# gluedCoupling_cost_le hsplit + hterm + calc
old_hsplit = """    congr 1; ext w hw
    by_cases hν : ν.val w = (0 : ℝ)
    · simp [hν]
    · rw [if_neg hν, if_neg hν]
      have hν' : ν.val w ≠ 0 := Ne.symm hν
      have hcol : M.vertices.sum (fun z => γ₂ w z) = ν.val w := hγ₂.2.2.2.1 w hw
      rw [Finset.mul_sum, ← Finset.sum_mul, mul_add]
      have hleft : (γ₁ x w / ν.val w) * M.vertices.sum (fun z => γ₂ w z * M.dist x w) =
          γ₁ x w * M.dist x w := by rw [Finset.sum_mul, hcol, mul_div_cancel₀ _ hν']
      rw [hleft]; ring"""

new_hsplit = """    congr 1; ext w
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
          rw [hcol, mul_div_cancel₀ _ hν']; ring"""

text = text.replace(old_hsplit, new_hsplit)

text = text.replace(
    """      rw [mul_comm (M.dist x z), mul_comm (M.dist x w + M.dist w z)]
      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv""",
    """      calc (γ₁ x w * γ₂ w z / ν.val w) * M.dist x z
          ≤ (γ₁ x w * γ₂ w z / ν.val w) * (M.dist x w + M.dist w z) :=
            mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv
        _ = (γ₁ x w * γ₂ w z / ν.val w) * (M.dist x w + M.dist w z) := rfl""",
)

text = text.replace(
    """      apply add_le_add_left le_rfl
      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
      exact hbound""",
    """      apply add_le_add le_rfl
      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
      exact hbound""",
)

if "sorry" in text.replace("declared (sorry)", ""):
    raise SystemExit("sorry found")

out = Path("/Users/nova/ugp-lean-exp/UgpLean/ContinuumLimit/WassersteinDistance.lean.final")
out.write_text(text)
print(f"Wrote {out} ({text.count(chr(10))+1} lines)")
