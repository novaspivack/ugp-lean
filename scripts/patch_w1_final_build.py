#!/usr/bin/env python3
"""Patch w1_restore.lean into buildable WassersteinDistance.lean."""
from pathlib import Path

src = Path("/tmp/w1_restore.lean").read_text()
text = src

# diagonalCoupling_right_outside
text = text.replace(
    "  · rw [if_pos h]; exact μ.2.2.1 y hy",
    "  · simp [h, μ.2.2.1 y hy]",
)

# exists_mass_imbalance_pair (only in that theorem)
text = text.replace(
    """  · push Not at hgt
    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt (Ne.symm hdiff)
    obtain ⟨xPlus, hxPlus, hgt'⟩ := exists_mass_imbalance_pos M μ ν x hlt hx""",
    """  · push Not at hgt
    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff
    obtain ⟨xPlus, hxPlus, hgt'⟩ := exists_mass_imbalance_pos M μ ν x hlt hx""",
)

# couplingTransportCost_eq_zero_of_eq calc -> hdiag/hcol
old_zero = """  calc
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

new_zero = """  have hdiag : γ x x = μ.val x := by
    have hsumx : M.vertices.sum (γ x) = γ x x := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun hne => absurd hx hne)]
      simp
    rw [← hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]
    simp
  have hnu : ν.val x = γ x x := by rw [← hcol, hγ.2.2.2.2 x hx]
  linarith [hdiag, hnu]"""

if old_zero not in text:
    raise SystemExit("couplingTransportCost_eq_zero_of_eq block not found")
text = text.replace(old_zero, new_zero)

# couplingTransportCost_pos_of_vertex_ne (before global Ne.symm replace)
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

if old_pos not in text:
    raise SystemExit("couplingTransportCost_pos block not found")
text = text.replace(old_pos, new_pos)

# Fix hoff hterm line
text = text.replace(
    """    have hterm := (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => hnn)).1 (hrow_zero a ha) b hb
    exact (mul_eq_zero.mp hterm).resolve_right (ne_of_gt (dist_pos_of_ne M hne))""",
    """    have hterm_nn : ∀ c ∈ M.vertices, 0 ≤ γ a c * M.dist a c :=
      fun c hc => mul_nonneg (hγ.1 a c) (M.dist_nonneg a c)
    have hzero : γ a b * M.dist a b = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nn).1 (hrow_zero a ha) b hb
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (dist_pos_of_ne M hne))""",
)

# delta_three_anchor hsum'
text = text.replace(
    "    field_simp [ne_of_gt h01]; linarith [hsum3, hδ0, hδ1]",
    "    field_simp [ne_of_gt h01]; nlinarith [hsum3, hδ0, hδ1, e2]",
)

# probExpectation_dist_sub args
text = text.replace(
    "    rw [← probExpectation_dist_sub, h a ha, sub_self]",
    "    rw [← probExpectation_dist_sub M μ ν a, h a ha, sub_self]",
)

# hδrest in true branches handled via hδvanish block replacement below

# two-anchor linarith: add hplus0
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

# gluedCoupling fixes
text = text.replace(
    """private theorem gluedCoupling_left_outside (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : ∀ x hx y, x ∉ S → γ₁ x y = 0) (x : ℕ) (hx : x ∉ S) (z : ℕ) :""",
    """private theorem gluedCoupling_left_outside (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : ∀ x y, x ∉ S → γ₁ x y = 0) (x : ℕ) (hx : x ∉ S) (z : ℕ) :""",
)

text = text.replace(
    "  · intro y hy x; exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂ (fun w z hz => hγ₂.2.2.1 w hz z) y hy x",
    "  · intro y hy x; exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂ (fun w z hz => hγ₂.2.2.1 z hz w) y hy x",
)

text = text.replace(
    "      simp [hν, Finset.sum_eq_zero fun x' _ => by simp [hcol x']]",
    "      simp [hν, hcol]",
)

text = text.replace(
    "    congr 1; ext w hw\n    by_cases hν : ν.val w = (0 : ℝ)",
    "    congr 1; ext w\n    intro hw\n    by_cases hν : ν.val w = (0 : ℝ)",
)

# exists_mass_imbalance: use sum_pos' / sum_neg' like restore
text = text.replace(
    """  have hsumpos : 0 < M.vertices.sum (fun t => μ.val t - ν.val t) :=
    lt_of_lt_of_le hpos (Finset.single_le_sum hnonneg hx)
  linarith""",
    """  have hsumpos : 0 < M.vertices.sum (fun t => μ.val t - ν.val t) :=
    Finset.sum_pos' hnonneg ⟨x, hx, hpos⟩
  linarith""",
)
text = text.replace(
    """  have hsumneg : M.vertices.sum (fun t => μ.val t - ν.val t) < 0 :=
    Finset.sum_neg' hnonpos ⟨x, hx, hneg⟩
  linarith""",
    """  have hsumneg : M.vertices.sum (fun t => μ.val t - ν.val t) < 0 :=
    Finset.sum_neg' hnonpos ⟨x, hx, hneg⟩
  linarith""",
)
text = text.replace("by_contra hall; push_neg at hall", "by_contra hall; push Not at hall")
text = text.replace("  · push_neg at hgt", "  · push Not at hgt")
text = text.replace("  by_contra hall; push_neg at hall", "  by_contra hall; push Not at hall")
text = text.replace("  by_contra hnot; push_neg at hnot", "  by_contra hnot; push Not at hnot")
text = text.replace("    · push_neg at hthird", "    · push Not at hthird")
text = text.replace("  · push_neg at ht0pos", "  · push Not at ht0pos")

# hδrest: restore cbabcc7 pattern (push Not after obtain)
text = text.replace(
    """      have hδvanish (v : ℕ) (hv : v ∈ M.vertices) : v = t0 ∨ v = tMinus ∨ δ v = 0 := by
        rcases em (v = t0) with ht0eq | ht0ne'
        · exact Or.inl ht0eq
        rcases em (v = tMinus) with htMeq | htMne'
        · exact Or.inr (Or.inl htMeq)
        rcases em (δ v = 0) with hδeq | hδne'
        · exact Or.inr (Or.inr hδeq)
        · exact absurd ⟨v, hv, ht0ne', htMne', hδne'⟩ hthird
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) (hu' : t ≠ u) :
          δ t = 0 := by
        by_cases htu : t = u
        · subst htu; exfalso; exact hudne rfl
        · rcases hδvanish t ht with h | h | hδ
          · exact absurd h ht0'
          · exact absurd h htM'
          · exact hδ""",
    """      push Not at hthird
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) (hu' : t ≠ u) :
          δ t = 0 := by
        rcases hthird t ht with h | h | h
        · exact absurd h ht0'
        · exact absurd h htM'
        · exact h""",
)

text = text.replace(
    """      have hδvanish (v : ℕ) (hv : v ∈ M.vertices) : v = tPlus ∨ v = t0 ∨ δ v = 0 := by
        rcases em (v = tPlus) with htPeq | htPne'
        · exact Or.inl htPeq
        rcases em (v = t0) with ht0eq | ht0ne'
        · exact Or.inr (Or.inl ht0eq)
        rcases em (δ v = 0) with hδeq | hδne'
        · exact Or.inr (Or.inr hδeq)
        · exact absurd ⟨v, hv, htPne', ht0ne', hδne'⟩ hthird
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) (hu' : t ≠ u) :
          δ t = 0 := by
        by_cases htu : t = u
        · subst htu; exfalso; exact hudne rfl
        · rcases hδvanish t ht with h | h | hδ
          · exact absurd h htP'
          · exact absurd h ht0'
          · exact hδ""",
    """      push Not at hthird
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) (hu' : t ≠ u) :
          δ t = 0 := by
        rcases hthird t ht with h | h | h
        · exact absurd h htP'
        · exact absurd h ht0'
        · exact h""",
)

# delta hsum' use nlinarith
text = text.replace(
    "    field_simp [ne_of_gt h01]; linarith [hsum3, hδ0, hδ1]",
    "    field_simp [ne_of_gt h01]; nlinarith [hsum3, hδ0, hδ1, e2]",
)

# W1_eq_zero_iff use push Not
text = text.replace(
    """      by_contra hall
      push_neg at hall
      exact hμν (probDist_eq_of_vertex_weights_eq hall)""",
    """      by_contra hall
      push Not at hall
      exact hμν (probDist_eq_of_vertex_weights_eq hall)""",
)

# Remove duplicate W1_pos if present from merge
while text.count("private theorem W1_pos_of_vertex_ne") > 1:
    first = text.index("private theorem W1_pos_of_vertex_ne")
    second = text.index("private theorem W1_pos_of_vertex_ne", first + 1)
    # remove second block up to next private/theorem at column 0
    end = text.index("\nprivate theorem ", second + 1)
    if end < second:
        end = text.index("\ntheorem ", second + 1)
    text = text[:second] + text[end:]

# W1_triangle linarith at end - use hc₁lt' pattern if missing
if "have hc₁lt' : c₁ < W1 M μ ν + ε / 2" not in text:
    text = text.replace(
        """  have hc₁lt' : c₁ < W1 M μ ν + ε / 2 := by simpa [W1] using hc₁lt
  have hc₂lt' : c₂ < W1 M ν ρ + ε / 2 := by simpa [W1] using hc₂lt
  linarith [hle, hcost, hc₁lt', hc₂lt', hW1μν, hW1νρ]""",
        """  have hc₁lt' : c₁ < W1 M μ ν + ε / 2 := by simpa [W1] using hc₁lt
  have hc₂lt' : c₂ < W1 M ν ρ + ε / 2 := by simpa [W1] using hc₂lt
  linarith [hle, hcost, hc₁lt', hc₂lt', hW1μν, hW1νρ]""",
    )

if "sorry" in text.replace("declared (sorry)", ""):
    raise SystemExit("sorry found in output")

out = Path("/Users/nova/ugp-lean-exp/UgpLean/ContinuumLimit/WassersteinDistance.lean.staging")
out.write_text(text)
print(f"Wrote {out} ({text.count(chr(10))+1} lines)")
