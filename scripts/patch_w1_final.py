#!/usr/bin/env python3
"""Apply known-good patches to WassersteinDistance.lean."""
from pathlib import Path

P = Path("/Users/nova/ugp-lean-exp/UgpLean/ContinuumLimit/WassersteinDistance.lean")
t = P.read_text()

replacements = [
    # diagonalCoupling_right_outside
    (
        "  · rw [if_pos h]; exact μ.2.2.1 y hy",
        "  · rw [h]; exact μ.2.2.1 y hy",
    ),
    # exists_mass_imbalance_pair hlt branch
    (
        "    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt (Ne.symm hdiff)",
        "    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff",
    ),
    # couplingTransportCost_eq_zero_of_eq — use sum_eq_single apply pattern
    (
        """  have hnn : 0 ≤ γ a b * M.dist a b := mul_nonneg (hγ.1 a b) (M.dist_nonneg a b)
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
    _ = ν.val x := hγ.2.2.2.2 x hx""",
        """    have hterm_nn : ∀ c ∈ M.vertices, 0 ≤ γ a c * M.dist a c :=
      fun c hc => mul_nonneg (hγ.1 a c) (M.dist_nonneg a c)
    have hzero : γ a b * M.dist a b = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nn).1 (hrow_zero a ha) b hb
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (dist_pos_of_ne M hne))
  have hdiag : γ x x = μ.val x := by
    rw [← hγ.2.2.2.1 x hx]
    apply Finset.sum_eq_single x
    · intro y hy hne; exact hoff x y hx hy hne
    · intro h; exact absurd hx h
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    apply Finset.sum_eq_single x
    · intro z hz hne; exact hoff z x hz hx hne
    · intro h; exact absurd hx h
  have hnu : ν.val x = γ x x := by rw [← hcol, hγ.2.2.2.2 x hx]
  linarith [hdiag, hnu]""",
    ),
    # productCoupling_pos
    (
        """  · obtain ⟨y, hy, hlt⟩ := exists_mass_imbalance_neg M μ ν x hgt hx
    refine productCoupling_cost_pos M μ ν hx hy (by intro heq; subst heq; linarith) hgt ?_
    exact lt_of_le_of_ne (ν.2.1 y hy) (Ne.symm (sub_ne_zero.mpr hlt))
  · push Not at hgt
    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt (Ne.symm hdiff)
    obtain ⟨y, hy, hgt'⟩ := exists_mass_imbalance_pos M μ ν x hlt hx
    refine productCoupling_cost_pos M μ ν hy hx (by intro heq; subst heq; linarith) hgt' ?_
    exact lt_of_le_of_ne (μ.2.1 x hx) (Ne.symm (sub_ne_zero.mpr hdiff))""",
        """  · obtain ⟨y, hy, hlt⟩ := exists_mass_imbalance_neg M μ ν x hgt hx
    have hμpos : 0 < μ.val x := lt_of_le_of_ne (μ.2.1 x hx) (Ne.symm (sub_ne_zero.mpr hgt))
    have hνpos : 0 < ν.val y := lt_of_le_of_ne (ν.2.1 y hy) (Ne.symm (sub_ne_zero.mpr hlt))
    exact productCoupling_cost_pos M μ ν hx hy (by intro heq; subst heq; linarith) hμpos hνpos
  · push Not at hgt
    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff
    obtain ⟨y, hy, hgt'⟩ := exists_mass_imbalance_pos M μ ν x hlt hx
    have hμpos : 0 < μ.val y := lt_of_le_of_ne (μ.2.1 y hy) (Ne.symm (sub_ne_zero.mpr hgt'))
    have hνpos : 0 < ν.val x := lt_of_le_of_ne (ν.2.1 x hx) (Ne.symm hdiff)
    exact productCoupling_cost_pos M μ ν hy hx (by intro heq; subst heq; linarith) hμpos hνpos""",
    ),
    # delta_three hsum'
    (
        "    field_simp [ne_of_gt h01]; linarith [hsum3, hδ0, hδ1]",
        "    field_simp [ne_of_gt h01]; nlinarith [hsum3, hδ0, hδ1]",
    ),
    # hδ0 subst branch
    (
        "        · subst htu; exact hudne rfl",
        "        · subst htu; exfalso; exact hudne rfl",
    ),
    # second hthird branch — replace broken block start
    (
        """    · obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthird
      push Not at hthird
      have hutPne : u ≠ tPlus := hutP
      have hut0ne : u ≠ t0 := hut0
      have hΔ : M.dist tPlus t0 < M.dist tPlus u + M.dist t0 u := by""",
        """    · have hthirdEx := hthird
      obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthirdEx
      have hutPne : u ≠ tPlus := hutP
      have hut0ne : u ≠ t0 := hut0
      have hΔ : M.dist tPlus t0 < M.dist tPlus u + M.dist t0 u := by""",
    ),
    # exists_probExpectation
    (
        "  exact hdiff (probExpectation_dist_eq_all_imp_vertex_eq M μ ν heq x hx)",
        "  exact absurd hdiff (probExpectation_dist_eq_all_imp_vertex_eq M μ ν heq x hx)",
    ),
    # gluedCoupling row inner
    (
        "        rw [Finset.sum_mul, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]",
        "        rw [← Finset.mul_sum, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]",
    ),
    # gluedCoupling col inner
    (
        "        rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]",
        "        rw [← Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]",
    ),
    # col zero branch
    (
        "      simp [hν, Finset.sum_eq_zero fun x' _ => by simp [hcol x']]",
        "      simp [hν, hcol]",
    ),
    # gluedCoupling_is_coupling
    (
        "  · intro y hy x; exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂ (fun w z hz => hγ₂.2.2.1 w hz z) y hy x\n  · exact gluedCoupling_row_sum M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂\n  · exact gluedCoupling_col_sum M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂",
        "  · intro y hy x; exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂ (fun w z hz => hγ₂.2.2.1 z hz w) y hy x\n  · intro x hx; exact gluedCoupling_row_sum M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂ x hx\n  · intro y hy; exact gluedCoupling_col_sum M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂ y hy",
    ),
    # hsplit ext
    (
        "    congr 1; ext w hw\n    by_cases hν : ν.val w = (0 : ℝ)\n    · simp [hν]",
        "    congr 1; ext w\n    intro hw\n    by_cases hν : ν.val w = (0 : ℝ)\n    · have hγxw := coupling_col_zero_of_mass_zero hγ₁ w hw hν x\n      simp [hν, hγxw, zero_mul, mul_zero, add_zero]",
    ),
    # gorard deprecated
    (
        "axiom gorard_vacuum_oric_zero",
        "@[deprecated \"Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped\" (since := \"2026-05-31\")]\naxiom gorard_vacuum_oric_zero",
    ),
    # W1_triangle linarith
    (
        "  unfold W1 at hle hW1μν hW1νρ ⊢\n  linarith [hle, hcost, hc₁lt, hc₂lt, hW1μν, hW1νρ]",
        """  have hc₁lt' : c₁ < W1 M μ ν + ε / 2 := by simpa [W1] using hc₁lt
  have hc₂lt' : c₂ < W1 M ν ρ + ε / 2 := by simpa [W1] using hc₂lt
  linarith [hle, hcost, hc₁lt', hc₂lt', hW1μν, hW1νρ]""",
    ),
]

for old, new in replacements:
    if old not in t:
        print(f"MISSING PATCH:\n{old[:80]}...")
    else:
        t = t.replace(old, new, 1)

if "sorry" in t.replace("declared (sorry)", ""):
    raise SystemExit("proof sorry found")

P.write_text(t)
print(f"Patched {P} ({t.count(chr(10))+1} lines)")
