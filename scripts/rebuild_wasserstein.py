#!/usr/bin/env python3
"""Rebuild WassersteinDistance.lean from git cbabcc7 with known-good proof patches."""
from __future__ import annotations

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"

base = subprocess.check_output(
    ["git", "show", "cbabcc7:UgpLean/ContinuumLimit/WassersteinDistance.lean"],
    cwd=ROOT,
    text=True,
)

# --- diagonalCoupling_right_outside ---
base = base.replace(
    "  · simp [h, μ.2.2.1 y hy]",
    "  · subst h; simp [μ.2.2.1 y hy]",
)

# --- couplingTransportCost_eq_zero_of_eq ---
base = base.replace(
    """  have hdiag : γ x x = μ.val x := by
    have hsumx : γ x x = M.vertices.sum (γ x) := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne.symm) (fun hne => absurd hx hne)]
    rw [hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne.symm) (fun hne => absurd hx hne)]
  have hnu : ν.val x = γ x x := by rw [← hcol, hγ.2.2.2.2 x hx]""",
    """  have hdiag : γ x x = μ.val x := by
    have hsumx : γ x x = M.vertices.sum (γ x) := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun hne => absurd hx hne)]
      simp
    rw [hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]
    simp
  have hnu : ν.val x = γ x x := by rw [← hcol, hγ.2.2.2.2 x hx]""",
)

# --- couplingTransportCost_pos_of_vertex_ne ---
base = base.replace(
    """  · obtain ⟨y, hy, hlt⟩ := exists_mass_imbalance_neg M μ ν x hgt hx
    refine productCoupling_cost_pos M μ ν hx hy (by intro heq; subst heq; linarith) hgt
      (lt_of_le_of_ne (ν.2.1 y hy) (sub_ne_zero.mpr hlt))
  · push Not at hgt
    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff
    obtain ⟨y, hy, hgt'⟩ := exists_mass_imbalance_pos M μ ν x hlt hx
    refine productCoupling_cost_pos M μ ν hy hx (by intro heq; subst heq; linarith)
      (lt_of_le_of_ne (μ.2.1 x hx) hdiff)
      (lt_of_le_of_ne (ν.2.1 y hy) (sub_ne_zero.mpr hlt))""",
    """  · obtain ⟨y, hy, hlt⟩ := exists_mass_imbalance_neg M μ ν x hgt hx
    have hμpos : 0 < μ.val x := by linarith [μ.2.1 x hx, ν.2.1 x hx, hgt]
    have hνpos : 0 < ν.val y := by linarith [ν.2.1 y hy, μ.2.1 y hy, hlt]
    exact productCoupling_cost_pos M μ ν hx hy (by intro heq; subst heq; linarith) hμpos hνpos
  · push Not at hgt
    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff
    obtain ⟨y, hy, hgt'⟩ := exists_mass_imbalance_pos M μ ν x hlt hx
    have hμpos : 0 < μ.val y := by linarith [μ.2.1 y hy, ν.2.1 y hy, hgt']
    have hνpos : 0 < ν.val x := by linarith [ν.2.1 x hx, μ.2.1 x hx, hlt]
    exact productCoupling_cost_pos M μ ν hy hx (by intro heq; subst heq; linarith) hμpos hνpos""",
)

# --- probExpectation three-point hδrest (both branches) ---
for old in [
    """          δ t = 0 := by
        by_cases htu : t = u
        · subst htu; exact absurd rfl hudne
        · rcases hex t ht with h | h | hδ
          · exact absurd h ht0'
          · exact absurd h htM'
          · exact hδ""",
    """          δ t = 0 := by
        by_cases htu : t = u
        · subst htu; exact absurd rfl hudne
        · rcases hex t ht with h | h | hδ
          · exact absurd h htP'
          · exact absurd h ht0'
          · exact hδ""",
]:
    new = old.replace("rcases hex t ht", "rcases hδvanish t ht").replace(
        "exact absurd rfl hudne", "exfalso; exact hudne rfl"
    )
    base = base.replace(old, new)

# Replace broken hex blocks with hδvanish definition
base = base.replace(
    """    · let hex := hthird
      obtain ⟨u, hu, hut0, hutM, hudne⟩ := hex
      push Not at hex
      have hut0ne : u ≠ t0 := hut0
      have hutMne : u ≠ tMinus := hutM""",
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
      have hutMne : u ≠ tMinus := hutM""",
)

base = base.replace(
    """    · let hex := hthird
      obtain ⟨u, hu, hutP, hut0, hudne⟩ := hex
      push Not at hex
      have hutPne : u ≠ tPlus := hutP
      have hut0ne : u ≠ t0 := hut0""",
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
      have hut0ne : u ≠ t0 := hut0""",
)

# --- two-point hdistPlus rewrites ---
base = base.replace(
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0, M.dist_self, mul_zero, add_zero] at hdistPlus",
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0, M.dist_self t0, mul_zero, add_zero] at hdistPlus",
)
base = base.replace(
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem, M.dist_self, mul_zero, add_zero] at hdistPlus",
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem, M.dist_self tPlus, mul_zero, add_zero] at hdistPlus",
)

# --- gluedCoupling ---
base = base.replace(
    "        rw [Finset.sum_mul, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]",
    "        rw [← Finset.mul_sum, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]",
)
base = base.replace(
    "        rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]",
    "        rw [Finset.sum_mul_comm, hγ₁.2.2.2.2 w hw, mul_div_cancel₀ _ (Ne.symm hν)]",
)

# --- gluedCoupling_cost_le ---
base = base.replace(
    """    by_cases hν : ν.val w = (0 : ℝ)
    · simp [hν]
    · rw [if_neg hν, if_neg hν]
      have hν' : ν.val w ≠ 0 := Ne.symm hν
      have hcol : M.vertices.sum (fun z => γ₂ w z) = ν.val w := hγ₂.2.2.2.1 w hw
      calc""",
    """    by_cases hν : ν.val w = (0 : ℝ)
    · have hγxw := coupling_col_zero_of_mass_zero hγ₁ w hw hν x
      rw [if_pos hν, if_pos hν]
      simp [hγxw, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
    · rw [if_neg hν, if_neg hν]
      have hν' : ν.val w ≠ 0 := Ne.symm hν
      have hcol : M.vertices.sum (fun z => γ₂ w z) = ν.val w := hγ₂.2.2.2.1 w hw
      calc""",
)

base = base.replace(
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

OUT.write_text(base)
print(f"Wrote {len(base.splitlines())} lines to {OUT}")
