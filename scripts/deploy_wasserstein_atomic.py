#!/usr/bin/env python3
"""Atomically deploy WassersteinDistance.lean from canonical + fixes."""
import os
from pathlib import Path

src = Path("/Users/nova/ugp-lean-exp/scripts/WassersteinDistance_canonical.lean")
dst = Path("/Users/nova/ugp-lean-exp/UgpLean/ContinuumLimit/WassersteinDistance.lean")
tmp = dst.with_suffix(".lean.tmpdeploy")

text = src.read_text()
text = text.replace("push_neg", "push Not")
text = text.replace(
    "have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt (Ne.symm hdiff)",
    "have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff",
)

old_calc = """  calc
    M.vertices.sum fun x => M.vertices.sum fun z => M.dist x z * γ₃ x z ≤
        M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = (0 : ℝ) then (0 : ℝ) else
                γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => hterm x z
    _ = M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w =>
            if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := hsplit
    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      unfold couplingTransportCost
      rw [← Finset.sum_add_distrib]
      apply add_le_add le_rfl
      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
      exact hbound"""

new_end = """  have hle_triple :
      M.vertices.sum fun x => M.vertices.sum fun z => M.dist x z * γ₃ x z ≤
        M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = (0 : ℝ) then (0 : ℝ) else
                γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) := by
    refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun z hz => hterm x z
  have hle_final :
      M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w =>
            if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z ≤
        couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
    rw [show couplingTransportCost M γ₁ =
          M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w from rfl,
        show couplingTransportCost M γ₂ =
          M.vertices.sum fun w => M.vertices.sum fun z => γ₂ w z * M.dist w z from rfl]
    rw [← Finset.sum_add_distrib]
    apply add_le_add_left le_rfl
    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    exact hbound
  exact le_trans (hsplit ▸ hle_triple) hle_final"""

if old_calc not in text:
    raise SystemExit("calc block not found in canonical")
text = text.replace(old_calc, new_end)

old_w1 = """theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
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
    · exact W1_nonneg M μ μ"""

new_w1 = """theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  constructor
  · intro hW1 x hx
    by_contra hne
    have hpos := W1_pos_of_vertex_ne M μ ν ⟨x, hx, hne⟩
    linarith [W1_nonneg M μ ν, hW1]
  · intro h
    have hμν : μ = ν := probDist_eq_of_vertex_weights_eq h
    subst hμν
    apply le_antisymm
    · have hle := W1_le_couplingCost M μ μ (diagonalCoupling M.vertices μ)
        (diagonalCoupling_is_coupling M.vertices μ)
      rw [diagonalCoupling_cost_zero M μ] at hle
      exact hle
    · exact W1_nonneg M μ μ"""

text = text.replace(old_w1, new_w1)
text = text.replace(
    "axiom gorard_vacuum_oric_zero",
    '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\naxiom gorard_vacuum_oric_zero',
    1,
)

if "sorry" in text.replace("- A declared (sorry)", ""):
    raise SystemExit("sorry in output")

tmp.write_text(text)
os.replace(tmp, dst)
print(f"Deployed {len(text.splitlines())} lines -> {dst}")
