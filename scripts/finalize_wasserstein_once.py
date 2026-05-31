#!/usr/bin/env python3
"""Apply all WassersteinDistance fixes and build."""
import os
import re
import subprocess
from pathlib import Path

CANON = Path("/Users/nova/ugp-lean-exp/scripts/WassersteinDistance_canonical.lean")
TARGET = Path("/Users/nova/ugp-lean-exp/UgpLean/ContinuumLimit/WassersteinDistance.lean")

text = CANON.read_text()
text = text.replace("push_neg", "push Not")

# prob-gap true branch pattern (both occurrences)
OLD_TRUE = """    · obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthird
      push Not at hthird
      have hut0ne : u ≠ t0 := hut0
      have hutMne : u ≠ tMinus := hutM"""

NEW_TRUE = """    · have hthirdEx := hthird
      obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthirdEx
      have hut0ne : u ≠ t0 := hut0
      have hutMne : u ≠ tMinus := hutM"""

OLD_TRUE2 = """    · obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthird
      push Not at hthird
      have hutPne : u ≠ tPlus := hutP
      have hut0ne : u ≠ t0 := hut0"""

NEW_TRUE2 = """    · have hthirdEx := hthird
      obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthirdEx
      have hutPne : u ≠ tPlus := hutP
      have hut0ne : u ≠ t0 := hut0"""

OLD_HDELTA = """      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) (hu' : t ≠ u) :
          δ t = 0 := by
        rcases hthird t ht with h | h | h0
        · exact absurd h ht0'
        · exact absurd h htM'
        · exact h0"""

NEW_HDELTA = """      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) (hu' : t ≠ u) :
          δ t = 0 := by
        by_contra hδne
        exact absurd ⟨t, ht, ht0', htM', hδne⟩ hthirdEx"""

OLD_HDELTA2 = """      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) (hu' : t ≠ u) :
          δ t = 0 := by
        rcases hthird t ht with h | h | h0
        · exact absurd h htP'
        · exact absurd h ht0'
        · exact h0"""

NEW_HDELTA2 = """      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) (hu' : t ≠ u) :
          δ t = 0 := by
        by_contra hδne
        exact absurd ⟨t, ht, htP', ht0', hδne⟩ hthirdEx"""

for o, n in [
    (OLD_TRUE, NEW_TRUE),
    (OLD_TRUE2, NEW_TRUE2),
    (OLD_HDELTA, NEW_HDELTA),
    (OLD_HDELTA2, NEW_HDELTA2),
    (
        "have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt (Ne.symm hdiff)",
        "have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff",
    ),
]:
    if o not in text:
        raise SystemExit(f"MISSING: {o[:60]!r}")
    text = text.replace(o, n)

# second false branch: add hplus0
OLD_FB2 = """      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem] at hdistPlus
      rw [Finset.sdiff_singleton_eq_erase] at hdistPlus
      simp only [M.dist_self tPlus, mul_zero, add_zero] at hdistPlus
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
      linarith [hsumErase0, hsplit, hrest0, hheadPlus]"""

NEW_FB2 = """      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem, M.dist_self tPlus, mul_zero,
        add_zero] at hdistPlus
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
      have hplus0 : δ t0 * M.dist t0 tPlus = 0 := by linarith [hdistPlus, hsplit, hrest0]
      linarith [hheadPlus, hplus0]"""

if OLD_FB2 in text:
    text = text.replace(OLD_FB2, NEW_FB2)

# gluedCoupling_cost_le ending: replace calc block
calc_pat = re.compile(
    r"  calc\n    M\.vertices\.sum fun x => M\.vertices\.sum fun z => M\.dist x z \* γ₃ x z ≤.*?exact hbound\n",
    re.DOTALL,
)
NEW_END = """  have hle_triple :
      (M.vertices.sum fun x => M.vertices.sum fun z => M.dist x z * γ₃ x z) ≤
      (M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = (0 : ℝ) then (0 : ℝ) else
                γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z)) := by
    refine Finset.sum_le_sum fun x hx => Finset.sum_le_sum fun z hz => hterm x z
  have hle_final :
      (M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w =>
            if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z) ≤
      (M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w => M.vertices.sum fun z => γ₂ w z * M.dist w z) := by
    rw [← Finset.sum_add_distrib]
    apply add_le_add_left le_rfl
    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    exact hbound
  exact le_trans (hsplit ▸ hle_triple) hle_final

"""
text, n = calc_pat.subn(NEW_END, text)
if n != 1:
    raise SystemExit(f"calc replace count {n}")

OLD_W1 = """theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
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

NEW_W1 = """theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
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

text = text.replace(OLD_W1, NEW_W1)
if "axiom gorard_vacuum_oric_zero" in text and "deprecated" not in text.split("axiom gorard_vacuum_oric_zero")[0][-200:]:
    text = text.replace(
        "axiom gorard_vacuum_oric_zero",
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\naxiom gorard_vacuum_oric_zero',
        1,
    )

if "sorry" in text.replace("- A declared (sorry)", ""):
    raise SystemExit("sorry remains")

for m in ("hthirdEx", "W1_eq_zero_iff", "dist_eq_zero_iff", "le_trans (hsplit"):
    if m not in text:
        raise SystemExit(f"missing marker {m}")

CANON.write_text(text)
subprocess.run(["chflags", "nouchg", str(TARGET)], check=False)
TARGET.write_text(text)
subprocess.run(["chflags", "uchg", str(TARGET)], check=True)
subprocess.run(["chflags", "uchg", str(CANON)], check=True)

for p in Path("/Users/nova/ugp-lean-exp/.lake/build/lib/UgpLean/ContinuumLimit").glob("WassersteinDistance*"):
    p.unlink()

r = subprocess.run(
    ["lake", "build", "UgpLean.ContinuumLimit.WassersteinDistance", "UgpLean.ContinuumLimit.GorardVacuumW1Bridge"],
    cwd="/Users/nova/ugp-lean-exp",
)
print("lines", len(text.splitlines()), "exit", r.returncode)
raise SystemExit(r.returncode)
