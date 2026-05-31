#!/usr/bin/env python3
"""Deploy a clean, building WassersteinDistance.lean from canonical base."""
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"
CANON = (ROOT / "scripts/WassersteinDistance_canonical.lean").read_text()
HEADER = subprocess.check_output(
    ["git", "show", "cbabcc7:UgpLean/ContinuumLimit/WassersteinDistance.lean"],
    cwd=ROOT,
    text=True,
).split("namespace GTE.ContinuumLimit.Wasserstein")[0].rstrip()

start = CANON.index("namespace GTE.ContinuumLimit.Wasserstein")
body = CANON[start:]

fixes = [
    ("  · simp [h, μ.2.2.1 y hy]", "  · subst h; simp [μ.2.2.1 y hy]"),
    ("  · push Not at hgt", "  · push_neg at hgt"),
    (
        "theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :\n"
        "    W1 M μ ν = 0 ↔ μ = ν := by\n"
        "  constructor\n"
        "  · intro hW1\n"
        "    apply probDist_eq_of_vertex_weights_eq\n"
        "    intro x hx\n"
        "    by_contra hne\n"
        "    have hpos := W1_pos_of_vertex_ne M μ ν ⟨x, hx, hne⟩\n"
        "    linarith [W1_nonneg M μ ν, hW1]\n"
        "  · intro hμν; subst hμν",
        "theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :\n"
        "    W1 M μ ν = 0 ↔ ∀ x ∈ M.vertices, μ.val x = ν.val x := by\n"
        "  constructor\n"
        "  · intro hW1\n"
        "    by_contra hne\n"
        "    push_neg at hne\n"
        "    have hpos := W1_pos_of_vertex_ne M μ ν hne\n"
        "    linarith [W1_nonneg M μ ν, hW1]\n"
        "  · intro h\n"
        "    have hμν : μ = ν := probDist_eq_of_vertex_weights_eq h\n"
        "    subst hμν",
    ),
    ("theorem probExpectation_dist_sub", "private theorem probExpectation_dist_sub"),
    (
        "axiom gorard_vacuum_oric_zero",
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n'
        "axiom gorard_vacuum_oric_zero",
    ),
    # coupling outside cases
    ("  · exact hγ.2.2.1 x hx w", "  · exact hγ.2.1 x hx w"),
    ("  · exact hγ.2.1 w hw z", "  · exact hγ.2.2.1 z hz w"),
    # row sum inner
    (
        "    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by\n"
        "        rw [← Finset.mul_sum, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]\n"
        "      simp [hν, hinner]",
        "    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by\n"
        "        have hconst : ∀ z, γ₁ x w * γ₂ w z / ν.val w = (γ₁ x w / ν.val w) * γ₂ w z :=\n"
        "          fun z => by ring\n"
        "        rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum, hγ₂.2.2.2.1 w hw,\n"
        "          mul_div_cancel₀ _ (Ne.symm hν)]\n"
        "      simp [hν, hinner]",
    ),
    # col sum inner + zero mass
    (
        "    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'\n"
        "      simp [hν, Finset.sum_eq_zero fun x' _ => by simp [hcol x']]",
        "    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'\n"
        "      simp [hν, hcol, Finset.sum_const_zero]",
    ),
    (
        "    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by\n"
        "        rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]\n"
        "      simp [hν, hinner]",
        "    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by\n"
        "        have hconst : ∀ x', γ₁ x' w * γ₂ w z / ν.val w = (γ₂ w z / ν.val w) * γ₁ x' w :=\n"
        "          fun x' => by ring\n"
        "        rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul,\n"
        "          mul_div_cancel₀ _ (Ne.symm hν)]\n"
        "      simp [hν, hinner]",
    ),
    # hterm triangle bound
    (
        "      rw [mul_comm (M.dist x z), mul_comm (M.dist x w + M.dist w z)]\n"
        "      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv",
        "      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv",
    ),
    # gap: triangle inequality
    (
        "      have hΔ : M.dist t0 tMinus < M.dist t0 u + M.dist tMinus u := by\n"
        "        refine lt_of_le_of_ne (M.triangle t0 u tMinus) ?_\n"
        "        intro h_eq\n"
        "        nlinarith [M.dist_nonneg, M.dist_comm, M.triangle t0 tMinus u, hut0ne, hutMne, hdistPM,\n"
        "          dist_pos_of_ne M hut0ne, dist_pos_of_ne M hutMne]",
        "      have hΔ : M.dist t0 tMinus < M.dist t0 u + M.dist tMinus u := by\n"
        "        have htri' : M.dist t0 tMinus ≤ M.dist t0 u + M.dist u tMinus := M.triangle t0 u tMinus\n"
        "        have htri : M.dist t0 tMinus ≤ M.dist t0 u + M.dist tMinus u := by\n"
        "          rw [M.dist_comm u tMinus]; exact htri'\n"
        "        refine lt_of_le_of_ne htri ?_\n"
        "        intro h_eq\n"
        "        nlinarith [M.dist_nonneg, hut0ne, hutMne, hdistPM, dist_pos_of_ne M hut0ne,\n"
        "          dist_pos_of_ne M hutMne]",
    ),
    (
        "      have hΔ : M.dist tPlus t0 < M.dist tPlus u + M.dist t0 u := by\n"
        "        refine lt_of_le_of_ne (M.triangle tPlus u t0) ?_\n"
        "        intro h_eq\n"
        "        nlinarith [M.dist_nonneg, M.dist_comm, M.triangle tPlus t0 u, hutPne, hut0ne, hdistPM,\n"
        "          dist_pos_of_ne M hutPne, dist_pos_of_ne M hut0ne]",
        "      have hΔ : M.dist tPlus t0 < M.dist tPlus u + M.dist t0 u := by\n"
        "        have htri' : M.dist tPlus t0 ≤ M.dist tPlus u + M.dist u t0 := M.triangle tPlus u t0\n"
        "        have htri : M.dist tPlus t0 ≤ M.dist tPlus u + M.dist t0 u := by\n"
        "          rw [M.dist_comm u t0]; exact htri'\n"
        "        refine lt_of_le_of_ne htri ?_\n"
        "        intro h_eq\n"
        "        nlinarith [M.dist_nonneg, hutPne, hut0ne, hdistPM, dist_pos_of_ne M hutPne,\n"
        "          dist_pos_of_ne M hut0ne]",
    ),
    # gap: hthirdEx before obtain
    (
        "    · obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthird\n"
        "      have hut0ne : u ≠ t0 := hut0",
        "    · have hthirdEx := hthird\n"
        "      obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthirdEx\n"
        "      have hut0ne : u ≠ t0 := hut0",
    ),
    (
        "        exact absurd ⟨t, ht, ht0', htM', hδne⟩ hthirdEx",
        "        exact absurd ⟨t, ht, ht0', htM', hδne⟩ hthirdEx",
    ),
    # two-anchor: add_sum_erase + hsumErase0
    (
        "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0] at hdistPlus\n"
        "      simp only [M.dist_self, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus\n"
        "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htMinusInErase] at hdistPlus\n"
        "      have hrest0 : ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) = 0 :=\n"
        "        Finset.sum_eq_zero fun t ht => by\n"
        "          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)\n"
        "          simp [hδ0 t htVert (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))\n"
        "            (Finset.ne_of_mem_erase ht), zero_mul]\n"
        "      have hsplit :\n"
        "          (M.vertices.erase t0).sum (fun t => δ t * M.dist t t0) =\n"
        "            δ tMinus * M.dist tMinus t0 +\n"
        "              ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) := by\n"
        "        rw [← Finset.add_sum_erase (M.vertices.erase t0) (fun t => δ t * M.dist t t0) tMinus htMinusInErase]\n"
        "      have hplus0 : δ tMinus * M.dist tMinus t0 = 0 := by linarith [hdistPlus, hsplit, hrest0]\n"
        "      linarith [hheadPlus, hplus0]",
        "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0, M.dist_self t0, mul_zero, add_zero] at hdistPlus\n"
        "      have hsumErase0 : (M.vertices.erase t0).sum (fun t => δ t * M.dist t t0) = 0 := by\n"
        "        linarith [hdistPlus]\n"
        "      have hrest0 : ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) = 0 :=\n"
        "        Finset.sum_eq_zero fun t ht => by\n"
        "          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)\n"
        "          simp [hδ0 t htVert (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))\n"
        "            (Finset.ne_of_mem_erase ht), zero_mul]\n"
        "      have hsplit :\n"
        "          (M.vertices.erase t0).sum (fun t => δ t * M.dist t t0) =\n"
        "            δ tMinus * M.dist tMinus t0 +\n"
        "              ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) := by\n"
        "        rw [← Finset.add_sum_erase (s := M.vertices.erase t0) (f := fun t => δ t * M.dist t t0)\n"
        "          htMinusInErase]\n"
        "      linarith [hsumErase0, hsplit, hrest0, hheadPlus]",
    ),
    (
        "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem] at hdistPlus\n"
        "      simp only [M.dist_self, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus\n"
        "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase] at hdistPlus\n"
        "      have hrest0 : ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) = 0 :=\n"
        "        Finset.sum_eq_zero fun t ht => by\n"
        "          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)\n"
        "          simp [hδ0 t htVert (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))\n"
        "            (Finset.ne_of_mem_erase ht), zero_mul]\n"
        "      have hsplit :\n"
        "          (M.vertices.erase tPlus).sum (fun t => δ t * M.dist t tPlus) =\n"
        "            δ t0 * M.dist t0 tPlus +\n"
        "              ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) := by\n"
        "        rw [← Finset.add_sum_erase (M.vertices.erase tPlus) (fun t => δ t * M.dist t tPlus) t0 ht0InErase]\n"
        "      linarith [hdistPlus, hsplit, hrest0, hheadPlus]",
        "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem, M.dist_self tPlus, mul_zero,\n"
        "        add_zero] at hdistPlus\n"
        "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase] at hdistPlus\n"
        "      have hsumErase0 : (M.vertices.erase tPlus).sum (fun t => δ t * M.dist t tPlus) = 0 := by\n"
        "        linarith [hdistPlus]\n"
        "      have hrest0 : ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) = 0 :=\n"
        "        Finset.sum_eq_zero fun t ht => by\n"
        "          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)\n"
        "          simp [hδ0 t htVert (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))\n"
        "            (Finset.ne_of_mem_erase ht), zero_mul]\n"
        "      have hsplit :\n"
        "          (M.vertices.erase tPlus).sum (fun t => δ t * M.dist t tPlus) =\n"
        "            δ t0 * M.dist t0 tPlus +\n"
        "              ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) := by\n"
        "        rw [← Finset.add_sum_erase (s := M.vertices.erase tPlus) (f := fun t => δ t * M.dist t tPlus)\n"
        "          ht0InErase]\n"
        "      linarith [hsumErase0, hsplit, hrest0, hheadPlus]",
    ),
    # M.dist_self with anchor arg in gap splits
    ("simp only [M.dist_self, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus",
     "simp only [M.dist_self t0, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus"),
]

out = HEADER + "\n\n" + body + "\n"
for old, new in fixes:
    if old not in out:
        print(f"WARN: pattern not found ({old[:60]}...)")
    else:
        out = out.replace(old, new, 1)

# CTC block: replace broken sum_eq_single version if present
CTC_OLD = """  have hdiag : γ x x = μ.val x := by
    have hsumx : γ x x = M.vertices.sum (γ x) := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne.symm) (fun hne => absurd hx hne)]
      simp
    rw [hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne.symm) (fun hne => absurd hx hne)]
    simp
  have hnu : ν.val x = γ x x := by rw [← hcol, hγ.2.2.2.2 x hx]
  linarith [hdiag, hnu]"""

CTC_NEW = """  have hdiag : γ x x = μ.val x := by
    have hsumx : M.vertices.sum (γ x) = μ.val x := hγ.2.2.2.1 x hx
    have hsplit : M.vertices.sum (γ x) = γ x x := by
      classical
      rw [← Finset.add_sum_erase (s := M.vertices) (f := γ x) hx, add_zero]
      apply Finset.sum_eq_zero
      intro b hb
      exact hoff x b hx (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)
    linarith [hsplit, hsumx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    classical
    rw [← Finset.add_sum_erase (s := M.vertices) (f := fun z => γ z x) hx, add_zero]
    apply Finset.sum_eq_zero
    intro z hz
    exact hoff z x (Finset.mem_of_mem_erase hz) hx (Finset.ne_of_mem_erase hz)
  have hnu : ν.val x = γ x x := by rw [← hcol, hγ.2.2.2.2 x hx]
  linarith [hdiag, hnu]"""

if CTC_OLD in out:
    out = out.replace(CTC_OLD, CTC_NEW)
elif "add_sum_erase (s := M.vertices) (f := γ x)" not in out:
    print("WARN: CTC block not patched")

if out.count("private theorem W1_pos_of_vertex_ne") != 1:
    raise SystemExit(f"Expected 1 W1_pos, found {out.count('private theorem W1_pos_of_vertex_ne')}")

tmp = Path("/tmp/w1_deploy.lean")
tmp.write_text(out)
TARGET.write_text(out)
print(f"Deployed {TARGET} ({out.count(chr(10)) + 1} lines)")
