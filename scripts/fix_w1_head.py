#!/usr/bin/env python3
"""Produce a clean zero-sorry WassersteinDistance.lean at /tmp/w1_final.lean."""
import re
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = Path("/tmp/w1_final.lean")
GAP = (ROOT / "UgpLean/ContinuumLimit/_gap_insert.lean").read_text()
GLUED = Path(ROOT / "scripts/finalize_wasserstein.py").read_text().split('glued_block = """')[1].split('""".strip()')[0]

src = subprocess.check_output(
    ["git", "show", "265c716:UgpLean/ContinuumLimit/WassersteinDistance.lean"],
    cwd=ROOT, text=True,
)

# Drop duplicate second couplingTransportCost block (legacy HEAD only).
lines = src.splitlines()
out: list[str] = []
i = 0
seen_zero = 0
while i < len(lines):
    s = lines[i].strip()
    if s == "private theorem couplingTransportCost_eq_zero_of_eq":
        seen_zero += 1
        if seen_zero >= 2:
            while i < len(lines) and not lines[i].strip().startswith("private theorem W1_pos_of_vertex_ne"):
                i += 1
            continue
    out.append(lines[i])
    i += 1
src = "\n".join(out) + "\n"

src = src.replace(
    "· simp [h, μ.2.2.1 y hy]",
    "· subst h; simp [μ.2.2.1 y hy]",
)
src = src.replace("· push Not at hgt", "· push_neg at hgt")

CTC_ZERO = """
private theorem couplingTransportCost_eq_zero_of_eq
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
    have hterm_nn : ∀ c ∈ M.vertices, 0 ≤ γ a c * M.dist a c :=
      fun c hc => mul_nonneg (hγ.1 a c) (M.dist_nonneg a c)
    have hzero : γ a b * M.dist a b = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg hterm_nn).1 (hrow_zero a ha) b hb
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (dist_pos_of_ne M hne))
  have hdiag : γ x x = μ.val x := by
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
  linarith [hdiag, hnu]
"""

for pattern in (
    r"private theorem couplingTransportCost_eq_zero_of_eq[\s\S]*?  linarith \[hdiag, hnu\]\n",
    r"private theorem couplingTransportCost_eq_zero_of_eq[\s\S]*?    _ = ν\.val x := hγ\.2\.2\.2\.2 x hx\n",
):
    new_src, n = re.subn(pattern, CTC_ZERO.strip() + "\n", src, count=1)
    if n:
        src = new_src
        break

GAP_CORE = """
private theorem exists_delta_neg_of_sum_zero (S : Finset ℕ) (δ : ℕ → ℝ)
    (hsum : S.sum δ = 0) {tPlus : ℕ} (htPlus : tPlus ∈ S.filter (fun t => 0 < δ t)) (htPluspos : 0 < δ tPlus) :
    ∃ tMinus ∈ S, δ tMinus < 0 := by
  by_contra hall; push_neg at hall
  have hnonneg : ∀ t ∈ S, 0 ≤ δ t := hall
  have hsumpos : 0 < S.sum δ :=
    lt_of_lt_of_le htPluspos (Finset.single_le_sum hnonneg (Finset.mem_filter.mp htPlus).1)
  linarith [hsum, hsumpos]

private theorem exists_delta_pos_of_sum_zero (S : Finset ℕ) (δ : ℕ → ℝ)
    (hsum : S.sum δ = 0) {tMinus : ℕ} (htMinus : tMinus ∈ S.filter (fun t => δ t < 0))
    (htMinusNeg : δ tMinus < 0) :
    ∃ tPlus ∈ S, 0 < δ tPlus := by
  by_contra hall; push_neg at hall
  have hnonpos : ∀ t ∈ S, δ t ≤ 0 := hall
  have hall0 : ∀ t ∈ S, δ t = 0 := (Finset.sum_eq_zero_iff_of_nonpos hnonpos).mp hsum
  linarith [htMinusNeg, hall0 tMinus (Finset.mem_filter.mp htMinus).1]

""" + GAP + """
private theorem exists_probExpectation_dist_gap (M : FiniteMetricSpace)
    (μ ν : ProbDist M.vertices) (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) :
    ((∃ a ∈ M.vertices, 0 < probExpectation M μ (M.dist · a) - probExpectation M ν (M.dist · a)) ∨
      ∃ a ∈ M.vertices, 0 < probExpectation M ν (M.dist · a) - probExpectation M μ (M.dist · a)) := by
  by_contra hnot; push_neg at hnot
  rcases hnot with ⟨hμ, hν⟩
  have heq : ∀ a ∈ M.vertices, probExpectation M μ (M.dist · a) = probExpectation M ν (M.dist · a) := by
    intro a ha; have hleμ := hμ a ha; have hleν := sub_nonpos.mp (hν a ha); linarith
  rcases hne with ⟨x, hx, hdiff⟩
  exact hdiff (probExpectation_dist_eq_all_imp_vertex_eq M μ ν heq x hx)
"""

src = re.sub(
    r"private theorem exists_delta_neg_of_sum_zero[\s\S]*?"
    r"exact hdiff \(probExpectation_dist_eq_all_imp_vertex_eq M μ ν heq x hx\)\n",
    GAP_CORE.strip() + "\n",
    src,
    count=1,
)

src = src.replace(
    """    have hμpos : 0 < μ.val x := lt_of_le_of_ne (μ.2.1 x hx) (Ne.symm (sub_ne_zero.mpr hgt))
    have hνpos : 0 < ν.val y := lt_of_le_of_ne (ν.2.1 y hy) (Ne.symm (sub_ne_zero.mpr hlt))""",
    """    have hμpos : 0 < μ.val x := by linarith [μ.2.1 x hx, ν.2.1 x hx, hgt]
    have hνpos : 0 < ν.val y := by linarith [ν.2.1 y hy, μ.2.1 y hy, hlt]""",
)

src = src.replace(
    """    have hμpos : 0 < μ.val y := lt_of_le_of_ne (μ.2.1 y hy) (Ne.symm (sub_ne_zero.mpr hgt'))
    have hνpos : 0 < ν.val x := lt_of_le_of_ne (ν.2.1 x hx) (Ne.symm hdiff)""",
    """    have hμpos : 0 < μ.val y := by linarith [μ.2.1 y hy, ν.2.1 y hy, hgt']
    have hνpos : 0 < ν.val x := by linarith [ν.2.1 x hx, μ.2.1 x hx, hlt]""",
)

old_w1pos = """private theorem W1_pos_of_vertex_ne (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) : 0 < W1 M μ ν := by
  have hcost := couplingTransportCost_pos_of_vertex_ne M μ ν hne
  have hle := W1_le_couplingCost M μ ν (productCoupling M.vertices μ ν)
    (productCoupling_is_coupling M.vertices μ ν)
  exact hcost.trans_le hle"""

if old_w1pos in src:
    w1pos_new = """
private theorem W1_pos_of_vertex_ne (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) : 0 < W1 M μ ν := by
  rcases exists_probExpectation_dist_gap M μ ν hne with h | h
  · rcases h with ⟨a, _, hpos⟩
    have hW1ge := W1_ge_of_lipschitz M μ ν (M.dist · a) (dist_lipschitz M a)
      (couplingCostSet_nonempty M μ ν)
    exact hpos.trans_le (le_trans (le_abs_self _) hW1ge)
  · rcases h with ⟨a, _, hpos⟩
    have hW1ge := W1_ge_of_lipschitz M μ ν (M.dist · a) (dist_lipschitz M a)
      (couplingCostSet_nonempty M μ ν)
    have hge : probExpectation M ν (M.dist · a) - probExpectation M μ (M.dist · a) ≤ W1 M μ ν := by
      calc probExpectation M ν (M.dist · a) - probExpectation M μ (M.dist · a) ≤
          |probExpectation M μ (M.dist · a) - probExpectation M ν (M.dist · a)| := by
            rw [abs_sub_comm]; exact le_abs_self _
        _ ≤ W1 M μ ν := hW1ge
    exact hpos.trans_le hge
""".strip()
    src = src.replace(old_w1pos, w1pos_new)

src = re.sub(
    r"/\*\* Glued coupling[\s\S]*?exact hbound\n",
    "/** Glued coupling of `γ₁ : μ ↝ ν` and `γ₂ : ν ↝ ρ` via disintegration at `ν`. -/\n"
    + GLUED.strip()
    + "\n",
    src,
    count=1,
)

src = src.replace(
    "axiom gorard_vacuum_oric_zero",
    '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n'
    "axiom gorard_vacuum_oric_zero",
    1,
)

OUT.write_text(src)
print(f"Wrote {OUT} ({src.count(chr(10)) + 1} lines)")
