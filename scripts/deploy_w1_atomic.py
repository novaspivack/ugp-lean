#!/usr/bin/env python3
"""Atomically deploy fixed WassersteinDistance.lean from cbabcc7 base."""
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"
GAP = (ROOT / "UgpLean/ContinuumLimit/_gap_insert.lean").read_text()

src = subprocess.check_output(
    ["git", "show", "cbabcc7:UgpLean/ContinuumLimit/WassersteinDistance.lean"],
    cwd=ROOT,
    text=True,
)

src = src.replace(
    "  · rw [if_pos h]; exact μ.2.2.1 y hy",
    "  · subst h; simp [μ.2.2.1 y hy]",
)
src = src.replace(
    "    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt (Ne.symm hdiff)",
    "    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff",
)

CTC_OLD = """  have hoff (a b : ℕ) (ha : a ∈ M.vertices) (hb : b ∈ M.vertices) (hne : a ≠ b) :
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

CTC_NEW = """  have hoff (a b : ℕ) (ha : a ∈ M.vertices) (hb : b ∈ M.vertices) (hne : a ≠ b) :
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
  linarith [hdiag, hnu]"""

if CTC_OLD not in src:
    raise SystemExit("CTC block not found")
src = src.replace(CTC_OLD, CTC_NEW)

W1POS_OLD = """private theorem W1_pos_of_vertex_ne (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) : 0 < W1 M μ ν := by
  have hcost := couplingTransportCost_pos_of_vertex_ne M μ ν hne
  have hle := W1_le_couplingCost M μ ν (productCoupling M.vertices μ ν)
    (productCoupling_is_coupling M.vertices μ ν)
  exact hcost.trans_le hle"""

GAP_BLOCK = """
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
  linarith [htMinusNeg, hall0 tMinus (Finset.mem_filter.mp htMinus).1)

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
    exact hpos.trans_le hge"""

if W1POS_OLD not in src:
    raise SystemExit("W1_pos block not found")
src = src.replace(W1POS_OLD, GAP_BLOCK.strip())

if "private theorem probExpectation_dist_sub" not in src:
    raise SystemExit("probExpectation_dist_sub missing")

TARGET.write_text(src)
print(f"Wrote {TARGET} ({src.count(chr(10)) + 1} lines)")
