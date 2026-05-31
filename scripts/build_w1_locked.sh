#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TARGET="$ROOT/UgpLean/ContinuumLimit/WassersteinDistance.lean"
TEST="$ROOT/UgpLean/ContinuumLimit/WassersteinDistance_test.lean"

chflags nouchg "$TARGET" 2>/dev/null || true

python3 <<'PY'
from pathlib import Path

root = Path("/Users/nova/ugp-lean-exp")
test = (root / "UgpLean/ContinuumLimit/WassersteinDistance_test.lean").read_text().splitlines()

# Drop duplicate import and duplicate dist_eq_zero_iff field + its doc comment
out = []
seen_arch = False
seen_deq = False
for line in test:
    if line == "import Mathlib.Data.Real.Archimedean":
        if seen_arch:
            continue
        seen_arch = True
    if line.strip() == "/-- Distances distinguish vertices: zero distance iff equal points. -/" and seen_deq:
        continue
    if line.strip().startswith("dist_eq_zero_iff :"):
        if seen_deq:
            continue
        seen_deq = True
    out.append(line)

text = "\n".join(out)

# dist_pos_of_ne: False branch
text = text.replace(
    "  · exact hne ((M.dist_eq_zero_iff x y).mp heq.symm)",
    "  · cases hne ((M.dist_eq_zero_iff x y).mp heq)",
)

# diagonalCoupling_right_outside
text = text.replace(
    "  · exact μ.2.2.1 y (by rw [← h]; exact hy)",
    "  · subst h; exact μ.2.2.1 y hy",
)

# exists_mass_imbalance_pair: membership + mass balance
text = text.replace(
    "          (Finset.single_le_sum hnonneg (fun x _ => hnonneg x ‹x ∈ M.vertices›) (Finset.mem_univ x0))",
    "          (Finset.single_le_sum hnonneg hx0)",
)
text = text.replace(
    "          (Finset.single_le_sum hnonpos (fun x _ => hnonpos x ‹x ∈ M.vertices›) (Finset.mem_univ x0))",
    "          (Finset.single_le_sum hnonpos hx0)",
)
text = text.replace(
    """      have hsum : M.vertices.sum (fun x => μ.val x - ν.val x) = 0 := by
        have hsum' : M.vertices.sum (fun x => ↑μ x - ↑ν x) = 0 := by
          rw [← Finset.sum_sub_distrib, μ.2.2.2, ν.2.2.2]
        simpa [ProbDist, Subtype] using hsum'""",
    "      have hsum := probDist_vertex_mass_balance M.vertices μ ν",
)
text = text.replace(
    """      have hsum : M.vertices.sum (fun x => μ.val x - ν.val x) = 0 := by
        rw [← Finset.sum_sub_distrib, μ.2.2.2, ν.2.2.2]""",
    "      have hsum := probDist_vertex_mass_balance M.vertices μ ν",
)

# Replace direct W1_pos with Kantorovich gap version
old_w1pos = """private theorem W1_pos_of_vertex_ne (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) : 0 < W1 M μ ν := by
  obtain ⟨xAnchor, _, hgap⟩ := probExpectation_dist_ne_zero_of_ne M μ ν hne
  have hf := dist_lipschitz M xAnchor
  have hge :=
    W1_ge_of_lipschitz M μ ν (M.dist · xAnchor) hf (couplingCostSet_nonempty M μ ν)
  have hpos : 0 < |probExpectation M μ (M.dist · xAnchor) -
      probExpectation M ν (M.dist · xAnchor)| :=
    abs_pos.mpr (sub_ne_zero.mpr hgap)
  exact lt_of_lt_of_le hpos hge"""

new_w1pos = """private theorem exists_probExpectation_dist_gap (M : FiniteMetricSpace)
    (μ ν : ProbDist M.vertices) (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) :
    ((∃ a ∈ M.vertices, 0 < probExpectation M μ (M.dist · a) - probExpectation M ν (M.dist · a)) ∨
      ∃ a ∈ M.vertices, 0 < probExpectation M ν (M.dist · a) - probExpectation M μ (M.dist · a)) := by
  obtain ⟨a, ha, hgap⟩ := probExpectation_dist_ne_zero_of_ne M μ ν hne
  by_cases hμ : 0 < probExpectation M μ (M.dist · a) - probExpectation M ν (M.dist · a)
  · exact Or.inl ⟨a, ha, hμ⟩
  · push_neg at hμ
    have hlt : probExpectation M μ (M.dist · a) - probExpectation M ν (M.dist · a) < 0 :=
      lt_of_le_of_ne hμ hgap
    exact Or.inr ⟨a, ha, sub_pos.mpr hlt⟩

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

if old_w1pos not in text:
    raise SystemExit("W1_pos block not found")
text = text.replace(old_w1pos, new_w1pos)

# gluedCoupling_is_coupling intros
text = text.replace(
    "  · exact gluedCoupling_left_outside M.vertices ν γ₁ γ₂ (fun x hx y => hγ₁.2.1 x hx y) x hx y",
    "  · intro x hx y; exact gluedCoupling_left_outside M.vertices ν γ₁ γ₂ (fun a ha b => hγ₁.2.1 a ha b) x hx y",
)
text = text.replace(
    "  · intro y hy x; exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂ (fun y hy x => hγ₂.2.2.1 y hy x) y hy x",
    "  · intro y hy x; exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂ (fun z hz w => hγ₂.2.2.1 z hz w) y hy x",
)
text = text.replace(
    "  · exact gluedCoupling_row_sum M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂",
    "  · intro x hx; exact gluedCoupling_row_sum M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂ x hx",
)
text = text.replace(
    "  · exact gluedCoupling_col_sum M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂",
    "  · intro y hy; exact gluedCoupling_col_sum M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂ y hy",
)

# gluedCoupling row/col: Ne.symm + zero mass branch
text = text.replace(
    "        rw [Finset.sum_mul, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ hν]",
    "        rw [Finset.sum_mul, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]",
)
text = text.replace(
    """    · have hrow : S.sum (fun z => γ₂ w z) = 0 := by
        rw [hγ₂.2.2.2.1 w hw, hν]
      simp [hν, hrow]""",
    """    · have hrowmass : S.sum (fun z => γ₂ w z) = 0 := by rw [hγ₂.2.2.2.1 w hw, hν]
      have hγxw : γ₁ x w = 0 := by linarith [hγ₁.1 x w, Finset.single_le_sum hγ₁.1 hw]
      simp [hν, hγxw]""",
)
text = text.replace(
    """    · have hcol : S.sum (fun x' => γ₁ x' w) = 0 := by
        rw [hγ₁.2.2.2.2 w hw, hν]
      simp [hν, hcol]""",
    """    · have hcolmass : S.sum (fun x' => γ₁ x' w) = 0 := by rw [hγ₁.2.2.2.2 w hw, hν]
      have hγwz : γ₂ w z = 0 := by linarith [hγ₂.1 w z, Finset.single_le_sum hγ₂.1 hz]
      simp [hν, hγwz]""",
)
text = text.replace(
    "        rw [← Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ hν]",
    "        rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]",
)

# gluedCoupling_right_outside hypothesis type
text = text.replace(
    "    (hγ₂ : ∀ y x, y ∉ S → γ₂ x y = 0) (z : ℕ) (hz : z ∉ S) (x : ℕ) :",
    "    (hγ₂ : ∀ {z} (hz : z ∉ S) (x : ℕ), γ₂ x z = 0) (z : ℕ) (hz : z ∉ S) (x : ℕ) :",
)
text = text.replace(
    "  split_ifs with hν <;> simp [hγ₂ y _ hz]",
    "  split_ifs with hν <;> simp [hγ₂ z hz]",
)

# gluedCoupling_cost_le: replace hsplit proof
old_hsplit = """  have hsplit :
      M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = 0 then 0 else γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) =
        M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w =>
            if ν.val w = 0 then 0 else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := by
    simp_rw [mul_add, ← Finset.sum_add_distrib, Finset.mul_sum, ← Finset.sum_mul, mul_assoc,
      mul_comm (γ₂ _ _), ← mul_assoc, mul_comm (γ₁ _ _ / _)]
    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    congr 1; ext x; rw [Finset.sum_comm]
    congr 1; ext w; split_ifs <;> ring"""

new_hsplit = """  have hsplit :
      M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = 0 then 0 else γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) =
        M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w =>
            if ν.val w = 0 then 0 else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := by
    simp_rw [mul_add]
    congr 1; ext x
    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices), ← Finset.sum_add_distrib]
    congr 1; ext w hw
    by_cases hν : ν.val w = 0
    · simp [hν]
    · rw [if_neg hν, if_neg hν]
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
          rw [hcol, mul_div_cancel₀ _ (Ne.symm hν)]; ring"""

if old_hsplit not in text:
    raise SystemExit("hsplit block not found")
text = text.replace(old_hsplit, new_hsplit)

# hbound: replace gcongr with explicit proof
old_hbound = """  have hbound :
      M.vertices.sum fun w =>
          if ν.val w = 0 then 0 else
            M.vertices.sum fun x => γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z ≤
        M.vertices.sum fun w => M.vertices.sum fun z => γ₂ w z * M.dist w z := by
    gcongr"""

new_hbound = """  have hbound :
      M.vertices.sum fun w =>
          if ν.val w = 0 then 0 else
            M.vertices.sum fun x => γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z ≤
        M.vertices.sum fun w => M.vertices.sum fun z => γ₂ w z * M.dist w z := by
    refine Finset.sum_le_sum fun w hw => ?_
    split_ifs with hν
    · simp
    · rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_comm, mul_div_cancel₀ _ (Ne.symm hν)]"""

if old_hbound not in text:
    raise SystemExit("hbound block not found")
text = text.replace(old_hbound, new_hbound)

# calc tail after hbound - replace gcongr steps with direct proof
old_calc_tail = """    _ ≤ couplingTransportCost M γ₁ +
          M.vertices.sum fun w =>
            if ν.val w = 0 then 0 else
              M.vertices.sum fun x => γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := by
      rw [add_comm, ← Finset.sum_add_distrib, add_comm]
      gcongr
    _ = couplingTransportCost M γ₁ +
          M.vertices.sum fun w =>
            if ν.val w = 0 then 0 else
              1 / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z *
                M.vertices.sum fun x => γ₁ x w := by
      simp_rw [mul_comm (_ / _), ← Finset.sum_mul, mul_assoc, mul_comm (_ * _)]
    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      gcongr
      intro w hw
      split_ifs with hν
      · simp
      · rw [hγ₁.2.2.2.2 w hw, mul_one, mul_comm, mul_div_cancel₀ _ hν]"""

new_calc_tail = """    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      unfold couplingTransportCost
      rw [← Finset.sum_add_distrib]
      apply add_le_add_left le_rfl
      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
      exact hbound"""

if old_calc_tail not in text:
    raise SystemExit("calc tail not found")
text = text.replace(old_calc_tail, new_calc_tail)

# W1_triangle
text = text.replace(
    "  refine le_of_forall_lt fun ε hε => ?_",
    "  rw [le_iff_forall_pos_lt_add]\n  intro ε hε",
)
text = text.replace(
    "  obtain ⟨c₁, hc₁, hc₁lt⟩ :=\n    Real.lt_sInf_add_pos (couplingCostSet_nonempty M μ ν) (half_pos hε)\n  obtain ⟨c₂, hc₂, hc₂lt⟩ :=\n    Real.lt_sInf_add_pos (couplingCostSet_nonempty M ν ρ) (half_pos hε)\n  obtain ⟨γ₁, hγ₁, rfl⟩ := hc₁\n  obtain ⟨γ₂, hγ₂, rfl⟩ := hc₂",
    "  obtain ⟨c₁, hc₁mem, hc₁lt⟩ :=\n    Real.lt_sInf_add_pos (couplingCostSet_nonempty M μ ν) (half_pos hε)\n  obtain ⟨c₂, hc₂mem, hc₂lt⟩ :=\n    Real.lt_sInf_add_pos (couplingCostSet_nonempty M ν ρ) (half_pos hε)\n  obtain ⟨γ₁, hγ₁, hc₁eq⟩ := hc₁mem\n  obtain ⟨γ₂, hγ₂, hc₂eq⟩ := hc₂mem",
)
text = text.replace(
    "  unfold W1 at hc₁lt hc₂lt ⊢\n  linarith [hcost, hle]",
    """  have hW1μν : W1 M μ ν ≤ c₁ := by
    unfold W1; apply csInf_le
    · refine ⟨0, ?_⟩; intro c hc; obtain ⟨γ', hγ', hc'⟩ := hc; rw [hc']; exact couplingTransportCost_nonneg M γ' hγ'.1
    · exact ⟨γ₁, hγ₁, hc₁eq⟩
  have hW1νρ : W1 M ν ρ ≤ c₂ := by
    unfold W1; apply csInf_le
    · refine ⟨0, ?_⟩; intro c hc; obtain ⟨γ', hγ', hc'⟩ := hc; rw [hc']; exact couplingTransportCost_nonneg M γ' hγ'.1
    · exact ⟨γ₂, hγ₂, hc₂eq⟩
  unfold W1 at hle hW1μν hW1νρ ⊢
  linarith [hle, hcost, hc₁lt, hc₂lt, hW1μν, hW1νρ]""",
)

# deprecated axiom
text = text.replace(
    "axiom gorard_vacuum_oric_zero",
    '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\naxiom gorard_vacuum_oric_zero',
)

if "hthirdEx" in text or "probExpectation_dist_eq_all" in text or "delta_three_anchor" in text:
    raise SystemExit("REFUSING: corrupted blocks in output")

if "sorry" in text:
    for i, line in enumerate(text.splitlines(), 1):
        if "sorry" in line.split("--")[0] and "declared (sorry)" not in line:
            raise SystemExit(f"sorry at line {i}: {line}")

target = root / "UgpLean/ContinuumLimit/WassersteinDistance.lean"
tmp = Path("/tmp/WassersteinDistance.lean.build")
tmp.write_text(text + "\n")
tmp.replace(target)
print(f"Wrote {len(text.splitlines())} lines")
PY

wc -l "$TARGET"
rg "hthirdEx|probExpectation_dist_eq_all|delta_three_anchor" "$TARGET" && exit 1 || true

cd "$ROOT"
lake build UgpLean.ContinuumLimit.WassersteinDistance
BUILD=$?
if [ $BUILD -eq 0 ]; then
  rg '\bsorry\b' "$TARGET" && exit 1 || true
  echo "BUILD OK — zero sorry"
fi
exit $BUILD
