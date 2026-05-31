#!/usr/bin/env python3
"""Apply all proof fixes to clean WassersteinDistance staging."""
import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
STAGING = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean.staging"
MAIN = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"

subprocess.run(["python3", str(ROOT / "scripts/build_clean_w1.py")], check=False)
text = STAGING.read_text()

def must_replace(old, new):
    global text
    if old not in text:
        raise SystemExit(f"missing: {old[:60]}...")
    text = text.replace(old, new)

# eq_zero: drop trailing simp after sum_eq_single
text = text.replace(
    "      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy (Ne.symm hne)) (fun hne => absurd hx hne)]\n      simp\n    rw [hsumx",
    "      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy (Ne.symm hne)) (fun hne => absurd hx hne)]\n    rw [hsumx",
)
text = text.replace(
    "    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]\n    simp\n  have hnu",
    "    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]\n  have hnu",
)

# coupling col/row outside branches
text = text.replace(
    "  · exact hγ.2.2.1 x hx w\n\nprivate theorem coupling_row_zero_of_mass_zero",
    "  · exact hγ.2.1 x hx w\n\nprivate theorem coupling_row_zero_of_mass_zero",
)
text = text.replace(
    "  · exact hγ.2.1 w hw z\n\nprivate theorem gluedCoupling_left_outside",
    "  · exact hγ.2.2.1 z hz w\n\nprivate theorem gluedCoupling_left_outside",
)

# glued outside + row/col sums
text = text.replace(
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _; split_ifs <;> simp [hγ₁ x hx]",
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _\n  by_cases hν : ν.val y = 0 <;> simp [hν, hγ₁ x y hx]",
)
text = text.replace(
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _; split_ifs <;> simp [hγ₂ y hz]",
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _\n  by_cases hν : ν.val y = 0 <;> simp [hν, hγ₂ y z hz]",
)
text = text.replace(
    "  · intro x hx y; exact gluedCoupling_left_outside M.vertices ν γ₁ γ₂ (fun a ha z => hγ₁.2.1 a ha z) x hx y",
    "  · intro x hx y; exact gluedCoupling_left_outside M.vertices ν γ₁ γ₂ (fun a b ha => hγ₁.2.1 a ha b) x hx y",
)

text = text.replace(
    """    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        rw [← Finset.mul_sum, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
    """    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        conv_lhs => arg 2; ext z; rw [div_mul_eq_mul_div, mul_comm (γ₂ w z)]
        rw [← Finset.mul_sum, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
)

text = text.replace(
    """    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'
      simp [hν, Finset.sum_eq_zero fun x' _ => by simp [hcol x']]
    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by
        rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
    """    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'
      have hzero : S.sum (fun x' => if ν.val w = 0 then 0 else γ₁ x' w * γ₂ w z / ν.val w) = 0 := by
        simp [hν]
      rw [hzero]
      exact (coupling_row_zero_of_mass_zero hγ₂ w hw hν z).symm
    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by
        conv_lhs => arg 2; ext x'; rw [div_mul_eq_mul_div, mul_comm (γ₁ x' w)]
        rw [← Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
)

# Replace gluedCoupling_cost_le block (canonical broken hsplit) with bak-style proof
OLD_COST = """theorem gluedCoupling_cost_le (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling M.vertices μ ν γ₁)
    (hγ₂ : IsCoupling M.vertices ν ρ γ₂) :
    couplingTransportCost M (gluedCoupling M.vertices ν γ₁ γ₂) ≤
      couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
  classical
  set γ₃ := gluedCoupling M.vertices ν γ₁ γ₂"""

NEW_COST = """theorem gluedCoupling_cost_le (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling M.vertices μ ν γ₁)
    (hγ₂ : IsCoupling M.vertices ν ρ γ₂) :
    couplingTransportCost M (gluedCoupling M.vertices ν γ₁ γ₂) ≤
      couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
  classical
  unfold couplingTransportCost gluedCoupling
  have hterm : ∀ x z,
      M.dist x z * M.vertices.sum (fun y => if ν.val y = 0 then 0 else γ₁ x y * γ₂ y z / ν.val y) ≤
        M.vertices.sum (fun y => if ν.val y = 0 then 0 else γ₁ x y * γ₂ y z / ν.val y *
          (M.dist x y + M.dist y z)) := by
    intro x z; rw [Finset.mul_sum]
    apply Finset.sum_le_sum; intro y hy; split_ifs with hν
    · simp
    · have hpos : 0 < ν.val y := lt_of_le_of_ne (ν.2.1 y (by simpa using hy)) (Ne.symm hν)
      have hdiv : 0 ≤ γ₁ x y * γ₂ y z / ν.val y :=
        div_nonneg (mul_nonneg (hγ₁.1 x y) (hγ₂.1 y z)) hpos.le
      rw [mul_comm (M.dist x z)]
      exact mul_le_mul_of_nonneg_left (M.triangle x y z) hdiv
  have hxy_part : M.vertices.sum (fun x => M.vertices.sum (fun z =>
        M.vertices.sum (fun y => if ν.val y = 0 then 0 else
          γ₁ x y * γ₂ y z / ν.val y * M.dist x y))) =
      M.vertices.sum (fun x => M.vertices.sum (fun y => γ₁ x y * M.dist x y)) := by
    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    apply Finset.sum_congr rfl; intro y hy
    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    apply Finset.sum_congr rfl; intro x _
    by_cases hν : ν.val y = 0
    · simp [hν, coupling_col_zero_of_mass_zero hγ₁ y hy hν x]
    · simp only [hν, ite_false]
      have hrγ₂ : M.vertices.sum (γ₂ y) = ν.val y := hγ₂.2.2.2.1 y hy
      rw [show (fun z => γ₁ x y * γ₂ y z / ν.val y * M.dist x y) =
              fun z => (γ₁ x y * M.dist x y / ν.val y) * γ₂ y z from by ext z; ring,
          ← Finset.mul_sum, hrγ₂]
      field_simp [hν]
  have hyz_part : M.vertices.sum (fun x => M.vertices.sum (fun z =>
        M.vertices.sum (fun y => if ν.val y = 0 then 0 else
          γ₁ x y * γ₂ y z / ν.val y * M.dist y z))) =
      M.vertices.sum (fun y => M.vertices.sum (fun z => γ₂ y z * M.dist y z)) := by
    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    apply Finset.sum_congr rfl; intro y hy
    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    by_cases hν : ν.val y = 0
    · have hzero_row : ∀ z, γ₂ y z = 0 := fun z => coupling_row_zero_of_mass_zero hγ₂ y hy hν z
      have hzero_col : ∀ x, γ₁ x y = 0 := fun x => coupling_col_zero_of_mass_zero hγ₁ y hy hν x
      simp [hν, Finset.sum_eq_zero fun z _ => hzero_row z,
            Finset.sum_eq_zero fun x _ => hzero_col x]
    · simp only [hν, ite_false]
      conv_lhs =>
        arg 2; ext z; arg 2; ext x
        rw [show γ₁ x y * γ₂ y z / ν.val y * M.dist y z =
                (γ₁ x y / ν.val y) * (γ₂ y z * M.dist y z) from by ring]
      rw [← Finset.sum_comm (s := M.vertices) (t := M.vertices)]
      apply Finset.sum_congr rfl; intro z _
      rw [show (fun x => γ₁ x y / ν.val y * (γ₂ y z * M.dist y z)) =
              fun x => (γ₂ y z * M.dist y z) * (γ₁ x y / ν.val y) from by ext x; ring,
          ← Finset.mul_sum, ← Finset.sum_div, hγ₁.2.2.2.2 y hy]
      field_simp [hν]
  calc
    M.vertices.sum (fun x => M.vertices.sum (fun z =>
          M.dist x z * M.vertices.sum (fun y => if ν.val y = 0 then 0 else γ₁ x y * γ₂ y z / ν.val y)))
        ≤ M.vertices.sum (fun x => M.vertices.sum (fun z =>
          M.vertices.sum (fun y => if ν.val y = 0 then 0 else
            γ₁ x y * γ₂ y z / ν.val y * (M.dist x y + M.dist y z)))) :=
      Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => hterm x z
    _ = M.vertices.sum (fun x => M.vertices.sum (fun z =>
            M.vertices.sum (fun y => if ν.val y = 0 then 0 else
              γ₁ x y * γ₂ y z / ν.val y * M.dist x y))) +
        M.vertices.sum (fun x => M.vertices.sum (fun z =>
            M.vertices.sum (fun y => if ν.val y = 0 then 0 else
              γ₁ x y * γ₂ y z / ν.val y * M.dist y z))) := by
      simp_rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro x _
      apply Finset.sum_congr rfl; intro z _
      rw [← Finset.sum_add_distrib]
      apply Finset.sum_congr rfl; intro y _; split_ifs <;> ring
    _ = M.vertices.sum (fun x => M.vertices.sum (fun y => γ₁ x y * M.dist x y)) +
        M.vertices.sum (fun y => M.vertices.sum (fun z => γ₂ y z * M.dist y z)) := by
      rw [hxy_part, hyz_part]

"""

# Find end of gluedCoupling_cost_le (before W1_eq_zero_iff)
start = text.find("theorem gluedCoupling_cost_le")
end = text.find("\n\ntheorem W1_eq_zero_iff")
if start == -1 or end == -1:
    raise SystemExit("could not locate gluedCoupling_cost_le block")
text = text[:start] + NEW_COST + text[end:]

# W1_pos block
OLD_W1 = """private theorem W1_pos_of_vertex_ne (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
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

GAP = """private theorem exists_probExpectation_dist_gap (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) :
    (∃ a ∈ M.vertices, 0 < (probExpectation M μ (M.dist · a) - probExpectation M ν (M.dist · a))) ∨
      ∃ a ∈ M.vertices, 0 < (probExpectation M ν (M.dist · a) - probExpectation M μ (M.dist · a))) := by
  obtain ⟨xPlus, hxPlus, xMinus, hxMinus, hPlus, hMinus⟩ := exists_mass_imbalance_pair M μ ν hne
  by_cases hμ : 0 < probExpectation M μ (M.dist · xPlus) - probExpectation M ν (M.dist · xPlus)
  · exact Or.inl ⟨xPlus, hxPlus, hμ⟩
  · right
    by_cases hν : 0 < probExpectation M ν (M.dist · xPlus) - probExpectation M μ (M.dist · xPlus)
    · exact ⟨xPlus, hxPlus, hν⟩
    · push_neg at hμ hν
      have heqP : probExpectation M μ (M.dist · xPlus) = probExpectation M ν (M.dist · xPlus) := by linarith
      have heqM : probExpectation M μ (M.dist · xMinus) = probExpectation M ν (M.dist · xMinus) := by linarith
      have hsumP : M.vertices.sum (fun t => (μ.val t - ν.val t) * M.dist t xPlus) = 0 := by
        rw [← probExpectation_dist_sub M μ ν xPlus, heqP, sub_self]
      have hsumM : M.vertices.sum (fun t => (μ.val t - ν.val t) * M.dist t xMinus) = 0 := by
        rw [← probExpectation_dist_sub M μ ν xMinus, heqM, sub_self]
      have hdistPM : 0 < M.dist xPlus xMinus := dist_pos_of_ne M (by intro heq'; subst heq'; linarith)
      have hpos : 0 < (μ.val xPlus - ν.val xPlus) * M.dist xPlus xMinus :=
        mul_pos (sub_pos.mpr hPlus) hdistPM
      have hneg : (μ.val xMinus - ν.val xMinus) * M.dist xMinus xPlus < 0 :=
        mul_neg_of_neg_of_pos hMinus (by rwa [M.dist_comm])
      have hdecomp : M.vertices.sum (fun t => (μ.val t - ν.val t) * M.dist t xMinus) =
          (μ.val xPlus - ν.val xPlus) * M.dist xPlus xMinus +
            (μ.val xMinus - ν.val xMinus) * M.dist xMinus xMinus +
            ((M.vertices.erase xPlus).erase xMinus).sum (fun t => (μ.val t - ν.val t) * M.dist t xMinus) := by
        rw [← Finset.add_sum_erase _ _ hxPlus, ← Finset.add_sum_erase _ _ (Finset.mem_erase.mpr ⟨by intro heq'; subst heq'; linarith, hxMinus⟩), M.dist_self, mul_zero, add_zero]
      linarith [hsumM, hdecomp, hpos, hneg]

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

# Remove old exists_probExpectation if present from partial merge, insert GAP before W1_pos
if "private theorem exists_probExpectation_dist_gap" in text:
    s = text.find("private theorem exists_probExpectation_dist_gap")
    e = text.find("noncomputable def gluedCoupling")
    if e == -1:
        e = text.find("private theorem W1_pos_of_vertex_ne")
    text = text[:s] + GAP + "\n\n" + text[e:]
else:
    text = text.replace(OLD_W1, GAP)

# couplingTransportCost_pos_of_coupling if missing
if "couplingTransportCost_pos_of_coupling" not in text:
    ins = """private theorem couplingTransportCost_pos_of_coupling (M : FiniteMetricSpace)
    (μ ν : ProbDist M.vertices) (γ : ℕ → ℕ → ℝ) (hγ : IsCoupling M.vertices μ ν γ)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) :
    0 < couplingTransportCost M γ := by
  rcases hne with ⟨x, hx, hdiff⟩
  by_contra h
  push_neg at h
  have hz : couplingTransportCost M γ = 0 :=
    le_antisymm h (couplingTransportCost_nonneg M γ hγ.1)
  exact hdiff (couplingTransportCost_eq_zero_of_eq M μ ν γ hγ hz x hx)

"""
    text = text.replace("theorem couplingTransportCost_pos_of_vertex_ne", ins + "theorem couplingTransportCost_pos_of_vertex_ne")

if "  split_ifs with h <;> simp [M.dist_self x, h]" in text:
    text = text.replace(
        "  split_ifs with h <;> simp [M.dist_self x, h]",
        "  split_ifs with hxy\n  · subst hxy; rw [M.dist_self x]; ring\n  · simp",
    )
if "  · simp [h, μ.2.2.1 y hy]" in text:
    text = text.replace("  · simp [h, μ.2.2.1 y hy]", "  · subst h; exact μ.2.2.1 y hy")

for i, line in enumerate(text.splitlines(), 1):
    if "sorry" in line.split("--")[0]:
        raise SystemExit(f"sorry at {i}")

STAGING.write_text(text)
MAIN.write_text(text)
print(f"Wrote {len(text.splitlines())} lines to staging and main")
