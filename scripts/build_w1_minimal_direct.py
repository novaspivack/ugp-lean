#!/usr/bin/env python3
"""Build minimal zero-sorry WassersteinDistance.lean from test base + extension."""
from pathlib import Path

ROOT = Path("/Users/nova/ugp-lean-exp")
TEST = (ROOT / "UgpLean/ContinuumLimit/WassersteinDistance_test.lean").read_text()
EXT = (ROOT / "UgpLean/ContinuumLimit/_w1_extension_insert.lean").read_text()
OUT = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean.staging"

EXTRA_IMPORTS = """import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
"""

DIST_EQ = "  dist_eq_zero_iff : ∀ x y, dist x y = 0 ↔ x = y\n"

MASS_BALANCE = """
private theorem probDist_vertex_mass_balance (S : Finset ℕ) (μ ν : ProbDist S) :
    S.sum (fun x => μ.val x - ν.val x) = 0 := by
  rw [Finset.sum_sub_distrib, μ.2.2.2, ν.2.2.2, sub_self]

"""

PROB_SUB = """
private theorem probExpectation_dist_sub (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (xAnchor : ℕ) :
    probExpectation M μ (M.dist · xAnchor) - probExpectation M ν (M.dist · xAnchor) =
      M.vertices.sum fun t => (μ.val t - ν.val t) * M.dist t xAnchor := by
  unfold probExpectation; rw [← Finset.sum_sub_distrib]; congr 1; funext t; ring

"""

GAP_DIRECT = """
private theorem exists_probExpectation_dist_gap (M : FiniteMetricSpace)
    (μ ν : ProbDist M.vertices) (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) :
    ((∃ a ∈ M.vertices, 0 < probExpectation M μ (M.dist · a) - probExpectation M ν (M.dist · a)) ∨
      ∃ a ∈ M.vertices, 0 < probExpectation M ν (M.dist · a) - probExpectation M μ (M.dist · a)) := by
  obtain ⟨xPlus, hxPlus, xMinus, hxMinus, hPlus, hMinus⟩ := exists_mass_imbalance_pair M μ ν hne
  have hnePM : xPlus ≠ xMinus := by
    intro heq; subst heq; linarith [hPlus, hMinus]
  have hdist : 0 < M.dist xPlus xMinus := dist_pos_of_ne M hnePM
  refine Or.inr ⟨xMinus, hxMinus, ?_⟩
  rw [probExpectation_dist_sub M μ ν xMinus]
  refine lt_of_lt_of_le (Finset.single_le_sum ?_) (Finset.sum_le_sum fun _ _ => le_rfl)
  · intro t ht
    exact mul_nonneg (sub_nonneg.mpr (le_of_lt hMinus)) (M.dist_nonneg t xMinus)
  · exact ⟨xPlus, hxPlus, mul_pos (sub_pos.mpr hPlus) hdist⟩

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

"""

W1_PROOFS = """
theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ μ = ν := by
  constructor
  · intro hW1
    by_contra hμν
    have hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x := by
      intro hall; push_neg at hall
      exact absurd hμν (probDist_eq_of_vertex_weights_eq hall)
    have hpos := W1_pos_of_vertex_ne M μ ν hne
    linarith [W1_nonneg M μ ν, hW1]
  · intro hμν; subst hμν
    apply le_antisymm
    · have hle := W1_le_couplingCost M μ μ (diagonalCoupling M.vertices μ)
        (diagonalCoupling_is_coupling M.vertices μ)
      rw [diagonalCoupling_cost_zero M μ] at hle
      exact hle
    · exact W1_nonneg M μ μ

theorem W1_triangle (M : FiniteMetricSpace)
    (μ ν ρ : ProbDist M.vertices) :
    W1 M μ ρ ≤ W1 M μ ν + W1 M ν ρ := by
  rw [le_iff_forall_pos_lt_add]
  intro ε hε
  obtain ⟨c₁, hc₁mem, hc₁lt⟩ :=
    Real.lt_sInf_add_pos (couplingCostSet_nonempty M μ ν) (half_pos hε)
  obtain ⟨c₂, hc₂mem, hc₂lt⟩ :=
    Real.lt_sInf_add_pos (couplingCostSet_nonempty M ν ρ) (half_pos hε)
  obtain ⟨γ₁, hγ₁, hc₁eq⟩ := hc₁mem
  obtain ⟨γ₂, hγ₂, hc₂eq⟩ := hc₂mem
  have hglued := gluedCoupling_is_coupling M μ ν ρ γ₁ γ₂ hγ₁ hγ₂
  have hcost := gluedCoupling_cost_le M μ ν ρ γ₁ γ₂ hγ₁ hγ₂
  have hle := W1_le_couplingCost M μ ρ (gluedCoupling M.vertices ν γ₁ γ₂) hglued
  have hW1μν : W1 M μ ν ≤ c₁ := by
    unfold W1; apply csInf_le
    · refine ⟨0, ?_⟩; intro c hc; obtain ⟨γ', hγ', hc'⟩ := hc; rw [hc']; exact couplingTransportCost_nonneg M γ' hγ'.1
    · exact ⟨γ₁, hγ₁, hc₁eq⟩
  have hW1νρ : W1 M ν ρ ≤ c₂ := by
    unfold W1; apply csInf_le
    · refine ⟨0, ?_⟩; intro c hc; obtain ⟨γ', hγ', hc'⟩ := hc; rw [hc']; exact couplingTransportCost_nonneg M γ' hγ'.1
    · exact ⟨γ₂, hγ₂, hc₂eq⟩
  have hc₁lt' : c₁ < W1 M μ ν + ε / 2 := by simpa [W1] using hc₁lt
  have hc₂lt' : c₂ < W1 M ν ρ + ε / 2 := by simpa [W1] using hc₂lt
  linarith [hle, hcost, hc₁lt', hc₂lt', hW1μν, hW1νρ]

"""

# Clean extension: remove duplicate W1_pos block marker, fix glued proofs
ext = EXT
ext = ext.replace(
    "  · rw [h]; exact μ.2.2.1 y hy",
    "  · simp [h, μ.2.2.1 y hy]",
)
if "rw [mul_comm (M.dist x z)" not in ext:
    ext = ext.replace(
        "      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv",
        "      rw [mul_comm (M.dist x z), mul_comm (M.dist x w + M.dist w z)]\n"
        "      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv",
    )
ext = ext.replace(
    "      simp [hν, Finset.sum_eq_zero fun x' _ => by simp [hcol x']]",
    "      simp [hν, hcol]",
)
# Remove old private W1_pos at end of extension (we supply GAP_DIRECT)
idx = ext.find("private theorem W1_pos_of_vertex_ne")
if idx >= 0:
    ext = ext[:idx].rstrip()

# Fix hsplit ext w hw
ext = ext.replace(
    "    congr 1; ext w hw\n    by_cases hν : ν.val w = 0",
    "    congr 1; ext w\n    intro hw\n    by_cases hν : ν.val w = 0",
)
ext = ext.replace(
    "  · intro y hy x; exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂ (fun w z hz => hγ₂.2.2.1 hz w) y hy x",
    "  · intro y hy x; exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂ (fun w z hz => hγ₂.2.2.1 z hz w) y hy x",
)

lines = TEST.splitlines(keepends=True)
out: list[str] = []
skip = False
i = 0
while i < len(lines):
    line = lines[i]
    if skip:
        if line.strip().startswith("theorem W1_triangle"):
            i += 1
            while i < len(lines) and not lines[i].strip().startswith("/-!"):
                i += 1
            skip = False
            continue
        i += 1
        continue
    if line.startswith("import Mathlib.Algebra.Order.BigOperators.Group.Finset"):
        out.append(line)
        out.append(EXTRA_IMPORTS)
        i += 1
        continue
    if "  triangle    : ∀ x y z, dist x z ≤ dist x y + dist y z" in line:
        out.append(line)
        out.append(DIST_EQ)
        i += 1
        continue
    if line.strip() == "def ProbDist (S : Finset ℕ) : Type :=":
        out.append(line)
        i += 1
        while i < len(lines) and not lines[i].startswith("/--"):
            out.append(lines[i])
            i += 1
        out.append(MASS_BALANCE)
        continue
    if line.strip().startswith("theorem W1_eq_zero_iff"):
        out.append(PROB_SUB)
        out.append(ext)
        out.append("\n")
        out.append(GAP_DIRECT)
        out.append(W1_PROOFS)
        skip = True
        i += 1
        continue
    if line.strip() == "axiom gorard_vacuum_oric_zero":
        out.append('@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n')
        out.append(line)
        i += 1
        continue
    out.append(line)
    i += 1

text = "".join(out)
if "sorry" in text.replace("declared (sorry)", ""):
    raise SystemExit("proof sorry in output")
OUT.write_text(text)
print(f"Wrote {OUT} ({text.count(chr(10))+1} lines)")
