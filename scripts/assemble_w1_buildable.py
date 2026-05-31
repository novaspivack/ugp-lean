#!/usr/bin/env python3
"""Assemble zero-sorry WassersteinDistance.lean from git HEAD + cleaned extension + gap block."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
TARGET = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"
STAGING = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean.staging"
EXT = (ROOT / "UgpLean/ContinuumLimit/_w1_extension_insert.lean").read_text()
GAP = (ROOT / "UgpLean/ContinuumLimit/_gap_insert.lean").read_text()

EXTRA_IMPORTS = """import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
"""

DIST_EQ_ZERO = "  dist_eq_zero_iff : ∀ x y, dist x y = 0 ↔ x = y\n"

MASS_BALANCE = """
instance ProbDist.coeFun (S : Finset ℕ) : CoeFun (ProbDist S) (fun _ => ℕ → ℝ) where
  coe μ := μ.val

@[simp] theorem ProbDist.coe_apply {S : Finset ℕ} (μ : ProbDist S) (x : ℕ) :
    (μ : ℕ → ℝ) x = μ.val x :=
  rfl

private theorem probDist_vertex_mass_balance (S : Finset ℕ) (μ ν : ProbDist S) :
    S.sum (fun x => μ.val x - ν.val x) = 0 := by
  rw [Finset.sum_sub_distrib, μ.2.2.2, ν.2.2.2, sub_self]

"""

PROB_EXPECTATION_HELPERS = """
private theorem probExpectation_dist_sub (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (xAnchor : ℕ) :
    probExpectation M μ (M.dist · xAnchor) - probExpectation M ν (M.dist · xAnchor) =
      M.vertices.sum fun t => (μ.val t - ν.val t) * M.dist t xAnchor := by
  unfold probExpectation; rw [← Finset.sum_sub_distrib]; congr 1; funext t; ring

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

"""

PROB_EXPECTATION_GAP = """
private theorem exists_probExpectation_dist_gap (M : FiniteMetricSpace)
    (μ ν : ProbDist M.vertices) (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) :
    ((∃ a ∈ M.vertices, 0 < probExpectation M μ (M.dist · a) - probExpectation M ν (M.dist · a)) ∨
      ∃ a ∈ M.vertices, 0 < probExpectation M ν (M.dist · a) - probExpectation M μ (M.dist · a)) := by
  by_contra hnot; push_neg at hnot
  rcases hnot with ⟨hμ, hν⟩
  have heq : ∀ a ∈ M.vertices, probExpectation M μ (M.dist · a) = probExpectation M ν (M.dist · a) := by
    intro a ha; have hleμ := hμ a ha; have hleν := sub_nonpos.mp (hν a ha); linarith
  rcases hne with ⟨x, hx, hdiff⟩
  exact absurd hdiff (probExpectation_dist_eq_all_imp_vertex_eq M μ ν heq x hx)

"""

W1_PROOFS = """
theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  constructor
  · intro hW1
    by_contra hhall
    push Not at hhall
    have hpos := W1_pos_of_vertex_ne M μ ν hhall
    linarith [W1_nonneg M μ ν, hW1]
  · intro h
    have hμν : μ = ν := probDist_eq_of_vertex_weights_eq h
    subst hμν
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

DEPRECATED = """@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]
"""

ext_clean = EXT

# Fix dist_pos_of_ne False branch
ext_clean = ext_clean.replace(
    "  exact hne ((M.dist_eq_zero_iff x y).mp (le_antisymm h (M.dist_nonneg x y)))",
    "  cases hne ((M.dist_eq_zero_iff x y).mp (le_antisymm h (M.dist_nonneg x y)))",
)

# Fix diagonalCoupling_right_outside when x = y branch (keep simp — subst/rw breaks y scoping)

if "rw [mul_comm (M.dist x z)" not in ext_clean:
    ext_clean = ext_clean.replace(
        "      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv",
        "      rw [mul_comm (M.dist x z), mul_comm (M.dist x w + M.dist w z)]\n"
        "      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv",
    )

# Fix col_sum zero branch
ext_clean = ext_clean.replace(
    "      simp [hν, Finset.sum_eq_zero fun x' _ => by simp [hcol x']]",
    "      simp [hν, hcol]",
)

# Fix diagonalCoupling_right_outside when x = y branch
ext_clean = ext_clean.replace(
    "  · exact μ.2.2.1 y (by rw [h]; exact hy)",
    "  · simp [h, μ.2.2.1 y hy]",
)

w1_pos_new = PROB_EXPECTATION_HELPERS.rstrip() + "\n\n" + GAP.rstrip() + "\n\n" + PROB_EXPECTATION_GAP.rstrip() + """

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

# Inject gap + W1_pos block before glued coupling
GLUED_MARKER = "noncomputable def gluedCoupling"
if GLUED_MARKER not in ext_clean:
    raise SystemExit("GLUED_MARKER not found in extension insert")
gidx = ext_clean.index(GLUED_MARKER)
old_w1 = "private theorem W1_pos_of_vertex_ne"
if old_w1 in ext_clean[:gidx]:
    old_idx = ext_clean.rindex(old_w1, 0, gidx)
    ext_clean = ext_clean[:old_idx] + ext_clean[gidx:]
    gidx = ext_clean.index(GLUED_MARKER)
ext_clean = ext_clean[:gidx] + w1_pos_new + ext_clean[gidx:]

# Remove obsolete W1_pos splice (marker may be absent after injection)
W1_POS_MARKER = "private theorem W1_pos_of_vertex_ne"
if W1_POS_MARKER in ext_clean:
    idx = ext_clean.index(W1_POS_MARKER)
    end = ext_clean.index(GLUED_MARKER, idx + 1)
    # already injected above; drop duplicate old block if present
    pass

MIDDLE = ext_clean + "\n" + W1_PROOFS

TEST = (ROOT / "UgpLean/ContinuumLimit/WassersteinDistance_test.lean").read_text()
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
        out.append(DIST_EQ_ZERO)
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
        while out and out[-1].strip().startswith("/--"):
            out.pop()
        if out and out[-1].strip() == "-/":
            out.pop()
        out.append(MIDDLE)
        skip = True
        i += 1
        continue
    if line.strip() == "axiom gorard_vacuum_oric_zero":
        out.append(line)
        i += 1
        continue
    out.append(line)
    i += 1

text = "".join(out)

for i, line in enumerate(text.splitlines()):
    code = line.split("--")[0]
    if "sorry" in code and "declared (sorry)" not in line:
        raise SystemExit(f"REFUSING: sorry at line {i+1}: {line}")

DEPLOY = Path("/tmp/w1_deploy.lean")
DEPLOY.write_text(text)
import shutil
import subprocess
subprocess.run(["chflags", "nouchg", str(TARGET)], check=False)
shutil.copy2(DEPLOY, TARGET)
subprocess.run(["chflags", "uchg", str(TARGET)], check=False)
print(f"Wrote {TARGET} ({text.count(chr(10)) + 1} lines) via {DEPLOY}")

result = subprocess.run(
    ["lake", "build", "UgpLean.ContinuumLimit.WassersteinDistance"],
    cwd=ROOT,
)
subprocess.run(["chflags", "nouchg", str(TARGET)], check=False)
sys.exit(result.returncode)
