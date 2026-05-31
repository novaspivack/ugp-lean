#!/usr/bin/env python3
"""Write complete product-path WassersteinDistance.lean in one atomic script."""
import subprocess
import sys
from pathlib import Path

ROOT = Path("/Users/nova/ugp-lean-exp")
sys.path.insert(0, str(ROOT / "scripts"))

# Generate insert via assemble module logic
import assemble_wasserstein_clean as asm  # noqa: E402

CANON = ROOT / "scripts/WassersteinDistance_canonical.lean"
TARGET = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"

canon = CANON.read_text()
g0 = canon.index("noncomputable def gluedCoupling")
g1 = canon.index("theorem W1_eq_zero_iff")
insert = asm.part_a + asm.part_b + asm.part_c + canon[g0:g1]

EXTRA_IMPORTS = """import Mathlib.Data.Real.Archimedean
import Mathlib.Algebra.BigOperators.Ring.Finset
import Mathlib.Algebra.BigOperators.Field
"""

DIST_EQ_ZERO_FIELD = "  dist_eq_zero_iff : ∀ x y, dist x y = 0 ↔ x = y\n"

MASS_BALANCE = """
private theorem probDist_vertex_mass_balance (S : Finset ℕ) (μ ν : ProbDist S) :
    S.sum (fun x => μ.val x - ν.val x) = 0 := by
  rw [Finset.sum_sub_distrib, μ.2.2.2, ν.2.2.2, sub_self]

"""

W1_PROOFS = """
theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  constructor
  · intro hW1
    by_contra hne
    push_neg at hne
    have hpos := W1_pos_of_vertex_ne M μ ν hne
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
  unfold W1 at hle hW1μν hW1νρ ⊢
  linarith [hle, hcost, hc₁lt, hc₂lt, hW1μν, hW1νρ]

"""

DEPRECATED_AXIOM = """@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]
axiom gorard_vacuum_oric_zero
"""

head = subprocess.check_output(
    ["git", "show", "d8c281f:UgpLean/ContinuumLimit/WassersteinDistance.lean"],
    cwd=ROOT,
    text=True,
)

lines = head.splitlines(keepends=True)
out: list[str] = []
skip = False
i = 0
while i < len(lines):
    line = lines[i]
    if skip:
        if line.strip().startswith("/-!"):
            skip = False
            out.append(line)
        i += 1
        continue
    if line.startswith("import Mathlib.Algebra.Order.BigOperators.Group.Finset"):
        out.append(line)
        out.append(EXTRA_IMPORTS)
        i += 1
        continue
    if "  triangle    : ∀ x y z, dist x z ≤ dist x y + dist y z" in line:
        out.append(line)
        out.append(DIST_EQ_ZERO_FIELD)
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
        out.append(insert)
        out.append(W1_PROOFS)
        skip = True
        i += 1
        continue
    if line.strip() == "axiom gorard_vacuum_oric_zero":
        out.append(DEPRECATED_AXIOM)
        i += 1
        continue
    out.append(line)
    i += 1

text = "".join(out)
assert "delta_three" not in text
assert "sorry" not in text.replace("declared (sorry)", "")
Path("/tmp/WassersteinDistance_product.lean").write_text(text)
TARGET.write_text(text)
print(f"Wrote {len(text.splitlines())} lines")
