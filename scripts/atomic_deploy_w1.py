#!/usr/bin/env python3
"""Build green WassersteinDistance from canonical + stash prob gap."""
import os
import re
import subprocess
from pathlib import Path

ROOT = Path("/Users/nova/ugp-lean-exp")
canonical = (ROOT / "scripts/WassersteinDistance_canonical.lean").read_text()
stash = Path("/tmp/w_stash.lean").read_text()

# prob gap from stash (obtain + push Not pattern)
ps = stash.index("private theorem probExpectation_dist_eq_all_imp_vertex_eq")
pe = stash.index("private theorem exists_probExpectation_dist_gap")
prob = stash[ps:pe]
prob = prob.replace(
    "    · obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthird\n      push Not at hthird",
    "    · have hthirdKeep := hthird\n      rcases hthirdKeep with ⟨u, hu, hut0, hutM, hudne⟩\n      push Not at hthird",
)
prob = prob.replace(
    "    · obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthird\n      push Not at hthird",
    "    · have hthirdKeep := hthird\n      rcases hthirdKeep with ⟨u, hu, hutP, hut0, hudne⟩\n      push Not at hthird",
)

cs = canonical.index("private theorem probExpectation_dist_eq_all_imp_vertex_eq")
ce = canonical.index("private theorem exists_probExpectation_dist_gap")
text = canonical[:cs] + prob + canonical[ce:]

text = text.replace("congr 1; ext w hw", "apply Finset.sum_congr rfl\n    intro w hw")

old_calc_tail = """    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      have hdecompCost :
          M.vertices.sum (fun x =>
              M.vertices.sum (fun w => γ₁ x w * M.dist x w) +
                M.vertices.sum (fun w =>
                  if ν.val w = (0 : ℝ) then (0 : ℝ) else
                    γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z)) =
            couplingTransportCost M γ₁ +
              M.vertices.sum (fun x =>
                M.vertices.sum (fun w =>
                  if ν.val w = (0 : ℝ) then (0 : ℝ) else
                    γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z)) := by
        simp_rw [← Finset.sum_add_distrib]
        unfold couplingTransportCost
        rfl
      rw [hdecompCost]
      exact add_le_add le_rfl (by
        rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
        exact hbound)"""

new_calc_tail = """    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      unfold couplingTransportCost
      rw [← Finset.sum_add_distrib]
      apply add_le_add le_rfl
      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
      exact hbound"""

text = text.replace(old_calc_tail, new_calc_tail)

text = re.sub(
    r"theorem W1_eq_zero_iff \(M : FiniteMetricSpace\) \(μ ν : ProbDist M\.vertices\) :.*?· exact W1_nonneg M μ μ",
    """theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ μ = ν := by
  constructor
  · intro hW1
    by_contra hμν
    have hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x := by
      by_contra hall
      push_neg at hall
      exact hμν (probDist_eq_of_vertex_weights_eq hall)
    linarith [W1_pos_of_vertex_ne M μ ν hne, W1_nonneg M μ ν, hW1]
  · intro hμν
    subst hμν
    apply le_antisymm
    · have hle := W1_le_couplingCost M μ μ (diagonalCoupling M.vertices μ)
        (diagonalCoupling_is_coupling M.vertices μ)
      rw [diagonalCoupling_cost_zero M μ] at hle
      exact hle
    · exact W1_nonneg M μ μ""",
    text,
    count=1,
    flags=re.DOTALL,
)

# add_sum_erase: canonical uses wrong named-arg order
text = text.replace(
    "rw [← Finset.add_sum_erase (s := M.vertices.erase t0) (f := fun t => δ t * M.dist t t0)\n          htMinusInErase]",
    "rw [← Finset.add_sum_erase (M.vertices.erase t0) (fun t => δ t * M.dist t t0) tMinus htMinusInErase]",
)
text = text.replace(
    "rw [← Finset.add_sum_erase (s := M.vertices.erase tPlus) (f := fun t => δ t * M.dist t tPlus)\n          ht0InErase]",
    "rw [← Finset.add_sum_erase (M.vertices.erase tPlus) (fun t => δ t * M.dist t tPlus) t0 ht0InErase]",
)

if "import Mathlib.Tactic.Ring" not in text:
    text = text.replace(
        "import Mathlib.Algebra.BigOperators.Field\n",
        "import Mathlib.Algebra.BigOperators.Field\nimport Mathlib.Tactic.Ring\n",
    )
if "set_option maxHeartbeats 800000" not in text:
    text = text.replace(
        "private theorem exists_delta_neg_of_sum_zero",
        "set_option maxHeartbeats 800000 in\n\nprivate theorem exists_delta_neg_of_sum_zero",
        1,
    )

if "sorry" in text.replace("- A declared (sorry)", ""):
    raise SystemExit("sorry in output")

dst = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"
tmp = dst.with_suffix(".lean.tmpdeploy")
tmp.write_text(text)
os.replace(tmp, dst)
print(f"Wrote {len(text.splitlines())} lines; prob has hthirdKeep:", "hthirdKeep" in text)

r = subprocess.run(
    ["lake", "build", "UgpLean.ContinuumLimit.WassersteinDistance"],
    cwd=ROOT,
    capture_output=True,
    text=True,
)
out = r.stdout + r.stderr
errs = [ln for ln in out.splitlines() if ln.startswith("error:")]
print(f"Wasserstein errors: {len(errs)}")
for ln in errs[:30]:
    print(ln)
if r.returncode != 0:
    raise SystemExit(r.returncode)

r2 = subprocess.run(
    ["lake", "build", "UgpLean.ContinuumLimit.GorardVacuumW1Bridge"],
    cwd=ROOT,
    capture_output=True,
    text=True,
)
print("GorardVacuumW1Bridge:", "OK" if r2.returncode == 0 else "FAIL")
if r2.returncode != 0:
    print((r2.stdout + r2.stderr)[-2000:])
    raise SystemExit(r2.returncode)
print("BUILD OK")
