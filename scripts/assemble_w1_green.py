#!/usr/bin/env python3
"""Assemble green WassersteinDistance.lean from staging + known fixes."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
text = (ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean.staging").read_text()

# Drop duplicate set_option block if present
first = text.find("set_option maxHeartbeats 800000 in")
if first != -1:
    second = text.find("set_option maxHeartbeats 800000 in", first + 1)
    if second != -1:
        text = text[:second].rstrip() + "\n\n" + text[second:].split("\n", 1)[1]

# eq_zero: correct hne direction in sum_eq_single
text = text.replace(
    "      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy (Ne.symm hne)) (fun hne => absurd hx hne)]\n    rw [← hsumx",
    "      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun hne => absurd hx hne)]\n    rw [← hsumx",
)

# glued row/col inner sums
text = text.replace(
    """    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        have hsum' : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) =
            S.sum (fun z => γ₂ w z * (γ₁ x w / ν.val w)) := by
          refine Finset.sum_congr rfl fun z _ => by ring
        rw [hsum', ← Finset.sum_mul, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
    """    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        have hconst : ∀ z, γ₁ x w * γ₂ w z / ν.val w = (γ₁ x w / ν.val w) * γ₂ w z := fun z => by ring
        rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
)

text = text.replace(
    """    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by
        have hsum' : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) =
            S.sum (fun x' => (γ₂ w z / ν.val w) * γ₁ x' w) := by
          refine Finset.sum_congr rfl fun x' _ => by ring
        rw [hsum', Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
    """    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by
        have hconst : ∀ x', γ₁ x' w * γ₂ w z / ν.val w = (γ₂ w z / ν.val w) * γ₁ x' w := fun x' => by ring
        rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
)

# gluedCoupling_cost_le — use finalize NEW_COST
NEW_COST = open(ROOT / "scripts/finalize_w1_staging.py").read().split('NEW_COST = """')[1].split('"""')[0]
start = text.find("theorem gluedCoupling_cost_le")
end = text.find("\n\ntheorem W1_eq_zero_iff")
text = text[:start] + NEW_COST + text[end:]

# probExpectation_dist_sub private
text = text.replace("theorem probExpectation_dist_sub", "private theorem probExpectation_dist_sub", 1)

# single deprecated on gorard axiom
while text.count('@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped"') > 1:
    text = text.replace(
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n'
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n',
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n',
        1,
    )

out = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"
out.write_text(text)
print(f"Wrote {len(text.splitlines())} lines")
