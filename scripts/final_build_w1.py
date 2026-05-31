#!/usr/bin/env python3
"""Write complete WassersteinDistance.lean and verify build."""
import subprocess
import sys
from pathlib import Path

ROOT = Path("/Users/nova/ugp-lean-exp")
SRC = Path("/tmp/WassersteinDistance_complete.lean")
TARGET = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"
TMP = Path("/tmp/WassersteinDistance.lean.build")

text = SRC.read_text()

text = text.replace(
    "set_option maxHeartbeats 800000 in\n\nset_option maxHeartbeats 800000 in\n",
    "set_option maxHeartbeats 800000 in\n",
    1,
)

old_hsplit = """  have hsplit :
      M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = (0 : ℝ) then (0 : ℝ) else
                γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) =
        M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w =>
            if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := by
    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    refine Finset.sum_congr rfl fun w hw => ?_
    by_cases hν : ν.val w = (0 : ℝ)
    · simp [hν]
    · rw [if_neg hν, if_neg hν]
      have hν' : ν.val w ≠ 0 := Ne.symm hν
      have hcol : M.vertices.sum (fun z => γ₂ w z) = ν.val w := hγ₂.2.2.2.1 w hw
      rw [Finset.mul_sum, ← Finset.sum_mul, mul_add]
      have hleft : (γ₁ x w / ν.val w) * M.vertices.sum (fun z => γ₂ w z * M.dist x w) =
          γ₁ x w * M.dist x w := by rw [Finset.sum_mul, hcol, mul_div_cancel₀ _ hν']
      rw [hleft]; ring"""

HSPLIT_BODY = """    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    refine Finset.sum_congr rfl fun w hw => ?_
    by_cases hν : ν.val w = (0 : ℝ)
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

new_hsplit = """  have hsplit :
      M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = (0 : ℝ) then (0 : ℝ) else
                γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) =
        M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w =>
            if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := by
""" + HSPLIT_BODY

if old_hsplit in text:
    text = text.replace(old_hsplit, new_hsplit, 1)
elif "  have hsplit :" in text and "congr 1; ext w hw" in text:
    import re
    text = re.sub(
        r"(  have hsplit :[\s\S]*?:= by\n)([\s\S]*?)(  have hbound :)",
        lambda m: m.group(1) + HSPLIT_BODY + "\n" + m.group(3),
        text,
        count=1,
    )
else:
    print("hsplit block not found", file=sys.stderr)
    sys.exit(1)

old_calc = """    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      unfold couplingTransportCost
      rw [← hsplit]
      exact add_le_add (le_rfl : (M.vertices.sum fun x =>
          M.vertices.sum fun w => γ₁ x w * M.dist x w) ≤ _) (by
        rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]; exact hbound)"""

new_calc = """    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      unfold couplingTransportCost
      rw [← Finset.sum_add_distrib]
      apply add_le_add
      · exact le_rfl
      · rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
        exact hbound"""

for old in [old_calc,
            """    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      unfold couplingTransportCost
      rw [← Finset.sum_add_distrib]
      apply add_le_add le_rfl
      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
      exact hbound"""]:
    if old in text:
        text = text.replace(old, new_calc, 1)
        break
else:
    if "apply add_le_add\n      · exact le_rfl" not in text:
        print("calc tail not found", file=sys.stderr)
        sys.exit(1)

text = text.replace(
    "  · intro y hy x\n    exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂\n      (fun w z hz => hγ₂.2.2.1 z hz w) y hy x",
    "  · intro y hy x\n    exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂\n      (fun w z hz => hγ₂.2.2.1 z hz w) y hy x",
)

for i, line in enumerate(text.splitlines(), 1):
    stripped = line.split("--")[0]
    if "sorry" in stripped and "declared (sorry)" not in line:
        print(f"sorry at line {i}: {line}", file=sys.stderr)
        sys.exit(1)

TMP.write_text(text)
TMP.replace(TARGET)
print(f"Wrote {len(text.splitlines())} lines to {TARGET}")

result = subprocess.run(
    ["lake", "build", "UgpLean.ContinuumLimit.WassersteinDistance"],
    cwd=ROOT,
    capture_output=True,
    text=True,
)
print(result.stdout[-3000:] if len(result.stdout) > 3000 else result.stdout)
print(result.stderr[-3000:] if len(result.stderr) > 3000 else result.stderr)
sys.exit(result.returncode)
