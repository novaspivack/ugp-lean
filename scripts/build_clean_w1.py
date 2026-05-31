#!/usr/bin/env python3
"""Build a clean zero-sorry WassersteinDistance.lean from canonical minus delta gap."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
CANON = ROOT / "scripts/WassersteinDistance_canonical.lean"
STAGING = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean.staging"

text = CANON.read_text()

replacements = [
    (
        "  · exact productCoupling_row_sum S μ ν\n  · exact productCoupling_col_sum S μ ν",
        "  · intro x hx; exact productCoupling_row_sum S μ ν x hx\n  · intro y hy; exact productCoupling_col_sum S μ ν y hy",
    ),
    (
        "  · exact diagonalCoupling_row_sum S μ\n  · exact diagonalCoupling_col_sum S μ",
        "  · intro x hx; exact diagonalCoupling_row_sum S μ x hx\n  · intro y hy; exact diagonalCoupling_col_sum S μ y hy",
    ),
    (
        "  · simp [h, μ.2.2.1 y hy]",
        "  · subst h; exact μ.2.2.1 y hy",
    ),
    (
        "  split_ifs with h <;> simp [M.dist_self, h]",
        "  split_ifs with hxy\n  · subst hxy; rw [M.dist_self x]; ring\n  · simp",
    ),
    (
        "axiom gorard_vacuum_oric_zero",
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\naxiom gorard_vacuum_oric_zero',
        1,
    ),
]

for item in replacements:
    old, new = item[0], item[1]
    count = item[2] if len(item) > 2 else -1
    if old not in text:
        print(f"skip (absent): {old[:80]}...")
        continue
    text = text.replace(old, new, count)

for i, line in enumerate(text.splitlines(), 1):
    code = line.split("--")[0]
    if "sorry" in code:
        raise SystemExit(f"sorry at line {i}: {line}")

STAGING.write_text(text)
print(f"Wrote {STAGING} ({len(text.splitlines())} lines)")
