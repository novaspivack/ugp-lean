#!/usr/bin/env python3
"""Assemble WassersteinDistance.lean with gap_v2 proof and fixed glued coupling."""
from pathlib import Path

ROOT = Path("/Users/nova/ugp-lean-exp/UgpLean/ContinuumLimit")
main = (ROOT / "WassersteinDistance.lean").read_text()
gap_v2 = (ROOT / "_gap_v2.lean").read_text().strip()
complete = (ROOT / "WassersteinDistance.lean.complete").read_text()

i0 = main.index("private theorem delta_three_anchor_contradiction")
part1 = main[:i0]

i1 = main.index("private theorem exists_probExpectation_dist_gap")
i2 = main.index("noncomputable def gluedCoupling")
part2 = main[i1:i2]

g0 = complete.index("noncomputable def gluedCoupling")
g1 = complete.index("\ntheorem probExpectation_dist_sub")
glued = complete[g0:g1]

cs = glued.index("theorem gluedCoupling_cost_le")
fixed_cost = (Path(__file__).parent / "w1_glued_cost_le.lean").read_text()
glued = glued[:cs] + fixed_cost + "\n"

i3 = main.index("theorem W1_eq_zero_iff")
part4 = main[i3:]

out = part1 + gap_v2 + "\n\n" + part2 + glued + part4
(ROOT / "WassersteinDistance.lean").write_text(out)
print(f"Wrote {len(out.splitlines())} lines")
