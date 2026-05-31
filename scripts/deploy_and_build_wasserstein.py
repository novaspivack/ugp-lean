#!/usr/bin/env python3
"""Copy fixed canonical WassersteinDistance.lean and build."""
import os
import subprocess
from pathlib import Path

src = Path("/Users/nova/ugp-lean-exp/scripts/WassersteinDistance_canonical.lean")
dst = Path("/Users/nova/ugp-lean-exp/UgpLean/ContinuumLimit/WassersteinDistance.lean")
tmp = dst.with_suffix(".lean.tmpdeploy")

text = src.read_text()
if "sorry" in text.replace("- A declared (sorry)", ""):
    raise SystemExit("sorry in canonical")
for needle in ("hthirdEx", "le_trans (hsplit", "W1_eq_zero_iff", "dist_eq_zero_iff"):
    if needle not in text:
        raise SystemExit(f"missing: {needle}")

subprocess.run(["chflags", "nouchg", str(dst)], check=False)
tmp.write_text(text)
os.replace(tmp, dst)
subprocess.run(["chflags", "uchg", str(dst)], check=True)

build_dir = Path("/Users/nova/ugp-lean-exp/.lake/build/lib/UgpLean/ContinuumLimit")
for p in build_dir.glob("WassersteinDistance*"):
    p.unlink()

r = subprocess.run(
    ["lake", "build", "UgpLean.ContinuumLimit.WassersteinDistance", "UgpLean.ContinuumLimit.GorardVacuumW1Bridge"],
    cwd="/Users/nova/ugp-lean-exp",
    capture_output=True,
    text=True,
)
out = (r.stdout or "") + (r.stderr or "")
print(out[-4000:])
raise SystemExit(r.returncode)
