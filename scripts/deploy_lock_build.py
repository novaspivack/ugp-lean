#!/usr/bin/env python3
import hashlib
import os
import subprocess
from pathlib import Path

src = Path("/Users/nova/ugp-lean-exp/scripts/WassersteinDistance_canonical.lean")
dst = Path("/Users/nova/ugp-lean-exp/UgpLean/ContinuumLimit/WassersteinDistance.lean")
repo = Path("/Users/nova/ugp-lean-exp")

text = src.read_text()
src_hash = hashlib.md5(text.encode()).hexdigest()

subprocess.run(["chflags", "nouchg", str(dst)], check=False)
dst.write_text(text)
subprocess.run(["chflags", "uchg", str(dst)], check=True)

if hashlib.md5(dst.read_text().encode()).hexdigest() != src_hash:
    raise SystemExit("deploy hash mismatch after write")

for p in (repo / ".lake/build/lib/UgpLean/ContinuumLimit").glob("WassersteinDistance*"):
    p.unlink()

r = subprocess.run(
    ["lake", "build", "UgpLean.ContinuumLimit.WassersteinDistance", "UgpLean.ContinuumLimit.GorardVacuumW1Bridge"],
    cwd=repo,
)
print("build exit", r.returncode)
print("lines", len(dst.read_text().splitlines()), "md5", hashlib.md5(dst.read_text().encode()).hexdigest())
raise SystemExit(r.returncode)
