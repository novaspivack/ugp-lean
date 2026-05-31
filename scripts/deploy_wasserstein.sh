#!/usr/bin/env bash
set -euo pipefail
ROOT="$(cd "$(dirname "$0")/.." && pwd)"
TARGET="$ROOT/UgpLean/ContinuumLimit/WassersteinDistance.lean"
CANON="$ROOT/scripts/WassersteinDistance_canonical.lean"

python3 <<PY
from pathlib import Path
root = Path("$ROOT")
text = (root / "scripts/WassersteinDistance_canonical.lean").read_text()
header = "import Mathlib.Data.Real.Archimedean\n\n"
text = text.replace("import Mathlib.Data.Finset.Basic", header + "import Mathlib.Data.Finset.Basic", 1)
needle = "def ProbDist (S : Finset ℕ) : Type :=\n  { f : ℕ → ℝ // (∀ x ∈ S, 0 ≤ f x) ∧ (∀ x ∉ S, f x = 0) ∧ S.sum f = 1 }"
insert = needle + """

instance ProbDist.coeFun (S : Finset ℕ) : CoeFun (ProbDist S) (fun _ => ℕ → ℝ) where
  coe μ := μ.val

@[simp] theorem ProbDist.coe_apply {S : Finset ℕ} (μ : ProbDist S) (x : ℕ) :
    (μ : ℕ → ℝ) x = μ.val x :=
  rfl"""
text = text.replace(needle, insert)
text = text.replace(
    "axiom gorard_vacuum_oric_zero",
    '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\naxiom gorard_vacuum_oric_zero',
)
Path("$TARGET").write_text(text + "\n")
print(f"deployed {len(text.splitlines())} lines")
PY

cd "$ROOT"
rm -f .lake/build/lib/lean/UgpLean/ContinuumLimit/WassersteinDistance.*
lake build UgpLean.ContinuumLimit.WassersteinDistance UgpLean.ContinuumLimit.GorardVacuumW1Bridge
rg '\bsorry\b' "$TARGET" | rg -v 'declared \(sorry\)' && exit 1 || true
echo "BUILD OK"
