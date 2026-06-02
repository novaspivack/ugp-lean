#!/usr/bin/env python3
"""Generate per-bin cosh upper-bound lemmas used by the r=5 mesh."""
from __future__ import annotations

import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from sech_taylor_proofs import exp_taylor_bound, pick_taylor_n, rat  # noqa: E402

OUT = ROOT / "UgpLean/Substrate/SechOverlapIntegralBounds_r5bins.lean"
BIN_STEP = 0.0005
COSH_SCALE = 100_000_000
R = 5
N = 550
SQRT2 = math.sqrt(2.0)


def bin_val(u: float) -> float:
    return math.ceil(u / BIN_STEP - 1e-12) * BIN_STEP


def bin_key(u: float) -> str:
    b = bin_val(u)
    num = int(round(b * 10000))
    return f"b{num}"


def emit_small_cosh_ub(name: str, x: float, num: int, den: int) -> list[str]:
    """`x²/2 ≤ 1`: Taylor bound on `exp(x²/2)`."""
    t = x * x / 2
    n, _, _ = pick_taylor_n(t)
    n = max(n, 8)
    tnum, tden = exp_taylor_bound(t, n)
    tnum_s = int(tnum * COSH_SCALE / tden) + 1
    num = max(num, tnum_s)
    x_expr = rat(x)
    exp_name = f"exp_{name}"
    return [
        f"lemma cosh_{name}_ub : cosh ({x_expr}) ≤ ({num} : ℝ) / {den} := by",
        f"  have {exp_name} : exp (({x_expr})^2 / 2) ≤ ({tnum_s} : ℝ) / {den} := by",
        f"    have ht : ({x_expr})^2 / 2 ≤ 1 := by norm_num",
        f"    have hupper := Real.exp_bound' (by norm_num) ht (n := {n}) (by norm_num)",
        f"    have htaylor :",
        f"        (∑ m ∈ Finset.range {n}, (({x_expr})^2 / 2) ^ m / (Nat.factorial m)) +",
        f"          (({x_expr})^2 / 2) ^ {n} * ({n} + 1) / (Nat.factorial {n} * {n}) ≤",
        f"          ({tnum_s} : ℝ) / {den} := by",
        "      simp [Finset.sum_range_succ, Nat.factorial]",
        "      norm_num",
        f"    linarith [hupper, htaylor]",
        f"  exact (cosh_le_exp_half_sq ({x_expr})).trans (le_trans {exp_name} (by norm_num))",
        "",
    ]


def emit_cosh_bin(name: str, b: float) -> list[str]:
    num, den = int(math.cosh(b) * COSH_SCALE) + 1, COSH_SCALE
    if b * b / 2 <= 1.0 - 1e-12:
        return emit_small_cosh_ub(name, b, num, den)
    k = min(5, max(2, int(math.ceil(b - 1e-12))))
    return emit_small_cosh_ub(name, float(k), num, den)


def main() -> None:
    bins: dict[str, float] = {}
    for i in range(N):
        u = 5 * (i + 1) / N
        for x in (u, u / R):
            if x <= 0:
                continue
            bins[bin_key(x)] = bin_val(x)
    lines = [
        "import UgpLean.Substrate.SechOverlapIntegralBounds_cosh",
        "",
        "namespace UgpLean.Substrate.PhiMDLFluctuationSpectrum",
        "",
        "open Real",
        "",
        "lemma cosh_mono_Ici {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : cosh x ≤ cosh y := by",
        "  exact cosh_strictMonoOn.monotoneOn (Set.mem_Ici.mpr hx)",
        "    (Set.mem_Ici.mpr (hx.trans hxy)) hxy",
        "",
    ]
    for name in sorted(bins, key=lambda k: bins[k]):
        lines += emit_cosh_bin(name, bins[name])
    lines += ["end UgpLean.Substrate.PhiMDLFluctuationSpectrum", ""]
    OUT.write_text("\n".join(lines))
    print(f"Wrote {OUT}, bins={len(bins)}")


if __name__ == "__main__":
    main()
