#!/usr/bin/env python3
# Run from: ugp-lean-exp/scripts/ or adjust paths accordingly
"""Generate batched r=11 mesh lower-bound proofs for SechOverlapIntegralBounds."""
from __future__ import annotations

import math
import signal
import sys
from fractions import Fraction
from pathlib import Path

TIMEOUT_SECONDS = 600


def _timeout_handler(signum, frame):
    print(f"\nTIMEOUT: wall-clock limit {TIMEOUT_SECONDS}s reached.")
    sys.exit(1)

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "UgpLean/Substrate/SechOverlapIntegralBounds_r11mesh.lean"

R = 11
N = 40000
H = 12 / N
MICRO = 1555245  # floor cert for half-line; 2*1555245 = 3110490 >= 3110481
BATCH = 200


def cosh_ub(x: float) -> tuple[int, int]:
    ax = abs(x)
    scale = 1_000_000_000
    if ax == 0:
        return scale, scale
    return int(math.cosh(ax) * scale) + 1, scale


def rat(x: float) -> str:
    fr = Fraction(x).limit_denominator(1_000_000)
    return f"({fr.numerator} : ℝ) / {fr.denominator}"


def point_lb(u: float) -> float:
    nu, _ = cosh_ub(u)
    nv, _ = cosh_ub(u / R)
    return 1e18 / (nu * nv) * H


def point_micro(u: float) -> int:
    return int(point_lb(u) * 1_000_000)


def batch_micro(indices: list[int]) -> int:
    return int(sum(point_lb(12 * (i + 1) / N) for i in indices) * 1_000_000)


def emit_batch(lines: list[str], batch_id: int, indices: list[int]) -> None:
    cert = batch_micro(indices)
    terms = " + ".join(
        f"({H} : ℝ) * sechProd {R} ({rat(12 * (i + 1) / N)})" for i in indices
    )
    refs = ", ".join(f"sech11_pt_{i}_ge" for i in indices)
    lines += [
        f"private lemma sech11_batch_{batch_id}_ge : ({cert} : ℝ) / 1000000 ≤ {terms} := by",
        f"  linarith [{refs}]",
        "",
    ]


def main() -> None:
    signal.signal(signal.SIGALRM, _timeout_handler)
    signal.alarm(TIMEOUT_SECONDS)
    lines = [
        "import UgpLean.Substrate.PhiMDLFluctuationSpectrum",
        "",
        "namespace UgpLean.Substrate.PhiMDLFluctuationSpectrum",
        "",
        "open Real",
        "",
        "lemma sech_ge_of_cosh_le {x C : ℝ} (hC : 0 < C) (hc : cosh x ≤ C) :",
        "    1 / C ≤ sech x := by",
        "  unfold sech",
        "  exact (one_div_le_one_div (cosh_pos x) hC).2 hc",
        "",
        f"def sech11_meshN : Nat := {N}",
        "",
    ]

    batch_indices: list[int] = []
    batch_id = 0

    for i in range(N):
        u = 12 * (i + 1) / N
        micro = point_micro(u)
        nu, du = cosh_ub(u)
        nv, dv = cosh_ub(u / R)
        lines += [
            f"private lemma sech11_pt_{i}_ge : ({micro} : ℝ) / 1000000 ≤ "
            f"({H} : ℝ) * sechProd {R} {rat(u)} := by",
            "  unfold sechProd; unfold sech",
            f"  have hc1 := sech_ge_of_cosh_le (by norm_num) "
            f"(show cosh {rat(u)} ≤ ({nu} : ℝ) / {du} by norm_num)",
            f"  have hc2 := sech_ge_of_cosh_le (by norm_num) "
            f"(show cosh {rat(u / R)} ≤ ({nv} : ℝ) / {dv} by norm_num)",
            "  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)",
            "  norm_num at hprod ⊢; linarith",
            "",
        ]
        batch_indices.append(i)
        if len(batch_indices) == BATCH:
            emit_batch(lines, batch_id, batch_indices)
            batch_id += 1
            batch_indices = []

    if batch_indices:
        emit_batch(lines, batch_id, batch_indices)
        batch_id += 1

    total = batch_micro(list(range(N)))
    assert total >= MICRO, f"cert too low: {total} < {MICRO}"

    term_refs = " + ".join(
        f"({H} : ℝ) * sechProd {R} ({rat(12 * (i + 1) / N)})" for i in range(N)
    )
    batch_refs = ", ".join(f"sech11_batch_{j}_ge" for j in range(batch_id))

    lines += [
        "lemma sech11_uniform_cert_le_riemann :",
        f"    ({MICRO} : ℝ) / 1000000 ≤",
        f"      ({H} : ℝ) * ({term_refs}) := by",
        f"  linarith [{batch_refs}]",
        "",
        "end UgpLean.Substrate.PhiMDLFluctuationSpectrum",
        "",
    ]

    OUT.write_text("\n".join(lines))
    print(f"Wrote {OUT} ({len(lines)} lines), total_micro={total}, batches={batch_id}")
    signal.alarm(0)


if __name__ == "__main__":
    main()
