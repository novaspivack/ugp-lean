#!/usr/bin/env python3
"""Generate r=5 half-line mesh with per-point Taylor cosh proofs."""
from __future__ import annotations

import math
import sys
from fractions import Fraction
from math import factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from sech_taylor_proofs import rat  # noqa: E402
from gen_sech5_cosh_bins import BIN_STEP, COSH_SCALE, R, bin_key, bin_val  # noqa: E402

OUT = ROOT / "UgpLean/Substrate/SechOverlapIntegralBounds_r5mesh.lean"

N = 550
H = 5 / N
HALF_TARGET = 1492288
BATCH = 50


def cosh_ub_rational(u: float) -> tuple[int, int]:
    b = bin_val(u)
    return int(math.cosh(b) * COSH_SCALE) + 1, COSH_SCALE


def sech_lb_micro(u: float) -> int:
    nu, du = cosh_ub_rational(u)
    nv, dv = cosh_ub_rational(u / R)
    return int(dv * du / nv / nu * H * 1_000_000)


def cosh_ub_val(u: float) -> float:
    num, den = cosh_ub_rational(u)
    return num / den


def emit_cosh_le(u: float, idx: int, comp: str) -> list[str]:
    u_expr = rat(u)
    name = f"cosh5_{comp}_{idx}_le"
    bk = bin_key(u)
    b_expr = rat(bin_val(u))
    num, _ = cosh_ub_rational(u)
    return [
        f"private lemma {name} : cosh {u_expr} ≤ ({num} : ℝ) / {COSH_SCALE} := by",
        f"  have hmono := cosh_mono_Ici ({u_expr}) (by norm_num) (by norm_num : ({u_expr}) ≤ ({b_expr}))",
        f"  exact hmono.trans cosh_{bk}_ub",
        "",
    ]


def batch_micro(indices: list[int]) -> int:
    return int(
        sum(1 / cosh_ub_val(5 * (i + 1) / N) / cosh_ub_val((5 * (i + 1) / N) / R) * H for i in indices)
        * 1_000_000
    )


def main() -> None:
    header = [
        "import UgpLean.Substrate.SechOverlapIntegralBounds_r5bins",
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
        f"def sech5_meshN : Nat := {N}",
        "",
    ]
    lines = list(header)
    batch_indices: list[int] = []
    batch_id = 0

    for i in range(N):
        u = 5 * (i + 1) / N
        micro = sech_lb_micro(u)
        lines += emit_cosh_le(u, i, "u")
        lines += emit_cosh_le(u / R, i, "v")
        lines += [
            f"private lemma sech5_pt_{i}_ge : ({micro} : ℝ) / 1000000 ≤ "
            f"({rat(H)} : ℝ) * sechProd {R} {rat(u)} := by",
            "  unfold sechProd; unfold sech",
            f"  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_{i}_le)",
            f"  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_{i}_le)",
            "  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)",
            "  norm_num at hprod ⊢; linarith",
            "",
        ]
        batch_indices.append(i)
        if len(batch_indices) == BATCH:
            cert = batch_micro(batch_indices)
            terms = " + ".join(f"({rat(H)} : ℝ) * sechProd {R} {rat(5 * (j + 1) / N)}" for j in batch_indices)
            refs = ", ".join(f"sech5_pt_{j}_ge" for j in batch_indices)
            lines += [
                f"private lemma sech5_batch_{batch_id}_ge : ({cert} : ℝ) / 1000000 ≤ {terms} := by",
                f"  linarith [{refs}]",
                "",
            ]
            batch_id += 1
            batch_indices = []

    if batch_indices:
        cert = batch_micro(batch_indices)
        terms = " + ".join(f"({rat(H)} : ℝ) * sechProd {R} {rat(5 * (j + 1) / N)}" for j in batch_indices)
        refs = ", ".join(f"sech5_pt_{j}_ge" for j in batch_indices)
        lines += [
            f"private lemma sech5_batch_{batch_id}_ge : ({cert} : ℝ) / 1000000 ≤ {terms} := by",
            f"  linarith [{refs}]",
            "",
        ]
        batch_id += 1

    total = batch_micro(list(range(N)))
    assert total >= HALF_TARGET, f"total {total} < {HALF_TARGET}"
    batch_refs = ", ".join(f"sech5_batch_{j}_ge" for j in range(batch_id))
    term_refs = " + ".join(f"({rat(H)} : ℝ) * sechProd {R} {rat(5 * (i + 1) / N)}" for i in range(N))
    lines += [
        f"lemma sech5_halfline_meshSum_ge : ({HALF_TARGET} : ℝ) / 1000000 ≤ ({term_refs}) := by",
        f"  linarith [{batch_refs}]",
        "",
        "end UgpLean.Substrate.PhiMDLFluctuationSpectrum",
        "",
    ]
    OUT.write_text("\n".join(lines))
    print(f"Wrote {OUT}, lines={len(lines)}, total_micro={total}, batches={batch_id}")


if __name__ == "__main__":
    main()
