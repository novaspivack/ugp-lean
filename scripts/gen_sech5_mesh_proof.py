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
from sech_taylor_proofs import pick_taylor_n, rat  # noqa: E402

OUT = ROOT / "UgpLean/Substrate/SechOverlapIntegralBounds_r5mesh.lean"

R = 5
N = 550
H = 5 / N
HALF_TARGET = 1492288
BATCH = 50

COSH_CEIL = {
    2: (3763, 1000),
    3: (10068, 1000),
    4: (27309, 1000),
    5: (84600, 1000),
}


def sech_lb_micro(u: float) -> int:
    nu = cosh_ub_val(u)
    nv = cosh_ub_val(u / R)
    return int(1 / nu / nv * H * 1_000_000)


def cosh_ub_val(u: float) -> float:
    if u <= 1.0:
        t = u * u / 2
        n, num, den = pick_taylor_n(t)
        return num / den
    k = int(math.ceil(u - 1e-12))
    num, den = COSH_CEIL[k]
    return num / den


def emit_cosh_le(u: float, idx: int, comp: str) -> list[str]:
    u_expr = rat(u)
    name = f"cosh5_{comp}_{idx}_le"
    if u <= 1.0:
        t = u * u / 2
        n, num, den = pick_taylor_n(t)
        exp_name = f"exp5_{comp}_{idx}_le"
        return [
            f"private lemma {exp_name} : exp (({u_expr})^2 / 2) ≤ ({num} : ℝ) / {den} := by",
            f"  refine exp_le_taylor (by norm_num) (by norm_num) (n := {n}) (by norm_num) ?_",
            "  simp [Finset.sum_range_succ, Nat.factorial]",
            "  norm_num",
            "",
            f"private lemma {name} : cosh {u_expr} ≤ ({num} : ℝ) / {den} := by",
            f"  exact (cosh_le_exp_half_sq {u_expr}).trans {exp_name}",
            "",
        ]
    k = int(math.ceil(u - 1e-12))
    num, den = COSH_CEIL[k]
    return [
        f"private lemma {name} : cosh {u_expr} ≤ ({num} : ℝ) / {den} := by",
        f"  gcongr",
        f"  exact cosh_{k}_le",
        "",
    ]


def batch_micro(indices: list[int]) -> int:
    return int(
        sum(1 / cosh_ub_val(5 * (i + 1) / N) / cosh_ub_val((5 * (i + 1) / N) / R) * H for i in indices)
        * 1_000_000
    )


def main() -> None:
    header = [
        "import UgpLean.Substrate.SechOverlapIntegralBounds_cosh",
        "",
        "namespace UgpLean.Substrate.PhiMDLFluctuationSpectrum",
        "",
        "open Real",
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
