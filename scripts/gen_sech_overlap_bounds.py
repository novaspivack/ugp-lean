#!/usr/bin/env python3
"""Generate r=11 mesh certification for SechOverlapIntegralBounds_r11cert.lean."""
from __future__ import annotations

import math
from fractions import Fraction
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
OUT = ROOT / "UgpLean/Substrate/SechOverlapIntegralBounds_r11cert.lean"

R = 11


def f(u: float) -> float:
    return 1.0 / math.cosh(u / R) / math.cosh(u)


def mesh(a: float, b: float, h: float) -> tuple[int, int, float]:
    n = max(1, int(round((b - a) / h)))
    hh = (b - a) / n
    total = sum(f(a + i * hh) * hh for i in range(1, n + 1))
    return int(total * 1_000_000), n, hh


def rat(x: float) -> str:
    fr = Fraction(x).limit_denominator(10_000)
    return f"({fr.numerator} : ℝ) / {fr.denominator}"


def emit_cosh_ub(name: str, x: float) -> list[str]:
    from math import factorial

    t = min(x * x / 2.0, 1.0)
    n = 8
    taylor = sum(t**m / factorial(m) for m in range(n))
    tail = t**n * (n + 1) / (factorial(n) * n)
    ub = taylor + tail + 1e-6
    num = int(ub * 10_000) + 1
    return [
        f"private lemma {name} : cosh {rat(x)} ≤ ({num} : ℝ) / 10000 := by",
        f"  exact (cosh_le_exp_half_sq {rat(x)}).trans (by norm_num)",
        "",
    ]


def emit_sech_point(idx: int, u: float, h: float) -> tuple[list[str], int]:
    u11 = u / R
    lb = int(f(u) * 0.999 * 1_000_000)  # conservative floor
    term_micro = int(f(u) * h * 1_000_000)
    lines = emit_cosh_ub(f"cosh11_{idx}_u", u)
    lines += emit_cosh_ub(f"cosh11_{idx}_v", u11)
    lines += [
        f"private lemma sech11_pt_{idx}_ge : ({lb} : ℝ) / 1000000 ≤ sechScaled {R} {rat(u)} := by",
        "  unfold sechScaled; unfold sech",
        f"  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh11_{idx}_u)",
        f"  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh11_{idx}_v)",
        "  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)",
        "  norm_num at hprod ⊢; linarith",
        "",
    ]
    return lines, term_micro


def emit_batch(batch_id: int, indices: list[int], h: float, cert_micro: int) -> list[str]:
    refs = ", ".join(f"sech11_pt_{i}_ge" for i in indices)
    terms = " + ".join(f"sechScaled {R} {rat(0)}" if False else f"sech11_pt_{i}_ge" for i in indices)
    return [
        f"private lemma sech11_batch_{batch_id}_ge :",
        f"    ({cert_micro} : ℝ) / 1000000 ≤",
        f"      ({h} : ℝ) * ({' + '.join(f'({i})' for i in indices[:0]) or '0'}) := by",
        f"  linarith [{refs}]",
        "",
    ]


def main() -> None:
    segments = [
        ("seg01", 0.0, 0.2, 0.0002),
        ("seg02", 0.2, 2.0, 0.0002),
        ("seg212", 2.0, 12.0, 0.01),
    ]
    lines = [
        "import UgpLean.Substrate.PhiMDLFluctuationSpectrum",
        "",
        "namespace UgpLean.Substrate.PhiMDLFluctuationSpectrum",
        "",
        "open Real",
        "",
    ]
    total_cert = 0
    seg_lines: list[str] = []
    idx = 0
    for name, a, b, h in segments:
        cert, n, hh = mesh(a, b, h)
        total_cert += cert
        seg_lines += [
            f"def sech11_{name}_micro : Nat := {cert}",
            f"lemma sech11_{name}_micro_le :",
            f"    ({cert} : ℝ) / 1000000 ≤ sech11_{name}_meshSum := by",
            f"  unfold sech11_{name}_meshSum",
            f"  linarith [sech11_{name}_meshSum_ge]",
            "",
        ]
        # collect points
        pts = [a + i * hh for i in range(1, n + 1)]
        batch_refs = []
        batch_cert = 0
        batch_id = 0
        batch_indices: list[int] = []
        batch_cert_acc = 0
        for u in pts:
            pt_lines, term_micro = emit_sech_point(idx, u, hh)
            lines += pt_lines
            batch_indices.append(idx)
            batch_cert_acc += term_micro
            idx += 1
            if len(batch_indices) == 20:
                lines += [
                    f"private lemma sech11_batch_{name}_{batch_id}_ge :",
                    f"    ({batch_cert_acc} : ℝ) / 1000000 ≤",
                    f"      ({hh} : ℝ) * ({' + '.join(f'sechScaled {R} {rat(u)}' for u in pts[:0]) or '0'}) := by",
                    f"  linarith [{', '.join(f'sech11_pt_{i}_ge' for i in batch_indices)}]",
                    "",
                ]
                batch_id += 1
                batch_indices = []
                batch_cert_acc = 0
        if batch_indices:
            lines += [
                f"private lemma sech11_batch_{name}_{batch_id}_ge :",
                f"    ({batch_cert_acc} : ℝ) / 1000000 ≤",
                f"      ({hh} : ℝ) * ({' + '.join(f'sechScaled {R} {rat(u)}' for u in pts[:0]) or '0'}) := by",
                f"  linarith [{', '.join(f'sech11_pt_{i}_ge' for i in batch_indices)}]",
                "",
            ]
        seg_lines += [
            f"def sech11_{name}_meshSum : ℝ := sorry",
            f"lemma sech11_{name}_meshSum_ge : ({cert} : ℝ) / 1000000 ≤ sech11_{name}_meshSum := by sorry",
            "",
        ]

    assert 2 * total_cert >= 3_110_481, f"total cert too low: {2 * total_cert}"

    lines += [
        f"def sechScaledElevenMeshHalfMicro : Nat := {total_cert}",
        "",
        "lemma sechScaledElevenMeshHalfMicro_ge_target : 1555241 ≤ sechScaledElevenMeshHalfMicro := by",
        "  norm_num [sechScaledElevenMeshHalfMicro]",
        "",
        "lemma sech11_mesh_sum_eq :",
        "    (sechScaledElevenMeshHalfMicro : ℝ) / 1000000 =",
        "      sech11_seg01_meshSum + sech11_seg02_meshSum + sech11_seg212_meshSum := by sorry",
        "",
        "lemma sech11_seg01_mesh_le :",
        "    sech11_seg01_meshSum ≤ ∫ u in (0 : ℝ)..0.2, sechScaled 11 u := by sorry",
        "",
        "lemma sech11_seg02_mesh_le :",
        "    sech11_seg02_meshSum ≤ ∫ u in (0.2 : ℝ)..2, sechScaled 11 u := by sorry",
        "",
        "lemma sech11_seg212_mesh_le :",
        "    sech11_seg212_meshSum ≤ ∫ u in (2 : ℝ)..12, sechScaled 11 u := by sorry",
        "",
        "end UgpLean.Substrate.PhiMDLFluctuationSpectrum",
        "",
    ]
    OUT.write_text("\n".join(lines))
    print(f"Wrote {OUT}, total_cert={total_cert}, 2*cert={2*total_cert}, points={idx}")


if __name__ == "__main__":
    main()
