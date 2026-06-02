#!/usr/bin/env python3
"""Generate UCL mass ordering cert, S-bound, and bridge Lean modules."""

from __future__ import annotations

import math
from fractions import Fraction
from pathlib import Path

log2_lo = Fraction(6931471803, 10**10)
log2_hi = Fraction(6931471808, 10**10)
logFourLo = 2 * log2_lo
k_L2 = Fraction(7, 512)

k_L_lo = Fraction(197371699, 10**10)
k_L_hi = Fraction(197372211, 10**10)
k_gen_lo = Fraction(15388417674, 10**10)
k_gen_hi = Fraction(15388417694, 10**10)
k_gen2_lo = Fraction(-8090169949, 10**10)
k_gen2_hi = Fraction(-8090169938, 10**10)
k_M_lo = Fraction(-805599027, 10**9)
k_M_hi = Fraction(-805599025, 10**9)
k_a, k_b, k_c = Fraction(1, 8), Fraction(-3, 2), Fraction(4, 3)
pi_lo = Fraction(314159265358979323846, 10**20)
pi_hi = Fraction(314159265358979323847, 10**20)
ln_phi_lo = Fraction(481211, 10**6)
ln_phi_hi = Fraction(481212, 10**6)


def k_const_corner(pi: Fraction, ln: Fraction) -> Fraction:
    return Fraction(-1, 1) / (Fraction(2, 1) * pi) + Fraction(63, 2048) * ln * ln

SCALE = 10**8


def log_bounds(n: int) -> tuple[Fraction, Fraction]:
    k = n.bit_length() - 1
    while (1 << k) > n:
        k -= 1
    base = 1 << k
    x = Fraction(n - base, base)
    return k * log2_lo + 2 * x / (2 + x), k * log2_hi + x


def L_bounds(b: int, c: int) -> tuple[Fraction, Fraction]:
    blo, bhi = log_bounds(b)
    clo, chi = log_bounds(c)
    return blo - chi, bhi - clo


def S_corners(mu: tuple[int, int, int], b: int, c: int, g: int) -> list[Fraction]:
    """Corner values of the k_const-free part of uclLogCalibration."""
    Llo, Lhi = L_bounds(b, c)
    mu_a, mu_b, mu_c = mu
    mob = k_a * mu_a + k_b * mu_b + k_c * mu_c
    prod = mu_a * mu_b * mu_c
    out: list[Fraction] = []
    for kl in (k_L_lo, k_L_hi):
        for L in (Llo, Lhi):
            for kg in (k_gen_lo, k_gen_hi):
                for kg2 in (k_gen2_lo, k_gen2_hi):
                    for km in (k_M_lo, k_M_hi):
                        out.append(
                            kl * L
                            + k_L2 * L * L
                            + kg * g
                            + kg2 * g * g
                            + km * prod
                            + mob
                        )
    return out


def floor_q(x: Fraction, scale: int = SCALE) -> Fraction:
    return Fraction(math.floor(float(x) * scale), scale)


def ceil_q(x: Fraction, scale: int = SCALE) -> Fraction:
    return Fraction(math.ceil(float(x) * scale), scale)


def strict_hi(x: Fraction, scale: int = SCALE) -> Fraction:
    q = ceil_q(x, scale)
    if q <= x:
        q = q + Fraction(1, scale)
    return q


def strict_lo(x: Fraction, scale: int = SCALE) -> Fraction:
    q = floor_q(x, scale)
    if q >= x:
        q = q - Fraction(1, scale)
    return q


def fmt_z(n: int) -> str:
    return f"({n} : ℤ)"


def fmt_mu(mu: tuple[int, int, int]) -> str:
    return " ".join(fmt_z(x) for x in mu)


def fmt_L(b: int, c: int) -> str:
    if c == 1:
        return f"Real.log ({b} : ℝ) - Real.log 1"
    return f"Real.log ({b} : ℝ) - Real.log ({c} : ℝ)"


def fmt_q(q: Fraction) -> str:
    return f"({q.numerator} : ℝ) / {q.denominator}"


TRIPLES = {
    "lep1": ((1, -1, -1), 73, 823, 1, "L_lep1"),
    "lep2": ((0, -1, -1), 42, 1023, 2, "L_lep2"),
    "lep3": ((-1, 0, 1), 275, 65535, 3, "L_lep3"),
    "up1": ((-1, 0, 0), 9, 275, 1, "L_up1"),
    "up2": ((-1, 0, 1), 275, 65535, 2, "L_up2"),
    "up3": ((0, 0, 1), 337920, 1, 3, "L_up3"),
    "dn1": ((0, -1, -1), 5, 42, 1, "L_dn1"),
    "dn2": ((0, -1, -1), 186, 1023, 2, "L_dn2"),
    "dn3": ((-1, -1, 1), 8191, 65535, 3, "L_dn3"),
}

PAIRS = [
    ("lepton", "lep1", "lep2", "12"),
    ("lepton", "lep2", "lep3", "23"),
    ("up", "up1", "up2", "12"),
    ("up", "up2", "up3", "23"),
    ("down", "dn1", "dn2", "12"),
    ("down", "dn2", "dn3", "23"),
]

s_bounds: list[str] = [
    """import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import UgpLean.ElegantKernel.Unconditional.UCLCalibration
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval
import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCoeffBounds
import UgpLean.ElegantKernel.Unconditional.KLFullClosure
import UgpLean.ElegantKernel.Unconditional.KConstFullClosure

namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingSBounds

open Real
open UgpLean.ElegantKernel
open UgpLean.ElegantKernel.Unconditional.UCLCalibration
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval
open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCoeffBounds
open UgpLean.ElegantKernel.Unconditional.KLFullClosure
open UgpLean.ElegantKernel.Unconditional.KConstFullClosure

/-! S-value interval bounds. -/

""",
]
s_meta: dict[str, tuple[Fraction, Fraction]] = {}

for key, (mu, b, c, g, Lname) in TRIPLES.items():
    corners = S_corners(mu, b, c, g)
    slo, shi = min(corners), max(corners)
    slo_q, shi_q = strict_lo(slo), strict_hi(shi)
    if not (slo_q <= slo and shi <= shi_q):
        raise SystemExit(f"rounding failed for {key}")
    s_meta[key] = (slo_q + Fraction(-153, 100), shi_q + Fraction(-151, 100))
    L = fmt_L(b, c)
    mu_expr = f"({mu[0]} : ℝ) * ({mu[1]} : ℝ) * ({mu[2]} : ℝ)"
    f_expr = (
        f"k_L_derived * ({L}) + (7 / 512 : ℝ) * ({L}) ^ 2 + k_gen_derived * {g} + "
        f"k_gen2 * ({g} : ℝ) ^ 2 + k_M * {mu_expr} + "
        f"(1 / 8 : ℝ) * {fmt_z(mu[0])} + (-3 / 2 : ℝ) * {fmt_z(mu[1])} + (4 / 3 : ℝ) * {fmt_z(mu[2])}"
    )
    proof_f = [
        f"  have hLlo := {Lname}_lo",
        f"  have hLhi := {Lname}_hi",
        "  have hkLlo := k_L_derived_lo",
        "  have hkLhi := k_L_derived_hi",
        "  have hkgenlo := k_gen_derived_lo",
        "  have hkgenhi := k_gen_derived_hi",
        "  have hkgen2lo := k_gen2_lo",
        "  have hkgen2hi := k_gen2_hi",
        "  have hkMlo := k_M_lo",
        "  have hkMhi := k_M_hi",
        "  rw [k_L_derived_closed_form]",
        "  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq]",
        "  nlinarith [hLlo, hLhi, hkLlo, hkLhi, hkgenlo, hkgenhi, hkgen2lo, hkgen2hi, hkMlo, hkMhi]",
    ]
    s_bounds += [
        f"private theorem {key}_f_lo : {fmt_q(slo_q)} < {f_expr} := by",
        *proof_f,
        "",
        f"private theorem {key}_f_hi : {f_expr} < {fmt_q(shi_q)} := by",
        *proof_f,
        "",
        f"theorem {key}_S_lo : {fmt_q(slo_q + Fraction(-153, 100))} < uclLogCalibration {fmt_mu(mu)} ({L}) {g} := by",
        f"  have hf := {key}_f_lo",
        f"  have hk := k_const_lo",
        f"  unfold uclLogCalibration",
        f"  linarith [hf, hk]",
        "",
        f"theorem {key}_S_hi : uclLogCalibration {fmt_mu(mu)} ({L}) {g} < {fmt_q(shi_q + Fraction(-151, 100))} := by",
        f"  have hf := {key}_f_hi",
        f"  have hk := k_const_hi",
        f"  unfold uclLogCalibration",
        f"  linarith [hf, hk]",
        "",
    ]

s_bounds.append("end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingSBounds\n")

certs = [
    "import Mathlib.Tactic.Linarith",
    "import Mathlib.Tactic.NormNum",
    "",
    "namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts",
    "",
    "def logFourLo : ℚ := 2 * 6931471803 / 10^10",
    "",
    "theorem log_four_lo_pos : 0 < logFourLo := by",
    "  unfold logFourLo",
    "  norm_num",
    "",
]

for sector, a, b, tag in PAIRS:
    _, shi = s_meta[a]
    slo_b, _ = s_meta[b]
    lhs = strict_hi(shi)
    rhs = logFourLo + strict_lo(slo_b)
    if not (shi < logFourLo + slo_b):
        raise SystemExit(f"cert margin failed {sector} {tag}")
    if not (lhs < rhs):
        raise SystemExit(f"rounded cert failed {sector} {tag}: {lhs} < {rhs}")
    certs += [
        f"theorem {sector}_cert_S{tag[0]}_lt_log4_plus_S{tag[1]} :",
        f"    ({lhs.numerator} : ℚ) / {lhs.denominator} < ({rhs.numerator} : ℚ) / {rhs.denominator} := by",
        "  norm_num",
        "",
    ]

certs.append("end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts\n")

bridge = [
    "import UgpLean.ElegantKernel.Unconditional.UCLCalibration",
    "import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds",
    "import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts",
    "import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingSBounds",
    "",
    "namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBridge",
    "",
    "open Real",
    "open UgpLean.ElegantKernel.Unconditional.UCLCalibration",
    "open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds",
    "open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCerts",
    "open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingSBounds",
    "",
]

for sector, a, b, tag in PAIRS:
    mu_a, b_a, c_a, g_a, _ = TRIPLES[a]
    mu_b, b_b, c_b, g_b, _ = TRIPLES[b]
    _, shi = s_meta[a]
    slo_b, _ = s_meta[b]
    shi_q = strict_hi(shi)
    slo_q = strict_lo(slo_b)
    L_a = fmt_L(b_a, c_a)
    L_b = fmt_L(b_b, c_b)
    bridge += [
        f"theorem {sector}_log_delta{tag} :",
        f"    uclLogCalibration {fmt_mu(mu_a)} ({L_a}) {g_a} <",
        f"      Real.log 4 + uclLogCalibration {fmt_mu(mu_b)} ({L_b}) {g_b} := by",
        f"  have hS1hi := {a}_S_hi",
        f"  have hS2lo := {b}_S_lo",
        f"  have hcert : ({shi_q.numerator} : ℝ) / {shi_q.denominator} <",
        f"      (↑logFourLo : ℝ) + ({slo_q.numerator} : ℝ) / {slo_q.denominator} := by",
        f"    exact_mod_cast {sector}_cert_S{tag[0]}_lt_log4_plus_S{tag[1]}",
        f"  have hlog4 := log_four_lo_lt_log_four",
        f"  linarith [hS1hi, hS2lo, hcert, hlog4]",
        "",
    ]

bridge.append("end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBridge\n")

root = Path("UgpLean/ElegantKernel/Unconditional")
(root / "UCLMassOrderingSBounds.lean").write_text("\n".join(s_bounds), encoding="utf-8")
(root / "UCLMassOrderingCerts.lean").write_text("\n".join(certs), encoding="utf-8")
(root / "UCLMassOrderingBridge.lean").write_text("\n".join(bridge), encoding="utf-8")
print("Wrote UCLMassOrderingSBounds.lean, UCLMassOrderingCerts.lean, UCLMassOrderingBridge.lean")
