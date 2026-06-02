#!/usr/bin/env python3
# Run from: ugp-lean-exp/scripts/ or adjust paths accordingly
"""Generate UCLMassOrderingDelta.lean — k_const cancels in generation differences."""

import math
import signal
import sys
from fractions import Fraction
from pathlib import Path

TIMEOUT_SECONDS = 600


def _timeout_handler(signum, frame):
    print(f"\nTIMEOUT: wall-clock limit {TIMEOUT_SECONDS}s reached.")
    sys.exit(1)


signal.signal(signal.SIGALRM, _timeout_handler)
signal.alarm(TIMEOUT_SECONDS)

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


def fmt_z(n: int) -> str:
    return f"({n} : ℤ)"


def fmt_mu(mu: tuple[int, int, int]) -> str:
    return " ".join(fmt_z(x) for x in mu)


def mobius_offset(mu: tuple[int, int, int], km: Fraction) -> Fraction:
    return k_a * mu[0] + k_b * mu[1] + k_c * mu[2] + km * mu[0] * mu[1] * mu[2]


def delta_max(mu1, mu2, L1lo, L1hi, L2lo, L2hi, g1, g2) -> float:
    maxd = -999.0
    for kl in (k_L_lo, k_L_hi):
        for kg in (k_gen_lo, k_gen_hi):
            for kg2 in (k_gen2_lo, k_gen2_hi):
                for km in (k_M_lo, k_M_hi):
                    mob1 = mobius_offset(mu1, km)
                    mob2 = mobius_offset(mu2, km)
                    for L1 in (L1lo, L1hi):
                        for L2 in (L2lo, L2hi):
                            d = (
                                kl * (L1 - L2)
                                + k_L2 * (L1**2 - L2**2)
                                + kg * (g1 - g2)
                                + kg2 * (g1**2 - g2**2)
                                + mob1 - mob2
                            )
                            maxd = max(maxd, float(d))
    return maxd


sectors = {
    "lepton": [
        ((1, -1, -1), 73, 823, 1, (0, -1, -1), 42, 1023, 2, "12"),
        ((0, -1, -1), 42, 1023, 2, (-1, 0, 1), 275, 65535, 3, "23"),
    ],
    "up": [
        ((-1, 0, 0), 9, 275, 1, (-1, 0, 1), 275, 65535, 2, "12"),
        ((-1, 0, 1), 275, 65535, 2, (0, 0, 1), 337920, 1, 3, "23"),
    ],
    "down": [
        ((0, -1, -1), 5, 42, 1, (0, -1, -1), 186, 1023, 2, "12"),
        ((0, -1, -1), 186, 1023, 2, (-1, -1, 1), 8191, 65535, 3, "23"),
    ],
}

ratio_names = {
    (73, 823): "lep1",
    (42, 1023): "lep2",
    (275, 65535): "lep3",
    (9, 275): "up1",
    (337920, 1): "up3",
    (5, 42): "dn1",
    (186, 1023): "dn2",
    (8191, 65535): "dn3",
}

lines = [
    "import Mathlib.Analysis.SpecialFunctions.Log.Basic",
    "import UgpLean.ElegantKernel.Unconditional.UCLCalibration",
    "import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval",
    "import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCoeffBounds",
    "import UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds",
    "import UgpLean.ElegantKernel.Unconditional.KLFullClosure",
    "",
    "namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingDelta",
    "",
    "open Real",
    "open UgpLean.ElegantKernel",
    "open UgpLean.ElegantKernel.Unconditional.UCLCalibration",
    "open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval",
    "open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingCoeffBounds",
    "open UgpLean.ElegantKernel.Unconditional.UCLMassOrderingBounds",
    "open UgpLean.ElegantKernel.Unconditional.KLFullClosure",
    "",
]

for sname, triples in sectors.items():
    for mu1, b1, c1, g1, mu2, b2, c2, g2, tag in triples:
        L1lo, L1hi = L_bounds(b1, c1)
        L2lo, L2hi = L_bounds(b2, c2)
        maxd = delta_max(mu1, mu2, L1lo, L1hi, L2lo, L2hi, g1, g2)
        if maxd >= float(logFourLo):
            raise SystemExit(f"FAIL {sname} {tag}: maxd={maxd}, logFourLo={float(logFourLo)}")
        rn1 = ratio_names[(b1, c1)]
        rn2 = ratio_names[(b2, c2)]
        L1 = f"Real.log ({b1} : ℝ) - Real.log ({c1} : ℝ)"
        L2 = f"Real.log ({b2} : ℝ) - Real.log ({c2} : ℝ)"
        if c1 == 1:
            L1 = f"Real.log ({b1} : ℝ) - Real.log 1"
        if c2 == 1:
            L2 = f"Real.log ({b2} : ℝ) - Real.log 1"
        lines += [
            f"/-- Log-space ordering `{g1} < {g2}` for the {sname} sector. -/",
            f"theorem {sname}_log_delta{tag} :",
            f"    uclLogCalibration {fmt_mu(mu1)} ({L1}) {g1} <",
            f"      Real.log 4 + uclLogCalibration {fmt_mu(mu2)} ({L2}) {g2} := by",
            f"  have hL1lo := L_{rn1}_lo",
            f"  have hL1hi := L_{rn1}_hi",
            f"  have hL2lo := L_{rn2}_lo",
            f"  have hL2hi := L_{rn2}_hi",
            "  have hkLlo := k_L_derived_lo",
            "  have hkLhi := k_L_derived_hi",
            "  have hkgenlo := k_gen_derived_lo",
            "  have hkgenhi := k_gen_derived_hi",
            "  have hkgen2lo := k_gen2_lo",
            "  have hkgen2hi := k_gen2_hi",
            "  have hkMlo := k_M_lo",
            "  have hkMhi := k_M_hi",
            "  have hlog4 := log_four_lo_lt_log_four",
            "  unfold uclLogCalibration",
            "  simp only [k_L2_eq, k_a_eq, k_b_eq, k_c_eq, k_L_derived_closed_form]",
            "  ring_nf",
            "  nlinarith [hL1lo, hL1hi, hL2lo, hL2hi, hkLlo, hkLhi, hkgenlo, hkgenhi,",
            "    hkgen2lo, hkgen2hi, hkMlo, hkMhi, hlog4]",
            "",
        ]

lines += ["end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingDelta", ""]

out_path = Path(__file__).resolve().parents[1] / "UgpLean/ElegantKernel/Unconditional/UCLMassOrderingDelta.lean"
with open(out_path, "w", encoding="utf-8") as f:
    f.write("\n".join(lines))
print(f"Wrote {out_path}")
signal.alarm(0)
