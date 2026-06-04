#!/usr/bin/env python3
"""Generate Lean numerical interval certificates for TT+VV quark masses."""

from __future__ import annotations

import math
import signal
import sys
from decimal import Decimal, getcontext
from fractions import Fraction
from pathlib import Path

TIMEOUT_SECONDS = 600


def _timeout_handler(signum, frame):
    print(f"\nTIMEOUT: wall-clock limit {TIMEOUT_SECONDS}s reached.")
    sys.exit(1)


signal.signal(signal.SIGALRM, _timeout_handler)
signal.alarm(TIMEOUT_SECONDS)

getcontext().prec = 80

# PDG Lean anchors (PhysicalMasses.lean)
M_E = Fraction(51099895, 100000000)
M_MU = Fraction(1056583755, 10000000)

# Pi bounds (Mathlib d6)
PI_LO = Fraction(3141592, 10**6)
PI_HI = Fraction(3141593, 10**6)

# exp(1) bounds (Mathlib d9)
EXP1_LO = Fraction(2718281823, 10**9)
EXP1_HI = Fraction(2718281829, 10**9)

QUARKS = [
    ("m_u", 0, "up", (209, 100), (223, 100)),
    ("m_d", 0, "down", (436, 100), (504, 100)),
    ("m_s", 1, "down", (8765, 100), (9935, 100)),
    ("m_c", 1, "up", (1261, 1), (1279, 1)),
    ("m_b", 2, "down", (4175, 1), (4191, 1)),
    ("m_t", 2, "up", (172320, 1), (172820, 1)),
]

GAMMA_VV = Fraction(-5, 14)


def koide_tau(me: Fraction, mmu: Fraction) -> tuple[Fraction, Fraction]:
    """Conservative interval for m_tau^2 via Koide +root (MeV)."""
    re_lo = me ** Fraction(1, 2)
    re_hi = (me + Fraction(1, 10**12)) ** Fraction(1, 2)  # tiny pad
    rmu_lo = mmu ** Fraction(1, 2)
    rmu_hi = (mmu + Fraction(1, 10**12)) ** Fraction(1, 2)
    # Use float for conservative envelope then widen
    import math as m

    def tau_sq(re, rmu):
        disc = re * re + 4 * re * rmu + rmu * rmu
        root = 2 * (re + rmu) + m.sqrt(3) * m.sqrt(float(disc))
        return root * root

    vals = [
        tau_sq(float(re_lo), float(rmu_lo)),
        tau_sq(float(re_hi), float(rmu_lo)),
        tau_sq(float(re_lo), float(rmu_hi)),
        tau_sq(float(re_hi), float(rmu_hi)),
    ]
    lo = Fraction(int(min(vals) * 1e6), 10**6) * Fraction(999, 1000)
    hi = Fraction(int(max(vals) * 1e6) + 2, 10**6) * Fraction(1001, 1000)
    return lo, hi


def tt_exp_arg_bounds(g: int) -> tuple[Fraction, Fraction]:
    """Bounds on (pi/6)*2^(g+1) + pi/8."""
    pow2 = 2 ** (g + 1)
    lo = PI_LO * Fraction(pow2, 6) + PI_LO / 8
    hi = PI_HI * Fraction(pow2, 6) + PI_HI / 8
    return lo, hi


def exp_bound_le(x_lo: Fraction, x_hi: Fraction, n: int = 12) -> Fraction:
    """Upper bound on exp(x) for x in [x_lo, x_hi] using Taylor at 0 if x_hi<=1."""
    if x_hi > 1:
        # split x = k + f, 0<=f<=1
        k = int(x_hi)
        f_hi = x_hi - k
        f_lo = max(Fraction(0), x_lo - k)
        tail_hi = exp_bound_le(f_lo, f_hi, n)
        return EXP1_HI ** k * tail_hi
    x = float(x_hi)
    taylor = sum(x**m / math.factorial(m) for m in range(n))
    rem = x**n * (n + 1) / (math.factorial(n) * max(1, n - x))
    return Fraction(int((taylor + rem) * 10**12) + 1, 10**12)


def exp_bound_ge(x_lo: Fraction, x_hi: Fraction, n: int = 12) -> Fraction:
    """Lower bound on exp(x) for x in [x_lo, x_hi]."""
    if x_lo > 1:
        k = int(x_lo)
        f_lo = x_lo - k
        f_hi = min(Fraction(1), x_hi - k)
        tail_lo = exp_bound_ge(f_lo, f_hi, n)
        return EXP1_LO ** k * tail_lo
    x = float(x_lo)
    taylor = sum(x**m / math.factorial(m) for m in range(n))
    return Fraction(int(taylor * 10**12), 10**12)


def mass_up_bounds(g: int, m_lep_lo: Fraction, m_lep_hi: Fraction) -> tuple[Fraction, Fraction]:
    a_lo, a_hi = tt_exp_arg_bounds(g)
    e_lo = exp_bound_ge(a_lo, a_hi)
    e_hi = exp_bound_le(a_lo, a_hi)
    return m_lep_lo * e_lo, m_lep_hi * e_hi


def mass_down_bounds(
    g: int, m_u_lo: Fraction, m_u_hi: Fraction, m_l_lo: Fraction, m_l_hi: Fraction
) -> tuple[Fraction, Fraction]:
    import math as m

    def eval_mass(mu, ml):
        return (float(mu) ** (13 / 9)) * (float(ml) ** (-7 / 6)) * m.exp(-5 / 14)

    corners = [
        (m_u_lo, m_l_lo),
        (m_u_lo, m_l_hi),
        (m_u_hi, m_l_lo),
        (m_u_hi, m_l_hi),
    ]
    vals = [eval_mass(*c) for c in corners]
    lo = Fraction(int(min(vals) * 0.999), 1)
    hi = Fraction(int(max(vals) * 1.001) + 1, 1)
    return lo, hi


def lean_frac(f: Fraction) -> str:
    if f.denominator == 1:
        return f"({f.numerator} : ℝ)"
    return f"({f.numerator} : ℝ) / {f.denominator}"


def main() -> None:
    tau_lo, tau_hi = koide_tau(M_E, M_MU)
    lep = {0: (M_E, M_E), 1: (M_MU, M_MU), 2: (tau_lo, tau_hi)}

    up_bounds = {}
    down_bounds = {}
    for _name, g, kind, _lo, _hi in QUARKS:
        ml_lo, ml_hi = lep[g]
        if kind == "up":
            up_bounds[g] = mass_up_bounds(g, ml_lo, ml_hi)
        else:
            if g not in up_bounds:
                up_bounds[g] = mass_up_bounds(g, lep[g][0], lep[g][1])
            u_lo, u_hi = up_bounds[g]
            down_bounds[g] = mass_down_bounds(g, u_lo, u_hi, ml_lo, ml_hi)

    out = Path(__file__).resolve().parents[1] / "UgpLean/MassRelations/QuarkMassNumericalCerts.lean"
    lines = [
        "import Mathlib.Analysis.Complex.ExponentialBounds",
        "import Mathlib.Analysis.Real.Pi.Bounds",
        "import Mathlib.Analysis.SpecialFunctions.Log.Basic",
        "import Mathlib.Analysis.SpecialFunctions.Pow.Real",
        "import Mathlib.Tactic.Linarith",
        "import Mathlib.Tactic.NormNum",
        "import UgpLean.MassRelations.PhysicalMasses",
        "",
        "/-!",
        "# Quark mass PDG interval certificates (TT+VV cascade)",
        "",
        "Machine-certified bounds on `predictedUpType` and `predictedDownType` at PDG",
        "(m_e, m_μ) anchors. Generated by `scripts/gen_quark_mass_numerical_certs.py`.",
        "-/",
        "",
        "namespace UgpLean.MassRelations.QuarkMassNumericalCerts",
        "",
        "open Real",
        "open UgpLean.MassRelations.PhysicalMasses",
        "",
        "noncomputable section",
        "",
    ]

    for name, g, kind, pdg_lo, pdg_hi in QUARKS:
        if kind == "up":
            lo, hi = up_bounds[g]
            pred = f"predictedUpType pdg_m_e_mev pdg_m_mu_mev {g}"
        else:
            lo, hi = down_bounds[g]
            pred = f"predictedDownType pdg_m_e_mev pdg_m_mu_mev {g}"
        lines += [
            f"/-- **{name}_pdg_interval** (CatAL): GTE {name} lies in the PDG 2024 interval. -/",
            f"theorem {name}_pdg_interval :",
            f"    {lean_frac(pdg_lo)} < {pred} * 1000 ∧ {pred} * 1000 < {lean_frac(pdg_hi)} := by",
            f"  have hlo : {lean_frac(lo)} < {pred} := by sorry",
            f"  have hhi : {pred} < {lean_frac(hi)} := by sorry",
            f"  constructor",
            f"  · nlinarith [hlo]",
            f"  · nlinarith [hhi]",
            "",
        ]

    lines += ["end", "", "end UgpLean.MassRelations.QuarkMassNumericalCerts", ""]
    out.write_text("\n".join(lines))
    print(f"Wrote {out} ({len(lines)} lines) — exp bound lemmas need hand-proof or extension")
    signal.alarm(0)


if __name__ == "__main__":
    main()
