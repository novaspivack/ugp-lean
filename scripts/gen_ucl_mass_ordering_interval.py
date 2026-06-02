#!/usr/bin/env python3
# Run from: ugp-lean-exp/scripts/ or adjust paths accordingly
"""Generate UCLMassOrderingInterval.lean log bound lemmas."""

import signal
import sys
from pathlib import Path

TIMEOUT_SECONDS = 600


def _timeout_handler(signum, frame):
    print(f"\nTIMEOUT: wall-clock limit {TIMEOUT_SECONDS}s reached.")
    sys.exit(1)

log2_lo_num = 6931471803
log2_hi_num = 6931471808
den = 10**10


def log_bounds_lean(n: int) -> dict:
    k = n.bit_length() - 1
    while (1 << k) > n:
        k -= 1
    base = 1 << k
    x_num = n - base
    x_den = base
    num_lo = k * log2_lo_num * (2 * x_den + x_num) + 2 * x_num * den
    den_lo = den * (2 * x_den + x_num)
    num_hi = k * log2_hi_num * x_den + x_num * den
    den_hi = den * x_den
    return dict(
        n=n,
        k=k,
        base=base,
        x_num=x_num,
        x_den=x_den,
        nlo=num_lo,
        dlo=den_lo,
        nhi=num_hi,
        dhi=den_hi,
    )


def emit_header() -> str:
    return """import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import UgpLean.ElegantKernel
import UgpLean.ElegantKernel.Unconditional.KConstFullClosure
import UgpLean.ElegantKernel.Unconditional.KLFullClosure
import UgpLean.ElegantKernel.Unconditional.KGenFullClosure

namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval

open Real
open UgpLean.ElegantKernel.Unconditional.KConstFullClosure
open UgpLean.ElegantKernel.Unconditional.KLFullClosure
open UgpLean.ElegantKernel.Unconditional.KGenFullClosure

/-! Interval bounds for log ratios used in UCL mass ordering. -/

private lemma log_two_lo : (6931471803 : ℝ) / 10^10 < Real.log 2 := by
  have h : (6931471803 : ℝ) / 10^10 = (0.6931471803 : ℝ) := by norm_num
  rw [h]
  exact Real.log_two_gt_d9
private lemma log_two_hi : Real.log 2 < (6931471808 : ℝ) / 10^10 := by
  have h : (6931471808 : ℝ) / 10^10 = (0.6931471808 : ℝ) := by norm_num
  rw [h]
  exact Real.log_two_lt_d9
"""


def emit_log_bounds(d: dict) -> str:
    n, k, base, xn, xd = d["n"], d["k"], d["base"], d["x_num"], d["x_den"]
    nlo, dlo, nhi, dhi = d["nlo"], d["dlo"], d["nhi"], d["dhi"]
    return f"""
private lemma log_{n}_decomp : Real.log {n} = {k} * Real.log 2 + Real.log ({n} / {base} : ℝ) := by
  have hpow : ({base} : ℝ) * ({n} / {base} : ℝ) = ({n} : ℝ) := by norm_num
  rw [← hpow, Real.log_mul (by norm_num) (by norm_num), show ({base} : ℝ) = (2 : ℝ) ^ {k} by norm_num, Real.log_pow]
  ring_nf

private lemma log_{n}_tail_eq : Real.log ({n} / {base} : ℝ) = Real.log (1 + ({xn} : ℝ) / {xd}) := by
  field_simp; ring_nf

private lemma log_{n}_tail_lo : ({2 * xn} : ℝ) / ({2 * xd + xn}) < Real.log (1 + ({xn} : ℝ) / {xd}) := by
  have hx : 0 < ({xn} : ℝ) / {xd} := by norm_num
  have hform : 2 * (({xn} : ℝ) / {xd}) / (({xn} : ℝ) / {xd} + 2) = ({2 * xn} : ℝ) / ({2 * xd + xn}) := by field_simp; ring
  rw [← hform]
  exact Real.lt_log_one_add_of_pos hx

private lemma log_{n}_tail_hi : Real.log (1 + ({xn} : ℝ) / {xd}) < ({xn} : ℝ) / {xd} := by
  have hx : 0 < ({xn} : ℝ) / {xd} := by norm_num
  have h1 : (1 : ℝ) + ({xn} : ℝ) / {xd} ≠ 1 := by norm_num
  have := Real.log_lt_sub_one_of_pos (by norm_num : 0 < 1 + ({xn} : ℝ) / {xd}) h1
  linarith

theorem log_{n}_lo : ({nlo} : ℝ) / {dlo} < Real.log {n} := by
  rw [log_{n}_decomp, log_{n}_tail_eq]
  have hklo : ({k} : ℝ) * ((6931471803 : ℝ) / 10^10) ≤ {k} * Real.log 2 := by
    nlinarith [log_two_lo]
  have htail := log_{n}_tail_lo
  linarith

theorem log_{n}_hi : Real.log {n} < ({nhi} : ℝ) / {dhi} := by
  rw [log_{n}_decomp, log_{n}_tail_eq]
  have hkhi : {k} * Real.log 2 ≤ ({k} : ℝ) * ((6931471808 : ℝ) / 10^10) := by
    nlinarith [log_two_hi]
  have htail := log_{n}_tail_hi
  linarith
"""


from typing import Optional


def emit_ratio_bounds(name: str, b: int, c: int, bd: dict, cd: Optional[dict]) -> str:
    if c == 1:
        return f"""
theorem L_{name}_lo : ({bd['nlo']} : ℝ) / {bd['dlo']} < Real.log ({b} : ℝ) - Real.log 1 := by
  simp [Real.log_one]
  exact log_{b}_lo

theorem L_{name}_hi : Real.log ({b} : ℝ) - Real.log 1 < ({bd['nhi']} : ℝ) / {bd['dhi']} := by
  simp [Real.log_one]
  exact log_{b}_hi
"""
    return f"""
theorem L_{name}_lo : ({bd['nlo']} : ℝ) / {bd['dlo']} - ({cd['nhi']} : ℝ) / {cd['dhi']} < Real.log ({b} : ℝ) - Real.log ({c} : ℝ) := by
  linarith [log_{b}_lo, log_{c}_hi]

theorem L_{name}_hi : Real.log ({b} : ℝ) - Real.log ({c} : ℝ) < ({bd['nhi']} : ℝ) / {bd['dhi']} - ({cd['nlo']} : ℝ) / {cd['dlo']} := by
  linarith [log_{b}_hi, log_{c}_lo]
"""


def main() -> None:
    signal.signal(signal.SIGALRM, _timeout_handler)
    signal.alarm(TIMEOUT_SECONDS)
    nums = [73, 823, 42, 1023, 275, 65535, 9, 337920, 5, 186, 8191]
    bounds = {n: log_bounds_lean(n) for n in nums}
    pairs = [
        ("lep1", 73, 823),
        ("lep2", 42, 1023),
        ("lep3", 275, 65535),
        ("up1", 9, 275),
        ("up2", 275, 65535),
        ("up3", 337920, 1),
        ("dn1", 5, 42),
        ("dn2", 186, 1023),
        ("dn3", 8191, 65535),
    ]
    parts = [emit_header()]
    for n in nums:
        parts.append(emit_log_bounds(bounds[n]))
    for name, b, c in pairs:
        parts.append(emit_ratio_bounds(name, b, c, bounds[b], bounds.get(c)))
    parts.append("\nend UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval\n")
    path = Path(__file__).resolve().parents[1] / "UgpLean/ElegantKernel/Unconditional/UCLMassOrderingInterval.lean"
    with open(path, "w", encoding="utf-8") as f:
        f.write("".join(parts))
    print(f"Wrote {path} ({len(''.join(parts).splitlines())} lines)")
    signal.alarm(0)


if __name__ == "__main__":
    main()
