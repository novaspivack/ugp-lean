#!/usr/bin/env python3
"""Helpers for generating exp/cosh Taylor proof terms in Lean."""
from __future__ import annotations

import math
from math import factorial
from fractions import Fraction


def exp_taylor_bound(t: float, n: int) -> tuple[int, int]:
    """Return numerator, denominator (10^6 scale) upper bound on exp(t)."""
    tail = t**n * (n + 1) / (factorial(n) * n)
    ub = sum(t**m / factorial(m) for m in range(n)) + tail
    return int(ub * 1_000_000) + 1, 1_000_000


def pick_taylor_n(t: float, max_n: int = 30) -> tuple[int, int, int]:
    """Find minimal n such that Taylor bound certifies exp(t)."""
    for n in range(3, max_n + 1):
        num, den = exp_taylor_bound(t, n)
        if num / den >= math.exp(t):
            return n, num, den
    raise ValueError(f"no Taylor bound for t={t}")


def rat(x: float) -> str:
    fr = Fraction(x).limit_denominator(1_000_000)
    return f"({fr.numerator} : ℝ) / {fr.denominator}"


def emit_exp_le_taylor(name: str, t_expr: str, t_val: float) -> list[str]:
    n, num, den = pick_taylor_n(t_val)
    lines = [
        f"private lemma {name} : exp ({t_expr}) ≤ ({num} : ℝ) / {den} := by",
        f"  refine exp_le_taylor (by norm_num) (by norm_num) (n := {n}) (by norm_num) ?_",
        "  simp [Finset.sum_range_succ, Nat.factorial]",
        "  norm_num",
        "",
    ]
    return lines


def emit_cosh_le_half_sq(name: str, u_expr: str, u_val: float, exp_name: str) -> list[str]:
    t_val = u_val * u_val / 2
    lines = emit_exp_le_taylor(exp_name, f"({u_expr})^2 / 2", t_val)
    lines += [
        f"private lemma {name} : cosh ({u_expr}) ≤ ({exp_name}_num : ℝ) := by",
        f"  exact (cosh_le_exp_half_sq ({u_expr})).trans {exp_name}",
        "",
    ]
    return lines


def cosh_ub_strategy(u: float) -> tuple[str, float, str]:
    """Return (proof_kind, t_or_u, description). kind in {'half_sq', 'ceil'}."""
    if u <= 1.0:
        return "half_sq", u, f"cosh_{u}_halfsq"
    return "ceil", math.ceil(u), f"cosh_{u}_ceil"


if __name__ == "__main__":
    n, num, den = pick_taylor_n(0.041322314)
    print(f"n={n}, bound={num/den}, exp={math.exp(0.041322314)}")
