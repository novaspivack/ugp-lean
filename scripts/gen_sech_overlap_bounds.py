#!/usr/bin/env python3
"""Generate per-cell sech product lower-bound lemmas for SechOverlapIntegralBounds.lean."""
from __future__ import annotations

import math
from pathlib import Path

OUT = Path(__file__).resolve().parents[1] / "UgpLean/Substrate/SechOverlapIntegralBounds_gen.lean"


def cert_val(exact: float, margin: float = 0.999) -> tuple[int, int]:
    """Conservative floor to micro-units."""
    v = int(exact * 1_000_000 * margin)
    return v, 1_000_000


def emit_cells(r: int, k_lo: int, k_hi: int) -> list[str]:
    lines: list[str] = []
    for k in range(k_lo, k_hi + 1):
        exact = 1.0 / math.cosh(k / r) / math.cosh(k)
        num, den = cert_val(exact)
        name = f"sech_prod_r{r}_at_{k}".replace("-", "neg")
        lines.append(
            f"private lemma {name}_ge :\n"
            f"    ({num} : ℝ) / {den} ≤ sech ({k} / ({r} : ℝ)) * sech ({k} : ℝ) := by\n"
            f"  unfold sech\n"
            f"  have hc1 := cosh_ub_{r}_{abs(k)}_le\n"
            f"  have hc2 := cosh_ub_{abs(k)}_le\n"
            f"  have h1 := sech_ge_of_cosh_le (cosh_pos _).le hc1\n"
            f"  have h2 := sech_ge_of_cosh_le (cosh_pos _).le hc2\n"
            f"  have hprod := mul_le_mul h1 h2 (by norm_num) (by norm_num)\n"
            f"  have hcheck : ({num} : ℝ) / {den} ≤ (1000000 : ℝ) / _ * (1000000 : ℝ) / _ := by\n"
            f"    norm_num [{name}_cosh_nums]\n"
            f"  linarith [hprod, hcheck]\n"
        )
    return lines


def main() -> None:
    # Unique |x| values for cosh bounds (manual rational UBs in Lean — listed for reference)
    print("Generator placeholder — bounds are hand-written in SechOverlapIntegralBounds.lean")


if __name__ == "__main__":
    main()
