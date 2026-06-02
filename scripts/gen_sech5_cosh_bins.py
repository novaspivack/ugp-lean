#!/usr/bin/env python3
"""Generate per-bin cosh upper-bound lemmas used by the r=5 mesh."""
from __future__ import annotations

import math
import sys
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from sech_taylor_proofs import exp_taylor_bound, pick_taylor_n, rat  # noqa: E402

OUT = ROOT / "UgpLean/Substrate/SechOverlapIntegralBounds_r5bins.lean"
BIN_STEP = 0.0005
COSH_SCALE = 100_000_000
R = 5
N = 550
SQRT2 = math.sqrt(2.0)

EXP_K_LEMMA = {
    1: "exp_one_le",
    2: "exp_two_le",
    3: "exp_three_le",
    4: "exp_four_le",
    5: "exp_five_le",
}

COSH_K_LEMMA = {
    2: "cosh_two_le",
    3: "cosh_three_le",
    4: "cosh_four_le",
    5: "cosh_five_le",
}

EXP_NEG_K_LEMMA = {
    1: "exp_neg_one_le",
    2: "exp_neg_two_le",
    3: "exp_neg_three_le",
    4: "exp_neg_four_le",
    5: "exp_neg_five_le",
}

NEG_UB = {1: 368, 2: 136, 3: 50, 4: 19, 5: 8}


def bin_val(u: float) -> float:
    return math.ceil(u / BIN_STEP - 1e-12) * BIN_STEP


def bin_key(u: float) -> str:
    b = bin_val(u)
    num = int(round(b * 10000))
    return f"b{num}"


def emit_small_cosh_ub(name: str, x: float, num: int, den: int) -> list[str]:
    """`x²/2 ≤ 1`: Taylor bound on `exp(x²/2)`."""
    t = x * x / 2
    n, _, _ = pick_taylor_n(t)
    n = max(n, 8)
    tnum, tden = exp_taylor_bound(t, n)
    tnum_s = int(tnum * COSH_SCALE / tden) + 1
    num = max(num, tnum_s)
    x_expr = rat(x)
    exp_name = f"exp_{name}"
    return [
        f"lemma cosh_{name}_ub : cosh ({x_expr}) ≤ ({num} : ℝ) / {den} := by",
        f"  have {exp_name} : exp (({x_expr})^2 / 2) ≤ ({tnum_s} : ℝ) / {den} := by",
        f"    have ht : ({x_expr})^2 / 2 ≤ 1 := by norm_num",
        f"    have hupper := Real.exp_bound' (by norm_num) ht (n := {n}) (by norm_num)",
        f"    have htaylor :",
        f"        (∑ m ∈ Finset.range {n}, (({x_expr})^2 / 2) ^ m / (Nat.factorial m)) +",
        f"          (({x_expr})^2 / 2) ^ {n} * ({n} + 1) / (Nat.factorial {n} * {n}) ≤",
        f"          ({tnum_s} : ℝ) / {den} := by",
        "      simp [Finset.sum_range_succ, Nat.factorial]",
        "      norm_num",
        f"    linarith [hupper, htaylor]",
        f"  exact (cosh_le_exp_half_sq ({x_expr})).trans (le_trans {exp_name} (by norm_num))",
        "",
    ]


def emit_integer_cosh_ub(name: str, b: float, k: int, num: int, den: int) -> list[str]:
    """Exact integer bin: rewrite to `cosh k` and apply hand-certified bound."""
    b_expr = rat(b)
    k_lemma = COSH_K_LEMMA[k]
    return [
        f"lemma cosh_{name}_ub : cosh ({b_expr}) ≤ ({num} : ℝ) / {den} := by",
        f"  rw [show {b_expr} = ({k} : ℝ) by norm_num]",
        f"  exact ({k_lemma}).trans (by norm_num)",
        "",
    ]


EXP_K_NUM = {1: 2719, 2: 7390, 3: 20086, 4: 54599, 5: 148414}


def emit_product_cosh_ub(name: str, b: float, num: int, den: int, *, tight: bool = False) -> list[str]:
    """`cosh b = (exp b + exp (-b))/2` with `exp b = exp k * exp frac`."""
    k = int(math.floor(b + 1e-12))
    frac = b - k
    b_expr = rat(b)
    frac_expr = rat(frac)
    exp_k = EXP_K_LEMMA[k]
    exp_neg_k = EXP_NEG_K_LEMMA[k]
    exp_frac = f"exp_frac_{name}"
    n, _, _ = pick_taylor_n(frac)
    n = max(n, 8)
    tnum, tden = exp_taylor_bound(frac, n)
    frac_ub = int(tnum * COSH_SCALE / tden) + 1
    if not tight:
        safe_num = (EXP_K_NUM[k] * frac_ub + NEG_UB[k] * den) // 2000 + 1
        num = max(num, safe_num)
    return [
        f"lemma cosh_{name}_ub : cosh ({b_expr}) ≤ ({num} : ℝ) / {den} := by",
        f"  have {exp_frac} : exp ({frac_expr}) ≤ ({frac_ub} : ℝ) / {den} := by",
        f"    have ht : ({frac_expr}) ≤ 1 := by norm_num",
        f"    have hupper := Real.exp_bound' (by norm_num) ht (n := {n}) (by norm_num)",
        f"    have htaylor :",
        f"        (∑ m ∈ Finset.range {n}, ({frac_expr}) ^ m / (Nat.factorial m)) +",
        f"          ({frac_expr}) ^ {n} * ({n} + 1) / (Nat.factorial {n} * {n}) ≤",
        f"          ({frac_ub} : ℝ) / {den} := by",
        "      simp [Finset.sum_range_succ, Nat.factorial]",
        "      norm_num",
        f"    linarith [hupper, htaylor]",
        f"  have hexp : exp ({b_expr}) = exp {k} * exp ({frac_expr}) := by",
        f"    rw [← exp_add, show ({k} : ℝ) + {frac_expr} = {b_expr} by norm_num]",
        f"  have hneg : exp (-({b_expr})) ≤ ({NEG_UB[k]} : ℝ) / 1000 := by",
        f"    exact (exp_le_exp_of_le (by norm_num : -({b_expr}) ≤ -({k} : ℝ))).trans {exp_neg_k}",
        f"  rw [cosh_eq]",
        f"  have hmul := mul_le_mul {exp_k} {exp_frac} (exp_pos ({frac_expr})).le (by norm_num)",
        f"  nlinarith [hmul, hneg, hexp, exp_pos ({b_expr}), exp_pos (-({b_expr}))]",
        "",
    ]


def certified_cosh_ub_num(b: float, den: int = COSH_SCALE) -> int:
    """Mesh/bin upper numerator for `cosh b`, including conservative inflation."""
    num = int(math.cosh(b) * den) + 1
    certified_num = {2: 3763, 3: 10068, 4: 27309, 5: 74211}
    k_round = int(round(b))
    if abs(b - k_round) <= 1e-9 and k_round in certified_num:
        num = max(num, certified_num[k_round] * (den // 1000) + 1)
    if b >= 5.0 - 1e-12:
        num = max(num, certified_num[5] * (den // 1000) + 1)
    if b <= SQRT2 - 1e-12:
        t = b * b / 2
        n = max(pick_taylor_n(t)[0], 8)
        tnum, tden = exp_taylor_bound(t, n)
        num = max(num, int(tnum * den / tden) + 1)
    elif not (abs(b - k_round) <= 1e-9 and 2 <= k_round <= 5):
        k_floor = int(math.floor(b + 1e-12))
        if k_floor >= 1 and b < 5.0:
            frac = b - k_floor
            n = max(pick_taylor_n(frac)[0], 8)
            tnum, tden = exp_taylor_bound(frac, n)
            frac_ub = int(tnum * den / tden) + 1
            safe_num = (EXP_K_NUM[k_floor] * frac_ub + NEG_UB[k_floor] * den) // 2000 + 1
            num = max(num, safe_num)
    return num


def emit_cosh_ub_lemma(name: str, b: float, *, private: bool = False, tight: bool = False) -> list[str]:
    num = int(math.cosh(b) * COSH_SCALE) + 1 if tight else certified_cosh_ub_num(b)
    den = COSH_SCALE
    k_round = int(round(b))
    prefix = "private " if private else ""
    body = emit_cosh_bin(name, b, num, den, tight=tight)
    if body and body[0].startswith("lemma "):
        body[0] = prefix + body[0]
    return body


def emit_cosh_bin(name: str, b: float, num: int | None = None, den: int = COSH_SCALE, *, tight: bool = False) -> list[str]:
    if num is None:
        num = int(math.cosh(b) * COSH_SCALE) + 1 if tight else certified_cosh_ub_num(b)
    k_round = int(round(b))
    if b <= SQRT2 - 1e-12:
        return emit_small_cosh_ub(name, b, num, den)
    if abs(b - k_round) <= 1e-9 and 2 <= k_round <= 5:
        return emit_integer_cosh_ub(name, b, k_round, num, den)
    if b >= 5.0 - 1e-12:
        return emit_integer_cosh_ub(name, b, 5, num, den)
    k_floor = int(math.floor(b + 1e-12))
    if k_floor < 1:
        return emit_small_cosh_ub(name, b, num, den)
    return emit_product_cosh_ub(name, b, num, den, tight=tight)


def main() -> None:
    bins: dict[str, float] = {}
    for i in range(N):
        u = 5 * (i + 1) / N
        for x in (u, u / R):
            if x <= 0:
                continue
            bins[bin_key(x)] = bin_val(x)
    lines = [
        "import UgpLean.Substrate.SechOverlapIntegralBounds_cosh",
        "",
        "namespace UgpLean.Substrate.PhiMDLFluctuationSpectrum",
        "",
        "open Real",
        "",
        "lemma cosh_mono_Ici {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : cosh x ≤ cosh y := by",
        "  exact cosh_strictMonoOn.monotoneOn (Set.mem_Ici.mpr hx)",
        "    (Set.mem_Ici.mpr (hx.trans hxy)) hxy",
        "",
    ]
    for name in sorted(bins, key=lambda k: bins[k]):
        lines += emit_cosh_bin(name, bins[name])
    lines += ["end UgpLean.Substrate.PhiMDLFluctuationSpectrum", ""]
    OUT.write_text("\n".join(lines))
    print(f"Wrote {OUT}, bins={len(bins)}")


if __name__ == "__main__":
    main()
