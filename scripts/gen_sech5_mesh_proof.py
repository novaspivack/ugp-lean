#!/usr/bin/env python3
"""Generate r=5 half-line mesh with per-point Taylor cosh proofs."""
from __future__ import annotations

import math
import re
import sys
from fractions import Fraction
from math import factorial
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
sys.path.insert(0, str(ROOT / "scripts"))
from sech_taylor_proofs import rat  # noqa: E402
from gen_sech5_cosh_bins import (  # noqa: E402
    BIN_STEP,
    COSH_SCALE,
    R,
    bin_key,
    bin_val,
    certified_cosh_ub_num,
    emit_cosh_ub_lemma,
)

OUT = ROOT / "UgpLean/Substrate/SechOverlapIntegralBounds_r5mesh.lean"

N = 550
H = 5 / N
HALF_TARGET = 1492288  # historical floor; generated cert uses exact micro sum
BATCH = 50


def cosh_ub_num_from_lemma_line(line: str) -> int:
    m = re.search(r"≤ \((\d+) : ℝ\) / (\d+)", line)
    if m is None:
        raise ValueError(f"cannot parse cosh bound from: {line!r}")
    return int(m.group(1))


def sech_lb_micro_from_lemma_lines(u_line: str, v_line: str) -> int:
    """Provable micro-units from emitted `cosh5_*_le` numerators (conservative floor)."""
    nu = cosh_ub_num_from_lemma_line(u_line)
    nv = cosh_ub_num_from_lemma_line(v_line)
    # Shave 1 micro-unit: `field_simp`/`linarith` margin on worst mesh points.
    return max(0, int(COSH_SCALE * COSH_SCALE / nv / nu * H * 1_000_000) - 1)


def emit_cosh_le(u: float, idx: int, comp: str) -> list[str]:
    internal = f"m{comp}{idx}"
    b = bin_val(u)
    lines = emit_cosh_ub_lemma(internal, b, private=True, tight=True)
    return [lines[0].replace(f"cosh_{internal}_ub", f"cosh5_{comp}_{idx}_le")] + lines[1:]


def batch_micro(micros: list[int], indices: list[int]) -> int:
    return sum(micros[i] for i in indices)


def main() -> None:
    header = [
        "import UgpLean.Substrate.PhiMDLFluctuationSpectrum",
        "import UgpLean.Substrate.SechOverlapIntegralBounds_r5bins",
        "",
        "namespace UgpLean.Substrate.PhiMDLFluctuationSpectrum",
        "",
        "open Real",
        "",
        "lemma sech_ge_of_cosh_le {x C : ℝ} (hC : 0 < C) (hc : cosh x ≤ C) :",
        "    1 / C ≤ sech x := by",
        "  unfold sech",
        "  simpa using one_div_le_one_div_of_le (cosh_pos x) hc",
        "",
        f"def sech5_meshN : Nat := {N}",
        "",
    ]
    lines = list(header)
    batch_indices: list[int] = []
    batch_id = 0
    micros: list[int] = []

    for i in range(N):
        u = 5 * (i + 1) / N
        u_lines = emit_cosh_le(u, i, "u")
        v_lines = emit_cosh_le(u / R, i, "v")
        micro = sech_lb_micro_from_lemma_lines(u_lines[0], v_lines[0])
        micros.append(micro)
        lines += u_lines
        lines += v_lines
        bu = bin_val(u)
        bv = bin_val(u / R)
        lines += [
            f"private lemma sech5_pt_{i}_ge : ({micro} : ℝ) / 1000000 ≤ "
            f"({rat(H)} : ℝ) * sechProd {R} ({rat(u)}) := by",
            "  unfold sechProd",
            "  simp only [sech, div_eq_mul_inv]",
            f"  have hbin_u : ({rat(u)}) ≤ ({rat(bu)}) := by norm_num",
            f"  have hbin_v : ({rat(u / R)}) ≤ ({rat(bv)}) := by norm_num",
            f"  have hcosh_u : cosh ({rat(u)}) ≤ cosh ({rat(bu)}) :=",
            f"    cosh_mono_Ici (by norm_num) hbin_u",
            f"  have hcosh_v : cosh ({rat(u / R)}) ≤ cosh ({rat(bv)}) :=",
            f"    cosh_mono_Ici (by norm_num) hbin_v",
            f"  have hc1 := sech_ge_of_cosh_le (by norm_num) (hcosh_u.trans cosh5_u_{i}_le)",
            f"  have hc2 := sech_ge_of_cosh_le (by norm_num) (hcosh_v.trans cosh5_v_{i}_le)",
            "  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)",
            "  field_simp at hprod ⊢",
            "  norm_num at hprod ⊢",
            "  linarith",
            "",
        ]
        batch_indices.append(i)
        if len(batch_indices) == BATCH:
            cert = batch_micro(micros, batch_indices)
            terms = " + ".join(f"({rat(H)} : ℝ) * sechProd {R} ({rat(5 * (j + 1) / N)})" for j in batch_indices)
            refs = ", ".join(f"sech5_pt_{j}_ge" for j in batch_indices)
            lines += [
                f"private lemma sech5_batch_{batch_id}_ge : ({cert} : ℝ) / 1000000 ≤ {terms} := by",
                f"  linarith [{refs}]",
                "",
            ]
            batch_id += 1
            batch_indices = []

    if batch_indices:
        cert = batch_micro(micros, batch_indices)
        terms = " + ".join(f"({rat(H)} : ℝ) * sechProd {R} ({rat(5 * (j + 1) / N)})" for j in batch_indices)
        refs = ", ".join(f"sech5_pt_{j}_ge" for j in batch_indices)
        lines += [
            f"private lemma sech5_batch_{batch_id}_ge : ({cert} : ℝ) / 1000000 ≤ {terms} := by",
            f"  linarith [{refs}]",
            "",
        ]
        batch_id += 1

    total = batch_micro(micros, list(range(N)))
    cert_target = min(total, HALF_TARGET)
    if total < HALF_TARGET:
        print(f"note: micro sum {total} < HALF_TARGET {HALF_TARGET}; cert uses {cert_target}")
    batch_refs = ", ".join(f"sech5_batch_{j}_ge" for j in range(batch_id))
    term_refs = " + ".join(f"({rat(H)} : ℝ) * sechProd {R} ({rat(5 * (i + 1) / N)})" for i in range(N))
    lines += [
        f"lemma sech5_halfline_meshSum_ge : ({cert_target} : ℝ) / 1000000 ≤ ({term_refs}) := by",
        f"  linarith [{batch_refs}]",
        "",
        "end UgpLean.Substrate.PhiMDLFluctuationSpectrum",
        "",
    ]
    OUT.write_text("\n".join(lines))
    print(f"Wrote {OUT}, lines={len(lines)}, total_micro={total}, batches={batch_id}")


if __name__ == "__main__":
    main()
