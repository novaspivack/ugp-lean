# Reproducing UgpLean Certifications

## Building the library

```bash
cd /path/to/ugp-lean          # or ugp-lean-exp for development
lake update
lake build UgpLean
```

A clean build completes with the standard Mathlib axiom signature
`[propext, Classical.choice, Quot.sound]`.  Two pre-existing `sorry` placeholders
in `GTE/AnalyticArchitecture` (Tenenbaum-class equidistribution) are outside the
core proof path and documented in the formalization paper §3.2.

---

## Lean certificate generators (`scripts/`)

Some theorems rely on rational bounds and `norm_num` witnesses produced by Python
scripts.  After regenerating any certificate, run `lake build UgpLean` to verify
the Lean proofs still check.

| Script | Output module(s) | Purpose | Regenerate |
|--------|-----------------|---------|-----------|
| `scripts/gen_ucl_mass_ordering_sbounds.py` | `UCLMassOrderingSBounds.lean`, `UCLMassOrderingDelta.lean` | Rational bounds for UCL mass-ordering coupled-corner deltas | `python3 scripts/gen_ucl_mass_ordering_sbounds.py` |
| `scripts/gen_ucl_mass_ordering_delta.py` | `UCLMassOrderingDelta.lean` | Log-delta bounds for UCL coefficients | `python3 scripts/gen_ucl_mass_ordering_delta.py` |
| `scripts/gen_ucl_mass_ordering_interval.py` | `UCLMassOrderingInterval.lean` | Log-bound interval lemmas | `python3 scripts/gen_ucl_mass_ordering_interval.py` |
| `scripts/gen_ucl_mass_ordering_certs.py` | `UCLMassOrderingSBounds.lean`, `UCLMassOrderingCerts.lean`, `UCLMassOrderingBridge.lean` | Prior UCL iteration (superseded by sbounds) | (retained for reference) |
| `scripts/gen_sech5_cosh_bins.py` | `SechOverlapIntegralBounds_r5bins.lean` | 990 per-bin cosh bounds for r=5; zero sorry | `python3 scripts/gen_sech5_cosh_bins.py` |
| `scripts/gen_sech5_mesh_proof.py` | `SechOverlapIntegralBounds_r5mesh.lean` (partial) | r=5 half-line mesh with per-point Taylor cosh proofs | `python3 scripts/gen_sech5_mesh_proof.py` |
| `scripts/gen_sech11_mesh_proof.py` | `SechOverlapIntegralBounds_r11cert.lean` | r=11 mesh certification (N=40000); not run to completion (CatA axiom used instead) | `python3 scripts/gen_sech11_mesh_proof.py` |
| `scripts/gen_sech_overlap_bounds.py` | `SechOverlapIntegralBounds_gen.lean` (placeholder scaffold) | Scaffold for sech overlap; main bounds hand-certified | (scaffold only) |
| `scripts/gen_degree_block.py` | `UgpLean/Spacetime/SpectralDimensionDegree.lean` | Periodic-successor degree proof block for causal graph | `python3 scripts/gen_degree_block.py` |
| `scripts/gen_inj.py` | `inj_proof_gen.lean` (intermediate) | Injectivity block for 20-neighbor periodic causal graph | Called by `gen_degree_block.py` |

---

## Sech overlap bounds — provenance

The aggregate bounds `596903/10⁶` and `282771/10⁶` in
`SechOverlapIntegralBounds.lean` (and `PhiMDLFluctuationSpectrum.lean`) were
derived from numerical analysis in `eta_b_exact_sech_overlap.py` (graduated to
`papers/47_gte_cosmology/scripts/`).  Without that script, a verifier cannot
independently confirm the certified values are accurate.

Two CatA axioms in `SechOverlapIntegralBounds_bridge.lean`:
- `sech_overlap_at_five_ge_certified` — `I(5) ≥ 596903/10⁶` (r=5 mesh result)
- `sech_overlap_at_eleven_ge_certified` — `I(11) ≥ 282771/10⁶` (r=11 mesh result)

A full Riemann-sum interval certificate (closing these to zero sorry) is tracked as
open item **OQ-083C-EPS1-CatAL**: requires a Lean proof of
`AntitoneOn.sum_le_integral_Ico` in Mathlib, or a direct `norm_num` interval
tactic over the mesh.

To verify the numerical values independently:
```bash
python3 papers/47_gte_cosmology/scripts/eta_b_exact_sech_overlap.py
```

---

## Hand-derived certificates (no Python generator)

The following bounds are hand-written in Lean and have no external generator:

- **`UCLLogBounds.lean`** — `log φ`, `log(2π)`, `√5`, golden-ratio rational
  certificates following the Mathlib `Real.pi_gt_d*` / Taylor `exp_bound'` pattern.

- **`SechOverlapIntegralBounds_cosh.lean`** — `cosh_two_le` through `cosh_five_le`
  proved by hand using `exp_bound'` and `exp_one_lt_d9` combined with `cosh_eq`.

- **`SechOverlapIntegralBounds_bridge.lean`** — two CatA axioms hand-written to
  document the mesh→integral bridge (see above).

---

## Native-decide and norm-num only (no external script)

The following use Lean's `native_decide` or `norm_num` with no external generator:

- `GUTStructure.lean` — GUT charge scan, CKM arithmetic, Mersenne structure
- `NeutrinoSector.lean` — PMNS orbit ratio scan
- `TE22/ScanCertificate.lean` — 34,560-universe PSC enumeration (`native_decide`)
- Classification modules (`TheoremA`, `TheoremB`, `Bounds`, `FormalRSUC`) — `native_decide`
