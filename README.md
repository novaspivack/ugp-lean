# ugp-lean

Lean 4 formalization of the Universal Generative Principle (UGP) and Generative Triple Evolution (GTE). Proves RSUC, certifies the n=10 sieve and canonical orbit, Quarter-Lock, and Turing universality. The classification is **n-parameterized**: predicates and candidate sets are indexed by ridge level n; at n=10 this yields the certified Lepton Seed.

## Build

```bash
lake update
lake build
```

**Toolchain:** Lean 4.29.0-rc3, Mathlib v4.29.0-rc3.

## Documentation

| Document | Description |
|----------|-------------|
| [docs/README.md](docs/README.md) | Documentation index |
| [docs/BUILD.md](docs/BUILD.md) | Build guide, troubleshooting |
| [docs/MODULES.md](docs/MODULES.md) | Module reference |
| [docs/THEOREMS.md](docs/THEOREMS.md) | Theorem catalog |
| [docs/DESIGN.md](docs/DESIGN.md) | Non-circularity, architecture |
| [docs/ADVISOR_STATUS.md](docs/ADVISOR_STATUS.md) | **Advisor status: scope, soundness, gaps** |

## Module structure

| Layer | Modules | Purpose |
|-------|---------|---------|
| **Core** | RidgeDefs, MirrorDefs, TripleDefs, SievePredicates, Disconfirmation, RidgeRigidity, MirrorAlgebra | Definitions, no computation |
| **Compute** | PrimeLock, Sieve, SieveExtended, ExclusionFilters, DecidablePredicates | Algorithms, native_decide |
| **Classification** | Bounds, TheoremA, TheoremB, RSUC, FormalRSUC, MonotonicStrengthening | RSUC two-theorem architecture |
| **GTE** | Evolution, Orbit | Canonical orbit |
| **Phase4** | DeltaUGP, GaugeCouplings, UCL, PR1 | Gauge, δ_UGP, stubs |
| **Universality** | Rule110, UWCA, TuringUniversal, ArchitectureBridge | Rule 110, Turing-universal |
| **Instance** | NemSBridge | NEMS Paper 25 bridge |

**Non-circularity:** Core/ may not import Compute/. See [docs/DESIGN.md](docs/DESIGN.md).

## Key theorems

- `ridgeSurvivors_10` — At n=10, survivors = {(24,42), (42,24)}
- `theoremA_general` — ∀n, UnifiedAdmissibleAt n t → t ∈ CandidatesAt n; `theoremA` is the n=10 corollary
- `rsuc_theorem` — Residual Seed Uniqueness; MDL selects Lepton Seed (1,73,823)
- `quarterLockLaw` — k_M = k_gen2 + ¼k_L²
- `canonical_orbit_triples` — (1,73,823) → (9,42,1023) → (5,275,65535)
- `strengthening_cannot_add_survivors` — Predicate strengthening cannot add survivors to Residual
- `ugp_is_turing_universal` — UGP substrate Turing-universal

## References

- [MANIFEST.md](MANIFEST.md) — Paper→Lean theorem mapping
- [Assumptions.md](Assumptions.md) — Premise ledger
- **UGP Formalization paper** — `NEMS_PAPERS/UGP_GTE_Formalization/` (definitive formal spec; theorem-indexed mapping)
- UGP_LEAN_PROGRAM_ROADMAP.md (in workspace)
<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429247
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
<!-- NOVA_ZPO_ZENODO_PAPER_BEGIN -->
**Archival paper (Zenodo preprint) (Zenodo):** https://doi.org/10.5281/zenodo.19433539
<!-- NOVA_ZPO_ZENODO_PAPER_END -->
