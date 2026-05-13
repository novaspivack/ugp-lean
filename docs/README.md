# ugp-lean System Documentation

**ugp-lean** is a Lean 4 formalization of the Universal Generative Principle (UGP) and Generative Triple Evolution (GTE). It provides machine-checked proofs of core UGP claims, including the Residual Seed Uniqueness Conjecture (RSUC), the Quarter-Lock Law, Turing universality of the UGP substrate (UWCA / Rule 110; history-lane reversibility), optional ML-9 coarse-entropy companions on a finite GTE simulation, precision Phase4 and cyclotomic layers, and the self-reference stack. The **canonical** module taxonomy and counts match `paper/ugp_lean_formalization.tex` (§Architecture).

## Documentation Index

Tracked here: **build**, **module graph**, **theorem catalog**, and **architecture** only. Advisor memos, program working notes, and other internal write-ups belong in a **local** file (e.g. `docs/ADVISOR_STATUS.md` is gitignored — keep your copy outside the published tree or only on your machine).

| Document | Description |
|----------|-------------|
| [BUILD.md](BUILD.md) | Prerequisites, build instructions, toolchain |
| [MODULES.md](MODULES.md) | Complete module reference and dependency graph |
| [THEOREMS.md](THEOREMS.md) | Theorem catalog: what ugp-lean proves |
| [DESIGN.md](DESIGN.md) | Non-circularity, architecture, proof strategy |

## Quick Start

```bash
cd ugp-lean
lake update
lake build
```

Build completes with 0 errors, 0 sorry on the core RSUC path. See [BUILD.md](BUILD.md) for details.

## Key Results

- **RSUC**: Residual Seed Uniqueness — exactly one equivalence class; MDL selects (1,73,823)
- **Theorem A (general)**: ∀n, UnifiedAdmissibleAt n t → t ∈ CandidatesAt n
- **Ridge sieve**: At n=10, survivors = {(24,42), (42,24)}
- **Quarter-Lock**: k_M = k_G + ¼k_L²
- **Canonical orbit**: (1,73,823) → (9,42,1023) → (5,275,65535)
- **Turing universality**: UGP substrate Turing-universal via Rule 110; exact UWCA sweep (`uwca_sweep_implements_rule110`); history-stack inverse (`uwca_augmented_left_inverse`)
- **ML-9 companion (finite)**: strict coarse Shannon-entropy drop on an 8→9 macro prefix along the Lepton GTE simulation at `n = 10` (`gte_entropy_prefix8_gt_prefix9`)

The classification is n-parameterized: predicates and candidate sets are indexed by ridge level n.

## Repository Layout

```
ugp-lean/
├── lakefile.lean, lean-toolchain
├── UgpLean.lean              # Root module, imports all
├── UgpLean/
│   ├── Core/                 # Definitions (no Compute)
│   ├── Compute/              # Algorithms, native_decide
│   ├── Classification/       # Theorem A/B, RSUC
│   ├── GTE/                  # Evolution, Orbit, UpdateMap, GTESimulation, EntropyNonMonotone, …
│   ├── MassRelations/, BraidAtlas/, ElegantKernel/, QuarterLock, LModelDerivation, Conjectures
│   │                         # (full list: docs/MODULES.md)
│   ├── Phase4/               # DeltaUGP, GaugeCouplings, UCL, PR1, AsymptoticSparsity,
│   │                         # PositiveRootTheorem, GaloisProtection, TwoLoopCoefficient
│   ├── GaloisStructure/     # CyclotomicLayers, MinimalCyclotomic
│   ├── CyclotomicCompleteness/ # CoxeterBiconditional, CyclotomicContainment
│   ├── TE22/                 # ScanCertificate (PSC universe scan)
│   ├── PSC/                  # RCCInfiniteFamilies
│   ├── Universality/         # Rule110, UWCA, UWCASimulation, UWCAHistoryReversible,
│   │                         # UWCAembedsRule110, TuringUniversal, ArchitectureBridge
│   ├── Papers/               # Citable stubs (Paper25, UGPMain)
│   └── Instance/             # NemSBridge
├── docs/
├── MANIFEST.md
├── Assumptions.md
└── README.md
```

## References

- **Roadmap**: `UGP_LEAN_PROGRAM_ROADMAP.md` (in workspace)
- **Paper 25 Upgrade**: `PAPER_25_UPGRADE_PLAN.md`
- **UGP Formalization**: `NEMS_PAPERS/UGP_GTE_Formalization/` — definitive formal specification with theorem-indexed mapping to ugp-lean modules (companion to Paper 25)
- **Source papers**: UGP Main Paper, JMP Math Foundations, gte_triples_explainer
