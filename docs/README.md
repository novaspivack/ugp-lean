# ugp-lean Documentation

**ugp-lean** is a Lean 4 formalization of the Universal Generative Principle (UGP) and Generative Triple Evolution (GTE) — a research program establishing that a single 7-state cellular automaton over GF(7) generates the Standard Model particle spectrum, gauge structure, and mass predictions from first principles.

The **canonical** module taxonomy and theorem inventory are in `paper/ugp_lean_formalization.tex`.

## Documentation Index

| Document | Description |
|---|---|
| [BUILD.md](BUILD.md) | Prerequisites, build instructions, toolchain |
| [MODULES.md](MODULES.md) | Module reference and dependency graph |
| [THEOREMS.md](THEOREMS.md) | Curated theorem highlights by layer |
| [DESIGN.md](DESIGN.md) | Non-circularity contract and architecture |

## Quick Start

```bash
lake update
lake build
```

Build completes with 0 errors, 0 sorry on the core proof path. See [BUILD.md](BUILD.md) for details.

## Key Results

**Core structure**
- **RSUC**: unique residual equivalence class; MDL selects (1, 73, 823)
- **Canonical orbit**: (1,73,823) → (9,42,1023) → (5,275,65535)
- **Quarter-Lock**: k_M = k_gen2 + ¼k_L²
- Orbit uniqueness: GEN₁→GEN₂→GEN₃→vacuum is the *only* PSC-admissible trajectory from GEN₁
- Vacuum uniqueness: all 16,807 states converge to vacuum in ≤7 steps; no false vacua

**Mass and mixing**
- Koide relation in closed algebraic form; Newton flow S₃-equivariance
- CKM Cabibbo angle |V_us| = exp(−13π/27) ≈ 0.2203 (1.9% off PDG)
- Neutrino mass ratio R ≈ 0.02936 within 1% of NuFIT 6.0
- η_B = 6.109×10⁻¹⁰ CatAL unconditional (+0.15σ vs PDG)

**Universality and self-reference**
- UGP substrate Turing-universal via Rule 110 embedding
- GTE update map is the *unique* lawful UWCA program up to bisimulation
- UWCA history-lane reversibility: backward ∘ forward = id
- Lawvere fixed-point, Rice's theorem, halting undecidability

## Repository Layout

```
ugp-lean/
├── lakefile.lean, lean-toolchain
├── UgpLean.lean              # Root module
├── UgpLean/
│   ├── Core/                 # Ridge/mirror/triple definitions (no Compute import)
│   ├── Compute/              # Sieve algorithms, native_decide
│   ├── Classification/       # Theorems A/B, RSUC
│   ├── GTE/                  # Evolution, orbit, update map, fiber bundle, analytic arch
│   ├── ElegantKernel/        # Quarter-Lock, UCL Elegant Kernel, Unconditional/
│   ├── MassRelations/        # Koide, CKM, PMNS, Higgs quartic, neutrino sector
│   ├── BraidAtlas/           # Charge theorem, EW bosons, dark braid, RHN gap
│   ├── Universality/         # Rule 110, UWCA, Turing universality, GTE compilation
│   ├── Polynomial/           # GF(7) explorations, causal tree, MDL unification, spin-7
│   ├── Physics/              # Kink physics, Z₇ vacuum selection, CMCA physical point
│   ├── Substrate/            # PhiMDL fluctuation, sech overlap bounds, Wightman axioms
│   ├── Gravity/              # Yukawa, FKTT, Wald entropy, FLRW, spinors
│   ├── Spacetime/            # Geodesic, mass gap, orbit hierarchy, QEC, quantum gravity
│   ├── Algebra/              # Z₇ Galois, SM gauge group, F₂₁/SU(3) embedding
│   ├── Framework/            # GTE-NEMS instance, optimality, coalgebra, CMCA continuum
│   ├── ContinuumLimit/       # Wasserstein distance, GF(7) vacuum fixed point
│   ├── QFT/                  # Gauged mass gap, chiral symmetry breaking
│   ├── VEVProof/             # EW Goldstone manifold, Goldstone entropy correction
│   ├── VEVNoGo/              # SRRG no-go theorem
│   ├── GaloisStructure/      # Cyclotomic layers, minimal cyclotomic
│   ├── CyclotomicCompleteness/ # Coxeter biconditional, cyclotomic containment
│   ├── Phase4/               # DeltaUGP, gauge couplings, Galois protection
│   ├── PSC/                  # RCC infinite families
│   ├── TE22/                 # Scan certificate
│   ├── SelfRef/              # Lawvere–Kleene, Rice–Halting
│   ├── Papers/, Instance/    # Citable stubs and NEMS bridge
│   └── Conjectures           # Resolved and open conjectures
├── docs/
├── MANIFEST.md               # Paper → Lean theorem mapping
├── Assumptions.md            # Premise ledger
└── README.md
```

## References

- **Formalization paper**: `paper/ugp_lean_formalization.tex` — definitive spec, complete theorem inventory
- **Theorem catalog**: [docs/THEOREMS.md](THEOREMS.md)
- **Module reference**: [docs/MODULES.md](MODULES.md)
- **Research page**: https://www.novaspivack.com/research/
