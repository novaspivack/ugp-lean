# ugp-lean

Machine-checked Lean 4 formalization of the **Universal Generative Principle (UGP)** — a research program by [Nova Spivack](https://www.novaspivack.com/) establishing that a single 7-state cellular automaton over GF(7) generates the Standard Model particle spectrum, gauge structure, and mass predictions from first principles.

**361 modules · zero sorry on the core proof path · Lean 4 + Mathlib**

---

## What this formalizes

The UGP framework identifies a unique GF(7) polynomial whose orbit under a single deterministic update rule reproduces:

- The Standard Model generation structure (3 generations, 5 families)
- Lepton and quark mass ratios (Koide relations, CKM/PMNS mixing angles)
- Gauge coupling hierarchy and electroweak structure
- Turing universality of the underlying substrate (Rule 110 embedding)
- Quantum gravity and metric structure (RT formula, Wald entropy)

This library provides machine-checked certificates for all of these claims at the level they can currently be formalized. Every theorem is zero sorry on the core proof path; the six documented stubs outside the core path await specific Mathlib API completions (manifold integrals, matrix exponentials).

See the [formalization paper](paper/ugp_lean_formalization.tex) for the complete theory and theorem inventory, and the [Complete GTE Framework](https://doi.org/10.5281/zenodo.20560550) for the broader theory this formalizes.

---

## Separation of concerns

| Repository | Role |
|---|---|
| **ugp-lean** (this repo) | GTE/UGP-specific formalizations: Z₇ algebra, PSC structure, CMCA dynamics, GTE particle spectrum, MDL initial state, RT formula, fermionic statistics, mass predictions |
| [**ugp-physics-lean**](https://github.com/novaspivack/ugp-physics-lean) | Standard physics infrastructure: Lorentzian geometry, Minkowski spacetime, spinor representations, spin-statistics, general relativistic structures |

**Dependency:** ugp-lean imports ugp-physics-lean for standard physics infrastructure. GTE-specific derivations live here; foundational physics facts that are independent of GTE theory belong in ugp-physics-lean.

---

## Build

```bash
lake update
lake build
```

**Toolchain:** Lean 4.29.0-rc6, Mathlib v4.29.1.

A clean build completes with the standard Mathlib axiom signature `[propext, Classical.choice, Quot.sound]`. The two equidistribution inputs in `GTE/AnalyticArchitecture` are explicit named axioms with precise citations (documented in the formalization paper). The six remaining `sorry` stubs are outside the core proof path: three in `Gravity/WaldEntropy` (pending Mathlib manifold integrals) and three in `Substrate/CogwheelDynamicsG21` (pending Mathlib matrix-exponential API).

---

## Module structure

361 modules organized in 17 layers. Full module lists are in [docs/MODULES.md](docs/MODULES.md) and the formalization paper.

| Layer | Modules | What it covers |
|---|---|---|
| **Core** | 7 | Ridge sieve definitions, mirror algebra, disconfirmation |
| **Compute** | 6 | Prime lock, sieve filters, decidable predicates |
| **Classification** | 7 | Theorems A/B, RSUC, monotonic strengthening, N_gen=3 uniqueness |
| **GTE** | 25 | GTE orbit, update map, generation structure, entropy, fiber bundle |
| **Structural** | 30 | Quarter-Lock, Elegant Kernel, UCL mass ordering closure |
| **MassRelations** | 33 | Koide, CKM, PMNS, Higgs quartic, neutrino sector, pion mass, Eisenstein identities, CKM θ₂₃ structural ratio |
| **BraidAtlas** | 13 | Charge theorem, EW bosons, dark braid, RHN gap |
| **Universality** | 52 | Rule 110, UWCA, Turing universality, GTE compilation/uniqueness, EW structure, Solovay completeness, bi-immunity, complex amplitude forcing |
| **Polynomial** | 19 | GF(7) explorations, causal tree, MDL unification, spin-7 ground space, PSL(2,7) unification, golden fiber taxonomy, golden quadratic arithmetic, admissible primes, Gaussian face arithmetic |
| **Algebra** | 3 | Eisenstein functor, A₄ structure from inert-2 ramification, Fano regular action |
| **Physics** | 8 | Z₇ vacuum selection, kink physics, CMCA physical point, BPS actions |
| **Substrate** | 8 | PhiMDL fluctuation spectrum, sech overlap bounds, VA quantization, chiral currents, coherence-measure uniqueness |
| **Gravity** | 4 | Yukawa overlap, FKTT coupling, Wald entropy scaffold, cosmological constant all-order vanishing |
| **QFT** | 2 | Gauged mass gap, chiral symmetry breaking |
| **Framework** | 6 | GTE-NEMS framework instance, optimality, final coalgebra, PR-5 independence, PSC measure uniformity, F21–SU(2) bridge |
| **SelfRef** | 2 | Lawvere–Kleene, Rice–Halting |
| **Spacetime** | ~12 | Geodesic theorem, mass gap, orbit mass hierarchy, QEC stabilizer |
| **Foundations / Cosmology / Phase4 / Other** | ~64 | Galois structure, cyclotomic completeness, PSC, conjectures, papers, CMCA filtration, thermodynamic bridge, cosmological constant bracket |

---

## Selected results

**Particle structure**
- The SM generation orbit GEN₁→GEN₂→GEN₃→vacuum is the *unique* PSC-admissible trajectory from GEN₁ (`fmdl_orbit_is_unique_psc_trajectory`)
- GEN₁ is a Garden-of-Eden state — no predecessor in the 16,807-state space (`fmdl_gen1_is_goe`)
- All 16,807 states converge to the vacuum in ≤7 steps; no false vacua (`fmdl_vacuum_is_unique_attractor`)
- Rule 110 is the unique CA rule satisfying the SM orbit and vacuum transparency (`rule110_unique_weight5_orbit_satisfier`)

**Mass relations**
- Koide relation certified in closed algebraic form; Newton flow S₃-equivariance proved
- CKM Cabibbo angle |V_us| = exp(−13π/27) ≈ 0.2203 (1.9% off PDG), derived from FN charge arithmetic
- Neutrino mass ratio within 1% of NuFIT 6.0; PMNS angles (θ₁₂, θ₂₃, θ₁₃, δ_CP) derived
- η_B = 6.109×10⁻¹⁰ CatAL unconditional (+0.15σ vs PDG), from kink–top BPS coupling

**Turing universality**
- GTE substrate is Turing-universal via Rule 110 embedding (`ugp_is_turing_universal`)
- GTE update map is the *unique* lawful UWCA program up to bisimulation (`gte_uniqueness_up_to_bisimulation`)
- UWCA history-lane reversibility: backward ∘ forward = id exactly

**Algebraic structure**
- Vacuum uniqueness: Fix(T_n) = {vacuum} for every ring size n; no false vacua dynamically (`vacuum_unique_temporal_fixed_point_ring`)
- Ground-space rigidity: cyclic zero-energy rings are exactly {0ⁿ, 1ⁿ, 5ⁿ} for all ring lengths n ≥ 3
- Z₇ winding conservation ≡ electric charge conservation for all SM color-singlet particles
- Parity-projection forcing: all 777 additive forms and 16,807 mod-2 recodings enumerated; Rule 110 forcing is maximal
- PSL(2,7) unification: F₂₁ ≅ PSL(2,7) as the automorphism group of the Fano plane; Borel-measurability of the F₂₁ action (`psl27_is_automorphism_group_fano_plane`)
- Golden fiber taxonomy: golden-fiber states at q=7 classified; golden-quadratic arithmetic certified (`golden_fiber_taxonomy_at_q7`)
- Eisenstein functor: A₄ structure derived from inert-2 ramification; Eisenstein norm-product |F₂₁| = Φ₆(2)Φ₆(3) verified
- N_gen = 3 uniqueness: the three-generation structure is the unique solution satisfying all GTE constraints (`ngen_uniqueness`)
- Cosmological constant vanishing: all CC contributions vanish at the algebraic level, all orders (`lambda_all_order_zero`)

---

## Documentation

| Document | Description |
|---|---|
| [docs/README.md](docs/README.md) | Documentation index |
| [docs/BUILD.md](docs/BUILD.md) | Build guide and troubleshooting |
| [docs/MODULES.md](docs/MODULES.md) | Complete module reference |
| [docs/THEOREMS.md](docs/THEOREMS.md) | Full theorem catalog |
| [docs/DESIGN.md](docs/DESIGN.md) | Non-circularity constraints and architecture |
| [Assumptions.md](Assumptions.md) | Premise ledger |
| [MANIFEST.md](MANIFEST.md) | Paper → Lean theorem mapping |
| [paper/ugp_lean_formalization.tex](paper/ugp_lean_formalization.tex) | Formalization paper (definitive spec) |

---

## Research program

This library is part of the **Reflexive Reality** research program.

| Link | Description |
|---|---|
| [Research page](https://www.novaspivack.com/research/) | Full index of all papers, programs, and Lean archives |
| [UGP Physics programme](https://www.novaspivack.com/research/physics-program) | The UGP Physics research programme |
| [Full abstracts](https://novaspivack.github.io/research/abstracts/#abs-toc) | Complete abstracts |
| [Zenodo program hub](https://doi.org/10.5281/zenodo.20644340) | Citable DOI hub for the UGP Physics program |
