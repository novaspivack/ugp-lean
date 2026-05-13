# ugp-lean

## Research Program

This repository is part of the **Reflexive Reality** research program by [Nova Spivack](https://www.novaspivack.com/).

**What this formalizes:** Machine-checked Lean 4 formalization of the Universal Generative Principle (UGP) — ridge sieve, GTE orbit, Quarter-Lock, UCL Elegant Kernel, mass relations, Turing universality (including UWCA history-lane reversibility), meta-law ML-9 finite entropy companions, and self-reference.  **117 modules, zero sorry on the core proof path** (see `paper/ugp_lean_formalization.tex` for the canonical layer diagram and module list).

| Link | Description |
|------|-------------|
| [Research page](https://www.novaspivack.com/research/) | Full index of all papers, programs, and Lean archives |
| [Full abstracts](https://novaspivack.github.io/research/abstracts/#abs-toc) | Complete abstract for this library's papers |
| [Zenodo program hub](https://doi.org/10.5281/zenodo.19429270) | Citable DOI hub for the NEMS program |

---

## Build

```bash
lake update
lake build
```

**Toolchain:** Lean 4.29.0-rc6, Mathlib v4.29.0-rc6.

A clean build completes with zero `sorry` and the standard Mathlib axiom signature `[propext, Classical.choice, Quot.sound]`.  Two pre-existing `sorry` placeholders in `GTE/AnalyticArchitecture` (Tenenbaum-class equidistribution) are outside the core proof path and documented in the formalization paper §3.2.

---

## Module structure (117 modules; **12 layers** in `paper/ugp_lean_formalization.tex` §Architecture)

| Layer | Count | Modules |
|-------|-------|---------|
| **Core** | 7 | RidgeDefs, MirrorDefs, TripleDefs, SievePredicates, Disconfirmation, RidgeRigidity, MirrorAlgebra |
| **Compute** | 6 | PrimeLock, Sieve, SieveExtended, SieveBelow10, ExclusionFilters, DecidablePredicates |
| **Classification** | 6 | Bounds, TheoremA, TheoremB, RSUC, FormalRSUC, MonotonicStrengthening |
| **GTE** | 21 | Evolution, Orbit, UpdateMap, GeneralTheorems, MersenneGcd, MersenneLadder, PrimeFactorAnalysis, ResonantFactory, MirrorDualConjecture, MirrorShift, UGPPrimes, InertPrimes, AnalyticArchitecture, DSIExport, StructuralTheorems, UniquenessCertificates, GTESimulation, EntropyNonMonotone, FiberBundle, LinearResponse, ScaleConnection |
| **Structural** | 19 | QuarterLock, LModelDerivation; *ElegantKernel/*: ChiralityFeature, D5StructuralAxiom, FibonacciHessian, KGen, KGen2, MuTriple, PentagonalUniqueness; *ElegantKernel/Unconditional/*: CyclotomicChain, D5Renormalization, FibonacciPentagonBridge, FullClosure, KConstFullClosure, KGenFullClosure, KLFullClosure, PentagonConstraint, RiccatiFixedPoint |
| **MassRelations** | 24 | *MassRelations* [umbrella], KoideClosedForm, KoideNewtonFlow, KoideAngle, KoideS3DiscreteIdentities, BinaryCascade, PhysicalMasses, SU3FlavorCartan, CartanFlavonPotential, FroggattNielsen, NeutrinoFroggattNielsen, HeavyFermionTower, ClebschGordan, DownRational, UpLeptonCyclotomic, Z2OrbifoldDepth, ClaimCBridge, LeptonMassPrediction, ScaleTransport, SeesawIndex, VVMechanism, VVAllCoefficientsFromNc, CKMTheta23, **CKMMixing** |
| **BraidAtlas** | 7 | ChargeTheorem, CompositeTriples, ChiralitySquaring, ChargeDerivation, CoxeterConductor, CoxeterConductorTowerLaw, EWBosons |
| **Universality** | 7 | Rule110, UWCA, UWCASimulation, UWCAHistoryReversible, UWCAembedsRule110, TuringUniversal, ArchitectureBridge |
| **SelfRef** | 2 | LawvereKleene, RiceHalting |

Additional modules — **Phase4** (8: DeltaUGP, GaugeCouplings, UCL, PR1, AsymptoticSparsity, PositiveRootTheorem, GaloisProtection, TwoLoopCoefficient), **GaloisStructure** (2), **CyclotomicCompleteness** (2), **PSC** (1: RCCInfiniteFamilies), **TE22** (1: ScanCertificate), **Papers** (2), **Instance** (1), **Conjectures** — per the formalization paper: `Phase4.GaloisProtection`, `TwoLoopCoefficient`, modules under `GaloisStructure.*` and `CyclotomicCompleteness.*`, and `TE22` carry fully mechanized statements where the paper claims zero sorry; `Papers` and `Instance` are chiefly citable stubs and bridges; `Conjectures` records resolved and open claims; `Phase4` also mixes stubs (e.g. UCL, PR1 presentation) with the precision theorems above.

**Non-circularity:** Core/ may not import Compute/. See [docs/DESIGN.md](docs/DESIGN.md).

---

## Key theorems

**Core structural chain**
- `ridgeSurvivors_10` — At n=10, survivors = {(24,42),(42,24)}
- `theoremA_general` — ∀n, UnifiedAdmissibleAt n t → t ∈ CandidatesAt n
- `rsuc_theorem` — Residual Seed Uniqueness; MDL selects Lepton Seed (1,73,823)
- `canonical_orbit_triples` — (1,73,823) → (9,42,1023) → (5,275,65535)
- `quarterLockLaw` — k_M = k_gen2 + ¼k_L²

**Claim C — Formal proof (MassRelations.ClaimCBridge, 2026-04-20)**
- `claim_C_formal` — cascadeState g = angleToAlpha1(ω₁) · 2^g + π/8; formal Claim C proved by combining Claim A (π/6 = SU(3) Weyl bisector) and Claim B (binary cascade doubles per generation); zero hypotheses, zero sorry
- `k_gen2_encodes_double_weyl_bisector` — k_gen2 = −φ · cos(2 · Weyl bisector); bridges Elegant Kernel to SU(3) geometry
- `pentagon_hexagon_TT_unified_bridge` — all five structural facts simultaneously: TT formula, Weyl bisector, k_gen2 = −φcos(2Weyl), k_gen = φcos(π/10), Pentagon-Hexagon Bridge

**UCL Unconditional Closure (ElegantKernel layer)**
- `thm_ucl2_fully_unconditional` — k_gen = φ·cos(π/10) = √(φ²−1/4) ≈ 1.5388; derived zero-hypothesis via Quarter-Lock substitution on Fibonacci char poly (replaces outdated conditional π/2 value in `KGen.lean`)
- `k_gen2_eq_neg_phi_half` — k_gen2 = −φ/2 = cos(4π/5); unique negative root of the pentagon quadratic 4k²+2k−1=0
- `k_gen_pentagon_hexagon_bridge` — k_gen + k_gen2 = φ·(cos(π/10) − cos(π/3)); bridges D₅ pentagonal (Fibonacci) and D₆ hexagonal (SU(3) Weyl) symmetries; proved 2026-04-20 from `thm_ucl2_fully_unconditional` + `k_gen2_eq_neg_phi_half` + Mathlib `cos_pi_div_three`
- `full_closure_summary` — All five UCL constraints simultaneously satisfiable; complete Elegant Kernel closure holds unconditionally

**Mass Relations (MassRelations layer)**
- `koide_iff_twoS_sq_eq_threeN` — Koide relation ↔ (2S)² = 3N algebraic normal form
- `koide_solved_form_root` — Koide-satisfying third mass in cyclotomic-12 closed form
- `newton_flow_fixes_null_cone` — Newton flow fixes every point on the Koide null cone
- `newton_flow_swap12_equivariant` / `newton_flow_rot123_equivariant` — Full S₃-equivariance of the Newton flow
- `cascadeState_closed_form` — Binary cascade closed form b_g = 2^{g−1} b₁
- `koidePredictedMTau_pos` — Predicted m_τ from (m_e, m_μ) is strictly positive

**CDM Mechanism — CKM Mixing (MassRelations.CKMMixing, 2026-05-11; 11 theorems, 0 sorry)**
- `cabibbo_effective_charge` — Δa_eff = α_d = 13/9 (effective FN charge = VV coefficient)
- `cabibbo_charge_from_GUT` — Δa_eff = 1 + rank(SU(5))/N_c² (GUT group-theory origin)
- `cabibbo_vev_formula` — |V_us|_CDM = (ε₁)^(α_d) = exp(−13π/27) ≈ 0.2203 (1.9% off PDG)
- `fn_vv_correction_additive` — KEY BRIDGE: fnMixChargeDown(α_d) = fnMixChargeDown(1) + (α_d−1); VV GUT coefficient shifts bare FN charge additively
- `fn_diagonalization_vv_bridge` — fnMixChargeDown(α_d) × log(ε₁) = −13π/27 (connects FN model to CDM structural log)
- `fn_cdm_physical_sorry` — Algebraic identity: log(cabibbo_structural_prediction) = fnMixChargeDown(α_d) × log(ε₁); proved via `Real.log_exp` (zero sorry)

**Universality and self-reference**
- `ugp_is_turing_universal` — UGP substrate Turing-universal via native Rule 110 embedding
- `uwca_sweep_implements_rule110` — UWCA sweep implements Rule 110 exactly
- `uwca_augmented_left_inverse` — UWCA + history stack: backward ∘ forward = id (exact lift)
- `gte_entropy_prefix8_gt_prefix9` — finite coarse Shannon-entropy drop along simulated GTE orbit (ML-9 companion; `GTE.EntropyNonMonotone`)
- `ugp_lawvere_fixed_point` / `ugp_kleene_recursion_thm` / `ugp_rice_theorem` / `ugp_halting_undecidable` — Self-reference layer

---

## Documentation

| Document | Description |
|----------|-------------|
| [docs/README.md](docs/README.md) | Documentation index |
| [docs/BUILD.md](docs/BUILD.md) | Build guide, troubleshooting |
| [docs/MODULES.md](docs/MODULES.md) | Module reference |
| [docs/THEOREMS.md](docs/THEOREMS.md) | Theorem catalog |
| [docs/DESIGN.md](docs/DESIGN.md) | Non-circularity, architecture |

## References

- [MANIFEST.md](MANIFEST.md) — Paper→Lean theorem mapping
- [Assumptions.md](Assumptions.md) — Premise ledger
- **Formalization paper** — `paper/ugp_lean_formalization.tex` (definitive formal spec; complete theorem inventory in Table 1)
<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429247
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
<!-- NOVA_ZPO_ZENODO_PAPER_BEGIN -->
**Archival paper (Zenodo preprint) (Zenodo):** https://doi.org/10.5281/zenodo.19433539
<!-- NOVA_ZPO_ZENODO_PAPER_END -->
