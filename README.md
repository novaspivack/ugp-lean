# ugp-lean

## Research Program

This repository is part of the **Reflexive Reality** research program by [Nova Spivack](https://www.novaspivack.com/).

**What this formalizes:** Machine-checked Lean 4 formalization of the Universal Generative Principle (UGP) — ridge sieve, GTE orbit, Quarter-Lock, UCL Elegant Kernel, mass relations, Turing universality (including UWCA history-lane reversibility), meta-law ML-9 finite entropy companions, and self-reference.  **148 modules, zero sorry on the core proof path** (see `paper/ugp_lean_formalization.tex` for the canonical layer diagram and module list).

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

**Toolchain:** Lean 4.29.0-rc6, Mathlib v4.29.1.

A clean build completes with zero `sorry` and the standard Mathlib axiom signature `[propext, Classical.choice, Quot.sound]`.  Two pre-existing `sorry` placeholders in `GTE/AnalyticArchitecture` (Tenenbaum-class equidistribution) are outside the core proof path and documented in the formalization paper §3.2.

---

## Module structure (148 modules; **13 layers** in `paper/ugp_lean_formalization.tex` §Architecture)

| Layer | Count | Modules |
|-------|-------|---------|
| **Core** | 7 | RidgeDefs, MirrorDefs, TripleDefs, SievePredicates, Disconfirmation, RidgeRigidity, MirrorAlgebra |
| **Compute** | 6 | PrimeLock, Sieve, SieveExtended, SieveBelow10, ExclusionFilters, DecidablePredicates |
| **Classification** | 6 | Bounds, TheoremA, TheoremB, RSUC, FormalRSUC, MonotonicStrengthening |
| **GTE** | 24 | Evolution, Orbit, UpdateMap, GeneralTheorems, MersenneGcd, MersenneLadder, PrimeFactorAnalysis, ResonantFactory, MirrorDualConjecture, MirrorShift, UGPPrimes, InertPrimes, AnalyticArchitecture, DSIExport, StructuralTheorems, UniquenessCertificates, GTESimulation, EntropyNonMonotone, FiberBundle, LinearResponse, ScaleConnection, GTBGenerationPrimes, NcColorArithmetic, **NuclearPairing** |
| **Structural** | 19 | QuarterLock, LModelDerivation; *ElegantKernel/*: ChiralityFeature, D5StructuralAxiom, FibonacciHessian, KGen, KGen2, MuTriple, PentagonalUniqueness; *ElegantKernel/Unconditional/*: CyclotomicChain, D5Renormalization, FibonacciPentagonBridge, FullClosure, KConstFullClosure, KGenFullClosure, KLFullClosure, PentagonConstraint, RiccatiFixedPoint |
| **MassRelations** | 25 | *MassRelations* [umbrella], KoideClosedForm, KoideNewtonFlow, KoideAngle, KoideS3DiscreteIdentities, BinaryCascade, PhysicalMasses, SU3FlavorCartan, CartanFlavonPotential, FroggattNielsen, NeutrinoFroggattNielsen, HeavyFermionTower, ClebschGordan, DownRational, UpLeptonCyclotomic, Z2OrbifoldDepth, ClaimCBridge, LeptonMassPrediction, ScaleTransport, SeesawIndex, VVMechanism, VVAllCoefficientsFromNc, CKMTheta23, CKMMixing, **NeutrinoMassRatio** |
| **BraidAtlas** | 13 | ChargeTheorem, CompositeTriples, ChiralitySquaring, ChargeDerivation, CoxeterConductor, CoxeterConductorTowerLaw, EWBosons, MirrorWindingNumber, EWBosonRHNConnection, **RHNGapTheorem**, **DarkBraidAtlas**, **DarkQuarkCharge**, **DarkGaugeCoupling** |
| **Universality** | 34 | Rule110, UWCA, UWCASimulation, UWCAHistoryReversible, UWCAembedsRule110, TuringUniversal, ArchitectureBridge, CUP4TotalParity, CUP11ModSeven, CUP3DUniqueness, CUP3DPSCUnification, CUP3DPhysicalIncompleteness, TwoLayerConfluence, GTECompilation, GTEUniqueness, GTEInfTapeEncoding, GTEComputability, HypothesisB, HypothesisBCChain, PSCUniversality, CookRule110Ref, GoEHierarchy, **GoEStabilityHierarchy**, **OrbitPerturbationCatalog**, **Z7ChargeConjugation**, **Z5TransitivityUniqueness**, **DimensionalSliceUniqueness**, **GTPNeutralDiscrimination**, **SMOrbitCausalIsolation**, **EWBosonStructure**, **EWChiralBridge**, **GUTStructure**, **CasimirMasslessEther**, **LawvereZone**, **ChiralPairVA**, **CouplingNoGo** |
| **SelfRef** | 2 | LawvereKleene, RiceHalting |
| **Framework** | 3 | **GTEFrameworkInstance**, **GTEOptimalityInstance**, **GTEFinalCoalgebra** |

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

**Neutrino Mass Ratio — Seesaw Arithmetic (MassRelations.NeutrinoMassRatio, 2026-05-16; 5 theorems, 0 sorry)**
- `fn_texture_gives_seesaw_exponent` — FN charge pair (q₁,q₂)=(3,2) gives exponent 3 + 2/9 = 29/9 = nuSeesawExponent
- `seesaw_ratio_independent_of_MR` — Mass-squared ratio (m₂²−m₁²)/(m₃²−m₁²) is independent of M_R (algebraic, abstract)
- `neutrino_mass_ratio_coarse_bound` — Certified coarse bound: 0.029 < R < 0.030 where R = (11^{58/9}−5^{58/9})/(19^{58/9}−5^{58/9}) ≈ 0.02936
- `neutrino_mass_ratio_tight_bound` — Full tight bound |R − 0.02936| < 0.0001; zero sorry via unit-width integer bounds on b^(58/9)
- `neutrino_mass_ratio_within_1pct_of_nufit` — |R − 0.02951| < 0.01 × 0.02951; within 1% of NuFIT 6.0 central value; zero sorry

**GTE Nuclear Parity — NuclearPairing (UgpLean.GTE.NuclearPairing, 2026-05-18; 8 theorems, 0 sorry)**

Physical motivation: GTE-theoretic basis for the F10 proton-parity stability feature and the 5^(3/2) = 11.18 MeV pairing constant prediction (paper P03). Proton: (a=5, b=11459, c=15; g=3). Neutron: (a=5, b=11441, c=15; g=3).

- `proton_b_seed_is_odd` — (**L001**) gte_b_proton % 2 = 1; the proton b-seed 11459 is odd
- `neutron_b_seed_is_odd` — (**L002**) gte_b_neutron % 2 = 1; the neutron b-seed 11441 is odd
- `proton_bseed_parity` — (**L003**) (Z × b_proton) % 2 = Z % 2; Z copies of the odd proton seed carry Z's parity
- `beff_parity` — (**L004**) (Z × b_p + N × b_n) % 2 = (Z+N) % 2; composite b_eff parity = mass-number parity A mod 2
- `b_seed_difference` — (**L005**) b_proton − b_neutron = 18 exactly
- `proton_parity_from_bseed` — (**L006**) conjunction of L001 + L003
- `gte_nuclear_parity_rule` — summary conjunction of L001–L005; zero sorry, axioms: propext, Classical.choice, Quot.sound only
- `pairing_sqrt_identity` — algebraic identity 5 × √5 = √125 (Lean-certified form of 5^(3/2) = √125); underpins the 5^(3/2) ≈ 11.18 MeV pairing constant prediction

Graduated to ugp-lean canonical (commit `cc6865f`).

**Universality and self-reference**
- `ugp_is_turing_universal` — UGP substrate Turing-universal via native Rule 110 embedding
- `uwca_sweep_implements_rule110` — UWCA sweep implements Rule 110 exactly
- `uwca_augmented_left_inverse` — UWCA + history stack: backward ∘ forward = id (exact lift)
- `gte_entropy_prefix8_gt_prefix9` — finite coarse Shannon-entropy drop along simulated GTE orbit (ML-9 companion; `GTE.EntropyNonMonotone`)
- `ugp_lawvere_fixed_point` / `ugp_kleene_recursion_thm` / `ugp_rice_theorem` / `ugp_halting_undecidable` — Self-reference layer

**CUP theorems — SM orbit forces Rule 110 (Universality layer)**
- `cup4_parity_uniqueness` — CUP-4: SM generation orbit algebraically forces Rule 110 as the unique vacuum-transparent binary CA rule; `cup1_orbit_uniquely_selects_rule110` (256 rules checked, native_decide)
- `cup11c_universal_mod7_CA_exists` — CUP-11c: a universal mod-7 CA exists; `CUP11ModSeven`
- `fmdl_gen1_is_garden_of_eden` — gen₁ = [1,5,2,2,1] has zero predecessors under f_MDL (native_decide over 7⁵ = 16,807 states)
- `fmdl_unique_uniform_fixed_point` — unique CA fixed point is k=0 (photon); `fmdl_massless_criterion`: massless iff k∈{0,1}
- `cup11b_z7_sum_conservation` — CUP-11b: gen₁ conserves Z₇ sum under fmdl_step5; gen₂/gen₃ do not (characterization of gen₁ as unique conserving generation)
- `orbit_perturbation_destroys_universality` — all 10 single-bit orbit perturbations yield no Rule 110 (orbit isolation with zero tolerance)
- `sm_orbit_complete_causal_isolation` — 6-part master theorem: GoE, unique predecessor chain, chain isolation, sum trajectory 4→4→3→0, GTP-3 structure, max GTP length 3 (all native_decide)
- `hypothesis_b_tape_level` — single Rule 110 Bool tape simultaneously computes both UGP dynamical sectors (1 named axiom)
- `hypothesis_c_psc_forces_universality` — PSC → SM structure → orbit → Rule 110 → Turing-universal (1 named axiom)

**GUT structure — SM observables from N_gen=3, N_fam=5 (`GUTStructure`)**
- `gut_weinberg_structure` — sin²θ_W(GUT) = N_gen/(N_gen+N_fam) = 3/8; holds for all N_gen∈{2,3,4,5}
- `weinberg_angle_closure` — sin²θ_W = 3/13 from palindrome decomposition alone, zero new axioms
- `wolfenstein_lambda_formula` — λ = N_gen²/(2^N_gen × N_fam) = 9/40; PDG: 0.22500 ± 0.00067 (0.000% error)
- `six_quark_neff_complete` — all six quark N_eff values (b_u=9, b_d=5, b_c=275, b_s=186, b_b=8191, b_t) from GTE arithmetic
- `ugp_r110_sm_joint_unification` — joint capstone: GTE arithmetic simultaneously forces Rule 110 and certifies sin²θ_W=3/13, λ=9/40, D=4, GoE chain, photon fixed point
- `gte_spacetime_dimension` — D = N_gen + 1 = 4; `three_dim_fmdl_structure_forced`: D=3 spatial forced by orthogonal Rule 110 slice constraint
- `charge_from_z7_winding` — Q = w*/3 for all SM fermions; `z7_color_subgroup_closed`: Z₃={1,2,4}⊂Z₇* closed
- `hypercharge_u_quark` + `weinberg_angle_from_hypercharge_sum` — U(1)_Y consistency; sin²θ_W=3/13 from hypercharge sum rule
- `gorard_matter_step_kappa_positive` — κ_SD > 0 at all SM generation neighborhoods (matter curves discrete geometry; P36 CatAL)
- `tail_length_strict_ordering` — gen₁ tail > gen₂ tail > gen₃ tail: generation mass hierarchy in CA orbit topology; `neff_not_monotone_in_tail`: naive eigenvalue-mass identification ruled out
- `qcd_beta0_from_gte` — β₀ = (11N_c − 2N_gen N_fam)/3 = 23/3; `orbit_sum_winding_classes`: orbit sum 4→4→3→0 encodes winding-class hierarchy
- `vacuum_ollivier_ricci_flatness` — κ_EE = 0 exactly (vacuum is CA-flat); `fmdl_perfect_code`: f_MDL achieves minimum 14 nonzero neighborhoods
- `eta_B_amplitude_structure` — baryogenesis amplitude exponent structure CatAL (n_EW=1, n_EM=2)
- `ward_mass_cancellation` — Z₇ winding current conserved at every f_MDL vertex (Ward identity)

**N_c=3 from substrate arithmetic (`GTE.NcColorArithmetic`)**
- `nc_eq_3_from_mersenne_gcd` — Route 1: GCD(2^10−1, 2^16−1) = 2^GCD(10,16)−1 = 3; zero custom axioms
- `nc_uniqueness_from_ridge_divisors` — Route 2: N_c is the unique n with n! = GCD(b₂,q₂) = 6; zero custom axioms

**GoE stability, orbit structure, dimensional uniqueness**
- `gen1_is_goe` / `gen2_unique_predecessor` / `sm_chain_fully_isolated` — orbital chain isolation: gen₁ GoE, gen₂/gen₃ unique predecessors, no other state maps to any SM generation (`GoEStabilityHierarchy`)
- `z5_prime_unique_transitivity` — p=5 is the unique prime ≤23 giving SM family transitivity; CA-internal reason for N_fam=5 (`Z5TransitivityUniqueness`)
- `ew_c_staircase` / `ew_c_arithmetic_progression` — W⁺/Z/H⁰ c-values {11,12,13} forced; `ew_higgs_is_scalar_boundary` (`EWBosonStructure`)
- `fmdl_matter_cp_violation` / `fmdl_conj_pair_asymmetry_unique` — f_MDL uniquely selected by MDL minimality + CP asymmetry; `ca_w_plus_is_emission_not_absorption` (`Z7ChargeConjugation`)

**GTE-NEMS Framework Instance and C1 Final Coalgebra**
- `gte_tpc_from_nems_classification` / `gte_tpc_real` — GTE instantiates NemS.Framework; transputation classification fires (1 Cook-bridge axiom; `GTEFrameworkInstance`)
- `gte_d_unique` — GTE D-uniqueness and optimality (`GTEOptimalityInstance`)
- `c1_final_coalgebra_derived` — GTE is the terminal F_PSC coalgebra in PSCSys; zero sorry, zero custom axioms
- `psc_optimal_zero_on_free` — PSCOptimal function must output 0 on all 325 free neighborhoods (`GTEFinalCoalgebra`)

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
