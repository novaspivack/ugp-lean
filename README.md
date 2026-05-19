# ugp-lean

## Research Program

This repository is part of the **Reflexive Reality** research program by [Nova Spivack](https://www.novaspivack.com/).

**What this formalizes:** Machine-checked Lean 4 formalization of the Universal Generative Principle (UGP) — ridge sieve, GTE orbit, Quarter-Lock, UCL Elegant Kernel, mass relations, Turing universality (including UWCA history-lane reversibility), meta-law ML-9 finite entropy companions, and self-reference.  **118 modules, zero sorry on the core proof path** (see `paper/ugp_lean_formalization.tex` for the canonical layer diagram and module list).

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

## Module structure (118 modules; **12 layers** in `paper/ugp_lean_formalization.tex` §Architecture)

| Layer | Count | Modules |
|-------|-------|---------|
| **Core** | 7 | RidgeDefs, MirrorDefs, TripleDefs, SievePredicates, Disconfirmation, RidgeRigidity, MirrorAlgebra |
| **Compute** | 6 | PrimeLock, Sieve, SieveExtended, SieveBelow10, ExclusionFilters, DecidablePredicates |
| **Classification** | 6 | Bounds, TheoremA, TheoremB, RSUC, FormalRSUC, MonotonicStrengthening |
| **GTE** | 24 | Evolution, Orbit, UpdateMap, GeneralTheorems, MersenneGcd, MersenneLadder, PrimeFactorAnalysis, ResonantFactory, MirrorDualConjecture, MirrorShift, UGPPrimes, InertPrimes, AnalyticArchitecture, DSIExport, StructuralTheorems, UniquenessCertificates, GTESimulation, EntropyNonMonotone, FiberBundle, LinearResponse, ScaleConnection, GTBGenerationPrimes, NcColorArithmetic, **NuclearPairing** |
| **Structural** | 19 | QuarterLock, LModelDerivation; *ElegantKernel/*: ChiralityFeature, D5StructuralAxiom, FibonacciHessian, KGen, KGen2, MuTriple, PentagonalUniqueness; *ElegantKernel/Unconditional/*: CyclotomicChain, D5Renormalization, FibonacciPentagonBridge, FullClosure, KConstFullClosure, KGenFullClosure, KLFullClosure, PentagonConstraint, RiccatiFixedPoint |
| **MassRelations** | 25 | *MassRelations* [umbrella], KoideClosedForm, KoideNewtonFlow, KoideAngle, KoideS3DiscreteIdentities, BinaryCascade, PhysicalMasses, SU3FlavorCartan, CartanFlavonPotential, FroggattNielsen, NeutrinoFroggattNielsen, HeavyFermionTower, ClebschGordan, DownRational, UpLeptonCyclotomic, Z2OrbifoldDepth, ClaimCBridge, LeptonMassPrediction, ScaleTransport, SeesawIndex, VVMechanism, VVAllCoefficientsFromNc, CKMTheta23, CKMMixing, **NeutrinoMassRatio** |
| **BraidAtlas** | 7 | ChargeTheorem, CompositeTriples, ChiralitySquaring, ChargeDerivation, CoxeterConductor, CoxeterConductorTowerLaw, EWBosons |
| **Universality** | 12 | Rule110, UWCA, UWCASimulation, UWCAHistoryReversible, UWCAembedsRule110, TuringUniversal, ArchitectureBridge, Z5TransitivityUniqueness, **GTECompilation**, **GTEUniqueness**, **DimensionalSliceUniqueness**, **GTPNeutralDiscrimination** |
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

**Z₇ Sum Conservation — CUP-11b Lean Certification (CUP3DUniqueness §6, 2026-05-18; 9 theorems, 0 sorry)**
- `z7_sum_generation_values` — exact Z₇ sums: gen₁=4, gen₂=4, gen₃=3, vacuum=0 (mod 7)
- `cup11b_z7_orbit_sum_sequence` — orbit sum trajectory under fmdl_step5: 4 → 4 → 3 → 0
- `cup11b_gen1_gen2_sum_equal` — gen₁ and gen₂ have identical Z₇ sums (= 4 mod 7)
- `cup11b_z7_sum_conservation` — **CUP-11b CatAL**: gen₁ conserves Z₇ sum; gen₂ and gen₃ break it
- `cup11b_z7_sum_conservation_unique` — gen₁ is the unique SM generation state conserving Z₇ sum
- `cup11b_gen1_rotations_conserve` — all 5 cyclic rotations of gen₁ conserve Z₇ sum
- `cup11b_z7_sum4_conserving_count` — exactly 10 of 7⁵ states with sum=4 conserve (native_decide)
- `cup11b_alt_rotations_conserve` — secondary orbit [0,2,5,2,2]: all 5 rotations also conserve
- `cup11b_z7_sum4_conserving_characterization` — **complete iff characterization** of sum-4-conserving states: exactly the rotations of gen₁ and [0,2,5,2,2]

**Decay Depth Profile and 7-Step Convergence (CUP3DUniqueness §7a, 2026-05-19; 4 theorems, 0 sorry)**

Physical motivation: The global decay depth of fmdl_step5 on Z₇⁵. The SM orbit achieves depth 3 = N_gen = maximum for non-binary states. The binary sublayer (Rule 110 dynamics) drives deeper chains (up to 7 steps). Python sweep of all 16,807 states confirmed maximum depth = 7; depth distribution: 14,146/1,655/75/10/170/715/35 at depths 1–7.

- `fmdl_orbit_depth_profile` — gen₁/2/3 reach vacuum in exactly 3/2/1 steps; depth ordering (decide)
- `fmdl_universal_7step_convergence` — **all 7⁵ states reach vacuum in ≤7 steps** (native_decide)
- `fmdl_depth7_witness_exact` — [0,0,1,5,2] is a depth-7 witness confirming max=7 (decide)
- `fmdl_max_depth_is_7` — max depth = 7; SM orbit depth 3 = N_gen = max for Z₇ non-binary sector

**Z₇/Z₂ Algebraic Structure — binary incompatibility (CUP3DUniqueness §7b, 2026-05-19; 4 theorems, 0 sorry)**

Physical motivation: Z₇ CA dynamics (CUP-11) are qualitatively richer than binary CAs (CUP-4). The specific winding value Z₇=4 (electron/W⁻) is the counterexample to mod-2 ring homomorphism, explaining why the Z₇ layer cannot be captured by any binary ring map.

- `z7_to_z2_reduction` (def) — the mod-2 reduction φ: Z₇ → Z₂
- `z7_binary_injection_not_surjective` — the injection Z₂→Z₇ (0↦0, 1↦1) is not surjective (decide)
- `z7_binary_not_ring_homomorphism` — φ: Z₇→Z₂ (mod 2) is NOT a ring hom; counterexample (4,4) (decide)
- `z7_binary_not_ring_hom_universal` — no (x,y) pair makes φ a ring hom (decide)
- `z7_z2_incompatible_additive` — combined: injection injective/not-surjective, reduction not additive (CatAL)

**Vacuum Fixed-Point Uniqueness — No False Vacua (CUP3DUniqueness §7c, 2026-05-19; 3 theorems, 0 sorry)**

Physical motivation: The vacuum (all-zeros in Z₇⁵) is the unique fixed point of fmdl_step5. No "false vacuum" states exist: all 16,807 states converge to vacuum within 7 steps (from `fmdl_universal_7step_convergence`). Sharply distinguishes the UGP framework from string-landscape scenarios where metastable vacua proliferate.

- `fmdl_unique_fixed_point` — **No False Vacua**: ∀ v, fmdl_step5 v = v → v = vacuum (native_decide, 16807 cases)
- `fmdl_no_nontrivial_cycles` — every state terminates at vacuum in ≤7 steps; no periodic orbit of period ≥2
- `fmdl_vacuum_is_unique_attractor` — complete 3-part statement: vacuum is fixed + universal attractor + unique fixed point (native_decide)

**Photon as CA Ether — Unique Uniform Fixed Point (CUP3DUniqueness §7d, 2026-05-19; 4 theorems, 0 sorry)**

Physical motivation: The photon (Z₇=0) is the unique winding value that is self-replicating under uniform f_MDL dynamics: fmdl(k,k,k) = k if and only if k = 0. For k=1, Rule 110 forces f(1,1,1)=0≠1; for k≥2, MDL-minimality forces f(k,k,k)=0≠k (free neighborhoods output 0); for k=0, the Rule 110 vacuum constraint gives f(0,0,0)=0=0. The photon IS the CA ether — the background medium itself, not an excitation above it. This closes the structural "why" behind the photon's GTE-triple absence: γ requires zero description length (K_MDL=0) because it is the vacuum.

- `fmdl_nonzero_diagonal_all_zero` — ∀ k≠0 in Z₇, fmdl k k k = 0 (decide)
- `fmdl_unique_uniform_fixed_point` — **Main theorem**: ∀ k : Fin 7, fmdl k k k = k ↔ k = 0 (decide)
- `photon_is_ca_ether` — explicit conjunction: fmdl 0 0 0 = 0 ∧ ∀ k≠0, fmdl k k k ≠ k (decide)
- `fmdl_uniform_fp_uniqueness_count` — Finset.card of uniform fixed points = 1 (decide)

**Minterm Set Uniqueness — CUP-4 extensions (CUP4TotalParity §10–§11, 2026-05-18; 13 theorems, 0 sorry)**

Physical motivation: Among all C(8,5)=56 elementary CA rules of Hamming weight 5, Rule 110 is the unique orbit-satisfier; its minterm set {1,2,3,5,6} is combinatorially forced by the SM generation structure.

- `hammingWeight` (def) — 8-bit popcount (computable)
- `rule110_hamming_weight_5` — Rule 110 has Hamming weight 5 (minterm set has cardinality 5)
- `rule111_hamming_weight_6` — Rule 111 has Hamming weight 6
- `rule110_unique_weight5_orbit_satisfier` — Among all weight-5 rules, Rule 110 is the unique SM orbit-satisfier (no vacuum condition needed: Rule 111 has weight 6)
- `minterm_set_z5_uniqueness` — For any weight-5 orbit-satisfier, the active bit pattern is exactly {1,2,3,5,6}
- `orbit_satisfier_weight_range` — SM orbit forces Hamming weight ∈ {5,6}; no other weight satisfies the orbit
- `orbit_weight_dichotomy` — **Orbit-Weight Dichotomy**: for orbit-satisfying rules, vacuum-transparency (000→0) ↔ Hamming weight 5 exactly
- `weight5_rule_count` — Exactly 56 = C(8,5) rules have Hamming weight 5
- `weight5_orbit_satisfier_count` — Exactly 1 of those 56 satisfies the SM orbit
- `weight5_orbit_satisfiers_eq_singleton` — {weight-5 orbit-satisfiers} = {110} as Finset
- `orbit_satisfiers_finset` — All orbit satisfiers = {110, 111} as Finset (Finset form of cup4_valid_rules)
- `minterm_set_as_finset` — Active neighbourhoods of any weight-5 orbit-satisfier = {1,2,3,5,6} : Finset (Fin 8)
- `rule110_non_minterm_set` — Non-minterms = {0,4,7} = {vacuum, left-only, all-ones} : Finset (Fin 8)

**Orbit Perturbation Catalog — CatAL certification (OrbitPerturbationCatalog.lean, 2026-05-18; 15 theorems, 0 sorry)**

Physical motivation: P28 Table 1 shows computationally that no single-bit perturbation of the SM orbit yields Rule 110 or any other universal CA rule. This module Lean-certifies that result and extends it to a complete global isolation theorem.

- `pertG2_pos0_catalog` — gen₂[0] 0→1: vac-transp satisfying rules iff r∈{234,238} (complete iff, native_decide)
- `pertG2_pos1_catalog` — gen₂[1] 1→0: no satisfying rule exists
- `pertG2_pos2_catalog` — gen₂[2] 0→1: no satisfying rule exists
- `pertG2_pos3_catalog` — gen₂[3] 1→0: no satisfying rule exists
- `pertG2_pos4_catalog` — gen₂[4] 1→0: no satisfying rule exists
- `pertG3_pos0_catalog` — gen₃[0] 1→0: no satisfying rule exists
- `pertG3_pos1_catalog` — gen₃[1] 1→0: satisfying rule iff r=106 (complete iff, native_decide)
- `pertG3_pos2_catalog` — gen₃[2] 1→0: no satisfying rule exists
- `pertG3_pos3_catalog` — gen₃[3] 1→0: no satisfying rule exists
- `pertG3_pos4_catalog` — gen₃[4] 1→0: no satisfying rule exists
- `orbit_perturbation_destroys_universality` — **Main catalog**: all 10 perturbed orbits yield r ≠ 110 (derived from catalog lemmas; zero sorry)
- `rule110_orbit_isolation_gen2` — ∀ g₂ : Fin 5 → Fin 2, Rule 110 maps smGen1 → g₂ iff g₂ = smGen2 (native_decide; 32 cases)
- `rule110_orbit_isolation_gen3` — ∀ g₃ : Fin 5 → Fin 2, Rule 110 maps smGen2 → g₃ iff g₃ = smGen3 (native_decide; 32 cases)
- `rule110_orbit_complete_isolation` — **Deepest result**: ∀ g₂ g₃, (Rule 110: smGen1→g₂→g₃) ↔ (g₂=smGen2 ∧ g₃=smGen3); covers all 1024 possible orbit pairs (native_decide)
- `rule110_orbit_is_globally_isolated` — Any (g₂,g₃)≠(smGen2,smGen3): Rule 110 does not produce orbit smGen1→g₂→g₃

**GoE Orbital Chain Isolation — Z₇ CA stability hierarchy (GoEStabilityHierarchy.lean, 2026-05-18; 9 theorems, 0 sorry)**

Physical motivation: The SM generation orbit gen₁→gen₂→gen₃→vacuum under fmdl_step5 forms a completely isolated linear chain in Z₇⁵ (16,807-state space). Each generation has a unique predecessor (its immediate orbital ancestor), except gen₁ which has none. This certifies the generation stability hierarchy from CA arithmetic alone.

- `fmdl_predecessor_count` (def) — counts predecessor states of any Z₇⁵ configuration under fmdl_step5
- `fmdl_gen1_predecessor_count = 0` — Garden of Eden restated as explicit count (native_decide)
- `fmdl_gen2_predecessor_count = 1` — gen₂ has exactly 1 predecessor (native_decide)
- `fmdl_gen3_predecessor_count = 1` — gen₃ has exactly 1 predecessor (native_decide)
- `fmdl_gen2_unique_predecessor` — **Orbital isolation**: ∀s : Z₇⁵, fmdl_step5(s)=gen₂ ↔ s=gen₁ (native_decide)
- `fmdl_gen3_unique_predecessor` — **Orbital isolation**: ∀s : Z₇⁵, fmdl_step5(s)=gen₃ ↔ s=gen₂ (native_decide)
- `fmdl_orbit_linear_chain` — **Main theorem**: GoE ∧ gen₂←gen₁ only ∧ gen₃←gen₂ only (combines above)
- `fmdl_generation_stability_ordering` — exact predecessor counts 0/1/1 for gen₁/gen₂/gen₃
- `fmdl_gen1_stability_dominance` — gen₁ has strictly fewer predecessors than gen₂ or gen₃

Note: pred(gen₂)=pred(gen₃)=1 (not a strict ordering), but `fmdl_orbit_linear_chain` provides the complete isolation structure which is the deeper result.

**All-Rotations Garden-of-Eden Theorem (GoEStabilityHierarchy §6, 2026-05-19; 2 theorems, 0 sorry)**

Physical motivation: All five first-generation particle families (e⁻, u, d, νR, νL) — obtained as cyclic rotations of gen₁ on the Z₅ ring — are Garden-of-Eden states. The 5-fold rotational symmetry of the SM first generation is exactly reflected in the GoE structure: the family structure IS the ring rotation structure. Connects N_fam=5 to the GoE stability property in a single theorem.

- `fmdl_gen1_all_rotations_are_goe` — **all 5 cyclic rotations of gen₁ have 0 predecessors** (native_decide)
- `fmdl_gen1_all_rotations_no_predecessor` — equivalent non-existence form: no state maps to any rotation of gen₁

**Z₅ Transitivity Uniqueness — CA-internal reason for five families (Z5TransitivityUniqueness.lean, 2026-05-18; 9 theorems, 0 sorry)**

Physical motivation: p = 5 is the unique prime ring size (among primes ≤ 23) for which Rule 110 acts with full transitivity on all cyclic rotations of a Hamming-weight-3 binary vector, producing a 2-step orbit to all-ones. This gives a CA-internal structural reason for the five-family count, converging with P01's algebraic N_fam = 5 derivation.

New reusable infrastructure:
- `rule110Ring p hp` — Rule 110 one-step on a general p-cell periodic ring (generalises `rule110StepPeriodic`)
- `cyclicShiftRing p hp k` — Cyclic shift for arbitrary ring size p
- `hammingWeightRing p v` — Hamming weight via Finset.filter.card

Key theorems:
- `z5_gen2_rotations_to_allones` — All 5 rotations of smGen2 reach smGen3 in 1 Rule 110 step (deepens CUP-9)
- `z5_full_transitivity_smGen1` — All 5 rotations of smGen1 reach smGen3 in 2 steps (proved by CUP-9 composition)
- `smGen1_hamming_weight_3` — smGen1 = [1,1,0,0,1] has Hamming weight 3
- `z5_weight3_full_transitivity_count` — Exactly 5 weight-3 vectors (the smGen1 rotations) are full-transitive on the 5-ring
- `no_hamming3_transitivity_p{3,7,11,13,17,19,23}` — 7 negative theorems: total 2-step isolation for all other small primes (no partial transitivity either)
- `z5_transitivity_uniqueness` — **Main theorem**: combined uniqueness statement over all primes ≤ 23 (positive + all negatives in one conjunction)
- `z5_class2_one_step_allones` — The other weight-3 class ([0,1,0,1,1] rotations) reaches all-ones in exactly 1 step

Note: build time ≈ 426s (native_decide for p=23 enumerates 2^23 vectors; confirmed by Python pre-check in 237ms).

**Dimensional Slice Uniqueness — Rule 110 forced on all d-dimensional slices (DimensionalSliceUniqueness.lean, 2026-05-18; 17 theorems, 0 sorry)**

Physical motivation: CUP-4 proves Rule 110 is uniquely forced by the SM orbit on a 1D 5-cell ring. This raises the objection: "Why 1D? Can a 2D or 3D CA evade Rule 110?" Answer: no. Any d-dimensional binary CA (d ≥ 1) satisfying the SM orbit on axis-aligned 5-cell periodic ring slices must apply Rule 110 on those slices. In the 3D case (f_MDL,3D), all three spatial axes are Rule 110 and P22 forces the cross-dimensional coupling to be Z₇ addition — the full 3D structure is derived, not assumed.

- `DimSliceCA d` / `DimSliceCAMulti d` — abstract d-dimensional CA types carrying axis-aligned slice rules
- `satisfies_sm_orbit` / `is_vacuum_transparent` — the orbit and vacuum conditions
- `dimensional_slice_uniqueness` — **Core theorem**: d-dim CA (d≥1) with orbit + vacuum on slices → slice_rule = 110 (CatAL, zero sorry)
- `dim_slice_rule110_forced` — structure-free form (hypotheses only, no DimSliceCA wrapper)
- `dim_slice_step_is_rule110Periodic` — slice step function equals rule110StepPeriodic
- `dimensional_slice_all_axes_rule110` — all d axes simultaneously forced to Rule 110
- `dim_slice_valid_rule_count` — exactly 1 of 256 rules satisfies orbit + vacuum (native_decide)
- `dim_slice_vacuum_essential` — without vacuum: 2 rules qualify (tightness; native_decide)
- `dim_slice_valid_rules_eq_singleton` — Finset identity: valid rules = {110} (native_decide)
- `two_dim_all_slices_rule110` — d=2 case: both axes forced to Rule 110
- `three_dim_all_slices_rule110` — d=3 case: all three axes forced to Rule 110
- `slice_rule_independent_of_dimension` — forced rule is Rule 110 for any d ≥ 1
- `three_dim_fmdl_structure_forced` — **Deepest result**: 3D f_MDL fully forced: Rule 110 slices (this module) ∧ Z₇ addition coupling (CUP3D.p22_z7_coupling_unique); the 3D structure is derived
- `dimensional_slice_universality` — master summary (count + tightness + singleton identity)

Build time: ~2s (all native_decide proofs are over Fin 256, very fast).

**GTE Compilation and Uniqueness (GTECompilation + GTEUniqueness, 2026-05-18; 12 theorems, 0 sorry)**

Physical motivation: The GTE update map T (particle mass cascade G₁→G₂→G₃) runs as a finite tile program on the Rule 110-universal UWCA substrate (P08, thm:gte-as-uwca). The canonical 1-tile program sigma_gte is the unique lawful UWCA program up to bisimulation (P08, thm:gte_uniqueness) — the universe is forced to run GTE, not just permitted to.

- `sigma_gte` — 1-tile UWCA program encoding the GTE odd-step arithmetic transition
- `gte_compilation_theorem` — `∀ s, uwca_eval sigma_gte s = gte_update_map s` (zero sorry; both sides reduce to the same arithmetic triple by `rfl`)
- `hypothesis_a_complete` — Full Hypothesis A: 4 components simultaneously (fMDL orbit → Rule 110; UWCA substrate → Rule 110; two-layer confluence; GTE compilation)
- `sigma_gte_is_lawful` — sigma_gte is a lawful UWCA program (existence witness)
- `empty_tileset_not_lawful` — the empty tile set cannot implement gte_update_map (lawful programs must have ≥1 tile)
- `IsMinimalProgram` — lawful + no proper shorter sub-program is lawful
- `sigma_gte_is_minimal` — sigma_gte's 1-tile set is minimal
- `gte_uniqueness_up_to_bisimulation` — **Main theorem**: `∀ prog, IsLawfulUWCAProgram prog → UWCABisim prog sigma_gte` (zero sorry; stronger than monograph — no minimality hypothesis needed)
- `lawful_iff_bisim_sigma_gte` — Characterization: `IsLawfulUWCAProgram prog ↔ UWCABisim prog sigma_gte`
- `gte_uniqueness_complete` — 3-part complete statement (existence ∧ minimality ∧ unconditional uniqueness)
- `gte_binary_uniqueness` — At the binary level, Rule 110 is the unique lawful CA rule (from CUP-4)
- `rule110_is_lawful` — Rule 110 satisfies all three UGP orbit constraints (existence closure)

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
**GTE Triple Discrimination of Z₇=0 Neutral Particles — partial closure of the neutral-sector open problem (GTPNeutralDiscrimination.lean, 2026-05-18; 10 theorems, 0 sorry)**

All five Z₇=0 Standard Model particles with GTE triples — three neutrino generations (νₑ, νμ, ντ) and the electroweak bosons (Z, H⁰) — are pairwise distinguishable by their (a, b, c) GTE triples. The Z₇ projection collapses all five to winding class 0, but the full triple preserves discriminating power. A two-level discriminant: b-component (b=1→neutrino sector, b=3→EW sector) as the first level; a-component (neutrino generations) or c-component (EW bosons) as the second. Partially resolves P28 §11.4: photon (γ) has no GTE triple (massless, fixed_zero) and remains open.

- `nu_e_triple`, `nu_mu_triple`, `nu_tau_triple`, `z_boson_triple`, `higgs_triple` — canonical triple constants
- `z7_zero_gte_triples_distinct` — 10 pairwise distinct pairs (CatAL, native_decide)
- `z_boson_b_index_distinct_from_neutrinos` — b=3 separates Z from all neutrinos
- `neutrino_a_indices_distinct` — a-component separates 3 generations
- `neutral_particle_discriminant` — computable discriminant function (labels 0–4)
- `neutral_discriminant_correct` — discriminant assigns unique labels to all 5 particles
- `gte_triple_neutral_discrimination` — **Master theorem**: all three aspects combined (CatAL, zero sorry)

<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429247
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
<!-- NOVA_ZPO_ZENODO_PAPER_BEGIN -->
**Archival paper (Zenodo preprint) (Zenodo):** https://doi.org/10.5281/zenodo.19433539
<!-- NOVA_ZPO_ZENODO_PAPER_END -->
