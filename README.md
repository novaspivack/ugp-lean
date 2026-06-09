# ugp-lean

> **Development sandbox:** This repository (`ugp-lean-exp`) is the active development branch for GTE/UGP Lean formalizations. Work here graduates to [`ugp-lean`](https://github.com/novaspivack/ugp-lean), the canonical public library, at milestone points.

## Separation of concerns

| Repository | Role |
|---|---|
| **ugp-lean-exp** (this repo) → **ugp-lean** | GTE/UGP-specific formalizations: Z₇ algebra, PSC structure, CMCA dynamics, GTE particle spectrum, MDL initial state, RT formula, fermionic statistics, mass predictions |
| [**ugp-physics-lean**](https://github.com/novaspivack/ugp-physics-lean) | Standard physics infrastructure: Lorentzian geometry, Minkowski spacetime, spinor representations, spin-statistics, general relativistic structures — physics facts independent of GTE theory |

**Dependency:** ugp-lean-exp imports ugp-physics-lean for standard physics infrastructure. GTE-specific derivations live here; foundational physics infrastructure that is not GTE-specific belongs in ugp-physics-lean.

---

## Research Program

This repository is part of the **Reflexive Reality** research program by [Nova Spivack](https://www.novaspivack.com/).

**What this formalizes:** Machine-checked Lean 4 formalization of the Universal Generative Principle (UGP) — ridge sieve, GTE orbit, Quarter-Lock, UCL Elegant Kernel, mass relations, Turing universality (including UWCA history-lane reversibility), meta-law ML-9 finite entropy companions, GTE-NEMS framework instantiation, quantum gravity completion, three-tape CMCA, self-reference, W₁ Wasserstein distance scaffold (fully CatAL, zero sorry), GTE polynomial explorations over GF(7)/GF(5) (ground states, period-475, GF(7³) number theory), and GTE WolframModel causal tree (binary tree structure, Horton ratio, botanical correspondence). **307 modules, zero sorry on the core proof path** (two pre-existing sorry placeholders in `GTE/AnalyticArchitecture` are outside the core path; see `paper/ugp_lean_formalization.tex` for the canonical layer diagram and module list). Sech overlap finite-$r$ bounds: **0 sorry** in `PhiMDLFluctuationSpectrum` and `SechOverlapIntegralBounds`; **2 CatA axioms** in `SechOverlapIntegralBounds_bridge.lean` document the mesh→integral bridge.

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

A clean build completes with the standard Mathlib axiom signature `[propext, Classical.choice, Quot.sound]`. Two pre-existing `sorry` placeholders in `GTE/AnalyticArchitecture` (Tenenbaum-class equidistribution) are outside the core proof path and documented in the formalization paper §3.2. The `ContinuumLimit/WassersteinDistance` module is now **fully proved, zero sorry**: `W1_nonneg`, `W1_le_couplingCost`, `W1_ge_of_lipschitz`, `W1_triangle`, `W1_eq_zero_iff`, `W1_attained`, `couplingCostSet_isCompact`, and `couplingCostSet_eq_image` are all machine-certified (graduated).

---

## Module structure (307 modules; **17 layers** in `paper/ugp_lean_formalization.tex` §Architecture)

| Layer | Count | Modules |
|-------|-------|---------|
| **Core** | 7 | RidgeDefs, MirrorDefs, TripleDefs, SievePredicates, Disconfirmation, RidgeRigidity, MirrorAlgebra |
| **Compute** | 6 | PrimeLock, Sieve, SieveExtended, SieveBelow10, ExclusionFilters, DecidablePredicates |
| **Classification** | 6 | Bounds, TheoremA, TheoremB, RSUC, FormalRSUC, MonotonicStrengthening |
| **GTE** | 24 | Evolution, Orbit, UpdateMap, GeneralTheorems, MersenneGcd, MersenneLadder, PrimeFactorAnalysis, ResonantFactory, MirrorDualConjecture, MirrorShift, UGPPrimes, InertPrimes, AnalyticArchitecture, DSIExport, StructuralTheorems, UniquenessCertificates, GTESimulation, EntropyNonMonotone, FiberBundle, LinearResponse, ScaleConnection, GTBGenerationPrimes, NcColorArithmetic, **NuclearPairing** |
| **Structural** | 30 | QuarterLock, LModelDerivation; *ElegantKernel/*: ChiralityFeature, D5StructuralAxiom, FibonacciHessian, KGen2, MuTriple, PentagonalUniqueness; *KGen.lean* deprecated (not imported); *ElegantKernel/Unconditional/*: CyclotomicChain, D5Renormalization, FibonacciPentagonBridge, FullClosure, KConstFullClosure, KGenFullClosure, KLFullClosure, PentagonConstraint, RiccatiFixedPoint, **MasterCertification**, **UCLMassOrdering**, **UCLKoide**, **UCLLogBounds**, **UCLMassOrderingSBounds**, **UCLMassOrderingCoeffBounds**, **UCLMassOrderingBounds**, **UCLMassOrderingBridge**, **UCLMassOrderingCerts**, **UCLMassOrderingInterval**, **UCLMassOrderingDelta**, **UCLCalibration** |
| **MassRelations** | 30 | *MassRelations* [umbrella], KoideClosedForm, KoideNewtonFlow, KoideAngle, KoideS3DiscreteIdentities, BinaryCascade, PhysicalMasses, SU3FlavorCartan, CartanFlavonPotential, FroggattNielsen, NeutrinoFroggattNielsen, HeavyFermionTower, ClebschGordan, DownRational, UpLeptonCyclotomic, Z2OrbifoldDepth, ClaimCBridge, LeptonMassPrediction, ScaleTransport, SeesawIndex, VVMechanism, VVAllCoefficientsFromNc, CKMTheta23, CKMMixing, NeutrinoMassRatio, **NeutrinoSector**, **HiggsQuartic**, **TranscendentalMassBounds**, **QuarkMassNumericalCerts**, **PionMassFromGOR** |
| **BraidAtlas** | 13 | ChargeTheorem, CompositeTriples, ChiralitySquaring, ChargeDerivation, CoxeterConductor, CoxeterConductorTowerLaw, EWBosons, MirrorWindingNumber, EWBosonRHNConnection, **RHNGapTheorem**, **DarkBraidAtlas**, **DarkQuarkCharge**, **DarkGaugeCoupling** |
| **Universality** | 45 | Rule110, UWCA, UWCASimulation, UWCAHistoryReversible, UWCAembedsRule110, TuringUniversal, ArchitectureBridge, CUP4TotalParity, CUP11ModSeven, CUP3DUniqueness, CUP3DPSCUnification, CUP3DPhysicalIncompleteness, TwoLayerConfluence, GTECompilation, GTEUniqueness, GoEHierarchy, **GoEStabilityHierarchy**, **ZGMMesInvariant**, GTEInfTapeEncoding, GTEComputability, HypothesisB, HypothesisBCChain, PSCUniversality, CookRule110Ref, **OrbitPerturbationCatalog**, **Z7ChargeConjugation**, **Z5TransitivityUniqueness**, **DimensionalSliceUniqueness**, **GTPNeutralDiscrimination**, **Z7ZeroSectorDiscriminant**, **Z7InvariantSubsets**, **SMOrbitCausalIsolation**, **EWBosonStructure**, **EWChiralBridge**, **GUTStructure**, **CasimirMasslessEther**, **LawvereZone**, **ChiralPairVA**, **CouplingNoGo**, **ChiralityEigenstates**, **WeakIsospin**, **PhiMDLUniversality**, **ParticlesComputationSpacetimeTrinity**, **FrobeniusChain**, **EWBosonNumericalCerts** |
| **Framework** | 3 | **GTEFrameworkInstance**, **GTEOptimalityInstance**, **GTEFinalCoalgebra** |
| **SelfRef** | 2 | LawvereKleene, RiceHalting |

| **Substrate** | +2 | **PhiMDLFluctuationSpectrum** (Pöschl–Teller, sech integrals; 0 sorry), **SechOverlapIntegralBounds** (+ `_cosh`, `_r5bins`, `_bridge`, `_r11cert`; 0 sorry in main module; 2 CatA axioms in `_bridge`) |
| **Gravity** | +1 | **YukawaOverlapExponent** (DPP tape counting; $\alpha=N_c-1=2$; sech bracket **CatAL-conditional** on bridge axioms; **eta_B_PDG_in_GTE_bracket** Planck bracket CatAL-conditional) + **FKTTCoupling** (kink–top BPS action; **η_B = 6.109×10⁻¹⁰ CatAL unconditional**; `kink_top_coupling_eq_eps_FN`, zero sorry, zero axioms; `phi_mdl_kink_bps_saturation := rfl`) |
| **MassRelations** | +1 | **PMNSNLOCorrection** ($\sin^2\theta_{23}^{\mathrm{NLO}}=209/441$; $2b_{R2}=|F_{21}|+1$; CatAL arithmetic) |
| **QFT** | 2 | **GaugedMassGap**, **ChiralSymmetryBreaking** |
| **Polynomial** | 2 | **PolyExplorations** (39 theorems, zero sorry: ground-state characterization `poly_p_uniform_gs_roots` CatAL; period-475 certs `period_475_returns` + `period_475_is_minimal` CatAL; GF(7³) 19-factor arithmetic; vacuum basin = 52; four-object framework; GF(7) arithmetic coprocessor `p_addition_via_L6` + `p_multiplication_from_two_gates`; PSC-projection bundle `psc_projection_gives_fmdl`; KL divergence certificate `kl_divergence_fmdl_p_nonzero`); **GTECausalTree** (8 theorems, zero sorry: `gte_rulegte_event_count` + `gte_rulegte_ten_generations` certify 1023-node binary tree causal graph for ruleGTE; `perfectTree_horton_ratio` certifies Horton $r_B=2$; `gte_causal_tree_summary` closes P49 §5.3–§5.4) |

Additional modules — **Phase4** (8: DeltaUGP, GaugeCouplings, UCL, PR1, AsymptoticSparsity, PositiveRootTheorem, GaloisProtection, TwoLoopCoefficient), **GaloisStructure** (2), **CyclotomicCompleteness** (2), **PSC** (1: RCCInfiniteFamilies), **TE22** (1: ScanCertificate), **Papers** (2), **Instance** (1), **Conjectures** — per the formalization paper: `Phase4.GaloisProtection`, `TwoLoopCoefficient`, modules under `GaloisStructure.*` and `CyclotomicCompleteness.*`, and `TE22` carry fully mechanized statements where the paper claims zero sorry; `Papers` and `Instance` are chiefly citable stubs and bridges; `Conjectures` records resolved and open claims; `Phase4` also mixes stubs (e.g. UCL, PR1 presentation) with the precision theorems above.

**Non-circularity:** Core/ may not import Compute/. See [docs/DESIGN.md](docs/DESIGN.md).

---

## Recent additions

**229 net-new theorems** (zero sorry on all listed results except 2 disclosed **CatA** axioms in `SechOverlapIntegralBounds_bridge.lean`; full inventory in `docs/THEOREMS.md` §Recent additions):

| Area | Module | Highlights |
|------|--------|------------|
| **UCL master cert** | `ElegantKernel/Unconditional/MasterCertification` | `elegant_kernel_full_certification` — all 9 EK coefficients CatAL; Tier 2 mass ordering; Tier 3 Koide $Q=2/3$ |
| **Quarter-Lock** | `QuarterLock` | `thm_quarter_lock_catal`: $k_M=-\varphi/2+7/2048$ |
| **PMNS** | `MassRelations/NeutrinoSector` | $\sin^2\theta_{12}=4/13$, $\sin^2\theta_{23}=19/42$, $\sin\theta_{13}=11/73$, $\delta_{\rm CP}=8\pi/7$, $J<0$ |
| **Higgs quartic** | `MassRelations/HiggsQuartic` | $\lambda=\dfrac{\varphi}{4\pi}(1+({\rm IPT}-1)/27)$; $0.12<\lambda<0.14$ |
| **Yukawa vertex / η_B** | `Substrate/PhiMDLFluctuationSpectrum`, `Substrate/SechOverlapIntegralBounds_*`, `Gravity/YukawaOverlapExponent`, `Physics/FKTTCoupling` | Pöschl–Teller + $\int\mathrm{sech}^3=\pi/2$; $\alpha=2$ CatAD; $f_1 f_2=1/3025$ suppression (sech bracket CatAL-conditional; 2 CatA axioms for mesh→integral bridge). **FKTT route: η_B = 6.109×10⁻¹⁰ (+0.15σ vs PDG) CatAL unconditional** — `kink_top_coupling_eq_eps_FN`, `fktt_coupling_bundle`, `bps_per_tape_action_eq_pi_over_Nc` (all zero sorry, zero axioms); T₁₁=0 by `rfl` (definitional BPS saturation). |
| **FGCI** | `Universality/FrobeniusChain` | $F(3)=G(3)=73$ unique at $N_c=3$; chain $\{7,73\}$; $b_{L2}=2N_c|Z_7|$ |
| **Dark baryon** | `Universality/GUTStructure` | $q_{\rm dark}/6=1/N_c$; dilution $2/6=1/3$; $D_{\rm top}=\exp(-1/N_c)$ via Z₇ transitivity |
| **Quark \& EW intervals** | `MassRelations/TranscendentalMassBounds`, `QuarkMassNumericalCerts`, `Universality/EWBosonNumericalCerts` | Six-quark PDG bands (CatAD); $M_W$ CatAL; $M_Z$, $\sin^2\theta_W$ threshold CatAD |
| **GTE Polynomial explorations** | `Polynomial/PolyExplorations` | 39 theorems, zero sorry: `poly_p_uniform_gs_roots` (ground states $\{0,1,5\}$, decide, CatAL); `period_475_returns` + `period_475_is_minimal` + `phi25_order_19_on_cycle` (period-475 certs, native_decide); `nineteen_divides_7cube_minus_1` + `ord_19_seven_equals_3` + `nineteen_unique_prime_in_7cube_minus_1` (GF(7³) 19-factor arithmetic); `poly_p_vacuum_basin_card_eq_52` (52-state basin); `four_object_GTE_pairwise_distinct` (p, $f_{\rm MDL}$, T distinct); `p_addition_via_L6` + `p_multiplication_from_two_gates` (GF(7) arithmetic coprocessor: 1-gate addition, 2-gate multiplication); `kl_divergence_fmdl_p_nonzero` (certifies $p\neq f_{\rm MDL}$ at $(1,1,5)$, CatAL); `psc_projection_gives_fmdl` bundle (PSC-projection characterisation, CatAL). |
| **GTE WolframModel causal tree** | `Polynomial/GTECausalTree` | 8 theorems, zero sorry: `perfectTree_numNodes` ($2^n-1$ nodes, induction); `perfectTree_height` ($n$); `perfectTree_numLeaves` ($2^n$); `gte_rulegte_event_count` ($\sum_{k=0}^{n-1}2^k=2^n-1$); `gte_rulegte_ten_generations` (decide: 1023 at depth 10); `perfectTree_horton_ratio` ($r_B=2$ at all levels); `gte_causal_tree_horton_ratio_eq_two` (decide); `gte_causal_tree_summary` (1023 nodes, height 10, 1024 leaves). Certifies P49 §5.3 WolframModel causal graph and §5.4 botanical correspondence. |

$D_{\rm top}=\exp(-1/N_c)$: machine-certified CatAL via Z₇ group transitivity (`d_top_derivation_chain_catal`, zero sorry). No dilute instanton gas approximation needed.

---

## Key theorems

**Core structural chain**
- `ridgeSurvivors_10` — At n=10, survivors = {(24,42),(42,24)}
- `theoremA_general` — ∀n, UnifiedAdmissibleAt n t → t ∈ CandidatesAt n
- `rsuc_theorem` — Residual Seed Uniqueness; MDL selects Lepton Seed (1,73,823)
- `canonical_orbit_triples` — (1,73,823) → (9,42,1023) → (5,275,65535)
- `quarterLockLaw` — k_M = k_gen2 + ¼k_L²

**Claim C — Formal proof (MassRelations.ClaimCBridge)**
- `claim_C_formal` — cascadeState g = angleToAlpha1(ω₁) · 2^g + π/8; formal Claim C proved by combining Claim A (π/6 = SU(3) Weyl bisector) and Claim B (binary cascade doubles per generation); zero hypotheses, zero sorry
- `k_gen2_encodes_double_weyl_bisector` — k_gen2 = −φ · cos(2 · Weyl bisector); bridges Elegant Kernel to SU(3) geometry
- `pentagon_hexagon_TT_unified_bridge` — all five structural facts simultaneously: TT formula, Weyl bisector, k_gen2 = −φcos(2Weyl), k_gen = φcos(π/10), Pentagon-Hexagon Bridge

**UCL Unconditional Closure (ElegantKernel layer)**
- `thm_ucl2_fully_unconditional` — k_gen = φ·cos(π/10) = √(φ²−1/4) ≈ 1.5388; derived zero-hypothesis via Quarter-Lock substitution on Fibonacci char poly (replaces outdated conditional π/2 value in `KGen.lean`)
- `k_gen2_eq_neg_phi_half` — k_gen2 = −φ/2 = cos(4π/5); unique negative root of the pentagon quadratic 4k²+2k−1=0
- `k_gen_pentagon_hexagon_bridge` — k_gen + k_gen2 = φ·(cos(π/10) − cos(π/3)); bridges D₅ pentagonal (Fibonacci) and D₆ hexagonal (SU(3) Weyl) symmetries; proved from `thm_ucl2_fully_unconditional` + `k_gen2_eq_neg_phi_half` + Mathlib `cos_pi_div_three`
- `full_closure_summary` — All five UCL constraints simultaneously satisfiable; complete Elegant Kernel closure holds unconditionally

**Mass Relations (MassRelations layer)**
- `koide_iff_twoS_sq_eq_threeN` — Koide relation ↔ (2S)² = 3N algebraic normal form
- `koide_solved_form_root` — Koide-satisfying third mass in cyclotomic-12 closed form
- `newton_flow_fixes_null_cone` — Newton flow fixes every point on the Koide null cone
- `newton_flow_swap12_equivariant` / `newton_flow_rot123_equivariant` — Full S₃-equivariance of the Newton flow
- `cascadeState_closed_form` — Binary cascade closed form b_g = 2^{g−1} b₁
- `koidePredictedMTau_pos` — Predicted m_τ from (m_e, m_μ) is strictly positive

**CDM Mechanism — CKM Mixing (MassRelations.CKMMixing; 11 theorems, 0 sorry)**
- `cabibbo_effective_charge` — Δa_eff = α_d = 13/9 (effective FN charge = VV coefficient)
- `cabibbo_charge_from_GUT` — Δa_eff = 1 + rank(SU(5))/N_c² (GUT group-theory origin)
- `cabibbo_vev_formula` — |V_us|_CDM = (ε₁)^(α_d) = exp(−13π/27) ≈ 0.2203 (1.9% off PDG)
- `fn_vv_correction_additive` — KEY BRIDGE: fnMixChargeDown(α_d) = fnMixChargeDown(1) + (α_d−1); VV GUT coefficient shifts bare FN charge additively
- `fn_diagonalization_vv_bridge` — fnMixChargeDown(α_d) × log(ε₁) = −13π/27 (connects FN model to CDM structural log)
- `fn_cdm_physical_sorry` — Algebraic identity: log(cabibbo_structural_prediction) = fnMixChargeDown(α_d) × log(ε₁); proved via `Real.log_exp` (zero sorry)

**Neutrino Mass Ratio — Seesaw Arithmetic (MassRelations.NeutrinoMassRatio; 5 theorems, 0 sorry)**
- `fn_texture_gives_seesaw_exponent` — FN charge pair (q₁,q₂)=(3,2) gives exponent 3 + 2/9 = 29/9 = nuSeesawExponent
- `seesaw_ratio_independent_of_MR` — Mass-squared ratio (m₂²−m₁²)/(m₃²−m₁²) is independent of M_R (algebraic, abstract)
- `neutrino_mass_ratio_coarse_bound` — Certified coarse bound: 0.029 < R < 0.030 where R = (11^{58/9}−5^{58/9})/(19^{58/9}−5^{58/9}) ≈ 0.02936
- `neutrino_mass_ratio_tight_bound` — Full tight bound |R − 0.02936| < 0.0001; zero sorry via unit-width integer bounds on b^(58/9)
- `neutrino_mass_ratio_within_1pct_of_nufit` — |R − 0.02951| < 0.01 × 0.02951; within 1% of NuFIT 6.0 central value; zero sorry

**GTE Nuclear Parity — NuclearPairing (UgpLean.GTE.NuclearPairing; 8 theorems, 0 sorry)**

Physical motivation: GTE-theoretic basis for the F10 proton-parity stability feature and the 5^(3/2) = 11.18 MeV pairing constant prediction (paper P03). Proton: (a=5, b=11459, c=15; g=3). Neutron: (a=5, b=11441, c=15; g=3).

- `proton_b_seed_is_odd` — (**L001**) gte_b_proton % 2 = 1; the proton b-seed 11459 is odd
- `neutron_b_seed_is_odd` — (**L002**) gte_b_neutron % 2 = 1; the neutron b-seed 11441 is odd
- `proton_bseed_parity` — (**L003**) (Z × b_proton) % 2 = Z % 2; Z copies of the odd proton seed carry Z's parity
- `beff_parity` — (**L004**) (Z × b_p + N × b_n) % 2 = (Z+N) % 2; composite b_eff parity = mass-number parity A mod 2
- `b_seed_difference` — (**L005**) b_proton − b_neutron = 18 exactly
- `proton_parity_from_bseed` — (**L006**) conjunction of L001 + L003
- `gte_nuclear_parity_rule` — summary conjunction of L001–L005; zero sorry, axioms: propext, Classical.choice, Quot.sound only
- `pairing_sqrt_identity` — algebraic identity 5 × √5 = √125 (Lean-certified form of 5^(3/2) = √125); underpins the 5^(3/2) ≈ 11.18 MeV pairing constant prediction

Machine-certified and included in the canonical library.

**Z₇ Sum Conservation — CUP-11b Lean Certification (CUP3DUniqueness §6; 9 theorems, 0 sorry)**
- `z7_sum_generation_values` — exact Z₇ sums: gen₁=4, gen₂=4, gen₃=3, vacuum=0 (mod 7)
- `cup11b_z7_orbit_sum_sequence` — orbit sum trajectory under fmdl_step5: 4 → 4 → 3 → 0
- `cup11b_gen1_gen2_sum_equal` — gen₁ and gen₂ have identical Z₇ sums (= 4 mod 7)
- `cup11b_z7_sum_conservation` — **CUP-11b CatAL**: gen₁ conserves Z₇ sum; gen₂ and gen₃ break it
- `cup11b_z7_sum_conservation_unique` — gen₁ is the unique SM generation state conserving Z₇ sum
- `cup11b_gen1_rotations_conserve` — all 5 cyclic rotations of gen₁ conserve Z₇ sum
- `cup11b_z7_sum4_conserving_count` — exactly 10 of 7⁵ states with sum=4 conserve (native_decide)
- `cup11b_alt_rotations_conserve` — secondary orbit [0,2,5,2,2]: all 5 rotations also conserve
- `cup11b_z7_sum4_conserving_characterization` — **complete iff characterization** of sum-4-conserving states: exactly the rotations of gen₁ and [0,2,5,2,2]

**Decay Depth Profile and 7-Step Convergence (CUP3DUniqueness §7a; 4 theorems, 0 sorry)**

Physical motivation: The global decay depth of fmdl_step5 on Z₇⁵. The SM orbit achieves depth 3 = N_gen = maximum for non-binary states. The binary sublayer (Rule 110 dynamics) drives deeper chains (up to 7 steps). Python sweep of all 16,807 states confirmed maximum depth = 7; depth distribution: 14,146/1,655/75/10/170/715/35 at depths 1–7.

- `fmdl_orbit_depth_profile` — gen₁/2/3 reach vacuum in exactly 3/2/1 steps; depth ordering (decide)
- `fmdl_universal_7step_convergence` — **all 7⁵ states reach vacuum in ≤7 steps** (native_decide)
- `fmdl_depth7_witness_exact` — [0,0,1,5,2] is a depth-7 witness confirming max=7 (decide)
- `fmdl_max_depth_is_7` — max depth = 7; SM orbit depth 3 = N_gen = max for Z₇ non-binary sector

**Z₇/Z₂ Algebraic Structure — binary incompatibility (CUP3DUniqueness §7b; 4 theorems, 0 sorry)**

Physical motivation: Z₇ CA dynamics (CUP-11) are qualitatively richer than binary CAs (CUP-4). The specific winding value Z₇=4 (electron/W⁻) is the counterexample to mod-2 ring homomorphism, explaining why the Z₇ layer cannot be captured by any binary ring map.

- `z7_to_z2_reduction` (def) — the mod-2 reduction φ: Z₇ → Z₂
- `z7_binary_injection_not_surjective` — the injection Z₂→Z₇ (0↦0, 1↦1) is not surjective (decide)
- `z7_binary_not_ring_homomorphism` — φ: Z₇→Z₂ (mod 2) is NOT a ring hom; counterexample (4,4) (decide)
- `z7_binary_not_ring_hom_universal` — no (x,y) pair makes φ a ring hom (decide)
- `z7_z2_incompatible_additive` — combined: injection injective/not-surjective, reduction not additive (CatAL)

**Vacuum Fixed-Point Uniqueness — No False Vacua (CUP3DUniqueness §7c; 3 theorems, 0 sorry)**

Physical motivation: The vacuum (all-zeros in Z₇⁵) is the unique fixed point of fmdl_step5. No "false vacuum" states exist: all 16,807 states converge to vacuum within 7 steps (from `fmdl_universal_7step_convergence`). Sharply distinguishes the UGP framework from string-landscape scenarios where metastable vacua proliferate.

- `fmdl_unique_fixed_point` — **No False Vacua**: ∀ v, fmdl_step5 v = v → v = vacuum (native_decide, 16807 cases)
- `fmdl_no_nontrivial_cycles` — every state terminates at vacuum in ≤7 steps; no periodic orbit of period ≥2
- `fmdl_vacuum_is_unique_attractor` — complete 3-part statement: vacuum is fixed + universal attractor + unique fixed point (native_decide)

**Measurement Orbit Uniqueness and Three-Level MDL Bundles — R11 (CUP3DUniqueness; 6 theorems, 0 sorry)**

Physical motivation: The SM generation orbit GEN₁→GEN₂→GEN₃→VAC is not just one valid trajectory among many — it is the *only* PSC-admissible 3-step trajectory from GEN₁. This certifies the discrete measurement mechanism of P51: each generation corresponds to a unique forced step in the fmdl orbit. GEN₂ and GEN₃ share positional-equality topology (a,b,a,c,a), distinguishing the two intermediate states algebraically.

- `gen2_outer_positions_constant` — GEN₂ outer positions equal: $v_0=v_2=v_4$ in the 5-cell orbit ring (decide)
- `gen3_outer_positions_constant` — GEN₃ outer positions equal: $v_0=v_2=v_4$ in the 5-cell orbit ring (decide)
- `gen2_gen3_topology_degenerate` — GEN₂ and GEN₃ share (a,b,a,c,a) topology; outer = outer, inner ≠ outer (decide)
- `fmdl_orbit_is_unique_psc_trajectory` — **Orbit uniqueness**: GEN₁→GEN₂→GEN₃→VAC is the uniquely forced 3-step trajectory from GEN₁; step-uniqueness at each stage + Garden-of-Eden property (decide + prior theorems)
- `mdl_three_level_orbit_bundle` — Level 1→2 bundle: the three orbit steps fmdl_step5(GEN_k) = GEN_{k+1}
- `mdl_three_level_polynomial_bundle` — Partial OP4 bundle: orbit steps ∧ SRRG φ diagonal fixed point (bridge to SRRGCABridge)

**Photon as CA Ether — Unique Uniform Fixed Point (CUP3DUniqueness §7d; 4 theorems, 0 sorry)**

Physical motivation: The photon (Z₇=0) is the unique winding value that is self-replicating under uniform f_MDL dynamics: fmdl(k,k,k) = k if and only if k = 0. For k=1, Rule 110 forces f(1,1,1)=0≠1; for k≥2, MDL-minimality forces f(k,k,k)=0≠k (free neighborhoods output 0); for k=0, the Rule 110 vacuum constraint gives f(0,0,0)=0=0. The photon IS the CA ether — the background medium itself, not an excitation above it. This closes the structural "why" behind the photon's GTE-triple absence: γ requires zero description length (K_MDL=0) because it is the vacuum.

- `fmdl_nonzero_diagonal_all_zero` — ∀ k≠0 in Z₇, fmdl k k k = 0 (decide)
- `fmdl_unique_uniform_fixed_point` — **Main theorem**: ∀ k : Fin 7, fmdl k k k = k ↔ k = 0 (decide)
- `photon_is_ca_ether` — explicit conjunction: fmdl 0 0 0 = 0 ∧ ∀ k≠0, fmdl k k k ≠ k (decide)
- `fmdl_uniform_fp_uniqueness_count` — Finset.card of uniform fixed points = 1 (decide)

**Minterm Set Uniqueness — CUP-4 extensions (CUP4TotalParity §10–§11; 13 theorems, 0 sorry)**

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

**Orbit Perturbation Catalog — CatAL certification (OrbitPerturbationCatalog.lean; 15 theorems, 0 sorry)**

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

**GoE Orbital Chain Isolation — Z₇ CA stability hierarchy (GoEStabilityHierarchy.lean; 9 theorems, 0 sorry)**

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

**All-Rotations Garden-of-Eden Theorem (GoEStabilityHierarchy §6; 2 theorems, 0 sorry)**

Physical motivation: All five first-generation particle families (e⁻, u, d, νR, νL) — obtained as cyclic rotations of gen₁ on the Z₅ ring — are Garden-of-Eden states. The 5-fold rotational symmetry of the SM first generation is exactly reflected in the GoE structure: the family structure IS the ring rotation structure. Connects N_fam=5 to the GoE stability property in a single theorem.

- `fmdl_gen1_all_rotations_are_goe` — **all 5 cyclic rotations of gen₁ have 0 predecessors** (native_decide)
- `fmdl_gen1_all_rotations_no_predecessor` — equivalent non-existence form: no state maps to any rotation of gen₁

**Z₅ Transitivity Uniqueness — CA-internal reason for five families (Z5TransitivityUniqueness.lean; 9 theorems, 0 sorry)**

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
- `z5_w3_t1_full_transitivity` — **New (§8)**: all 5 rotations of [0,1,0,1,1] reach all-ones in t=1 step (full Z₅ transitivity at Hamming weight 3, step 1)
- `z5_w3_exclusive_among_primes` — weight-3 full-transitivity under Rule 110 is exclusive to p=5 among primes ≤ 11, at t=1 or t=2 (§8)
- `p7_w4_t1_full_transitivity` — p=7's unique full-transitive class: weight-4 vector [0,1,0,1,0,1,1] reaches all-ones in 1 step (§8)

Full (p,w,t) transitivity spectrum: Python sweep confirms p=5 uniquely weight-3-transitive; p=7 hits only at weight 4. Note: build time ≈ 442s (native_decide for §8 primes; §5 positives fast, §8 p=11 native_decide largest).

**Dimensional Slice Uniqueness — Rule 110 forced on all d-dimensional slices (DimensionalSliceUniqueness.lean; 17 theorems, 0 sorry)**

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

**GTE Compilation and Uniqueness (GTECompilation + GTEUniqueness; 12 theorems, 0 sorry)**

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
- `minimal_lawful_has_card_one` — any minimal lawful UWCA program has exactly 1 tile (= sigma_gte; §5)
- `UWCAIsomorphic` — definition: same tile count + bisimulation (§5)
- `gte_uniqueness_isomorphism` — **Isomorphism theorem**: any minimal lawful UWCA is isomorphic to sigma_gte (Myhill-Nerode; §5)
- `gte_isomorphism_symmetric` — any two minimal lawful programs are mutually isomorphic (§5)

**Universality and self-reference**
- `ugp_is_turing_universal` — UGP substrate Turing-universal via native Rule 110 embedding
- `uwca_sweep_implements_rule110` — UWCA sweep implements Rule 110 exactly
- `uwca_augmented_left_inverse` — UWCA + history stack: backward ∘ forward = id (exact lift)
- `gte_entropy_prefix8_gt_prefix9` — finite coarse Shannon-entropy drop along simulated GTE orbit (ML-9 companion; `GTE.EntropyNonMonotone`)
- `ugp_lawvere_fixed_point` / `ugp_kleene_recursion_thm` / `ugp_rice_theorem` / `ugp_halting_undecidable` — Self-reference layer

**GTE-NEMS Framework Instance (Framework.GTEFrameworkInstance; zero sorry, one bridge axiom)**
- `GTEFramework` — GTE-Möbius architecture as `NemS.Framework` over `BeableState`
- `gte_not_categorical` — vacuum and gen₁ disagree on record query 0
- `gte_nems` / `GTEPSCBundle` — NEMS + determinacy PSC bundle
- `GTEDiagonalCapable` — ASR via vacuum reachability + Cook encoding (bridge axiom `gte_partrec_eval_iff_fmdl_phi`)
- `gte_tpc_from_nems_classification` / `gte_tpc_real` — transputation classification on the GTE substrate

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
**GTE Triple Discrimination of Z₇=0 Neutral Particles — partial closure of the neutral-sector open problem (GTPNeutralDiscrimination.lean; 10 theorems, 0 sorry)**

All five Z₇=0 Standard Model particles with GTE triples — three neutrino generations (νₑ, νμ, ντ) and the electroweak bosons (Z, H⁰) — are pairwise distinguishable by their (a, b, c) GTE triples. The Z₇ projection collapses all five to winding class 0, but the full triple preserves discriminating power. A two-level discriminant: b-component (b=1→neutrino sector, b=3→EW sector) as the first level; a-component (neutrino generations) or c-component (EW bosons) as the second. Partially resolves P28 §11.4: photon (γ) has no GTE triple (massless, fixed_zero) and remains open.

- `nu_e_triple`, `nu_mu_triple`, `nu_tau_triple`, `z_boson_triple`, `higgs_triple` — canonical triple constants
- `z7_zero_gte_triples_distinct` — 10 pairwise distinct pairs (CatAL, native_decide)
- `z_boson_b_index_distinct_from_neutrinos` — b=3 separates Z from all neutrinos
- `neutrino_a_indices_distinct` — a-component separates 3 generations
- `neutral_particle_discriminant` — computable discriminant function (labels 0–4)
- `neutral_discriminant_correct` — discriminant assigns unique labels to all 5 particles
- `gte_triple_neutral_discrimination` — **Master theorem**: all three aspects combined (CatAL, zero sorry)

**Rule 111 Near-Miss — Vacuum Uniquely Selects Rule 110 (DimensionalSliceUniqueness §4b; 2 theorems, 0 sorry)**

Physical motivation: Spec 07 proved exactly 2 of 256 binary CA rules satisfy the SM orbit without vacuum transparency. This section names Rule 111 as the unique near-miss and gives the full Finset identity. Vacuum transparency (f(0,0,0)=0) is the single physical criterion that selects Rule 110 from the pair {110, 111}.

- `vacuum_selects_rule110_over_rule111` — 4-part Finset identity: orbit rules without vacuum = {110,111} exactly; Rule 110 passes vacuum transparency; Rule 111 fails; orbit rules with vacuum = {110} (native_decide, CatAL)
- `rule111_orbit_valid_no_vacuum` — Rule 111 is the unique near-miss; all orbit-satisfying rules are exactly {110,111} and only Rule 110 also satisfies vacuum transparency (native_decide, CatAL)

**GTP-3 Z₇-Sum Trajectory Uniqueness (GoEStabilityHierarchy §9; 3 theorems, 0 sorry)**

Physical motivation: Every GoE-rooted 3-step terminating path (GTP-3) in Z₇⁵ under f_MDL has the universal Z₇-sum fingerprint 4→4→3. Python exhaustive search confirms exactly 5 GTP-3 chains — all cyclic rotations of gen₁ — and distinguishes them from the alt orbit [0,2,5,2,2] class (depth-2, GTP-2).

- `gtp3_sum_trajectory_of_gen1_rotations` — all 5 gen₁ rotations have Z₇-sum trajectory 4→4→3 (decide, CatAL)
- `gtp3_alt_depth_is_two` — alt orbit [0,2,5,2,2] rotations reach vacuum in exactly 2 steps (GTP-2, not GTP-3) (decide, CatAL)
- `gtp3_sum_trajectory_master` — joint master theorem: GTP-3 fingerprint 4→4→3 vs GTP-2 alt class (CatAL)

**Orbit Sum Trajectory Invariance (CUP3DUniqueness §9; 3 theorems + 2 definitions, 0 sorry)**

Physical motivation: The Z₇-sum sequence 4→4→3→0 across the generation cascade is determined by the 15 orbit-constraint output values and holds for ALL 7^328 orbit-admissible functions — not just fmdl. Any CA consistent with the SM particle spectrum exhibits the same sum trajectory.

- `apply_f_ring` — definition: generalized Z₇ ring step for arbitrary f: Fin 7 → Fin 7 → Fin 7 → Fin 7
- `is_orbit_admissible` — definition: f maps gen₁→gen₂, gen₂→gen₃, gen₃→vacuum (orbit-producing predicate)
- `fmdl_is_orbit_admissible` — fmdl satisfies orbit-admissibility (decide, CatAL)
- `orbit_sum_trajectory_invariant` — for any orbit-admissible f: z7_sum trajectory of orbit images is 4→3→0 (rw+decide, CatAL)
- `orbit_sum_full_trajectory` — complete 4-step trajectory 4→4→3→0 for all orbit-admissible f (CatAL)

**GEN2/GEN3 Topological Degeneracy (CUP3DUniqueness R14; 3 theorems, 0 sorry)**

Physical motivation: The WolframModel causal graph of the GTE update rule (ruleGTE) exhibits binary branching, with GEN2 and GEN3 states arising at interior levels of the fractal binary tree. Both states share the structural topology (a,b,a,c,a): positions {0,2,4} carry one repeated winding value, positions {1,3} carry distinct minority values. This topological degeneracy explains the symmetric branching structure of the ruleGTE causal graph at those levels, and provides the formal GTE-side mechanism for the botanical L-system isomorphism (R14, 2026-06-08).

- `gen2_outer_positions_constant` — fmdl_gen2_z7[0]=fmdl_gen2_z7[2]=fmdl_gen2_z7[4] (decide, CatAL)
- `gen3_outer_positions_constant` — fmdl_gen3_z7[0]=fmdl_gen3_z7[2]=fmdl_gen3_z7[4] (decide, CatAL)
- `gen2_gen3_topology_degenerate` — both GEN2 and GEN3 have identical positional-equality pattern (a,b,a,c,a); outer positions equal, inner positions distinct (decide, CatAL)

**Z₅ Ring Equivariance of fmdl (CUP3DUniqueness §10; 1 definition + 1 theorem, 0 sorry)**

Physical motivation: The five SM particle families [e⁻, u, d, νR, νL] in the 5-cell ring are related by Z₅ rotational symmetry. PSC Presentation Invariance (PI) requires that observable quantities be invariant under bijections preserving physical structure; the Z₅ cyclic rotation group acts on the 5-cell ring, and fmdl treats all 5 positions identically. This is the exact discrete gauge symmetry of the ring geometry derived from PI. Note: fmdl is NOT equivariant under Z₇ additive shifts (2030 counterexamples); Z₅ rotational symmetry is the correct and complete ring gauge symmetry.

- `cyclic_rotate` — definition: cyclic rotation of a 5-cell Z₇ ring by k positions (generalizes rotate5 from CUP4TotalParity to Fin 7 cells)
- `fmdl_z5_equivariant` — **Main theorem**: ∀ (v : Fin 5 → Fin 7) (k : Fin 5), fmdl_step5(cyclic_rotate v k) = cyclic_rotate(fmdl_step5 v) k; zero failures over 7⁵ × 5 = 84,035 cases (native_decide, CatAL)

**SU(5) GUT Weinberg Angle, f_MDL Structural Bridge, CKM Count Theorem, CKM Quark N_eff Formulas, b_sum = 390 Weinberg Factorization, Z₂ Longitudinal Mode MDL Universality, Coupling Ratio Duality, smGen1 SU(5) Projector, Mersenne Prime Structure, CP Irrationality Chain, Joint Selection Theorem, GTE Master Formula, Weinberg Physical Bridge, Weinberg Three-Tier Prediction, Bidirectional Unification Summary, MDL Robustness / Z₇ Free Minterm Count, Z₂ Longitudinal Universality Structural Chain, Chern-Simons Level k=30, Mersenne Cascade Discriminator 12→2, f_MDL Perfect Code §36, Alpha Chain §38, and W⁺ Decay Lemma §39 (GUTStructure.lean; 192 theorems + 23 definitions, 0 sorry)**

Physical motivation: The GTE structural constants N_gen = 3 (Rule 110 orbit depth, CatAL) and N_fam = 5 (Z₅ family ring size, CatAL) satisfy the arithmetic identity N_gen + N_fam = 2^N_gen (3 + 5 = 8 = 2³). This implies that the GUT-scale Weinberg angle sin²θ_W(M_GUT) = N_gen/(N_gen + N_fam) = N_gen/2^N_gen = 3/8 — agreeing exactly with the standard SU(5) GUT prediction. The denominator then increases to c_H = 13 at M_Z by exactly N_fam = 5. A new structural identity (§9) connects the CA dynamics layer: the MDL-minimal CA function f_MDL produces nonzero output on exactly c_H + 1 = 14 of the 343 possible neighborhoods.

*§1–§8: GUT Weinberg structure*
- `n_gen`, `n_fam` — GTE structural constants (3, 5)
- `ngen_plus_nfam_eq_pow2` — N_gen + N_fam = 2^N_gen (norm_num, CatAL)
- `gut_weinberg_angle_ngen_nfam` — (N_gen:ℚ)/(N_gen+N_fam) = 3/8 (norm_num, CatAL)
- `gut_weinberg_angle_pow2` — (N_gen:ℚ)/2^N_gen = 3/8 (norm_num, CatAL)
- `su5_dim_matches_nfam` — N_fam = 5 = dim(SU(5) fundamental) (rfl, CatAL)
- `su5_5plet_partition` — N_fam−N_gen=2 ∧ N_gen+2=N_fam (3+2 partition) (norm_num, CatAL)
- `running_shift_equals_nfam` — c_H − 2^N_gen = N_fam = 5 (norm_num, CatAL)
- `running_shift_denominator` — N_gen+2·N_fam = c_H ∧ shift=N_fam (norm_num, CatAL)
- `gut_to_ew_denominator_chain` — 3/8 (GUT) ∧ 3/13 (EW) (norm_num, CatAL)
- `gut_weinberg_ngen2/3/4/5` — universal formula N_gen/2^N_gen for N_gen ∈ {2,3,4,5} (norm_num, CatAL)
- `gut_weinberg_structure` — **Combined theorem**: all 7 structural identities (norm_num, CatAL)

*§9: f_MDL nonzero count = c_H + 1 (structural bridge, CatAL)*
- `b_higgs` — GTE b-component of H⁰: b_H = 3 = N_gen (def)
- `fmdl_nonzero_count` — count of (l,c,r) with f_MDL(l,c,r) ≠ 0: value = 14 (def; certified by Z7ChargeConjugation.fmdl_nonzero_count_14)
- `b_higgs_eq_ngen` — b_higgs = n_gen (rfl, CatAL)
- `fmdl_count_eq_chiggs_plus_one` — fmdl_nonzero_count = c_higgs + 1 = 14 (norm_num, CatAL)
- `fmdl_count_decomposition` — fmdl_nonzero_count = b_higgs + (c_higgs − b_higgs) + 1 = 3+10+1 (norm_num, CatAL)
- `fmdl_count_ngen_nfam` — fmdl_nonzero_count = n_gen + 2·n_fam + 1 = 3+10+1 (norm_num, CatAL)

*§13: Z₅ ring contribution — running shift physical naming (Ranks 57 & 58, CatAL)*
- `running_shift_is_z5_ring` — c_H − 2^N_gen = N_fam (alias of §5; explicit Z₅ ring naming, CatAL)
- `z5_ring_contributes_nfam_to_denominator` — c_H = 2^N_gen + N_fam (norm_num, CatAL)
- `gte_family_capacity_identity` — N_gen + N_fam = 2^N_gen (alias of §2; GUT orbit-filling naming, CatAL)

*§14: CKM matrix count theorem (Rank 68, CatAL)*
- `ckm_dof_count` / `ckm_real_dimension` — N_gen² = 9 (norm_num; CKM matrix real d.o.f. = dim U(N_gen), CatAL)
- `gut_capacity_times_ring` / `gte_generation_capacity` — 2^N_gen × N_fam = 40 (norm_num; GUT-orbit × family-ring capacity, CatAL)
- `wolfenstein_lambda_formula` / `wolfenstein_density_formula` — (N_gen:ℚ)²/(2^N_gen×N_fam) = 9/40 (norm_num; Wolfenstein λ arithmetic, CatAL)
- `wolfenstein_lambda_value` — (9:ℚ)/40 = 225/1000 (norm_num; exact decimal 0.225, 0.000% vs PDG, CatAL)

*§15: CKM quark N_eff structural formulas and R_b = sin²θ_W(GUT) (Rank 67, CatAL)*
- `b_u`, `b_d`, `b_c`, `b_s`, `b_b` — GTE quark N_eff definitions (9, 5, 275, 186, 8191)
- `neff_u_eq_ngen_sq` — b_u = N_gen² = 9 (norm_num; up quark G1 seed, CatAL)
- `neff_d_eq_nfam` — b_d = N_fam = 5 (norm_num; down quark at Z₅ boundary, CatAL)
- `neff_c_eq_nfam_poly` — b_c = N_fam²(2N_fam+1) = 275 (norm_num; G2 up-type, CatAL)
- `neff_s_eq_gen_higgs_form` — b_s = 2N_gen(2c_H+N_fam) = 186 (norm_num; G2 down-type, CatAL)
- `neff_b_eq_mersenne` — b_b = 2^c_H − 1 = 8191 (norm_num; G3 Mersenne prime, CatAL)
- `wolfenstein_A_sq_rational` — A² = (186:ℚ)/275 (norm_num; Wolfenstein A squared, CatAL)
- `ckm_unitarity_triangle_radius_eq_gut_weinberg` — R_b = N_gen/2^N_gen = 3/8 = sin²θ_W(GUT) ★★★★★ (alias of gut_weinberg_angle_pow2; cross-sector identity, CatAL)
- `ckm_from_gte_arithmetic` — **Combined CKM theorem**: N_gen²=9 ∧ 2^N_gen×N_fam=40 ∧ λ=9/40 ∧ R_b=3/8 (norm_num, CatAL)

*§16: SM generation N-value sum b_sum = 390 — all SM structural numbers in one object (Rank 49, CatAL)*
- `b_gen1`, `b_gen2`, `b_gen3`, `b_sum` — GTE generation b-values (73, 42, 275) and their sum
- `b_sum_value` — b_sum = 390 (norm_num, CatAL)
- `b_sum_is_product` — b_sum = 2 · N_gen · N_fam · c_H (norm_num; all four SM structural numbers as factors, CatAL)
- `b_sum_factorization` — b_sum = 2 × 3 × 5 × 13 (norm_num; explicit prime factorization, CatAL)
- `weinberg_numerator_in_bsum` — N_gen ∣ b_sum (norm_num; 3 divides 390, CatAL)
- `weinberg_denominator_in_bsum` — c_H ∣ b_sum (norm_num; 13 divides 390, CatAL)
- `weinberg_ratio_from_bsum` — (N_gen:ℚ) / c_H = 3/13 (norm_num; Weinberg ratio as ratio of prime factors of b_sum, CatAL)
- `nw_plus_chiggs_eq_pow2` — N_gen + c_H = 2⁴ (norm_num; 3+13=16=2⁴, the ridge subtraction constant, CatAL)
- `b_sum_structure` — **Combined b_sum theorem**: all 6 arithmetic identities (norm_num, CatAL)

*§17: Z₂ longitudinal mode universality — MDL-minimal universal Z₂ rule (Rank 43, CatAL arithmetic)*
- `rule124Output`, `rule124Minterms` — Rule 124 rule table and minterm set {2,3,4,5,6}
- `rule124_minterms_card` — Rule 124 has exactly 5 ones (native_decide, CatAL)
- `rule124_output_iff_minterm` — Rule 124 output ↔ in {2,3,4,5,6} (native_decide, CatAL)
- `rule124_quiescent` — Rule 124 maps (0,0,0)→0 (native_decide; satisfies neutral-sector quiescent condition, CatAL)
- `rule110_and_124_joint_mdl_count` — Rule 110 and Rule 124 share MDL count = 5 (native_decide, CatAL; arithmetic component of conditional universality theorem)
- `rule110_preferred_by_sublayer_consistency` — Rule 110 minterms ≠ Rule 124 minterms (native_decide; arithmetic basis for sublayer-consistency selection of Rule 110, CatAL)

*§18: Coupling ratio duality — sin²θ_W = 3/13 ⟺ r = α₁⁻¹/α₂⁻¹ = 2 (Rank 54, CatAL algebra)*
- `weinberg_at_r2` — N_gen/(N_gen + N_fam × 2) = 3/13 (norm_num; EW scale formula at coupling ratio r=2, CatAL)
- `weinberg_at_r1_gut` — N_gen/(N_gen + N_fam × 1) = 3/8 (norm_num; GUT scale formula at r=1, alias of §3, CatAL)
- `beta_function_diff_two_nfam` — 2 × N_fam = 10 (norm_num; β-function differential arithmetic b₁−b₂=2N_fam, CatAL)
- `universal_coupling_ratio_cancellation` — (N_gen/N_fam)×(2N_fam/N_gen) = 2 (norm_num; universal residue after N_gen/N_fam cancellation, CatAL)
- `coupling_ratio_duality` — **Combined duality theorem**: all four identities (r=2→3/13, r=1→3/8, β-diff=10, universal residue=2; norm_num, CatAL)

*§19: smGen1 as SU(5) projector — Z₅ ring partition (Rank 55, CatAL counting)*
- `sm_gen1` — Fin 5 → Fin 2 := ![1,1,0,0,1] (GTE first-generation binary pattern)
- `sm_gen1_active_count` — active positions (value=1) count = N_gen = 3 (decide, CatAL; matches SU(5) colored sector)
- `sm_gen1_inactive_count` — inactive positions (value=0) count = N_fam−N_gen = 2 (decide, CatAL; matches SU(5) leptonic sector)
- `sm_gen1_partition_matches_su5` — **Combined partition theorem**: active=3, inactive=2, 3+2=5 (decide; smGen1 as SU(5) projector, CatAL)

*§20: Mersenne prime structure, top quark formula, CP irrationality (Rank 67C + B-53, CatAL)*
- `b_top` — b_t = 2^(c_H−2) × N_gen × N_fam × (2N_fam+1) = 337920 (def; top quark N_eff)
- `neff_b_value` — b_b = 8191 (rfl, CatAL)
- `neff_b_is_prime` — Nat.Prime b_b (norm_num; 8191 is Mersenne prime, CatAL)
- `chiggs_is_5th_mersenne_exp` — c_H=13 ∧ N_fam=5 ∧ (∀ p ∈ {2,3,5,7,13}, Nat.Prime (2^p−1)) (norm_num+native_decide, CatAL)
- `neff_t_formula` — b_top = 337920 (norm_num, CatAL)
- `neff_t_factors` — b_top = 2^11 × N_gen × N_fam × (2N_fam+1) (norm_num, CatAL)
- `top_bottom_ratio_q` — (b_top:ℚ)/b_b = 337920/8191 (norm_num; tracks M_top/M_bottom −0.49%, CatAL)
- `bb_bs_product_not_square` — ¬∃ n:ℕ, n²=b_b×b_s (norm_num+linarith; implies tan(γ) irrational, CatAL)
- `bb_bs_sqrt_floor` — Nat.sqrt(b_b×b_s) = 1234 (native_decide; confirms non-square, CatAL)
- `neff_s_not_prime` — ¬ Nat.Prime b_s (native_decide; 186=2×3×31 composite, CatAL)
- `neff_b_s_coprime` — Nat.gcd b_b b_s = 1 (native_decide; 8191 prime ∧ 8191∤186, CatAL)
- `tan_gamma_numerator_not_square` — ¬∃ k:ℕ, k²=b_b×b_s×n_gen² (norm_num+linarith; 3702²<13711734<3703², CatAL; implies tan(γ) irrational)
- `cp_violation_irrationality_chain` — **Combined CP irrationality certificate**: b_b prime ∧ gcd=1 ∧ b_b×b_s non-square ∧ b_b×b_s×N_gen² non-square (exact ⟨...⟩; CatAL — CP violation is arithmetically irreducible)

*§21: Joint Selection Theorem — N_fam = 5 uniquely selected by Mersenne c_H AND Z₅ transitivity (Rank 67C-bis, CatAL)*
- `mersenne_ch_prime_p2` — 2^7−1=127 is prime at N_fam=2 (norm_num, CatAL)
- `mersenne_ch_not_prime_p3` — 2^9−1=511 not prime at N_fam=3 (norm_num, CatAL; 511=7×73)
- `mersenne_ch_prime_p5` — 2^13−1=8191 is prime at N_fam=5 (alias of neff_b_is_prime, CatAL)
- `mersenne_ch_prime_p7` — 2^17−1=131071 is prime at N_fam=7 (norm_num, CatAL; sibling universe)
- `mersenne_ch_not_prime_p11` — 2^25−1 not prime at N_fam=11 (norm_num; 31×1082401, CatAL)
- `mersenne_ch_not_prime_p13` — 2^29−1 not prime at N_fam=13 (norm_num, CatAL)
- `mersenne_ch_not_prime_p17` — 2^37−1 not prime at N_fam=17 (norm_num; 223×616318177, CatAL)
- `mersenne_ch_not_prime_p19` — 2^41−1 not prime at N_fam=19 (norm_num, CatAL)
- `mersenne_ch_not_prime_p23` — 2^49−1 not prime at N_fam=23 (norm_num; 127×4432676798593, CatAL)
- `joint_selection_theorem` — **Main theorem**: among primes ≤ 23, N_fam=5 is the UNIQUE prime satisfying BOTH (i) Mersenne prime c_H AND (ii) Z₅ full weight-3 transitivity under Rule 110. Combines the full Mersenne landscape (9 cases) + transitivity exclusion of p=2 and p=7. CatAL upgrade of the CatAD Joint Selection result from Rank 67C-bis. (norm_num + Z5TransitivityUniqueness, zero sorry)
- `double_mersenne_exponent_identity` — N_fam=5 and c_H=13 are BOTH Mersenne prime exponents; pivot: c_H−2·N_fam=N_gen (3 arithmetic facts, norm_num, CatAL)

*§23: GTE Master Formula — all SM EW parameters from N_gen = 3 alone (Rank 70, CatAL capstone ★★★★★)*
- `gte_generating_triple` — N_fam = 2^N_gen−N_gen ∧ c_H = 2^(N_gen+1)−N_gen ∧ c_H = N_gen+2·N_fam (norm_num; arithmetic cascade from N_gen alone, CatAL)
- `gte_master_formula_gut_weinberg` — sin²θ_W(GUT) = N_gen/2^N_gen = 3/8 (alias of gut_weinberg_angle_pow2; capstone form, CatAL)
- `gte_master_formula_ew_weinberg` — sin²θ_W(EW) = N_gen/c_H = 3/13 (alias of weinberg_angle_closure; capstone form, CatAL)
- `gte_master_formula_wolfenstein` — λ = N_gen²/(2^N_gen×N_fam) = 9/40 (alias of wolfenstein_lambda_formula; capstone form, CatAL)
- `gte_master_formula_rb` — R_b = N_gen/2^N_gen = 3/8 = sin²θ_W(GUT) (alias; cross-sector bridge, CatAL)
- `gte_cross_sector_bridge` — sin²θ_W(GUT) = R_b ∧ λ = (N_gen/N_fam)×sin²θ_W(GUT) = 9/40 (norm_num; three-sector arithmetic identity, CatAL)
- `gte_arithmetic_root` — N_gen + N_fam = 2^N_gen (alias of ngen_plus_nfam_eq_pow2; algebraic pivot of the master formula, CatAL)
- `ngen_3_mersenne_uniqueness` — Nat.Prime (2^N_fam−1) ∧ Nat.Prime (2^c_H−1) (norm_num; double Mersenne window; N_fam=5 and c_H=13 are Mersenne prime exponents, CatAL)
- `gte_master_formula_complete` ★★★★★ — **CAPSTONE THEOREM**: N_fam=2^N_gen−N_gen ∧ c_H=2^(N_gen+1)−N_gen ∧ sin²θ_W(GUT)=3/8 ∧ sin²θ_W(EW)=3/13 ∧ λ=9/40 ∧ N_gen+N_fam=2^N_gen; all four SM EW parameters from N_gen=3 alone; four independent real predictions, zero free parameters (norm_num, zero sorry, zero new axioms; CatAL)

*§24: Weinberg Angle Three-Tier Prediction — k=N_gen orbit-average term (Rank 76, CatAL; upgraded from CatA)*
- `weinberg_residual_correction` — (λ_formula)^N_gen / (2·c_H) = 729/1664000; k=N_gen term of the binomial orbit-average expansion; C(3,3)=1 (norm_num, CatAL)
- `weinberg_residual_as_orbit_average` — (9/40)³ / (2·13) = 729/1664000; pure-numeric form (norm_num, CatAL)
- `weinberg_two_term_prediction` — N_gen/c_H + (9/40)^N_gen/(2·c_H) = 384729/1664000; complete two-term Weinberg prediction, 0.09 PDG σ (norm_num, CatAL)
- `weinberg_denominator_factors` — 2^(3·N_gen+1) × N_fam³ × c_H = 1664000; denominator = pure GTE primes (norm_num, CatAL)
- `weinberg_n3_uniqueness` — n=2 correction (1/72) ≠ δ(3) ∧ n=3 correction = 729/1664000; N_gen=3 uniqueness (norm_num, CatAL)

*§12 (extended): Weinberg Physical Bridge — P22 EWChiralBridge import explicit*
- `parity_restriction_explicit` — ∀ l c r : Fin 7, ca_parity l c r = (r,c,l); the Parity Restriction Theorem as an explicit standalone Lean theorem (rfl from definition, zero axioms, CatAL)
- `weinberg_physical_bridge` — 4-conjunct theorem: (A) Parity Restriction, (B) U(1)_Y count = N_gen = 3, (C) SU(2)_L count = 2·N_fam = 10, (D) sin²θ_W = 3/13; explicitly cites `EWChiralBridge.doublet_partner_is_left_chiral` and `EWChiralBridge.u1y_couples_both_chiralities` as imported P22 bridge axioms (zero sorry; full CatAL pending P22 EWStructure formalization, CatAL conditional)

*§27: Bidirectional UGP–Rule 110–SM Unification Summary (Rank 85, CatAL capstone ★★★★★)*
- `ugp_arith_forces_rule110` — Arrow A1/A3-R: ∀ r : Fin 256, SM orbit conditions ↔ r=110; CUP-4 alias in unification context (alias of cup1_orbit_uniquely_selects_rule110, CatAL)
- `sm_selects_gte_triple` — Arrow A2-R: n_gen=3 ∧ n_fam=5 ∧ c_H=13; SM structural constants = GTE generating triple (rfl, CatAL)
- `gte_predicts_ew_mixing` — Arrow A2: sin²θ_W(EW)=3/13 ∧ sin²θ_W(GUT)=3/8; both Weinberg angles from N_gen alone (aliases of §12/§3, CatAL)
- `gte_predicts_ckm_lambda` — Arrow A2: λ=9/40; Wolfenstein parameter from N_gen alone (alias of wolfenstein_lambda_formula §14, CatAL)
- `rule110_encodes_sm_particles` — Arrow A3: (photon=unique CA fixed point) ∧ (gen₁=Garden of Eden) ∧ (fmdl never outputs Z₇=4); three Rule 110 CA certifications of SM particle structure (CUP3DUniqueness theorems, CatAL)
- `ugp_r110_sm_joint_unification` ★★★★★ — **UNIFICATION CAPSTONE**: 7-conjunct theorem: (1) N_gen+N_fam=2^N_gen; (2) sin²θ_W(EW)=3/13; (3) sin²θ_W(GUT)=3/8; (4) λ=9/40; (5) double Mersenne endpoint (2^N_fam−1 and 2^c_H−1 both prime); (6) photon CA fixed point; (7) gen₁ Garden of Eden. P35 Theorem 1 candidate. (zero sorry, zero new axioms; CatAL)

*§28: MDL Robustness and Z₇ Free Minterm Count (CatAL, zero sorry)*
- `z7_fixed_neighborhood_count` — Exactly 18 of the 343 Z₇³ neighborhoods satisfy isFixedNeighborhood (10 orbit from gen1→gen2 + gen2→gen3 steps, 8 binary Rule 110; native_decide, CatAL)
- `z7_free_neighborhood_count` — Exactly 325 = 343 − 18 neighborhoods are free; MDL zeros all 325, uniquely selecting f_MDL (native_decide, CatAL)
- `mdl_robustness_z7` ★★★★ — **MDL ROBUSTNESS**: Any orbit-admissible MDL-minimal Z₇ CA function must equal fmdl, regardless of orbit depth (naming alias of Z7ChargeConjugation.fmdl_mdl_uniqueness; zero sorry, CatAL). Combined with CatA computation: 15 orbit-constrained Z₇ neighborhoods (5 cells × 3 generations, no repeats), disjoint from 8 binary neighborhoods; total 23 constrained, 320 free.

*§29: Z₂ Longitudinal Universality Structural Chain (Rank 89, CatAL)*
- `n_rule110_minterms` — Hamming weight (minterm count) of Rule 110 = 5 (def; equals MDL description length of Rule 110 as a Z₂ CA rule)
- `rule110_minterms_eq_five` — n_rule110_minterms = 5 (rfl, CatAL)
- `z_boson_cvalue_equals_mdl_plus_z7` ★★★ — **c-VALUE MDL IDENTITY**: n_rule110_minterms + 7 = c_Z = 12; the Z boson GTE c-value equals the Z₇ modulus (7 free Z₂ CA bits) plus the Rule 110 minterm count (5); arithmetic certification of the structural chain c_Z = 7 + MDL(Rule 110) = 12 (norm_num, CatAL)
- `z_boson_mdl_class4_chain` — **THREE-CONJUNCT CHAIN**: (1) n_rule110_minterms=5 ∧ (2) 5+7=c_Z ∧ (3) c_Z=c_H−1; the arithmetic backbone of the Z₂ longitudinal universality CatAD result — c_Z=12 forces MDL(rule_Z)=5, landing at the isolated Class 4 resonance in the qualifying Z₂ CA rule space (norm_num, zero sorry, CatAL)

*§30: Mersenne Cascade Discriminator — 12→2 Doublet-Paired Candidates (Rank 80 Round 02, CatAL)*
- `bt_is_composite` — ¬ Nat.Prime b_top (b_t = 337920 is composite; top quark N_eff not Mersenne prime; norm_num, CatAL)
- `bb_not_eq_bt` — b_b ≠ b_top (Mersenne G3 endpoint 8191 ≠ top G3 endpoint 337920; norm_num, CatAL)
- `bb_mersenne_bt_not` ★★★★ — **ARITHMETIC ASYMMETRY**: b_b = Mersenne prime M₁₃ ∧ b_t = composite; the down cascade (c_d=42=b_L2) terminates with G3 = 8191 (Mersenne prime) while the up cascade (c_u=275=b_L3) terminates with G3 = 337920 (composite); this asymmetry is the arithmetic basis of the cascade discriminator (exact, CatAL)
- `cascade_c_pair_mersenne_unique` ★★★★★ — **DISCRIMINATOR**: (c_u=b_L3=275, c_d=b_L2=42) is the unique c-pair from B_lep selected by the Mersenne G3 constraint; c=b_L1=73 (electron N_eff) is structurally inadmissible; the three B_lep values are mutually distinct; certifies the 12→2 cascade reduction combined with §26 (norm_num, CatAL)
- `quark_cascade_mersenne_discriminator` — **JOINT THEOREM**: b_b = Mersenne prime M₁₃ ∧ b_t not prime ∧ b_u = N_gen² ∧ b_d = N_fam; packages the cascade discriminator (§30) with the N_eff assignments (§26) in one certified statement (exact, CatAL)

---

**P22 EWStructure Chirality Bridge — Formal Stub for Weinberg Derivation (EWChiralBridge.lean; 1 theorem + 2 axioms + 2 definitions, 0 sorry; 2 axioms pending P22 formalization)**

Physical motivation: The physical identification of palindromic CA neighborhoods with U(1)_Y gauge channels and non-palindromic neighborhoods with SU(2)_L channels rests on P22's result that SU(2)_L is exclusively left-chiral and U(1)_Y is parity-even. This module formalizes that bridge as two `axiom` declarations (pending P22 Lean module) plus a non-trivial derived theorem. The import chain `GUTStructure → EWChiralBridge` is wired; replacing the 2 axioms with P22 proofs will make the full Weinberg chain zero-axiom CatAL.

- `FermionChirality` — inductive type: `T` (left-chiral SU(2)_L doublet) and `Tdagger` (right-chiral singlet)
- `EWGaugeSector` — inductive type: `U1Y` and `SU2L`
- `ewGaugeCoupling : EWGaugeSector → Finset FermionChirality` — **axiom** (physical function from P22; uninterpreted pending P22 Lean formalization)
- `doublet_partner_is_left_chiral` — **axiom**: `ewGaugeCoupling SU2L = {T}`; SU(2)_L couples exclusively to left-chiral fermions (P22 EWStructure CatAL, stub)
- `u1y_couples_both_chiralities` — **axiom**: `ewGaugeCoupling U1Y = {T, T†}`; U(1)_Y couples to both chiralities (P22 EWStructure CatAL, stub)
- `su2l_u1y_chirality_asymmetry` — **theorem** (zero sorry, `decide`): `ewGaugeCoupling SU2L ≠ ewGaugeCoupling U1Y`; {T} ≠ {T, T†} — SU(2)_L is chiral while U(1)_Y is vector

---

**EW Boson GTE Triple Arithmetic and Goldstone Cascade Formula (EWBosonStructure.lean; 11 theorems + 6 definitions, 0 sorry)**

Physical motivation: The three EW bosons with defined GTE triples — W⁺(5,3,11), Z(5,3,12), H⁰(5,3,13) — share identical (a=5, b=3) components and form a unit-step arithmetic progression in c. This c-staircase is the unique such structure in the GTE triple dataset. Each c-step encodes one layer of EW cascade complexity corresponding to broken SU(2)_L generator directions in the Higgs mechanism. The scalar boundary c_H = 13 = N_gen + 2×N_fam marks the EW cascade endpoint: particles with c < c_H are massive spin-1 gauge bosons; the particle at c = c_H is the spin-0 Higgs scalar. The Goldstone cascade formula c_P = c_H − d_P certifies that each unit c-step counts one absorbed Goldstone boson degree of freedom.

- `c_w_plus`, `c_z_boson`, `c_higgs` — cascade depth constants (11, 12, 13)
- `w_plus_triple`, `z_triple`, `higgs_triple` — GTE triple constants (5,3,c)
- `ew_c_staircase` — c_W = c_H − 2 ∧ c_Z = c_H − 1 ∧ c_H = 13 (decide, CatAL)
- `ew_c_arithmetic_progression` — c_Z = c_W + 1 ∧ c_H = c_Z + 1 ∧ c_H = c_W + 2 (decide, CatAL)
- `ew_mass_ordering` — c_W < c_Z < c_H matching M_W < M_Z < M_H (decide, CatAL)
- `ew_higgs_is_scalar_boundary` — c_W < c_H ∧ c_Z < c_H ∧ c_H = 13 (decide, CatAL)
- `ew_triples_distinct` — W⁺, Z, H⁰ triples pairwise distinct (differ only in c) (decide, CatAL)
- `ew_boson_structure` — **Combined theorem**: all 5 structural facts in one conjunction (decide, CatAL)

*§5: Goldstone cascade formula — c_P = c_H − d_P (Rank 53, CatAL)*
- `d_higgs`, `d_z`, `d_w` — broken SU(2)_L generator ranks (0, 1, 2)
- `goldstone_cascade_higgs` — c_H = c_H − 0 (simp; Higgs is scalar remnant, d_H=0, CatAL)
- `goldstone_cascade_z` — c_Z = c_H − 1 = 12 (simp; Z absorbs 1 neutral Goldstone mode, CatAL)
- `goldstone_cascade_w` — c_W = c_H − 2 = 11 (simp; W⁺ absorbs 2 charged Goldstone modes, CatAL)
- `goldstone_cascade_formula` — **Combined formula**: c_P = c_H − d_P for all three EW bosons (simp, CatAL)

---

**Primordial T(2,3) Topology — Cascade Period p=2 Selection (GUTStructure.lean §31; 5 theorems, 0 sorry)**

Three-constraint Lean certification that p=2 is the unique valid cascade period for T(p,N_gen):
(1) GoE structural necessity (p≥2: `CUP3D.fmdl_gen1_is_garden_of_eden`, CatAL);
(2) PSC topological connectedness (gcd(p,N_gen)=1 for T(p,q) to be a knot, not a link);
(3) MDL minimality (p=2 is the smallest p≥2 coprime to N_gen=3).

- `cascade_period_coprimality` — Nat.gcd 2 n_gen = 1 (T(2,3) is a single-component knot; norm_num, CatAL)
- `cascade_period_3_fails_coprimality` — Nat.gcd 3 n_gen ≠ 1 (T(3,3) is a 3-link; p=3 PSC-excluded; norm_num, CatAL)
- `mdl_cascade_period_minimum` — ∀ p≥2, gcd(p,N_gen)=1 → MDL(2) ≤ MDL(p) (monotone MDL; omega, CatAL)
- `fmdl_cascade_period_two_unique` — gcd(2,N_gen)=1 ∧ ∀ p≥2 coprime to N_gen, 2≤p (joint statement; CatAL)
- `cascade_period_minimum_is_two` ★ — (gcd(2,N_gen)=1) ∧ (MDL(2)=10) ∧ (MDL minimality) — **three-constraint selection theorem** (norm_num + omega, CatAL)

Both T(2,3) parameters are now GTE-derived at CatAL level: q=N_gen=3 (`fmdl_ngen_equals_three`, CatAL) and p=2 (§31, CatAL). Rank 93 upgraded: CatD+ → CatAD → **CatAL**.

---

**SU(2)_L Charge Assignment from Z₇ Color-Subgroup Structure (GUTStructure.lean §33; 6 theorems + 2 definitions, 0 sorry)**

The 2→1 step in the quark G1 seed derivation (Rank 99): the charge assignment (up-type ↔ N_eff=N_gen²=9; down-type ↔ N_eff=N_fam=5) is derived from the Z₃ multiplicative subgroup structure of Z₇*. The Z₃ subgroup {1,2,4} (generated by 2, since 2³≡1 mod 7) identifies w(u)=2 as in the color subgroup and w(d)=6 as in the coset {3,5,6}. Z₇ alignment: N_gen² mod 7 = 9 mod 7 = 2 = w(u) (canonical aligned); N_fam mod 7 = 5 ≠ w(u) (charge-swap excluded). Combined with §26 (MDL doublet-pairing, ∞→12) and §30 (Mersenne discriminator, 12→2), this closes the full three-step quark G1 seed selection at CatAD with CatAL arithmetic support.

- `z7_color_subgroup_closed` — {1,2,4} closed under multiplication mod 7 (decides, CatAL)
- `z7_color_subgroup_generator` — 2³ % 7 = 1, establishing the Z₃ subgroup (norm_num, CatAL)
- `w_u_in_color_subgroup` — w(u)=2 ∈ {1,2,4} (simp, CatAL)
- `w_d_in_color_coset` — w(d)=6 ∉ {1,2,4} (simp, CatAL)
- `neff_u_z7_aligned` — N_gen² mod 7 = w(u) = 2 (norm_num, CatAL)
- `neff_d_z7_not_aligned` — N_fam mod 7 ≠ w(u) (norm_num, CatAL)
- `su2l_charge_assignment_z7_discriminator` ★★★★ — joint: (N_gen² mod 7 = w_u) ∧ (N_fam mod 7 ≠ w_u) ∧ (w_u ∈ {1,2,4}) ∧ (w_d ∉ {1,2,4}); canonical selected, charge-swap excluded (CatAL)

Rank 99 result: Step 3 (2→1) upgraded from unexplained postulate to GTE-motivated CatAD derivation with full CatAL arithmetic certificate. Enables Rank 100 native_decide capstone.

---

**f_MDL Perfect Code — Lower Bound 14 (GUTStructure.lean §36; 2 theorems, 0 sorry)**

Machine-checked certification that f_MDL is a perfect code: it achieves the minimum number of non-zero output neighborhoods (14) consistent with orbit admissibility + Rule 110 binary sublayer + vacuum transparency. The lower bound 14 = 9 (orbit-forced) + 5 (binary-forced) follows from the structural disjointness of orbit and binary neighborhoods. MDL-minimality forces all 320 free neighborhoods to zero, so no non-zero output is redundant.

- `fmdl_perfect_code` ★★★★★ — packages (i) exactly 14 non-zero outputs (native_decide) and (ii) unique MDL-minimal orbit-admissible function (delegates to Z7ChargeConjugation.fmdl_mdl_uniqueness); CatAL, zero sorry
- `fmdl_nonzero_lower_bound` ★★ — 3 + 10 + 1 = fmdl_nonzero_count = 14 (palindrome decomposition arithmetic certificate; norm_num, CatAL)

---

**Dark Sector Period-2 Orbits: Rule 110 on 4-Cell Binary Ring (GUTStructure.lean §35; 7 theorems + 2 definitions, 0 sorry)**

Machine-checked certification that the four dark sector stable states are exactly the period-2 orbits of Rule 110 on a 4-cell binary periodic ring — no more, no less. The complete orbit structure of the 4-cell ring is certified: one fixed point (vacuum), two period-2 cycles (dark sector), eleven transients. The identification provides the deepest structural account of dark sector stability: ring size N=4 (dark sector) admits Rule 110 period-2 orbits, while N=5 (visible sector) does not.

State encoding: big-endian binary (s₀ = bit 3, s₃ = bit 0). Dark cycle states: 14 = (1,1,1,0) ↔ 11 = (1,0,1,1) and 13 = (1,1,0,1) ↔ 7 = (0,1,1,1). All four have Z₇ winding sum = 3 (W⁺ charge class).

- `rule110_4cell_ring` — the Rule 110 map on the 4-cell binary periodic ring (Fin 16 → Fin 16)
- `dark_sector_vacuum_fixed_point` ★★★ — state 0 = (0,0,0,0) is the unique fixed point (decide, CatAL)
- `dark_sector_cycles_are_period2` ★★★★ — all four dark cycle states {14,11,13,7} satisfy period-2: f(f(s))=s ∧ f(s)≠s (decide, CatAL)
- `dark_sector_period2_exhaustive` ★★★★★ — the four dark cycle states are EXACTLY the period-2 orbits: (f(f(s))=s ∧ f(s)≠s) ↔ s∈{7,11,13,14} (decide, CatAL)
- `dark_sector_orbit_structure` ★★★★★ — complete orbit characterization: unique fixed point + exhaustive period-2 set (decide, CatAL)
- `dark_states_z7_winding_3` ★★★ — all four dark cycle states have Z₇ winding sum = 3 (decide, CatAL)
- `dark_ring_size_eq_n_gen_plus_one` ★★ — dark ring size 4 = N_gen + 1 (norm_num, CatAL)
- `dark_budget_identity` ★★ — (dark cycle count) + (dark ring size) = 2^N_gen: 4+4=8 (norm_num, CatAL)

---

**Full 6-Quark N_eff GTE Arithmetic Closure (GUTStructure.lean §34; 3 theorems, 0 sorry)**

The capstone certification packaging the complete GTE quark N_eff spectrum. Assembles individually certified structural formulas (§15, §20, §25) with the three-step G1 seed derivation chain (§26 MDL-doublet pairing, §30 Mersenne discriminator, §33 Z₇ alignment) into three joint theorems — closing the full six-quark derivation at CatAL for the arithmetic result.

- `six_quark_neff_complete` ★★★★★ — 6-conjunct joint theorem: b_u=N_gen²=9, b_d=N_fam=5, b_c=N_fam²(2N_fam+1)=275, b_s=2N_gen(2c_H+N_fam)=186, b_b=2^c_H−1=8191 (Mersenne prime M₁₃), b_top=2^c_W·N_gen·N_fam·(2N_fam+1)=337920 (exact assembly, zero sorry)
- `quark_g1_canonical_assignment` ★★★ — Z₇ arithmetic fingerprint: b_u % 7 = 2 (aligned with w(u)=2), b_d % 7 = 5, b_u ≠ b_d; charge-swap candidate excluded (norm_num, CatAL)
- `quark_neff_all_distinct` ★★★ — all six quark b-values mutually distinct: b_u≠b_d, b_u≠b_b, b_u≠b_top, b_d≠b_b, b_d≠b_top, b_b≠b_top (norm_num, CatAL)

Rank 100 result: all six quark N_eff values GTE-derived and machine-certified at CatAL level for the arithmetic content.

---

**CA Masslessness Criterion, EW Vertex, Ether Z₇ Winding, Helicity Parity Violation (CasimirMasslessEther.lean; 12 theorems + 1 definition, 0 sorry)**

Three results, Lean-certified via native_decide:

*§1 — Rank 46: CA Masslessness Criterion*

Physical motivation: The criterion fmdl(0,k,0)=k — whether a Z₇ value k survives stably in a vacuum neighborhood — selects exactly k∈{0,1} from Z₇. This gives a CA-level masslessness/massiveness partition matching the SM: Z₇=0 (photon/EM vacuum) and Z₇=1 (neutrino-weight sector) are CA-massless; Z₇∈{2,3,4,5,6} (all SM massive particles) decay to vacuum. The Z₇=1 CA-masslessness is at the winding-sector level; GTE gives neutrinos tiny mass at a deeper level.

- `fmdl_massless_criterion` — ∀ k : Fin 7, fmdl 0 k 0 = k ↔ (k = 0 ∨ k = 1) (native_decide, CatAL)
- `fmdl_massless_unique` — exactly one non-zero CA-massless value: k=1 (native_decide, CatAL)
- `fmdl_massive_decay` — ∀ k ≠ 0,1: fmdl 0 k 0 = 0 (native_decide, CatAL)

*§2 — Rank 48: (u,γ,u)→W⁺ CA-Level Electroweak Vertex*

Physical motivation: The orbit neighborhood fmdl(2,0,2)=3 defines a CA-level EW vertex: two u-quarks flanking a photon produce a W⁺. Sourced from the gen₂ orbit [2,5,2,0,2] where position 3 (photon-slot) evolves to W⁺ in gen₃. Photon transparency: 34/36 = 94.44% of matter-matter configurations.

- `u_photon_u_to_W_vertex` — fmdl 2 0 2 = 3 (native_decide, CatAL)
- `nu_photon_nu_absorption` — fmdl 1 0 1 = 1 (native_decide, CatAL)
- `photon_absorption_events` — exactly 2 absorption events among 36 matter pairs (native_decide, CatAL)

*§3 — Rank 50: Rule 110 Ether Z₇ Winding = 1 (Neutrino Sector Background)*

Physical motivation: The Rule 110 ether (period-14 background [0,1,0,1,1,1,0,0,0,1,1,1,0,1]) has Z₇ sum mod 7 = 1 (neutrino-sector winding), not 0 (EM vacuum winding). The ether is the neutrino-sector propagation medium; matter (gliders) propagates through the neutrino background. The EM vacuum is the separate Z₇=0 fixed point.

- `ether_period` (def) — [0,1,0,1,1,1,0,0,0,1,1,1,0,1] : List (Fin 7)
- `ether_period_length` — ether_period.length = 14 (native_decide)
- `ether_z7_sum_mod7` — (ether_period.map (·.val)).sum % 7 = 1 (native_decide, CatAL)
- `ether_z7_composition` — 6 zeros, 8 ones per period (native_decide)
- `ether_not_em_vacuum` — ether_period ≠ replicate 14 0 (native_decide)
- `casimir_sector_structure` — **Combined theorem**: masslessness criterion + EW vertex + ether winding (native_decide, CatAL)

*§39 — WPlusDecay: W⁺ Decay Lemma (Rank 145-WDT, CatAL)*

Physical motivation: The W⁺ boson (Z₇=3) is a virtual mediator in the GTE CA. Combined with the W⁺ creation theorem (`CUP3D.fmdl_w_emission`), this section certifies the complete CA lifecycle: W⁺ is created from a (u,vac,u) triple in one step and immediately decays to vacuum in the next. This is the Fermi contact interaction at the CA scale (E ≪ M_W).

- `wplus_center_maps_to_vacuum` — **Main theorem**: ∀ l r : Fin 7, CUP3D.fmdl l 3 r = 0 (decide; all 49 center-3 neighborhoods map to vacuum, CatAL)
- `wplus_creation_then_decay` — **Combined theorem**: fmdl 2 0 2 = 3 ∧ ∀ l r, fmdl l 3 r = 0 (decide; complete W⁺ CA lifecycle, CatAL)

*§4 — Helicity Parity Violation (CatAL)*

Physical motivation: The CA masslessness criterion implies a left-right asymmetry between the two transverse photon helicity modes. The positive-helicity mode (Z₇=1, h=+1) is CA-stable (fmdl(0,1,0)=1); the negative-helicity mode (Z₇=6, h=−1) decays to vacuum in one step (fmdl(0,6,0)=0). This provides CA-arithmetic grounding for helicity parity violation. Machine-certified in P33, Proposition 5.4 (CatAL).

- `helicity_plus_stable` — fmdl 0 1 0 = 1 (native_decide, CatAL)
- `helicity_minus_decays` — fmdl 0 6 0 = 0 (native_decide, CatAL)
- `helicity_parity_violation` — fmdl 0 1 0 = 1 ∧ fmdl 0 6 0 = 0 ∧ fmdl 0 1 0 ≠ fmdl 0 6 0 (native_decide, CatAL)

**CA-Level Chirality and Parity (ChiralityEigenstates.lean, Rank 12; 5 theorems, 0 sorry)**

Spatial parity `P` on the 5-cell ring reverses cell order: `fmdl_mirror v i = v (4 − i)`. Four machine-certified results (native_decide / decide, zero sorry, zero named axioms):

- `fmdl_p_violation_count` — #{(l,c,r) | fmdl l c r ≠ fmdl r c l} = 14 (native_decide, CatAL)
- `gen1_is_chiral` — fmdl_gen1_z7 ≠ fmdl_mirror fmdl_gen1_z7 (decide, CatAL)
- `p_gen1_two_step_decay` — fmdl_step5² (fmdl_mirror gen₁) = vac (native_decide, CatAL)
- `gen3_p_covariant` — fmdl_step5 (fmdl_mirror gen₃) = fmdl_mirror (fmdl_step5 gen₃) (native_decide, CatAL)
- `sm_orbit_is_left_handed` — combined theorem: all four properties simultaneously (zero sorry)

**Weak Isospin Identification (WeakIsospin.lean, Rank 94c; 10+ theorems, 0 sorry)**

Formalizes the identification of weak isospin as $\mathbb{Z}_7$ species-winding arithmetic. Key results (all proved by `decide`, zero sorry, zero custom axioms):

- `wb_conservation_charged_current` — W_B conserved at all 4 SM charged-current vertices mod 7
- `weak_isospin_doublet_delta_four` — ΔW_B = 4 between both SM doublet partner pairs
- `species_formula_forces_delta_four` — species formula W_B = 4k mod 7 at k = 0,1,4,5 forces doublet structure
- `wb_wplus_uniquely_determined` — W_B(W⁺) = 3 is the unique Z₇ element satisfying both CC constraints
- `wb_wminus_uniquely_determined` — W_B(W⁻) = 4 is the unique Z₇ element satisfying conjugate CC constraints
- `w_bosons_z7_conjugate` — W_B(W⁺) + W_B(W⁻) = 0 mod 7 (charge-conjugate pair)
- `weak_isospin_identification` — combined certification: doublet partition + ΔW_B=4 + CC conservation + W-boson uniqueness

<!-- NOVA_ZPO_ZENODO_SOFTWARE_BEGIN -->
**Archival software (Zenodo):** https://doi.org/10.5281/zenodo.19429247
<!-- NOVA_ZPO_ZENODO_SOFTWARE_END -->
<!-- NOVA_ZPO_ZENODO_PAPER_BEGIN -->
**Archival paper (Zenodo preprint) (Zenodo):** https://doi.org/10.5281/zenodo.19433539
<!-- NOVA_ZPO_ZENODO_PAPER_END -->

---

**Z₇ Winding–Charge Equivalence (GUTStructure.lean §50 `WindingChargeEquivalence`, Rank 189-WCT; 4 theorems, 0 sorry)**

Formal certification that Z₇ winding conservation is equivalent to electric charge conservation for all SM color-singlet particles. The GTE charge formula 3Q = w* (§49) maps integer charges injectively to Z₇ classes, making Z₇ an arithmetic encoding of U(1)_EM at the observable-particle level. All proofs by `norm_num`.

- `wplus_decay_z7_eq_charge` — all three charge-conserving splits of Q=+1 satisfy Z₇: (3+0)%7=3, (3+4)%7=0, (0+0)%7=0 (norm_num, CatAL)
- `proton_decay_dominant_z7` — dominant channel p→e⁺+π⁰ certified: 3 ≡ 3+0 (mod 7); w(e⁺)=w(p)=3 (norm_num, CatAL)
- `z7_charge_homomorphism` — Q↦w*=3Q (mod 7) is a group homomorphism for all SM charges including fractional quarks: Q∈{+1,0,−1,+2/3,−1/3} → w*∈{3,0,4,2,6} (norm_num, CatAL)
- `winding_charge_equivalence` — **Main theorem**: Z₇ winding sum = initial winding for all five representative SM color-singlet charge classes, including quark pairs u+ū and d+d̄ (norm_num, CatAL)

---

**CA Ether Dispersion Relation E = v_CA × k (GUTStructure.lean §58 `EtherDispersion`, Rank 212-CEK Thread 2; 9 theorems + 2 defs, 0 sorry)**

Formal certification of the CA ether dispersion relation E(k) = v_CA × k evaluated at the Brillouin zone boundary. v_CA = 2/3 is grounded directly in Cook's Rule 110 glider catalog: the A glider (Cook Figure 5) has period (Δt=3, Δx=2), giving speed v_CA = Δx/Δt = 2/3. This is the first CatAL connection between the Cook glider catalog data and the neutrino mass formula. Added `import Rule110.CookGliderCatalog` to GUTStructure.lean. Build: ✔ [3300/3300] in 10s (5 extra from CookGliderCatalog import chain).

- `a_glider_period` — A glider Δt = 3 (rfl; Cook Figure 5 data, CatAL)
- `a_glider_displacement` — A glider Δx = 2 (rfl; Cook Figure 5 data, CatAL)
- `v_CA_from_a_glider` — **Main certificate**: Δt=3 ∧ Δx=2 ∧ v_CA=2/3 (⟨rfl,rfl,rfl⟩; directly grounded in CookGliderCatalog, CatAL)
- `e_bz_eq_v_times_k` — v_CA × k_BZ = 1/21 (norm_num; BZ boundary energy rational proxy, CatAL)
- `e_bz_rational_proxy` — (2:ℚ)/3/14 = 1/21 (norm_num, CatAL)
- `linear_dispersion_at_BZ` — v_CA × k_BZ = 1/21 (alias for e_bz_eq_v_times_k, CatAL)
- `ether_energy_denominator_factored` — 3 × 7 × 13 = 273 (norm_num, CatAL)
- `ether_dispersion_complete` — **Master conjunction**: v_CA=2/3 ∧ k_BZ=1/14 ∧ v_CA×k_BZ=1/21 (⟨rfl,rfl,norm_num⟩, CatAL)
- `dispersion_denominator_chain` — 21×13=273 ∧ (2/3)/14=1/21 (norm_num, CatAL)

---

**Spacetime Layer — Geodesic, Centroid, Mass Gap, Spatial Lifting, QEC Stabilizer (zero sorry on listed theorems)**

*Rank 17-GEO — Geodesic Theorem + P34 Centroid (`GeodesicTheorem.lean`, `CentroidMeasure.lean`)*

- `causal_sequence_exists` — timelike causal sequence with DWeight preservation and fixed spatial position (CatAL)
- `geodesic_preferred_direction` — well-defined `[D]`-weighted centroid at every step; spatial centroid invariant along timelike worldline (CatAL)
- `beableCentroid` / `centroid_well_defined` — point-localization P34 `[D]` centroid over causal nodes (CatAL)
- `d2_orbit_closed_iter` / `beable_spatial_propagation` — D2 orbit closure and spatial propagation (CatAL)
- `geodesic_theorem` — full D2 preferred-direction via distributed measure (CatAD; structural)

*Rank 42-MGP — Mass Gap (`MassGap.lean`)*

- `gte_mass_gap` — positive mass gap Δ > 0 for all physical non-vacuum beables (CatAL, zero axioms)
- `gte_mass_formula_physical` — Δ ≥ 1.8 MeV (PDG conservative up-quark lower bound); `smGenMass` (CatAL)

*Rank 79-MASSES — Orbit Generation Mass Hierarchy (`OrbitMassHierarchy.lean`)*

- `orbit_generation_ordering` — ∀ s : SmSector, gen₃ mass lb > gen₂ mass lb > gen₁ mass lb > 0; closes OA-1 (physical generation ordering from cascade depth); all three SM sectors (lepton/upQuark/downQuark) (CatAL)
- `cross_sector_gen1_ordering` — down-quark gen₁ lb > up-quark gen₁ lb > lepton gen₁ lb > 0 (CatAL)
- `lepton_gen1_below_beable_gap` — electron mass lb (0.51 MeV) < Level A beable floor (1.8 MeV), formalizing the Level A/B two-level structure (CatAL)
- `up_quark_gen1_matches_beable_gap` — up-quark gen₁ lb exactly equals the beable-level floor (CatAL)
- Per-sector mass floor constants: m_electron_lb=0.51 MeV, m_muon_lb=105 MeV, m_tau_lb=1770 MeV; m_up_lb=1.8 MeV, m_charm_lb=1200 MeV, m_top_lb=170 GeV; m_down_lb=4 MeV, m_strange_lb=80 MeV, m_bottom_lb=4 GeV
- **Self-Consistency Condition (SCC) — §7 (4 new CatAL theorems, 16 total):**
 - `leptonic_sector_heaviest_gen3` — τ lepton (gen₃) has the greatest mass lb in the leptonic (color-singlet, pure-Z₇) sector; specialization of `orbit_generation_ordering` to `SmSector.lepton` (CatAL)
 - `mphi_equals_tau_mass_scc` — SCC identification m_φ = m_τ = 1776.86 MeV; `mphi_scc := m_tau_pdg_eV` by structural self-consistency (F₂₁ = Z₇ ⋊ Z₃ + three-generation closure + MDL minimality); proved by `rfl` (CatAL)
 - `mkink_from_scc` — BPS kink mass M_kink = (8/49)·m_τ = 290.10 MeV; proved by `rfl` (CatAL)
 - `fpi_from_scc` — pion decay constant f_π = M_kink/π = 92.34 MeV (+0.30% vs PDG 92.07, 2.6× precision improvement, no free parameters); definitional equality in ℝ via `Real.pi`, proved by `rfl` (CatAL)

*Rank 55-3DLT — Spatially Extended Lifting (`SpatiallyExtendedLifting.lean`)*

- `causal_path_exists` — causal path existence for forward-causal pairs (theorem, not axiom; CatAL)
- `spatially_extended_composite_lifting` / `meson_bound_state_exists` — 3D meson existence (CatAL)

*Rank 38-QEC — QEC Stabilizer Code (`QECStabilizer.lean`)*

- `qec_gte_is_stabilizer_code` — the [D]-measure defines a QEC structure: code subspace = PSC-admissible beables; fmdl_step5 is the stabilizer; DWeight = 0 is the syndrome; mass gap bounds error energy (CatAL, zero sorry)
- `qec_orbit_closure` — fmdl_step5 maps every code word to a code word (vacuum is fixed point; gen₁→gen₂→gen₃→vacuum; CatAL)
- `qec_dweight_projector` — DWeight > 0 ↔ InCodeSubspace (projector onto code subspace; CatAL)
- `qec_error_detected` — perfect error detection: ¬PSCAdmissible b → DWeight b = 0 (CatAL)
- `qec_generation_mass_advance` — generation mass index (GTE_mass) is a logical observable: fmdl_step5 advances mass monotonically along non-vacuum orbit (CatAL)
- `qec_mass_gap_error_energy` — error energy bounded below by Δ ≥ 1.8 MeV (from gte_mass_gap; CatAL)

*Rank 28-QGR — Quantum Gravity (`QuantumGravity.lean`)*

- Beable-level QGR evidence structure; geometry CatA, particles CatAL, dynamics CatAD-strong (centroid CatAL partial)

*Rank 63-DMDL — [D]-Weighted SR Formula (`DWeightSRFormula.lean`)*

- Algebraic framework for the [D]-average of τ_c reproducing γ(v) = 1/√(1−v²/c²)
- `dmdl_dweight_positive`: every PSC-admissible beable has DWeight > 0 (CatAL)
- `dmdl_dweight_iff_code`: DWeight > 0 ↔ InCodeSubspace (CatAL)
- `dmdl_error_weight_zero`: non-PSC states have DWeight = 0 in [D]-average (CatAL)
- `dmdl_proper_time_ratio`: SR algebraic identity (c²−v²)/c² = 1−(v/c)² (CatAL)
- `dmdl_time_dilation_nonzero`: for v > 0, proper-time ratio < 1 (CatAL)
- `dmdl_dweight_sr_formula`: DWeight positivity + SR formula combined (CatAL)
- `dmdl_lorentz_factor_algebraic`: γ⁻² = (c²−v²)/c² identity (CatAL)
- `dmdl_tau_c_ratio_structure`: structural τ_c ratio bridge (CatAL)
- `dmdl_qec_sr_bundle`: full bundle — DWeight projector + SR formula (CatAL, zero sorry, propext+choice+Quot only)
- Computational (CatA): τ_c_ratio = 1.569±0.003, γ = 1.659, corrected error 1.2–1.8% at β=0.798, M=7

*Rank 244-MPH — Multi-Particle Hilbert Space (`MultiParticleHilbert.lean`)*

- Multi-particle state space built from QEC code subspace {vac, gen₁, gen₂, gen₃}
- `code_word_cardinality`: 4 code words (bijection with Fin 4, CatAL)
- `n_particle_state_count`: 4^N basis states for N particles (CatAL)
- `multiDWeight_eq_one`: DWeight product = 1 on all multi-states (CatAL)
- `multiMass_append`: mass observable is additive (CatAL)
- `multiMass_le`: total mass ≤ 3N for N particles (CatAL)
- `mass_hierarchy_three_states`: gen₃ > gen₂ > gen₁ > 0 (CatAL)
- `smGenMass_multi_anchor`: non-vacuum mass ≥ 1.8 MeV (CatAL)
- `multiparticle_orbit_closure`: f_MDL preserves code words (CatAL)
- `inner_product_positive_definite`: Kronecker basis IP positive definite (CatAL)
- `multiparticle_space_well_defined`: bundle theorem (CatAL); zero sorry

**Algebraic Universality Certificate — GF(7) Polynomial (PhiMDLUniversality.lean; 3 theorems, 0 sorry)**

An independent, Cook-free Turing universality certificate for Rule 110, Φ_MDL, and the UWCA:

- `rule110_z7_poly_rep` — Rule 110 update function equals the multilinear polynomial p(L,C,R) = C+R−CR−LCR over F₇ = ℤ/7ℤ, verified exhaustively by `native_decide` (CatAL, zero sorry)
- `rule110_center1_is_nand` — At center cell C=1, p(L,1,R) = 1−LR = NAND(L,R), proved by `decide` (CatAL, zero sorry)
- `z7_prime_field_universality` — NAND functional completeness ⟹ Rule 110 Turing universal without the Cook cyclic tag system construction (CatAL, 1 named axiom; Cook (2004) is a corollary)

Module: `UgpLean.Universality.PhiMDLUniversality`; companion: `rule110-lean/Rule110/AlgebraicUniversality.lean`.

**Particles-Computation-Spacetime Trinity (ParticlesComputationSpacetimeTrinity.lean; zero sorry)**

One Φ_MDL kink bundles three CatAL roles from the same 19-bit polynomial `p(L,C,R) = C+R−CR−LCR`:

- `particles_computation_spacetime_trinity` — master `Nonempty ParticlesComputationSpacetimeTrinityBundle` certificate (CatAL)
- `particles_computation_spacetime_trinity_certified` — constructive bundle witness: charge from winding, fermion ID, PSC sectors, Rule 110 step, Turing universality; Role 3 cross-ref `psc_orbit_is_curvature_geodesic`
- `particles_computation_spacetime_trinity_with_universality` — conjunction + `z7kg_kink_universality` (CatAL)

**Single-Source Principle — Five GTE Polynomial Roles (FiveRolesPolynomial.lean; zero sorry)**

The same 19-bit polynomial `p(L,C,R) = C+R−CR−LCR` serves five physical roles at `K_extra = 0`:

- `gte_polynomial_five_roles_k_extra_zero` — **master Single-Source Principle bundle** (CatAL/CatA): Role 1 Rule 110 (`rule110_z7_poly_rep`), Role 2 gauge (`gte_winding_sm_vertex_conserved_full` docstring ref), Role 3 gravity (`unique_cubic_gravity_coupling`), Role 4 entanglement (CatA Bell S=2.4459), Role 5 baryon (`gte_baryon_number_topological_charge`); plus exactly five distinct roles
- `gte_polynomial_five_roles_certified` — per-role substance (five zero-sorry sub-theorems)
- `gte_polynomial_five_labelled_roles` — structural role count and gravity/entanglement distinctness
- `gte_polynomial_three_roles_k_zero` — sub-bundle in `PMDLGravityTheorems.lean` (Roles 1+3 only)

---

**Algebraic Necessity, Gravity Sector, QCA/QEC (zero sorry on listed theorems)**

*Rank 075-ALGEC — Algebraic Necessity (`Universality/AlgebraicNecessityTheorem.lean`)*

- `algebraic_necessity_theorem` — F₂₁ = Z₇ ⋊ Z₃ is the unique non-abelian group of order 21; N_gen = 3 uniquely forced (CatAL)
- `b0_uniquely_forces_n7` — one-loop QCD b₀ = |Z₇| = 7 forces the Z₇ orbit period (CatAL)
- `no_ca_replica_as_corollary` — no finite-CA exact Lorentz replica as structural corollary (CatAL)

*Frobenius Prime & Beta Coefficient (`FrobeniusPrimeIdentity.lean`, `BetaCoefficientIdentity.lean`)*

- `frobenius_prime_bundle` — |Z₇| = |Z₃|² − |Z₃| + 1 unifies F₂₁ and PSC n=10 derivations (CatAL)
- `gte_beta_coefficient_bundle` — b₀ = (11N_c − 2N_f)/3 = |F₂₁|/N_c = |Z₇| = 7 (CatAL)
- `gte_planck_cascade_group_identity` — Planck cascade group-order identity (CatAL)

*Z₃-Invariant Entropy & Hierarchy CatAL Closure (`Z3InvariantEntropy.lean`, `Z3SubOrbitDisjointness.lean`, `PSCOrbitWindows.lean`)*

- `psc_admissible_implies_color_neutral` — PSC-admissible beables exclude free single-quark color carriers (CatAL)
- `z3_invariant_entropy_closes_hierarchy` — bundles numeric identity, PSC confinement, two-equal orbit non-selection, and Z₃ sub-orbit disjointness (CatAL)

*Rank 075-GR — Stress–Energy & Async Lifting (`StressEnergyTensor.lean`, `AsyncLiftingTheorem.lean`)*

- `phimdl_tmunu_symmetric` / `phimdl_tmunu_vacuum_zero` — Klein–Gordon T_μν symmetry and vacuum cancellation (CatAL)
- `phimdl_gravity_sector_prerequisites` — emergent-gravity prerequisite bundle (CatAL)
- `async_algebraic_lifting_theorem` — async DWeight/PSC evaluation equals sync global evaluation (CatAL)

*Geodesic Pass 4 (`GeodesicTheorem.lean` updates)*

- `dweight_centroid_follows_orbit` / `gte_discrete_equivalence_principle` — discrete Ehrenfest and iterated DWeight preservation (CatAL)
- `gte_geodesic_theorem_orbital` — PSC orbit persistence under f_MDL iteration (CatAL)
- `timelike_adjacent_is_geodesic_path` / `d2_geodesic_step_is_geodesic_path` — single-step geodesic identification (CatAL)

*Rank 074-3D — Winding–Coin Decoupling (`Substrate/WindingCoinDecoupling.lean`)*

- `diagonal_coin_decouples_sectors` — PSC maps commuting with Z₇ winding are diagonal (CatAL)
- `phimdl_domain_wall_junction_tension_exact` — domain-wall junction tension from BPS action (CatAL)

*Rank 074-C2 — Coherence Measure Uniqueness (`Substrate/CoherenceMeasureUniqueness.lean`)*

- `c2_uniqueness_structural_bundle` — MDL-unique [D] under architectural restrictions (CatAL)
- `c2_thermal_closure_bundle` — Gibbs free-energy gap selects canonical sector distribution; KL sorrys closed (CatAL)

*No Class 4 & CMCA Continuum (`NoClass4OuterTotalisticZ7.lean`, `Framework/CMCAContinuumLimit.lean`)*

- `no_class4_outer_totalistic_z7_3d` — no outer-totalistic Z₇ VN6 rule is Wolfram Class 4 (1 axiom `chirality_necessary_for_class4`)
- `no_finite_ca_exact_lorentz_replica` / `cmca_continuum_limit_is_phimdl` — no-CA-replica theorem; Φ_MDL is unique exact-Lorentz limit (CatAL)

*Rank 38-QEC — Updated QEC bundle (`Spacetime/QECStabilizer.lean`)*

- `dweight_pos_of_admissible` / `dweight_pos_iff_admissible` — DWeight projector ↔ PSC code subspace (CatAL)
- `qec_gte_is_stabilizer_code` — full 38-QEC dictionary bundle (CatAL)

*Rank 13-LSD — Fourier heat-kernel scaffolding (`Spacetime/Spectral/HeatKernelFourier.lean`)*

- `cayley_eigenvalue_at_zero_eq_degree` — zero sorry; 3 documented analytical sorrys in Gaussian-limit chain

---

## New modules (three-tape CMCA)

### Spacetime
- `UgpLean.Spacetime.HolographicScaling` — Three-tape CMCA is holographic: \(7^{3L}\) vs \(7^{L^3}\); \(3/L^2 \to 0\) (CatAL)

### Algebra
- `UgpLean.Algebra.ChargeFromPolynomial` — \(3Q(w)=p(0,w,0)=w\); gravity/EM degree split; tape role asymmetry; non-separability (CatAL)
- `UgpLean.Algebra.SU3GluonCount` — 8 SU(3) gluon generators from \(\Delta w=\pm1\); baryon color neutrality (CatAL)
- `UgpLean.Algebra.ColorConfinementMDL` — \(\Delta K=\log_2(9)\) MDL cost of free colored quarks (CatAL)
- `UgpLean.Algebra.BaryonNumber` — \(B=(1/3)\sum \chi_q(w_j)\) topological charge; \(B=1/3\) from \(N_{\mathrm{tapes}}=3\) (CatAL)
- `UgpLean.Algebra.ChiralDoublet` — Rule124 = Rule110 with L↔R spatial reflection (CatAL)
- `UgpLean.Algebra.SRRGCABridge` — \(1/\varphi\) = positive root of \(p(x,x,x)=x\) (CatAL)
- `UgpLean.Algebra.GaugeMDL` — three previously axiomatic SU(2)_L propositions now machine-certified: potential invariance, covariant derivative minimality, W-boson generator algebra. All zero sorry.

### BraidAtlas
- `UgpLean.BraidAtlas.WindingToBraidRep` — Fermionic sectors \(\{2,4,6\}\) = non-primitive roots of \(\mathbb{Z}_7^\times\); algebraic ID (CatAL)

### Gravity
- `UgpLean.Gravity.PMDLGravityTheorems` — MDL uniqueness, vacuum fixed-point, mass hierarchy (CatAL)
- `UgpLean.Framework.MDLTower` — **MDL-TOWER CatAL**: `mdl_tower_bundle` unifies three nested MDL roles (theory selection via `mdl_ca_rule_coding_closed`, PMDL gravity via `unique_cubic_gravity_coupling`, Born rule via `born_rule_unconditional`); `mdl_tower_three_levels_non_circular`; zero sorry, zero axioms
- `UgpLean.Universality.NgenUniversalityPartial` — **N_gen partial CatAL**: `ngen_partial_universality_catal` bundles five independent CatAL constraints forcing N_gen = 3 (PSC PI Layer I 34,560 enumeration, DPP, CMCA, TPC, Gorard D²=16); full seven-constraint theorem open; zero sorry, zero axioms
- `UgpLean.TE22.ScanCertificate` — **PSC-PI-NGEN CatAL**: `psc_enumeration_forces_ngen_3` via native_decide over 34,560 universe descriptions (12 Layer I survivors, all N_gen=3); zero sorry
- `UgpLean.Gravity.GorardRicciFlatVacuum` — Vacuum Ricci-flat; causal diamond \(V=T^4/4\) (CatAL)
- `UgpLean.Gravity.LorentzGroupSO13` — All 12 \(\mathfrak{so}(1,3)\) commutation relations; Thomas precession (CatAL)
- `UgpLean.Gravity.FermionicStatistics` — Fermionic statistics chain zero sorry; exchange phase formula (CatAL)
- `UgpLean.Gravity.PSCEpochSelection` — PSP axiom L1/L2/T-PSP; \(\Omega_\Lambda = 0.690\) numerical bound; **Incompleteness-Cosmology chain** `incompleteness_implies_nonzero_omega_lambda` (CatAL)
- `UgpLean.Gravity.Z7AnomalyFree` — Z₇ global scalar anomaly-free: shift invariance, Jacobian = 1, vacuum sector equiprobability (all zero sorry, CatAL; graduated)

### ContinuumLimit
- `UgpLean.ContinuumLimit.GorardVacuumW1Bridge` — Gorard ORIC adjacent-edge κ=0 ∀ n; vacuum W₁=1; conditional on W₁=1 gives κ=0 (CatAL, zero sorry; graduated)
- `UgpLean.ContinuumLimit.WassersteinDistance` — Full W₁ Wasserstein metric scaffold: non-negativity, Kantorovich dual lower bound, triangle inequality via glued coupling, zero-iff-equal, infimum attained, coupling set compact (all zero sorry, CatAL; graduated)
- `UgpLean.Universality.MDLDerivabilityCriterion` (§5 extended) — **T96-02 CA-level closure CatAL**: `z5_fmdl_no_psc_kink_orbits` (GTE polynomial over GF(5) with winding-based PSC predicate, `native_decide`, 3125 states); `mdl_total_z7z3_strictly_beats_z5z3` (total MDL gap 3+0 < 5+6, `decide`); `mdl_ca_rule_coding_closed` (explicit K_data witness, master closure); non-circular MDL derivation Z₇×Z₃ fully machine-certified without SM input

### Lorentzian ([ugp-physics-lean](https://github.com/novaspivack/ugp-physics-lean))
- `UgpPhysicsLean.Lorentzian.MinkowskiSpace` — Minkowski metric, LorentzGroup (CatAL)
- `UgpPhysicsLean.Lorentzian.SpinorRep` — Spinor \(2\pi\) rotation = \(-1\); spin-statistics axiom (CatAL + 1 named axiom)
