# ugp-lean: Module Reference

## Dependency Rule

**Core/ may not import Compute/** — enforced to prevent circularity in RSUC.

## Module Graph (Simplified)

```
UgpLean.lean
├── Core (no Compute)
│   ├── RidgeDefs, MirrorDefs, TripleDefs, SievePredicates,
│   ├── Disconfirmation, RidgeRigidity, MirrorAlgebra
├── Compute (RidgeDefs, MirrorDefs)
│   ├── PrimeLock, Sieve, SieveBelow10, SieveExtended,
│   └── ExclusionFilters, DecidablePredicates
├── Classification
│   ├── Bounds, TheoremA, TheoremB, RSUC,
│   └── FormalRSUC, MonotonicStrengthening
├── GTE
│   ├── Evolution, Orbit, UpdateMap, GTESimulation, EntropyNonMonotone,
│   ├── MersenneGcd, MersenneLadder, MirrorDualConjecture, MirrorShift,
│   ├── InertPrimes, ResonantFactory, AnalyticArchitecture, FiberBundle,
│   ├── LinearResponse, ScaleConnection, UGPPrimes, PrimeFactorAnalysis,
│   ├── DSIExport, GeneralTheorems, StructuralTheorems, UniquenessCertificates
├── BraidAtlas
│   ├── ChargeTheorem (Q = W_g/N_c; mirror_winding_number_zero axiom)
│   ├── CompositeTriples (composite c-rule + baryon (a,b,c))
│   ├── ChiralitySquaring (V−A arithmetic signature)
│   ├── ChargeDerivation (SM winding from N_c)
│   ├── CoxeterConductor (Q(ζ₁₂₀) Toda spectrum theorem)
│   ├── CoxeterConductorTowerLaw (8X³−6X−1 irreducibility)
│   └── EWBosons (c(W)=11, c(Z)=12, c(H)=13 from N_c)
├── ElegantKernel (k_L²=7/512)
│   ├── ChiralityFeature, FibonacciHessian, KGen, KGen2,
│   ├── PentagonalUniqueness, D5StructuralAxiom, MuTriple, and Unconditional/*
├── MassRelations
│   ├── KoideAngle, KoideClosedForm, KoideNewtonFlow,
│   ├── KoideS3DiscreteIdentities, CKMTheta23, CKMMixing,
│   ├── ClebschGordan, BinaryCascade, PhysicalMasses,
│   ├── ScaleTransport, SeesawIndex, FroggattNielsen, NeutrinoFroggattNielsen,
│   ├── CartanFlavonPotential, ClaimCBridge, DownRational, SU3FlavorCartan,
│   ├── HeavyFermionTower, LeptonMassPrediction, UpLeptonCyclotomic,
│   ├── VVMechanism, VVAllCoefficientsFromNc, Z2OrbifoldDepth
├── GaloisStructure (CyclotomicLayers, MinimalCyclotomic)
├── CyclotomicCompleteness
│   ├── CoxeterBiconditional (h|60 ↔ 2h|120 biconditional; per-algebra h|60 certs; B₄ conductor; e7_double_failure; coxeter_biconditional_summary)
│   └── CyclotomicContainment (cyclotomic120_contains_primitive_root; cyclotomic_field_embedding; per-algebra AlgHom certs for G₂, F₄/E₆, E₈; zero sorry)
├── Phase4 (DeltaUGP, GaugeCouplings, UCL, PR1, AsymptoticSparsity,
│           PositiveRootTheorem, GaloisProtection, TwoLoopCoefficient)
├── NullDiscipline [migrated to ugp-physics-lean: SaturationBarrier, TheoremEligibility]
├── IPT [migrated to ugp-physics-lean: InformationProfitThreshold]
├── PSC (RCCInfiniteFamilies) [ThreeRouteForcing migrated to ugp-physics-lean]
├── TE22 (ScanCertificate)
├── SelfRef (LawvereKleene, RiceHalting)
├── Universality (Rule110, UWCA, UWCASimulation, UWCAembedsRule110,
│                  UWCAHistoryReversible, TuringUniversal, ArchitectureBridge)
├── QuarterLock, LModelDerivation, Conjectures
├── Papers (Paper25, UGPMain)
└── Instance (NemSBridge)
```

**Module count:** 117 `.lean` files. The **12-layer** diagram and per-layer module names are authoritative in `paper/ugp_lean_formalization.tex` (§Architecture, Figure/module stack).

## Module Descriptions

### Core Layer

| Module | Purpose |
|--------|---------|
| **RidgeDefs** | Rₙ = 2ⁿ − 16, strictRidgeMin=16, UGP-1 params (s=7, g=13, t=20) |
| **MirrorDefs** | b₁=b₂+q₂+7, q₁=q₂−13, c₁=b₁q₁+20; leptonB=73, leptonC1=823, mirrorC1=2137 |
| **TripleDefs** | `Triple` structure, LeptonSeed, LeptonMirror, MirrorEquiv, lexLt |
| **SievePredicates** | SemanticFloor; QuarterLockRigidAt n, RelationalAnchorAt n, UnifiedAdmissibleAt n; legacy n=10: QuarterLockRigid, RelationalAnchor, UnifiedAdmissible |
| **Disconfirmation** | MirrorEquivClass equivalence, lexLt_seed_mirror |
| **RidgeRigidity** | Ridge remainder lock (m₂=15), quotient-gap 13 |
| **MirrorAlgebra** | mirrorS, discSq, symmetric mirror form, discriminant |

### Compute Layer

| Module | Purpose |
|--------|---------|
| **PrimeLock** | Nat.Prime 823, 2137; mirror_prime_lock; c1_from_divisor |
| **Sieve** | ridgeSurvivorsFinset, ridgeSurvivors_10 = {(24,42),(42,24)} |
| **SieveExtended** | n∈[5,30] sieve range, mirrorDualCount_10 |
| **ExclusionFilters** | exclude_16..63 — composite c₁ for listed divisors |
| **DecidablePredicates** | decUnifiedAdmissible, correctness lemmas |

### Classification Layer

| Module | Purpose |
|--------|---------|
| **Bounds** | CandidatesAt n : Finset Triple (biUnion over ridgeSurvivorsFinset n); Candidates = CandidatesAt 10 |
| **TheoremA** | theoremA_general: UnifiedAdmissibleAt n t → t ∈ CandidatesAt n; theoremA: n=10 corollary |
| **TheoremB** | ResidualAt n, Residual = ResidualAt 10; Residual = Candidates; MDL selects LeptonSeed |
| **RSUC** | rsuc_theorem (combines A + B) |
| **FormalRSUC** | rsuc_formal, rsuc_canon (two-layer RSUC with interpretation) |
| **MonotonicStrengthening** | strengthening_cannot_add_survivors |

### GTE Layer

| Module | Purpose |
|--------|---------|
| **Evolution** | fib13=233, canonicalGen2/3, canonical_orbit_triples, even_step_rigidity |
| **Orbit** | canonical_orbit_three_steps |

### Structural / Phase 4 / Universality

| Module | Purpose |
|--------|---------|
| **QuarterLock** | quarterLockLaw, kernelDefect, quarterLockStability |
| **ElegantKernel** | k_L2=7/512, L_model=log₂(2000/3) |
| **DeltaUGP** | deltaUGPFormula, leptonB_matches_deltaUGP |
| **GaugeCouplings** | g1Sq_bare, g2Sq_bare, g3Sq_bare; D₂, D₃ |
| **UCL, PR1** | Structural stubs |
| **Rule110** | rule110Output, rule110Minterms, Cook citation |
| **UWCA** | UWCATile, rule110Tiles |
| **UWCAembedsRule110** | uwca_simulates_rule110 |
| **TuringUniversal** | ugp_is_turing_universal |
| **ArchitectureBridge** | uniqueness_of_physical_program |

### Papers & Instance

| Module | Purpose |
|--------|---------|
| **Paper25** | Citable stubs for Paper 25 |
| **UGPMain** | Citable stubs for UGP Main |
| **NemSBridge** | GTESpace instance, RSUC for nems-lean |

### BraidAtlas Layer (P17 algebraic substrate)

| Module | Purpose |
|--------|---------|
| **ChargeTheorem** | Theorem C-W (Q = W_g/N_c); anomaly cancellation forces N_c=3; SM charge derivation; GTE-P7 mirror dark matter quantum numbers (Q=0, color singlet) |
| **CompositeTriples** | Composite c-rule; baryon (a, b, c) derivation including proton/neutron and full strange-baryon octet; meson constraints |
| **ChiralitySquaring** | Arithmetic signature of V−A chiral structure: (13×17×29)² perfect square; 17×137 not perfect square |
| **ChargeDerivation** | SM winding pattern derived from N_c; Y_QL = 1/(2N_c) unifies VV slope and braid winding |
| **CoxeterConductor** | Arithmetic backbone of the Coxeter–conductor theorem; **E7 falsifier** (h=18 ∤ 120); φ(120)=32, 3∤32; lcm(30,12,8,6,3,2,1)=120 |
| **CoxeterConductorTowerLaw** | Tower-Law step: 8X³−6X−1 irreducible over ℚ via rational-root theorem; finrank ℚ[X]/(p) = 3 (zero sorry; tower-law certificate) |
| **EWBosons** | Electroweak boson c-values c(W)=11, c(Z)=12, c(H)=13 derived from canonical ridge factorisation + Higgs gap identity at n=10; consecutive triple centred on 2·T(N_c); triangular-number unification |

### CyclotomicCompleteness Layer (Q(ζ₁₂₀) filter arithmetic)

| Module | Purpose |
|--------|---------|
| **CoxeterBiconditional** | Arithmetic backbone of the Coxeter–conductor biconditional: h\|60 ↔ 2h\|120 (omega); per-algebra h\|60 certs for G₂(6), F₄(12), E₆(12), E₈(30) via norm\_num; B₄ conductor analysis (conductor=8, actual field Q(√2) ⊆ Q(ζ₈) ⊆ Q(ζ₁₂₀)); `e7_double_failure` (18∤60 AND 18∤120); `coxeter_biconditional_summary` master theorem; all zero sorry. Imports BraidAtlas.CoxeterConductor. |
| **CyclotomicContainment** | Field-theoretic biconditional: **Theorem A** `cyclotomic120_contains_primitive_root` — for h\|60, `CyclotomicField 120 ℚ` contains a primitive 2h-th root of unity (zero sorry). **Theorem B** `cyclotomic_field_embedding` — injective ℚ-algebra embedding `CyclotomicField (2h) ℚ →ₐ[ℚ] CyclotomicField 120 ℚ` whenever h\|60 (zero sorry). Per-algebra `AlgHom` certificates: `g2_cyclotomic_embedding` (h=6), `f4_e6_cyclotomic_embedding` (h=12), `e8_cyclotomic_embedding` (h=30). Uses Mathlib `IsCyclotomicExtension`, `IsPrimitiveRoot`, `IsSplittingField`. Imports CoxeterBiconditional. |

### MassRelations Layer (CKM and Koide structural identities)

| Module | Purpose |
|--------|---------|
| **CKMTheta23** | P01 OP(v): ridge--Mersenne identity `R_n = D_1 · M_(n−4)` for n ≥ 4; CKM θ_23 ratio τ(R_10)/D_1 = 30/16 = 15/8 at n = 10 and unique to n = 10 across [5,20]; bundled `op_v_ckm_theta23_closure` certificate (zero sorry) |
| **KoideS3DiscreteIdentities** | P01 OP(vii): discrete shadow of the S₃ equal-norm condition on the lepton a-component; canonical orbit a-values (a_e, a_μ, a_τ) = (1, 9, 5) satisfy `2 · a_τ = a_e + a_μ` (i.e., 2·5 = 1+9 = 10); bundled `lepton_a_discrete_S3_identity` certificate (zero sorry, zero hypotheses) |
| **CKMMixing** | CDM mechanism (2026-05-11): derives Wolfenstein Cabibbo parameter λ ≈ \|V_us\| from GUT group theory and VV down-type coefficient α_d = 13/9; certifies \|V_us\|_CDM = ε₁^(α_d) = exp(−13π/27) ≈ 0.2203 (1.9% off PDG); key theorems: `cabibbo_effective_charge` (Δa_eff = α_d), `cabibbo_charge_from_GUT` (GUT group-theory origin), `cabibbo_vev_formula` (CDM VEV formula), `fn_vv_correction_additive` (additive VV propagation bridge), `fn_diagonalization_vv_bridge`, `fn_cdm_physical_sorry` (algebraic identity; zero sorry); all 20 theorems zero sorry |

### PSC Layer

| Module | Purpose |
|--------|---------|
| **RCCInfiniteFamilies** | RCC over all four infinite classical Lie families (B_n, C_n, D_n, A_n): Layer I/II fail by w_0 = −id Weyl-element argument and dimension thresholds |
| **ThreeRouteForcing** | **Migrated to ugp-physics-lean** (`UgpPhysicsLean.PSC.ThreeRouteForcing`). P01 OP(i) parametric carrier for the [Gödel–Turing ∧ Reflexive Landauer ∧ Norfleet holonomy defect] ⇔ PSC capstone (no smuggling, zero sorry, zero axioms). |
