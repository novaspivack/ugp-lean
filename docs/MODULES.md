# ugp-lean: Module Reference

440 `.lean` files across 32 directories (plus 7 root-level modules). The definitive layer diagram and per-module descriptions are in `paper/ugp_lean_formalization.tex` §Architecture.

## Dependency Rule

**Core/ may not import Compute/** — enforced to prevent circular reasoning in RSUC. See [DESIGN.md](DESIGN.md).

---

## Layer Overview

| Layer | Files | What it contains |
|---|---|---|
| [Core](#core) | 7 | Ridge/mirror/triple definitions — no algorithms |
| [Compute](#compute) | 6 | Sieve algorithms, `native_decide` proofs |
| [Classification](#classification) | 7 | Theorems A/B, RSUC, monotonic strengthening, N_gen uniqueness |
| [GTE](#gte) | 32 | GTE orbit, update map, generation structure, entropy, fiber bundle |
| [ElegantKernel](#elegantkernel) | 28 | Quarter-Lock, UCL Elegant Kernel, unconditional closure |
| [MassRelations](#massrelations) | 40 | Koide, CKM, PMNS, Higgs quartic, neutrino sector, pion mass |
| [BraidAtlas](#braidatlas) | 14 | Charge theorem, EW bosons, dark matter quantum numbers |
| [Universality](#universality) | 97 | Rule 110, UWCA, Turing universality, GTE compilation/uniqueness, GTP-3 uniqueness, winding superselection |
| [Polynomial](#polynomial) | 18 | GF(7) ground states, period-475, spin-7 spectroscopy, MDL unification |
| [Physics](#physics) | 8 | Kink physics, Z₇ vacuum selection, CMCA physical point, BPS coupling |
| [Substrate](#substrate) | 31 | PhiMDL fluctuation spectrum, sech overlap bounds, Wightman axioms |
| [Gravity](#gravity) | 28 | Yukawa, FKTT, Wald entropy, FLRW, spinors, CC residual |
| [Spacetime](#spacetime) | 39 | Geodesic, mass gap, orbit hierarchy, QEC, quantum gravity, holography |
| [Algebra](#algebra) | 25 | Z₇/F₂₁ Galois structure, SM gauge group, SRRG–CA bridge, octonion certificates, Q(ζ₇) Galois group, cyclotomic disjointness |
| [Framework](#framework) | 10 | GTE-NEMS instance, MDL tower, CMCA continuum limit, coalgebra |
| [ContinuumLimit](#continuumlimit) | 7 | Wasserstein distance, GF(7) vacuum fixed point, Gorard bridge |
| [QFT](#qft) | 2 | Gauged mass gap, chiral symmetry breaking |
| [VEVProof](#vevproof) | 3 | EW Goldstone manifold, entropy correction, PSC entropy duality |
| [VEVNoGo](#vevnogo) | 1 | SRRG no-go theorem |
| [GaloisStructure](#galoisstructure) | 2 | Cyclotomic layers, minimal cyclotomic |
| [CyclotomicCompleteness](#cyclotomiccompleteness) | 2 | Coxeter biconditional, Q(ζ₁₂₀) field embedding |
| [Phase4](#phase4) | 8 | DeltaUGP, gauge couplings, Galois protection, two-loop coefficient |
| [PSC](#psc) | 2 | RCC infinite families |
| [TE22](#te22) | 1 | SM gauge universe scan certificate |
| [SelfRef](#selfref) | 2 | Lawvere–Kleene, Rice–Halting |
| [Papers / Instance](#papers--instance) | 3 | Citable stubs, NEMS bridge |
| [Cosmology](#cosmology) | 3 | CC bracket Hurwitz, MDL initial state, primordial amplitude |
| [Foundations](#foundations) | 2 | CMCA record filtration, CMCA thermodynamic bridge |
| [Measurement](#measurement) | 1 | Landauer floor |
| [Particles](#particles) | 2 | Kink fusion rules, muon Borel identity |
| [QM](#qm) | 2 | Bilinear neutrino no-go, Kähler state manifold |
| Root-level modules | 7 | Conjectures register, ElegantKernel/QuarterLock/LModelDerivation/MassRelations umbrellas, GTEDerivationChain, OQ26Arithmetic |

---

## Core

Predicate and structural *definitions* only. No algorithms, no `native_decide`. **May not import Compute/.**

| Module | Purpose |
|---|---|
| **RidgeDefs** | Rₙ = 2ⁿ − 16; UGP-1 parameters (s=7, g=13, t=20) |
| **MirrorDefs** | Mirror map (b₂,q₂) ↦ (b₁,q₁,c₁); leptonB=73, leptonC1=823 |
| **TripleDefs** | `Triple` structure; LeptonSeed, LeptonMirror, lexLt |
| **SievePredicates** | SemanticFloor; QuarterLockRigidAt n; RelationalAnchorAt n; UnifiedAdmissibleAt n |
| **Disconfirmation** | MirrorEquivClass equivalence; lexLt_seed_mirror |
| **RidgeRigidity** | Ridge remainder lock (m₂=15); quotient-gap 13 |
| **MirrorAlgebra** | mirrorS, discSq, symmetric mirror form, discriminant |

## Compute

Algorithms and computational evidence. Imports Core.

| Module | Purpose |
|---|---|
| **PrimeLock** | `Nat.Prime 823`, `Nat.Prime 2137`; mirror_prime_lock |
| **Sieve** | `ridgeSurvivorsFinset`; `ridgeSurvivors_10 = {(24,42),(42,24)}` |
| **SieveExtended** | Sieve for n ∈ [5,30]; `mirrorDualCount_10` |
| **SieveBelow10** | Survivors empty for n < 10; n=10 is minimal admissible ridge |
| **ExclusionFilters** | Composite c₁ exclusions for divisors 16–63 |
| **DecidablePredicates** | `decUnifiedAdmissible`; correctness lemmas |

## Classification

| Module | Purpose |
|---|---|
| **Bounds** | `CandidatesAt n` — biUnion over ridgeSurvivorsFinset n |
| **TheoremA** | `theoremA_general`: UnifiedAdmissibleAt n t → t ∈ CandidatesAt n |
| **TheoremB** | `Residual = Candidates`; MDL selects LeptonSeed |
| **RSUC** | `rsuc_theorem`: unique residual up to MirrorEquiv; MDL selects (1,73,823) |
| **FormalRSUC** | `rsuc_formal`, `rsuc_canon` — two-layer RSUC with semantic interpretation |
| **MonotonicStrengthening** | Strengthened predicates cannot add survivors |

## GTE

| Module | Purpose |
|---|---|
| **Evolution** | Canonical orbit triples; even-step rigidity |
| **Orbit** | `canonical_orbit_three_steps` |
| **UpdateMap** | GTE update map T; ridge remainder lock (all n≥5); mirror b₁-invariance |
| **GeneralTheorems** | General GTE structural theorems |
| **MersenneGcd** | `gcd(2ᵃ−1, 2ᵇ−1) = 2^gcd(a,b)−1` |
| **MersenneLadder** | RC tier structure: 1023, 65535 Mersenne boundaries |
| **PrimeFactorAnalysis** | c-value factorizations; gen 1/2/3 isolation and entanglement |
| **ResonantFactory** | Twin-prime program; Q₊ = Q₋ + 2; Hasse local density |
| **MirrorDualConjecture** | τ(Rₙ) = 5·τ(2^(n−4)−1); MDL c₁ monotone across levels |
| **MirrorShift** | Mirror-shift arithmetic |
| **UGPPrimes** | UGP prime sequence; infinitude conjecture (open) |
| **InertPrimes** | Inert prime structure |
| **AnalyticArchitecture** | Two named axioms (Tenenbaum III.6); Q₋⊥Q₊ proved |
| **DSIExport** | Real-valued c₁ on hyperbola; derivative positive on shell |
| **StructuralTheorems** | Mirror fiber size 2; fingerprint fixed-point (Tarski) |
| **UniquenessCertificates** | Uniqueness certificates for GTE structure |
| **GTESimulation** | GTE simulation on Z₇⁵ |
| **EntropyNonMonotone** | ML-9 companion: coarse Shannon-entropy drop |
| **FiberBundle** | GTE fiber bundle structure |
| **LinearResponse** | Linear response around GTE orbit |
| **ScaleConnection** | Scale connection for GTE |
| **GTBGenerationPrimes** | GTB generation prime certificates (823, 2137, 9007, …) |
| **NcColorArithmetic** | N_c = 3 color arithmetic |
| **NuclearPairing** | 5^(3/2) pairing constant; proton/neutron b-seed parity (8 theorems) |
| **SylowIndexCouplingHierarchy** | Gauge coupling hierarchy from Sylow indices of F₂₁ |

## ElegantKernel

| Module | Purpose |
|---|---|
| **QuarterLock** | `quarterLockLaw`: k_M = k_gen2 + ¼k_L² |
| **LModelDerivation** | L_model = log₂((D₁·5³)/3) derived |
| **ElegantKernel** (root) | k_L² = 7/512 |
| **ChiralityFeature** | Chirality feature of the EK |
| **D5StructuralAxiom** | D₅ pentagonal structure |
| **FibonacciHessian** | Fibonacci Hessian eigenvalue |
| **KGen2** | k_gen2 = −φ/2 = cos(4π/5) |
| **MuTriple** | μ-triple structure |
| **PentagonalUniqueness** | Pentagon quadratic uniqueness |
| **Unconditional/** | 18 modules: full UCL unconditional closure — CyclotomicChain, D5Renormalization, FibonacciPentagonBridge, FullClosure, KConstFullClosure, KGenFullClosure, KLFullClosure, PentagonConstraint, RiccatiFixedPoint, MasterCertification, UCLMassOrdering, UCLKoide, UCLLogBounds, UCLMassOrderingSBounds, UCLMassOrderingCoeffBounds, UCLMassOrderingBounds, UCLMassOrderingBridge, UCLMassOrderingCerts, UCLMassOrderingInterval, UCLMassOrderingDelta, UCLCalibration |

## MassRelations

| Module | Purpose |
|---|---|
| **MassRelations** (umbrella) | Top-level umbrella import |
| **KoideClosedForm** | Koide ↔ (2S)² = 3N algebraic normal form |
| **KoideNewtonFlow** | Newton flow fixes Koide null cone; S₃-equivariance |
| **KoideAngle** | Koide angle parametrization |
| **KoideS3DiscreteIdentities** | Discrete shadow of S₃: 2·a_τ = a_e + a_μ |
| **BinaryCascade** | Cascade closed form b_g = 2^(g−1)·b₁ |
| **PhysicalMasses** | Physical mass values and bounds |
| **SU3FlavorCartan** | SU(3) flavor Cartan structure |
| **CartanFlavonPotential** | Cartan flavon potential |
| **FroggattNielsen** | FN charge assignments for charged leptons |
| **NeutrinoFroggattNielsen** | FN texture (q₁,q₂)=(3,2); seesaw exponent 29/9 |
| **HeavyFermionTower** | Heavy fermion tower |
| **ClebschGordan** | Clebsch–Gordan coefficients for mass relations |
| **DownRational** | α_d = 13/9 from N_c = 3 |
| **UpLeptonCyclotomic** | Cyclotomic structure for up-type and lepton masses |
| **Z2OrbifoldDepth** | Z₂ orbifold depth structure |
| **ClaimCBridge** | Claim C (formal): TT = Weyl·2^g; Pentagon–Hexagon Bridge |
| **LeptonMassPrediction** | Lepton mass predictions |
| **ScaleTransport** | Scale transport |
| **SeesawIndex** | Seesaw index |
| **VVMechanism** | VV mechanism |
| **VVAllCoefficientsFromNc** | All VV coefficients derived from N_c |
| **CKMTheta23** | θ₂₃ ratio τ(R₁₀)/D₁ = 15/8; unique at n=10 |
| **CKMMixing** | CDM mechanism; \|V_us\| = exp(−13π/27); 20 theorems, 0 sorry |
| **NeutrinoMassRatio** | R ≈ 0.02936 within 1% of NuFIT 6.0; 5 theorems |
| **NeutrinoSector** | PMNS angles: sin²θ₁₂=4/13, sin²θ₂₃=19/42, δ_CP=8π/7 |
| **HiggsQuartic** | λ = φ/(4π)·(1 + (IPT−1)/27); 0.12 < λ < 0.14 |
| **TranscendentalMassBounds** | Six-quark PDG bands (CatAD) |
| **QuarkMassNumericalCerts** | Quark mass numerical certificates |
| **PionMassFromGOR** | Pion mass from Gell-Mann–Oakes–Renner |
| **PMNSNLOCorrection** | sin²θ₂₃^NLO = 209/441; 2b_R2 = \|F₂₁\| + 1 |

## BraidAtlas

| Module | Purpose |
|---|---|
| **ChargeTheorem** | Q = W_g/N_c; anomaly cancellation forces N_c=3 |
| **CompositeTriples** | Composite c-rule; all 9 light baryon b-formulas |
| **ChiralitySquaring** | V−A arithmetic signature: (13×17×29)² perfect square |
| **ChargeDerivation** | SM winding pattern from N_c |
| **CoxeterConductor** | Coxeter–conductor arithmetic; E₇ falsifier (h=18 ∤ 120) |
| **CoxeterConductorTowerLaw** | 8X³−6X−1 irreducible over ℚ; tower-law certificate |
| **EWBosons** | c(W)=11, c(Z)=12, c(H)=13 from ridge factorization |
| **MirrorWindingNumber** | Mirror winding number zero |
| **EWBosonRHNConnection** | EW boson–RHN connection |
| **RHNGapTheorem** | Right-handed neutrino gap theorem |
| **DarkBraidAtlas** | Dark matter quantum numbers |
| **DarkQuarkCharge** | Dark quark charge |
| **DarkGaugeCoupling** | Dark gauge coupling |

## Universality

97 files covering Rule 110 universality, UWCA, GTE compilation, orbit isolations, Z₇/Z₅ structure, and parity forcing. Key modules:

| Module | Purpose |
|---|---|
| **Rule110** | rule110Output, minterms, Cook citation |
| **UWCA / UWCASimulation** | UWCA sweep implements Rule 110 exactly |
| **UWCAHistoryReversible** | backward ∘ forward = id; history-lane reversibility |
| **UWCAembedsRule110** | UWCA simulates Rule 110 |
| **TuringUniversal** | `ugp_is_turing_universal` |
| **GTECompilation** | sigma_gte 1-tile program; `gte_compilation_theorem` by `rfl` |
| **GTEUniqueness** | `gte_uniqueness_up_to_bisimulation`: unique lawful UWCA program |
| **GoEHierarchy / GoEStabilityHierarchy** | Garden-of-Eden structure; orbital chain isolation |
| **CUP3DUniqueness** | SM orbit uniqueness; no false vacua; Z₇/Z₂ incompatibility |
| **CUP4TotalParity** | Minterm set uniqueness; Rule 110 unique weight-5 orbit satisfier |
| **CUP3DPSCUnification** | PSC and orbit unification in 3D |
| **Z5TransitivityUniqueness** | p=5 unique prime for full transitivity of weight-3 vector |
| **DimensionalSliceUniqueness** | Rule 110 forced on all d-dimensional axis-aligned slices |
| **OrbitPerturbationCatalog** | Complete orbit perturbation isolation (15 theorems) |
| **ParityProjectionForcing / Battery** | 777 additive forms + 16,807 mod-2 recodings; forcing maximal |
| **TriangleLiftTheorem / Structural** | 7⁸ exhaustive census; orbit + vacuum transparency force unique GF(7) rule |
| **EWBosonNumericalCerts** | M_W CatAL; M_Z, sin²θ_W threshold CatAD |
| **GUTStructure** | Dark baryon dilution; D_top = exp(−1/N_c) via Z₇ transitivity |
| **Z7ChargeConjugation** | Z₇ charge conjugation |
| **SMOrbitCausalIsolation** | SM orbit causal isolation |
| **PSCUniversality** | PSC universality |
| **GTP3Uniqueness** | GTP-3 uniqueness and count: SM orbit is the only GoE-rooted terminating 3-chain (exhaustive, 16,807 states) |
| **WindingSectorSuperselection** | Winding-sector superselection; topological kink stability |
| *(+ 72 more)* | See `UgpLean/Universality/` for full list |

## Polynomial

| Module | Purpose |
|---|---|
| **PolyExplorations** | 39 theorems: ground states {0,1,5}, period-475, GF(7³) 19-factor, vacuum basin=52 |
| **GTECausalTree** | 8 theorems: 1023-node binary tree, Horton r_B=2 |
| **MDLThreeLevelUnification** | Cross-module CatAL bundle: theory selection, PSC projection, orbit uniqueness |
| **GoldenQuadratic** | p(x,x,x)−x = −x(x²+x−1); SRRG and Rule 110 as ℤ-quadratic fibers |
| **SpinSevenGroundSpace** | Ground-space rigidity: cyclic zero-energy rings = {0ⁿ,1ⁿ,5ⁿ} for all n≥3 |
| **BiquadraticCompositum** | cond(K)=15=N_gen·N_fam for K=ℚ(√−3,√5); 15 theorems |
| **AGL17ChiralZ2** | \|AGL(1,7)\|=42; reflection swaps Rule 110 ↔ Rule 124 |
| **EisensteinIdentities** | F₂₁ ≅ (ℤ[ω]/(3+ω))⁺⋊μ₃; Φ₆ ladder identity web |
| **DynamicalZeta** | Fix(T_n)={vacuum} for all ring sizes; period-475 Artin–Mazur ζ |
| **SpinSevenWallSpectroscopy** | Directed wall energies; gap exponent 3/2; 14 theorems |
| **SpinSevenSpectatorAmplitude** | Zero-energy spectral radius ρ=1; gap-law A=1; 10 theorems |
| **SpinSevenGapAmplitude** | Through-walk counts; A²=1; 13 theorems |
| **SpinSevenTransferPrimitivity** | Perron–Frobenius hypothesis package, uniform in β; 7 theorems |

## Physics

| Module | Purpose |
|---|---|
| **ZSevenVacuumSelection** | V_coupling breaks Z₇ shift; bias minimum at k=0; vacuum-selection certs |
| **KinkVacuumPolarization** | One-loop kink vacuum-polarization spectrum |
| **KinkFormFactor** | Kink form factor; dissolution constant Λ_diss |
| **KinkPoleMassSpectralCore** | Pöschl–Teller spectral skeleton; Levinson identity (PARTIAL) |
| **BurnsideCosetCharges** | Coset-charge spectrum t_V=3, c_coset=−1 |
| **CCOneJumpResidual** | D_res left-c.e. bracket; σ* falsifiability horizon; 6 CatAL + 1 PARTIAL |
| **FKTTCoupling** | η_B=6.109×10⁻¹⁰ CatAL unconditional; BPS saturation by `rfl` |
| **CMCAPhysicalPoint** | aM=1/7, am_φ=7/8; Tape Saturation Theorem; M_Pl/Λ_GTE = 3¹⁰·7¹⁸/2⁴ |

## Substrate

| Module | Purpose |
|---|---|
| **PhiMDLFluctuationSpectrum** | Pöschl–Teller potential; sech integrals; 0 sorry |
| **SechOverlapIntegralBounds** | ∫sech³ = π/2; finite-r sech overlap bounds; 0 sorry |
| **SechOverlapIntegralBounds_bridge** | Mesh→integral bridge; 2 CatA axioms (documented) |
| **SechOverlapIntegralBounds_{cosh,r5bins,r5mesh,r11cert}** | Supporting sech bound certificates |
| **Substrate** (root) | Substrate-level definitions |
| **Wightman Axioms** | Wightman axioms for GTE substrate |
| **PSCStructureLorentzPreserved** | PSC structure Lorentz-preserved |
| **LagrangianLorentzScalar** | Lagrangian as Lorentz scalar |
| **PhiMDLPropagator** | φ_MDL propagator |
| **CMCAHilbertFockBridge** | CMCA Hilbert–Fock bridge |
| **TransputationG41 / TransputationStateSelector** | Transputation in G₄₁ |
| *(+ others)* | See `UgpLean/Substrate/` for full list |

## Gravity

| Module | Purpose |
|---|---|
| **YukawaOverlapExponent** | α = N_c−1 = 2; sech bracket CatAL-conditional on bridge axioms |
| **FKTTCoupling** | (re-exported from Physics) |
| **WaldEntropy** | Wald entropy scaffold; 3 sorry pending Mathlib manifold integrals |
| **WaldChainAndInitialState** | Wald chain and MDL initial state |
| **FermionicStatistics** | Fermionic statistics in GTE framework |
| **SpinorRep** | Spinor representation |
| **MinkowskiSpace** | Minkowski spacetime |
| **LorentzGroupSO13** | Lorentz group SO(1,3) |
| **MinimalCoupling** | Minimal coupling |
| **FLRWFieldEquation** | FLRW field equation |
| **PMDLGravityTheorems** | PMDL gravity theorems |
| **NRTVacuumEnergy** | NRT vacuum energy |
| **PlanckDensityBound** | Planck density bound |
| **CCImpossibilityBundle** | CC impossibility bundle |
| **CCResidual / CMBSpectralTilt** | Cosmological constant residual; CMB spectral tilt |
| **RelationalTime / PageWoottersZ7** | Page–Wooters relational time in Z₇ |
| **PSCEpochSelection** | PSC epoch selection |
| **Z7AnomalyFree** | Z₇ anomaly cancellation |
| **TemporalVoxelCC** | Carrier pricing chain; Ω = 3π/14 |
| *(+ others)* | See `UgpLean/Gravity/` for full list |

## Spacetime

| Module | Purpose |
|---|---|
| **GeodesicTheorem** | Preferred-direction geodesic via D-weighted centroid (CatAD) |
| **CentroidMeasure** | Point-localization centroid; spatial centroid invariant |
| **MassGap** | Δ > 0 for all non-vacuum beables; Δ ≥ 1.8 MeV |
| **OrbitMassHierarchy** | gen₃ mass > gen₂ mass > gen₁ mass > 0 for all SM sectors |
| **QuantumGravity** | Quantum gravity completion |
| **QECStabilizer** | Quantum error-correction stabilizer |
| **CausalGraph / CausalInvariance** | Causal structure and invariance |
| **HolographicScaling** | Holographic scaling |
| **LiftingTheorem / SpatiallyExtendedLifting** | Spatial lifting theorems |
| **ColorConfinement** | Color confinement |
| **StressEnergyTensor** | Stress-energy tensor |
| **GravitonFockSpace** | Graviton Fock space |
| **AnomalyRenormalizability** | Anomaly and renormalizability |
| **ThreeGenerationCapstone** | Three-generation capstone theorem |
| **UniversalSimulation** | Universal simulation |
| **ChiralGliderDynamics** | Chiral glider dynamics |
| **SpectralDimension** | Spectral dimension |
| *(+ others)* | See `UgpLean/Spacetime/` for full list |

## Algebra

| Module | Purpose |
|---|---|
| **CyclotomicZ7Galois** | Z₇ Galois structure ((ZMod 7)ˣ arithmetic certificates) |
| **CyclotomicZ7GaloisGroup** | Actual Galois group Gal(Q(ζ₇)/Q) ≅ Z₆ = Z₂ × Z₃ (CPT × generation) via Mathlib `autEquivPow` |
| **CyclotomicFieldDisjointness** | No ℚ-algebra embedding Q(ζ₇) ↪ Q(ζ₁₂₀) (degree obstruction 6 ∤ 32) |
| **F21SU3Embedding** | F₂₁ → SU(3) embedding |
| **SMGaugeGroup** | SM gauge group derivation |
| **GaugeMDL** | Gauge-MDL connection |
| **SRRGCABridge** | SRRG–CA bridge |
| **BaryonNumber** | Baryon number |
| **ChargeFromPolynomial** | Charge from polynomial |
| **ChiralDoublet** | Chiral doublet structure |
| **ColorConfinementMDL** | Color confinement from MDL |
| **PolynomialContinuumBridge** | Polynomial–continuum bridge |
| **RSCodeOrbit** | RS code orbit |
| **SU3GluonCount** | SU(3) gluon count |

## Framework

| Module | Purpose |
|---|---|
| **GTEFrameworkInstance** | GTE substrate as `NemS.Framework`; NEMS + determinacy PSC bundle |
| **GTEOptimalityInstance** | GTE optimality instance |
| **GTEFinalCoalgebra** | GTE final coalgebra |
| **GTECategoryStructure** | Category structure on GTE |
| **MDLTower** | MDL tower structure |
| **CMCAContinuumLimit** | CMCA continuum limit |
| **CMCAMDLMinimality** | CMCA MDL minimality |
| **PhiMDLBridge** | φ_MDL bridge |

## ContinuumLimit

| Module | Purpose |
|---|---|
| **WassersteinDistance** | W₁ distance; W₁_nonneg, W₁_triangle, W₁_eq_zero_iff — all zero sorry |
| **GF7VacuumFixedPoint** | GF(7) vacuum as continuum fixed point |
| **GorardRationalFormula** | Gorard rational formula |
| **GorardVacuumW1Bridge** | Gorard vacuum W₁ bridge |
| **DiscreteBianchi** | Discrete Bianchi identity |

## QFT

| Module | Purpose |
|---|---|
| **GaugedMassGap** | Gauged mass gap |
| **ChiralSymmetryBreaking** | Chiral symmetry breaking |

## VEVProof

| Module | Purpose |
|---|---|
| **EWGoldstoneManifold** | EW Goldstone manifold |
| **GoldstoneEntropyCorrection** | Goldstone entropy correction |
| **PSCEntropyDuality** | PSC entropy duality |

## VEVNoGo

| Module | Purpose |
|---|---|
| **SRRGNoGo** | SRRG VEV no-go theorem |

## GaloisStructure

| Module | Purpose |
|---|---|
| **CyclotomicLayers** | Cyclotomic layers |
| **MinimalCyclotomic** | Minimal cyclotomic field |

## CyclotomicCompleteness

| Module | Purpose |
|---|---|
| **CoxeterBiconditional** | h\|60 ↔ 2h\|120; per-algebra certs for G₂, F₄, E₆, E₈; E₇ falsifier |
| **CyclotomicContainment** | Q(ζ_{2h}) →ₐ[ℚ] Q(ζ₁₂₀) when h\|60; zero sorry |

## Phase4

| Module | Purpose |
|---|---|
| **DeltaUGP** | δ_UGP formula; leptonB_matches_deltaUGP |
| **GaugeCouplings** | g₁², g₂², g₃² bare values |
| **GaloisProtection** | One-loop QED correction vanishes |
| **TwoLoopCoefficient** | Two-loop colour coefficient = 8/9 |
| **AsymptoticSparsity** | Asymptotic sparsity |
| **PositiveRootTheorem** | Positive root theorem |
| **UCL, PR1** | Informational stubs (companion derivations in ugp-physics-lean) |

## PSC

| Module | Purpose |
|---|---|
| **RCCInfiniteFamilies** | RCC over B_n, C_n, D_n, A_n infinite classical Lie families |

## TE22

| Module | Purpose |
|---|---|
| **ScanCertificate** | SM gauge uniquely selected; UGP g₁²/g₂² within 2% of SM@Mz |

## SelfRef

| Module | Purpose |
|---|---|
| **LawvereKleene** | Lawvere fixed-point theorem; Kleene recursion |
| **RiceHalting** | Rice's theorem; halting undecidability |

## Papers / Instance

| Module | Purpose |
|---|---|
| **Papers/Paper25** | Citable stubs for Paper 25 (RSUC) |
| **Papers/UGPMain** | Citable stubs for UGP Main paper |
| **Instance/NemSBridge** | GTESpace instance; RSUC for nems-lean |

## Conjectures

Tracks resolved and open conjectures. 7 of 10 resolved; 3 open (MirrorDualConjecture, UGPPrimeInfinitude, MuFlipDistance).

---

## Non-Circularity

**Core/ may not import Compute/**. This is enforced structurally — if violated, `lake build` fails. See [DESIGN.md](DESIGN.md) for the rationale.
