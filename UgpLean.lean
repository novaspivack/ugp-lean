import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs
import UgpLean.Core.TripleDefs
import UgpLean.Core.SievePredicates
import UgpLean.Core.Disconfirmation
import UgpLean.Core.RidgeRigidity
import UgpLean.Core.MirrorAlgebra
import UgpLean.Compute.PrimeLock
import UgpLean.Compute.Sieve
import UgpLean.Compute.SieveExtended
import UgpLean.Compute.SieveBelow10
import UgpLean.Compute.ExclusionFilters
import UgpLean.Compute.DecidablePredicates
import UgpLean.Classification.Bounds
import UgpLean.Classification.TheoremA
import UgpLean.Classification.TheoremB
import UgpLean.Classification.RSUC
import UgpLean.Classification.FormalRSUC
import UgpLean.Classification.MonotonicStrengthening
import UgpLean.GTE.Evolution
import UgpLean.GTE.Orbit
import UgpLean.GTE.PrimeFactorAnalysis
import UgpLean.GTE.UpdateMap
import UgpLean.GTE.MersenneGcd
import UgpLean.GTE.MersenneLadder
import UgpLean.BraidAtlas.ChargeTheorem
import UgpLean.BraidAtlas.CompositeTriples
import UgpLean.BraidAtlas.ChiralitySquaring
import UgpLean.BraidAtlas.ChargeDerivation
import UgpLean.BraidAtlas.CoxeterConductor
import UgpLean.BraidAtlas.CoxeterConductorTowerLaw
import UgpLean.BraidAtlas.EWBosons
import UgpLean.BraidAtlas.MirrorWindingNumber
import UgpLean.BraidAtlas.EWBosonRHNConnection
import UgpLean.BraidAtlas.RHNGapTheorem
import UgpLean.BraidAtlas.DarkBraidAtlas
import UgpLean.BraidAtlas.DarkQuarkCharge
import UgpLean.BraidAtlas.DarkGaugeCoupling
import UgpLean.GTE.FiberBundle
import UgpLean.GTE.LinearResponse
import UgpLean.GTE.ScaleConnection
import UgpLean.MassRelations.ScaleTransport
import UgpLean.GTE.MirrorDualConjecture
import UgpLean.GTE.NuclearPairing
import UgpLean.GTE.MirrorShift
import UgpLean.GTE.GeneralTheorems
import UgpLean.GTE.GTESimulation
import UgpLean.GTE.EntropyNonMonotone
import UgpLean.GTE.UGPPrimes
import UgpLean.GTE.ResonantFactory
import UgpLean.GTE.InertPrimes
import UgpLean.GTE.AnalyticArchitecture
import UgpLean.GTE.StructuralTheorems
import UgpLean.GTE.UniquenessCertificates
import UgpLean.GTE.GTBGenerationPrimes
import UgpLean.GTE.DSIExport
import UgpLean.GTE.NcColorArithmetic
import UgpLean.GTE.SylowIndexCouplingHierarchy
import UgpLean.SelfRef.LawvereKleene
import UgpLean.SelfRef.RiceHalting
import UgpLean.Conjectures
import UgpLean.QuarterLock
import UgpLean.ElegantKernel
import UgpLean.ElegantKernel.ChiralityFeature
import UgpLean.ElegantKernel.KGen2
import UgpLean.ElegantKernel.D5StructuralAxiom
import UgpLean.ElegantKernel.FibonacciHessian
import UgpLean.ElegantKernel.PentagonalUniqueness
import UgpLean.ElegantKernel.KGen
import UgpLean.ElegantKernel.Unconditional.D5Renormalization
import UgpLean.ElegantKernel.Unconditional.FibonacciPentagonBridge
import UgpLean.ElegantKernel.Unconditional.RiccatiFixedPoint
import UgpLean.ElegantKernel.Unconditional.PentagonConstraint
import UgpLean.ElegantKernel.Unconditional.FullClosure
import UgpLean.ElegantKernel.Unconditional.CyclotomicChain
import UgpLean.ElegantKernel.Unconditional.KGenFullClosure
import UgpLean.ElegantKernel.Unconditional.KLFullClosure
import UgpLean.ElegantKernel.Unconditional.KConstFullClosure
import UgpLean.LModelDerivation
import UgpLean.Instance.NemSBridge
import UgpLean.Papers.Paper25
import UgpLean.Papers.UGPMain
import UgpLean.Phase4.DeltaUGP
import UgpLean.Phase4.GaugeCouplings
import UgpLean.ElegantKernel.MuTriple
import UgpLean.Phase4.UCL
import UgpLean.Phase4.PR1
import UgpLean.Phase4.AsymptoticSparsity
import UgpLean.Phase4.PositiveRootTheorem
import UgpLean.GaloisStructure.CyclotomicLayers
import UgpLean.GaloisStructure.MinimalCyclotomic
import UgpLean.CyclotomicCompleteness.CoxeterBiconditional
import UgpLean.CyclotomicCompleteness.CyclotomicContainment
import UgpLean.MassRelations.VVMechanism
import UgpLean.MassRelations.VVAllCoefficientsFromNc
import UgpLean.MassRelations.NeutrinoFroggattNielsen
import UgpLean.MassRelations.CKMTheta23
import UgpLean.MassRelations.CKMMixing
import UgpLean.MassRelations.NeutrinoMassRatio
import UgpLean.MassRelations
import UgpLean.Phase4.GaloisProtection
import UgpLean.Phase4.TwoLoopCoefficient
import UgpLean.Universality.Rule110
import UgpLean.Universality.UWCA
import UgpLean.Universality.UWCASimulation
import UgpLean.Universality.UWCAHistoryReversible
import UgpLean.Universality.UWCAembedsRule110
import UgpLean.Universality.TuringUniversal
import UgpLean.Universality.ArchitectureBridge
import UgpLean.Universality.CUP4TotalParity
import UgpLean.Universality.CUP11ModSeven
import UgpLean.Universality.TwoLayerConfluence
import UgpLean.Universality.GTECompilation
import UgpLean.Universality.GTEInfTapeEncoding
import UgpLean.Universality.GTEComputability
import UgpLean.Universality.GTEUniqueness
import UgpLean.Universality.HypothesisB
import UgpLean.Universality.HypothesisBCChain
import UgpLean.Universality.GoEHierarchy
import UgpLean.Universality.GoEStabilityHierarchy
import UgpLean.Universality.ZGMMesInvariant
import UgpLean.Universality.LawvereZone
import UgpLean.Universality.PSCUniversality
import UgpLean.Universality.CUP3DUniqueness
import UgpLean.Universality.CUP3DPSCUnification
import UgpLean.Universality.CUP3DPhysicalIncompleteness
import UgpLean.Universality.CookRule110Ref
import UgpLean.Universality.OrbitPerturbationCatalog
import UgpLean.Universality.Z7ChargeConjugation
import UgpLean.Universality.FMDLClassification
import UgpLean.Universality.DimensionalSliceUniqueness
import UgpLean.Universality.Z5TransitivityUniqueness
import UgpLean.Universality.GTPNeutralDiscrimination
import UgpLean.Universality.Z7ZeroSectorDiscriminant
import UgpLean.Universality.SMOrbitCausalIsolation
import UgpLean.Universality.EWBosonStructure
import UgpLean.Universality.EWChiralBridge
import UgpLean.Universality.GUTStructure
import UgpLean.Universality.TwoRoleTheorem
import UgpLean.Universality.EWScalePrediction
import UgpLean.Framework.GTEFrameworkInstance
import UgpLean.Framework.GTEOptimalityInstance
import UgpLean.Framework.GTEFinalCoalgebra
import UgpLean.Framework.PhiMDLBridge
import UgpLean.Framework.GTECategoryStructure
import UgpLean.Framework.CMCAContinuumLimit
import UgpLean.Framework.CMCAMDLMinimality
import UgpLean.Universality.ChiralPairVA
import UgpLean.Universality.CouplingNoGo
import UgpLean.Universality.DynamicalCouplingBridge
import UgpLean.Universality.ExcitationCoupling
import UgpLean.Universality.LorentzInvariance
import UgpLean.Universality.ChiralityEigenstates
import UgpLean.Universality.WeakIsospin
import UgpLean.TE22.ScanCertificate
import UgpLean.PSC.RCCInfiniteFamilies
import UgpLean.PSC.RCCComplete
import UgpLean.VEVNoGo.SRRGNoGo
import UgpLean.VEVProof.GoldstoneEntropyCorrection
import UgpLean.VEVProof.PSCEntropyDuality
import UgpLean.VEVProof.EWGoldstoneManifold
import UgpLean.Universality.MDLDerivabilityCriterion
import UgpLean.Universality.BornRuleMDL
import UgpLean.Universality.ThooftEffectMeasureBridge
import UgpLean.Universality.PSCEffectMeasureGeneric
import UgpLean.Universality.PSCEffectMeasure
import UgpLean.Universality.FockSpaceKink
import UgpLean.Universality.BeableWindingPartitionInstance
import UgpLean.Universality.DualFrameBornRule
import UgpLean.Universality.PhiMDLThermalState
import UgpLean.Universality.SylowIndexCouplingHierarchy
import UgpLean.Universality.GaugeInvariance
import UgpLean.Universality.BetaCoefficientIdentity
import UgpLean.Universality.FrobeniusPrimeIdentity
import UgpLean.Universality.Z3SubOrbitDisjointness
import UgpLean.Universality.Z3InvariantEntropy
import UgpLean.Universality.PSCOrbitWindows
import UgpLean.Substrate.LExtended
import UgpLean.Substrate.Substrate
import UgpLean.Substrate.PSCPreservingTransformation
import UgpLean.Substrate.CoherenceMeasure
import UgpLean.Substrate.CoherenceMeasureUniqueness
import UgpLean.Substrate.QECStabilizer
import UgpLean.Substrate.GEQECCode
import UgpLean.Substrate.TransputationStateSelector
import UgpLean.Substrate.DConstraints
import UgpLean.Substrate.LagrangianLorentzScalar
import UgpLean.Substrate.PSCStructureLorentzPreserved
import UgpLean.Substrate.PSCPILorentzMain
import UgpLean.Substrate.NoetherAngularMomentum
import UgpLean.Substrate.WindingCoinDecoupling
import UgpLean.Universality.CasimirMasslessEther
import UgpLean.Spacetime.CausalGraph
import UgpLean.Spacetime.SpectralDimension
import UgpLean.Spacetime.SpectralDimensionDegree
import UgpLean.Spacetime.Spectral.DegreeNormalized
import UgpLean.Spacetime.Spectral.SpectralDimensionFromAsymptotic
import UgpLean.Spacetime.Spectral.HeatKernelFourier
import UgpLean.Spacetime.Spectral.HeatKernelLaplace
import UgpLean.Spacetime.Spectral.ThermodynamicLimit
import UgpLean.Universality.NoClass4OuterTotalisticZ7
import UgpLean.Spacetime.PhiMDLZ7PotentialMDL
import UgpLean.Spacetime.ChiralPairDecoupling
import UgpLean.Spacetime.ColorConfinement
import UgpLean.Spacetime.AnomalyRenormalizability
import UgpLean.Spacetime.LiftingTheorem
import UgpLean.Universality.AlgebraicDescentTheorem
import UgpLean.Universality.AlgebraicNecessityTheorem
import UgpLean.Spacetime.GeodesicTheorem
import UgpLean.Spacetime.CentroidMeasure
import UgpLean.Spacetime.SpatiallyExtendedLifting
import UgpLean.Spacetime.MassGap
import UgpLean.Spacetime.OrbitMassHierarchy
import UgpLean.Spacetime.QECStabilizer
import UgpLean.Spacetime.DWeightSRFormula
import UgpLean.Spacetime.MultiParticleHilbert
import UgpLean.Spacetime.QuantumGravity
import UgpLean.Spacetime.GravitonFockSpace
import UgpLean.Spacetime.StressEnergyTensor
import UgpLean.Gravity.MinimalCoupling
import UgpLean.Gravity.FLRWFieldEquation
import UgpLean.Gravity.PlanckDensityBound
import UgpLean.Gravity.CurvedBackgroundPreconditions
import UgpLean.Gravity.BounceAndArithmetic
import UgpLean.Gravity.PSCQECWaldConnections
import UgpLean.Gravity.WaldChainAndInitialState
import UgpLean.Gravity.DimensionalDecomposition
import UgpLean.Gravity.RelationalTime
import UgpLean.Gravity.PMDLGravityTheorems
import UgpLean.Gravity.GorardRicciFlatVacuum
import UgpLean.OQ26Arithmetic
import UgpLean.GTEDerivationChain
import UgpLean.Algebra.CyclotomicZ7Galois
import UgpLean.Algebra.RSCodeOrbit
import UgpLean.Spacetime.PhysicalExclusion
import UgpLean.Spacetime.ThreeGenerationCapstone
import UgpLean.Spacetime.CausalInvariance
import UgpLean.Spacetime.ChiralGliderDynamics
import UgpLean.Spacetime.ChiralMirrorSpeedSymmetry
import UgpLean.Spacetime.OrbitDepthEtherPeriod
import UgpLean.Spacetime.PhiMDLKinkQuantumNumbers
import UgpLean.Spacetime.AsyncLiftingTheorem
import UgpLean.QFT.GaugedMassGap
import UgpLean.QFT.ChiralSymmetryBreaking
import UgpLean.Universality.PhiMDLUniversality

/-!
# UgpLean — Universal Generative Principle: Lean 4 Formalization

Formalization of UGP (Universal Generative Principle) and GTE (Generative Triple Evolution).

## Module structure

- `UgpLean.Core.*`               — RidgeDefs, MirrorDefs, TripleDefs, SievePredicates, Disconfirmation
- `UgpLean.Compute.*`            — PrimeLock, Sieve, SieveExtended, DecidablePredicates
- `UgpLean.Classification.*`     — Bounds, Theorem A/B, RSUC
- `UgpLean.GTE.*`                — Evolution, Orbit, UpdateMap, GTESimulation, EntropyNonMonotone, MersenneGcd, MirrorDualConjecture, MirrorShift, InertPrimes
- `UgpLean.SelfRef.*`            — Lawvere/Kleene fixed-point, Rice's theorem, halting undecidability
- `UgpLean.QuarterLock`          — k_M = k_gen2 + ¼k_L²
- `UgpLean.ElegantKernel`        — k_L² = 7/512, L_model
- `UgpLean.LModelDerivation`     — L_model derived from D₁, 5³, orbit length 3
- `UgpLean.Phase4.*`             — DeltaUGP, GaugeCouplings, UCL, PR1, AsymptoticSparsity (all n), PositiveRootTheorem
- `UgpLean.GaloisStructure.*`    — CyclotomicLayers (Galois stability of UGP layers in Q(ζ₁₂₀))
- `UgpLean.CyclotomicCompleteness.*` — CoxeterBiconditional: h|60 ↔ 2h|120 arithmetic biconditional; per-algebra h|60 certs (G₂,F₄,E₆,E₈); B₄ conductor analysis; e7_double_failure; coxeter_biconditional_summary. CyclotomicContainment: full field-theoretic embedding CyclotomicField(2h)ℚ →ₐ[ℚ] CyclotomicField(120)ℚ when h|60; per-algebra certificates for G₂,F₄/E₆,E₈ (all zero sorry). [H9SelfConsistency and GoldenRatioFixedPoint migrated to ugp-physics-lean]
- `UgpLean.Universality.*`       — Rule110, UWCA, UWCASimulation, UWCAHistoryReversible, UWCAembedsRule110, Turing universality, Architecture bridge
- `UgpLean.Universality.FMDLClassification` — Cat IV structural prerequisites: 14/343 sparsity cert, binary sublayer = Rule 110 (zero sorry), SM encoding, Law=Description=Execution (2026-05-21)
- `UgpLean.Universality.AlgebraicDescentTheorem` — Rank 135-ALDESC: Algebraic Descent Theorem; M-independence of F_21 orbit structure, PSC admissibility, three generations, color confinement, b₀=7, θ=0, Casimir invariants C_F=4/3 C_A=3; all CatAL zero sorry (2026-05-23)
- `UgpLean.Universality.AlgebraicNecessityTheorem` — Rank 075-ALGEC-NECESSITY: Algebraic Necessity Theorem; F₂₁ = Z₇ ⋊ Z₃ is the unique non-abelian group of order 21 (Burnside pq certificates, zero sorry); N_gen=3 uniquely forced; no-CA-replica as corollary; all CatAL zero sorry (2026-05-26)
- `UgpLean.Universality.BetaCoefficientIdentity` — b₀ = |Z₇| = 7 from F₂₁ = Z₇ ⋊ Z₃: (11N_c − 2N_f)/3 = |F₂₁|/|Z₃|; Planck cascade group identity; zero sorry (2026-05-26)
- `UgpLean.Universality.FrobeniusPrimeIdentity` — |Z₇| = |Z₃|² − |Z₃| + 1 unifies F₂₁ and PSC n=10 derivations; frobenius_prime_bundle; zero sorry (2026-05-26)
- `UgpLean.Papers.*`             — Paper25, UGPMain (citable stubs)

- `UgpLean.TE22.*`               — ScanCertificate (TE2.2 PSC scan framework, UGP coupling predictions)
- `UgpLean.PSC.*`                — RCCInfiniteFamilies (RCC closed over all infinite classical families; B_n/C_n w0=-id, D_n/A_n dimension bounds). [ThreeRouteForcing migrated to ugp-physics-lean]
- `UgpLean.MassRelations.NeutrinoFroggattNielsen` — MDL-unique FN texture (q1, q2) = (N_c, strand) for b^(29/9)
- `UgpLean.Phase4.GaloisProtection` — Galois-protection non-renormalization theorem; one-loop cancellation from T/T† pairing
- `UgpLean.Phase4.TwoLoopCoefficient` — two-loop color coefficient (Nc²-1)/Nc² = 8/9; O3 structural identification
- `UgpLean.MassRelations.CKMMixing` — CDM mechanism (2026-05-11): effective Cabibbo FN charge Δa_eff = α_d = 13/9 from GUT group theory; |V_us|_CDM = ε₁^(α_d) = exp(−13π/27) ≈ 0.2203 (zero sorry)
- `UgpLean.MassRelations.NeutrinoMassRatio` — Seesaw mass-squared ratio R ≈ 0.02936 from FN texture (q₁,q₂)=(3,2) and b-values {5,11,19}; coarse bound 0.029 < R < 0.030 certified zero sorry (2026-05-16)
- `UgpLean.Spacetime.CausalGraph` — Rank 12-LCG: causal graph of 3D f_MDL spacetime; `CausalNode`, `CausalAdj`, `CausalGraph`; rule-independence theorem zero sorry (2026-05-21)
- `UgpLean.Spacetime.SpectralDimension` — heat-kernel defs + `spectralDimension` limit (CatAL); 1 documented honest sorry on `spectral_dim_cayley_Z4_eq_4` retained as historical statement mathematically false at fixed `(L, T)`; the active "spectral dimension = 4" claim is the thermodynamic-limit theorem `Spectral.causal_graph_spectral_dim_thermodynamic_limit`
- `UgpLean.Spacetime.SpectralDimensionDegree` — `periodic_causal_node_degree` CatAL (0 sorry)
- `UgpLean.Spacetime.Spectral.DegreeNormalized` — physical (degree-normalized) random-walk heat kernel definitions (0 sorry)
- `UgpLean.Spacetime.Spectral.SpectralDimensionFromAsymptotic` — bridge from a diffusive heat-kernel asymptotic to the scaling-law log-ratio limit (pure real analysis, 0 sorry)
- `UgpLean.Spacetime.Spectral.HeatKernelFourier` — Rank 13-LSD Fourier-on-`ZMod` reduction: `cayley_eigenvalue_at_zero_eq_degree` (zero sorry); 3 documented analytical sorrys in `physical_heat_kernel_eq_character_sum`, `cayley_eigenvalue_quadratic_expansion`, `discrete_torus_gaussian_limit`; assembled in `causal_graph_heat_kernel_diffusive_asymptotic_fourier`
- `UgpLean.Spacetime.Spectral.HeatKernelLaplace` — Laplace-method asymptotic delegates to `HeatKernelFourier` (zero sorry in body; 3 analytical sorrys in dependency chain)
- `UgpLean.Spacetime.Spectral.ThermodynamicLimit` — `causal_graph_spectral_dim_thermodynamic_limit`: the thermodynamic-limit "spectral dimension = 4" theorem for the 3D f_MDL causal graph (zero sorry in the body; reduces via the bridge to the Fourier/Laplace chain in `HeatKernelFourier`)
- `UgpLean.Universality.NoClass4OuterTotalisticZ7` — OQ-3DALG-6: `no_class4_outer_totalistic_z7_3d` zero sorry (1 axiom `chirality_necessary_for_class4`); reflection-invariance lemmas zero sorry; `outer_totalistic_z7_vn6_rule_space_card` zero sorry
- `UgpLean.Spacetime.PhiMDLZ7PotentialMDL` — Rank 69d: `phimdl_z7_potential_mdl_minimal` CatAL (0 sorry)
- `UgpLean.Spacetime.ChiralPairDecoupling` — Rank 14-LCD: chiral pair causal decoupling; `ChiralLayer`, `ChiralNode`, `ChiralPairAdj`; `chiral_pair_no_cross_layer_edges` zero sorry, `chiral_pair_walk_layer_invariant` zero sorry (2026-05-21)
- `UgpLean.Spacetime.ColorConfinement` — Rank 25-CCF: color confinement from PSC RC + Absence Theorem; `color_confinement` and `physical_particles_are_color_neutral` zero sorry, one named bridge axiom `psc_rc_requires_color_neutrality` (CatAD, 2026-05-21)
- `UgpLean.Spacetime.AnomalyRenormalizability` — Ranks 26-ANO + 27-RNM: anomaly cancellation and renormalizability PSC-forced; `anomaly_cancellation_psc_forced`, `physical_anomaly_cancellation`, `renormalizability_psc_forced`, `physical_renormalizability`, `anomaly_and_renorm_psc_forced`; all zero sorry, zero axioms (CatAL, 2026-05-21)
- `UgpLean.Spacetime.GeodesicTheorem` — Rank 17-GEO: geodesic theorem; D2 orbit closure; `causal_sequence_exists`; `geodesic_preferred_direction` (CatAL); structural D2 argument for full geodesic (CatAD)
- `UgpLean.Spacetime.CentroidMeasure` — P34 `[D]` centroid: `beableCentroid`, `centroid_well_defined`, point-localization model (CatAL, zero sorry)
- `UgpLean.Spacetime.SpatiallyExtendedLifting` — Rank 55-3DLT: `causal_path_exists` theorem (CatAL); meson/baryon bound states
- `UgpLean.Spacetime.MassGap` — Rank 42-MGP: `gte_mass_gap`, `gte_mass_formula_physical`, `smGenMass` (CatAL, zero sorry)
- `UgpLean.Spacetime.QuantumGravity` — Rank 28-QGR: beable-level quantum gravity evidence structure (CatAD-strong)
- `UgpLean.Spacetime.StressEnergyTensor` — Rank 075-TMUNU: Φ_MDL T_μν symmetry, vacuum-zero, BPS pressure-free axiom, gravity prerequisites bundle (CatAL/CatAD, 2026-05-26)
- `UgpLean.Gravity.MinimalCoupling` — EPIC_078: `minimal_coupling_is_mdl_minimal`, `z7_superselection_preserved_by_flat_metric` (CatAL, zero sorry)
- `UgpLean.Gravity.PlanckDensityBound` — EPIC_078 Rank 078-LC4: `planck_density_bound_via_lifting`, `planck_density_state_count` (CatAL, zero sorry)
- `UgpLean.Gravity.CurvedBackgroundPreconditions` — EPIC_078 Rank 078-LC6: `phimdl_no_curvature_coupling`, `mdl_selects_flat_cosmology`, `gte_rs_code_achieves_singleton_bound`, `epic_078_functional_completeness_lean_support` (CatAL, zero sorry)
- `UgpLean.Gravity.WaldChainAndInitialState` — EPIC_078 Rank 078-LC9: `rt_formula_key_precondition`, `z7_potential_zero_at_vacuum`, `mdl_initial_state_flat_spatial_sections`, `phimdl_xi_zero_implies_key_preconditions`, `epic_078_wald_chain_and_initial_state` (CatAL, zero sorry)
- `UgpLean.Gravity.PSCQECWaldConnections` — EPIC_078 Rank 078-LC8: `psc_admissible_eq_rs_eval_points`, `gte_rs_code_params_from_psc`, `gte_ghet_t2_t5_certified`, `phimdl_rt_formula_wald_precondition_chain`, `epic_078_psc_qec_wald_master` (CatAL, zero sorry)
- `UgpLean.Gravity.DimensionalDecomposition` — EPIC_078 Rank 078-LC11: `cmca_three_axes_give_31d`, `spacetime_dim_from_ngen`, `galois_symmetry_3d`, `so13_generator_count`, `cmca_tensor_product_gives_31d_minkowski` (CatAL, zero sorry)
- `UgpLean.Gravity.RelationalTime` — EPIC_079 Rank 079-LC1: `without_shared_clock_uncoupled`, `shared_clock_gives_31d`, `tau_c_adds_temporal_dimension`, `dimensional_protocol_principle_master` (CatAL, zero sorry)
- `UgpLean.Gravity.PMDLGravityTheorems` — EPIC_079 Ranks 079-MDL-UNIQUE, 079-FIXED-POINT, 079-UNIFIED-POLY: `vacuum_unique_fixed_point_z7`, `unique_cubic_gravity_coupling`, `gte_gravity_mass_hierarchy`, `gte_polynomial_three_roles_k_zero` (CatAL, zero sorry)
- `UgpLean.Spacetime.MultiParticleHilbert` — Rank 244-MPH: multi-particle Hilbert space algebraic layer; `code_word_cardinality` (4 code words, Equiv with Fin 4), `n_particle_state_count` (4^N states), `multiDWeight_eq_one`, `multiMass_append`, `multiMass_le`, `mass_hierarchy_three_states`, `smGenMass_multi_anchor`, `multiparticle_orbit_closure`, `inner_product_positive_definite`, `multiparticle_space_well_defined`; all CatAL, zero sorry (2026-05-24)
- `UgpLean.Spacetime.CausalInvariance` — Rank 37-LCI: f_MDL causal invariance + Lamport consistency + SR connection; `ForwardCausalAdj`, `forward_causal_time_step`, `forward_causal_acyclic`, `transgen_time_strictly_increases`, `lamport_irrefl`, `lamport_strict_partial_order`, `lamport_order_update_independent`, `afca_sr_causal_structure`; all zero sorry, zero axioms (CatAL/CatAD — Lamport properties CatAL, Minkowski isomorphism CatAD, 2026-05-21)
- `UgpLean.Spacetime.DWeightSRFormula` — Rank 63-DMDL: [D]-weighted SR formula; `dmdl_dweight_positive`, `dmdl_proper_time_ratio`, `dmdl_dweight_sr_formula`, `dmdl_lorentz_factor_algebraic`, `dmdl_tau_c_ratio_structure`, `dmdl_qec_sr_bundle`; all zero sorry, zero custom axioms (CatAL, 2026-05-24)
- `UgpLean.Spacetime.AsyncLiftingTheorem` — Rank 32-ALT2: Asynchronous Lifting Theorem; `async_algebraic_lifting_theorem`, `async_color_confinement`, `async_dweight_is_local`, `async_psc_admissible_is_local`; all CatAL, zero sorry — async ALT is definitionally the sync ALT because DWeight and PSCAdmissible are local state predicates (2026-05-26)

**Non-circularity:** Core/ does not import Compute/. See README.md.
-/
