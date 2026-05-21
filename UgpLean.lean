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
import UgpLean.Universality.LawvereZone
import UgpLean.Universality.PSCUniversality
import UgpLean.Universality.CUP3DUniqueness
import UgpLean.Universality.CUP3DPSCUnification
import UgpLean.Universality.CUP3DPhysicalIncompleteness
import UgpLean.Universality.CookRule110Ref
import UgpLean.Universality.OrbitPerturbationCatalog
import UgpLean.Universality.Z7ChargeConjugation
import UgpLean.Universality.DimensionalSliceUniqueness
import UgpLean.Universality.Z5TransitivityUniqueness
import UgpLean.Universality.GTPNeutralDiscrimination
import UgpLean.Universality.SMOrbitCausalIsolation
import UgpLean.Universality.EWBosonStructure
import UgpLean.Universality.EWChiralBridge
import UgpLean.Universality.GUTStructure
import UgpLean.Framework.GTEFrameworkInstance
import UgpLean.Framework.GTEOptimalityInstance
import UgpLean.Framework.GTEFinalCoalgebra
import UgpLean.Universality.CasimirMasslessEther
import UgpLean.Universality.ChiralPairVA
import UgpLean.Universality.CouplingNoGo
import UgpLean.TE22.ScanCertificate
import UgpLean.PSC.RCCInfiniteFamilies
import UgpLean.PSC.RCCComplete
import UgpLean.VEVNoGo.SRRGNoGo
import UgpLean.VEVProof.GoldstoneEntropyCorrection
import UgpLean.VEVProof.PSCEntropyDuality
import UgpLean.VEVProof.EWGoldstoneManifold
import UgpLean.Universality.GoEStabilityHierarchy
import UgpLean.Universality.OrbitPerturbationCatalog
import UgpLean.Universality.Z7ChargeConjugation
import UgpLean.Universality.Z5TransitivityUniqueness
import UgpLean.Universality.DimensionalSliceUniqueness
import UgpLean.Universality.GTPNeutralDiscrimination
import UgpLean.Universality.SMOrbitCausalIsolation
import UgpLean.Universality.EWBosonStructure
import UgpLean.Universality.EWChiralBridge
import UgpLean.Universality.GUTStructure
import UgpLean.Universality.CasimirMasslessEther
import UgpLean.Universality.LawvereZone
import UgpLean.Universality.ChiralPairVA
import UgpLean.Universality.CouplingNoGo
import UgpLean.Framework.GTEFrameworkInstance
import UgpLean.Framework.GTEOptimalityInstance
import UgpLean.Framework.GTEFinalCoalgebra
import UgpLean.Spacetime.CausalGraph
import UgpLean.Spacetime.SpectralDimension
import UgpLean.Spacetime.ChiralPairDecoupling

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
- `UgpLean.Papers.*`             — Paper25, UGPMain (citable stubs)

- `UgpLean.TE22.*`               — ScanCertificate (TE2.2 PSC scan framework, UGP coupling predictions)
- `UgpLean.PSC.*`                — RCCInfiniteFamilies (RCC closed over all infinite classical families; B_n/C_n w0=-id, D_n/A_n dimension bounds). [ThreeRouteForcing migrated to ugp-physics-lean]
- `UgpLean.MassRelations.NeutrinoFroggattNielsen` — MDL-unique FN texture (q1, q2) = (N_c, strand) for b^(29/9)
- `UgpLean.Phase4.GaloisProtection` — Galois-protection non-renormalization theorem; one-loop cancellation from T/T† pairing
- `UgpLean.Phase4.TwoLoopCoefficient` — two-loop color coefficient (Nc²-1)/Nc² = 8/9; O3 structural identification
- `UgpLean.MassRelations.CKMMixing` — CDM mechanism (2026-05-11): effective Cabibbo FN charge Δa_eff = α_d = 13/9 from GUT group theory; |V_us|_CDM = ε₁^(α_d) = exp(−13π/27) ≈ 0.2203 (zero sorry)
- `UgpLean.MassRelations.NeutrinoMassRatio` — Seesaw mass-squared ratio R ≈ 0.02936 from FN texture (q₁,q₂)=(3,2) and b-values {5,11,19}; coarse bound 0.029 < R < 0.030 certified zero sorry (2026-05-16)
- `UgpLean.Spacetime.CausalGraph` — Rank 12-LCG: causal graph of 3D f_MDL spacetime; `CausalNode`, `CausalAdj`, `CausalGraph`; rule-independence theorem zero sorry (2026-05-21)
- `UgpLean.Spacetime.SpectralDimension` — Rank 13-LSD: spectral dimension dₛ = 4; `FinAdjPeriodic`, `CausalGraphPeriodic`, `causal_graph_periodic_rule_independent` zero sorry; degree=20, torus isomorphism, dₛ=4 stated with sorry (2026-05-21)
- `UgpLean.Spacetime.ChiralPairDecoupling` — Rank 14-LCD: chiral pair causal decoupling; `ChiralLayer`, `ChiralNode`, `ChiralPairAdj`; `chiral_pair_no_cross_layer_edges` zero sorry, `chiral_pair_walk_layer_invariant` zero sorry (2026-05-21)

**Non-circularity:** Core/ does not import Compute/. See README.md.
-/
import UgpLean.Spacetime.LiftingTheorem
import UgpLean.Spacetime.UniversalSimulation
