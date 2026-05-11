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
import UgpLean.GTE.FiberBundle
import UgpLean.GTE.LinearResponse
import UgpLean.GTE.ScaleConnection
import UgpLean.MassRelations.ScaleTransport
import UgpLean.GTE.MirrorDualConjecture
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
import UgpLean.GTE.DSIExport
import UgpLean.SelfRef.LawvereKleene
import UgpLean.SelfRef.RiceHalting
import UgpLean.Conjectures
import UgpLean.QuarterLock
import UgpLean.ElegantKernel
import UgpLean.LModelDerivation
import UgpLean.Instance.NemSBridge
import UgpLean.Papers.Paper25
import UgpLean.Papers.UGPMain
import UgpLean.Phase4.DeltaUGP
import UgpLean.Phase4.GaugeCouplings
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
import UgpLean.Phase4.GaloisProtection
import UgpLean.Phase4.TwoLoopCoefficient
import UgpLean.Universality.Rule110
import UgpLean.Universality.UWCA
import UgpLean.Universality.UWCASimulation
import UgpLean.Universality.UWCAHistoryReversible
import UgpLean.Universality.UWCAembedsRule110
import UgpLean.Universality.TuringUniversal
import UgpLean.Universality.ArchitectureBridge
import UgpLean.TE22.ScanCertificate
import UgpLean.PSC.RCCInfiniteFamilies

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
- `UgpLean.Universality.*`       — Rule110, UWCA, UWCAHistoryReversible, Turing universality, Architecture bridge
- `UgpLean.Papers.*`             — Paper25, UGPMain (citable stubs)

- `UgpLean.TE22.*`               — ScanCertificate (TE2.2 PSC scan framework, UGP coupling predictions)
- `UgpLean.PSC.*`                — RCCInfiniteFamilies (RCC closed over all infinite classical families; B_n/C_n w0=-id, D_n/A_n dimension bounds). [ThreeRouteForcing migrated to ugp-physics-lean]
- `UgpLean.MassRelations.NeutrinoFroggattNielsen` — MDL-unique FN texture (q1, q2) = (N_c, strand) for b^(29/9)
- `UgpLean.Phase4.GaloisProtection` — Galois-protection non-renormalization theorem; one-loop cancellation from T/T† pairing
- `UgpLean.Phase4.TwoLoopCoefficient` — two-loop color coefficient (Nc²-1)/Nc² = 8/9; O3 structural identification

**Non-circularity:** Core/ does not import Compute/. See README.md.
-/
