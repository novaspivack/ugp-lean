# ugp-lean Theorem Manifest

**Companion:** The UGP Formalization paper (`NEMS_PAPERS/UGP_GTE_Formalization/`) provides a complete theorem-indexed table mapping every definition and theorem to ugp-lean modules. Use it as the definitive paper-level reference for the artifact.

| Paper / Source | Lean Module | Lean Theorem | Status |
|----------------|-------------|--------------|--------|
| UGP Main, ridge Rₙ = 2ⁿ − 16 | Core.RidgeDefs | ridge_def, ridge_10 | ✓ |
| UGP Main, mirror (b₂,q₂) ↦ (b₁,q₁,c₁) | Core.MirrorDefs | b1FromPair, q1FromQ2, c1FromPair | ✓ |
| UGP Main, prime-lock c₁ prime | Compute.PrimeLock | prime_823, prime_2137 | ✓ |
| UGP Main, n=10 survivors | Compute.Sieve | ridgeSurvivors_10 | ✓ |
| gte_triples_explainer, Lepton Seed | Core.TripleDefs | LeptonSeed, LeptonMirror | ✓ |
| Paper 25, RSUC | Classification.RSUC | rsuc_theorem | ✓ |
| Paper 25, Theorem A (general) | Classification.TheoremA | theoremA_general | ✓ |
| Paper 25, Theorem A (n=10) | Classification.TheoremA | theoremA | ✓ |
| Paper 25, Theorem B, ResidualAt | Classification.TheoremB | ResidualAt, Residual, ResidualAt_10_eq_Residual, theoremB, mdl_selects_LeptonSeed | ✓ |
| Paper 25, Formal RSUC | Classification.FormalRSUC | rsuc_formal, rsuc_canon | ✓ |
| Paper 25, Monotonic strengthening | Classification.MonotonicStrengthening | strengthening_cannot_add_survivors | ✓ |
| Paper 25, n-parameterized candidates | Classification.Bounds | CandidatesAt, CandidatesAt_10_eq | ✓ |
| Quarter-Lock Law | QuarterLock | quarterLockLaw | ✓ |
| Elegant Kernel k_L² | ElegantKernel | k_L2, k_L2_pos | ✓ |
| GTE canonical orbit | GTE.Evolution, GTE.Orbit | canonical_orbit_triples, canonical_orbit_three_steps | ✓ |
| Sieve Extended n∈[5,30] | Compute.SieveExtended | mirrorDualCount_10 | ✓ |
| MirrorEquivClass equiv | Core.Disconfirmation | MirrorEquivClass.isEquiv | ✓ |
| Papers citable stubs | Papers.Paper25, Papers.UGPMain | rsuc, n10_survivors | ✓ |
| **Phase 4** | | | |
| DeltaUGP | Phase4.DeltaUGP | deltaUGPFormula, leptonB_matches_deltaUGP | ✓ |
| Gauge couplings | Phase4.GaugeCouplings | D1, g1Sq_bare, g1Sq_bare_eq_D1_over_125 | ✓ |
| UCL, PR-1 | Phase4.UCL, Phase4.PR1 | Structural stubs | ✓ |
| **Phase 5** | | | |
| Rule 110 | Universality.Rule110 | rule110Output, rule110Minterms | ✓ |
| UWCA | Universality.UWCA | rule110Tiles | ✓ |
| Turing universality | Universality.TuringUniversal | ugp_is_turing_universal | ✓ |
| Architecture bridge | Universality.ArchitectureBridge | uniqueness_of_physical_program | ✓ |
| **Monograph additions** | | | |
| Ridge remainder lock | Core.RidgeRigidity | ridge_remainder_lock, m2_canonical | ✓ |
| Quotient-gap 13 | Core.RidgeRigidity | quotient_gap_13, survivor_gap_* | ✓ |
| Even-step rigidity | GTE.Evolution | even_step_rigidity, worked_orbit_enforced | ✓ |
| Mirror prime-lock | Compute.PrimeLock | mirror_prime_lock, c1_from_divisor | ✓ |
| Exclusion filters | Compute.ExclusionFilters | exclude_16..exclude_63 | ✓ |
| Trace identifiability | GTE.Evolution | trace_identifiability | ✓ |
| L_model exact | ElegantKernel | L_model, L_model_pos | ✓ |
| L_model derived | LModelDerivation | L_model_eq_log_residual, L_model_from_gauge_structure | ✓ |
| Stability of Quarter-Lock | QuarterLock | quarterLockStability_holds | ✓ |
| Symmetric mirror algebra | Core.MirrorAlgebra | mirrorS, discSq, ugp1_mirror_params | ✓ |
