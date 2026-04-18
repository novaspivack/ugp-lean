# ugp-lean Theorem Manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** v4.29.0-rc6 (via `lakefile.lean`)  
**Build:** `lake build` from this directory  
**Root import:** `UgpLean.lean`  
**Last verified:** 2026-04-18 — matches `lean-toolchain` and Mathlib pin; theorem table below.

**2026-04-18 integrity fix:** `fingerprint_fixed_point_exists` (Tarski) restated
on `Set ℕ` (the natural complete lattice for unbounded prime patterns) and proven
via Mathlib's `OrderHom.lfp`.  The previous `Finset ℕ`-with-only-monotonicity
statement was **false** (counter-example: `F(P) = P ∪ {max(P)+1}` monotone, no
fixed point).  A bounded `Finset ℕ` variant `fingerprint_fixed_point_bounded` is
also provided for the restricted-range case.  Both are zero-sorry and depend
only on Mathlib standard axioms.  Paper `ugp_lean_formalization.tex` updated to
match.  See registry at `ugp-physics:specs/WORKING_NOTES/TECH_DEBT_LEAN_SORRY_REGISTRY.md`.

**Companion:** The UGP Formalization paper (`NEMS_PAPERS/UGP_GTE_Formalization/`) provides a complete theorem-indexed table mapping every definition and theorem to ugp-lean modules. Use it as the definitive paper-level reference for the artifact.

| Paper / Source | Lean Module | Lean Theorem | Status |
|----------------|-------------|--------------|--------|
| ML-9 / SPEC_04_06: coarse entropy non-monotone on 8→9 step prefix (Lepton GTE sim, n=10) | GTE.GTESimulation; GTE.EntropyNonMonotone | gte_entropy_prefix8_gt_prefix9; Hpred8_gt_Hpred9 | ✓ |
| SPEC_04_06 T2: UWCA + history stack, backward ∘ forward = id | Universality.UWCAHistoryReversible | uwca_augmented_left_inverse; uwca_history_lane_step_reversible | ✓ |
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
| k_L² = 7/512 from UGP structure | ElegantKernel | k_L2_eq, k_L2_from_ugp1_s, block_denom_in_half_ridge_interval | ✓ |
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
| **TE22 Scan Certificate (Apr 2026)** | | | |
| TE22 coupling predictions are algebraically independent of SM data | TE22.ScanCertificate | ugp_coupling_predictions_are_independent | ✓ |
| UGP g1²/g2² prediction within 2% of SM@Mz | TE22.ScanCertificate | ugp_g1g2_prediction_close_to_SM | ✓ |
| TE22 SM gauge uniquely selected (decidable fragment) | TE22.ScanCertificate | SM_gauge_uniquely_selected, isSMGauge_iff, SM_is_D_minimizer_extended | ✓ (via `decide`) |
| TE22 SM full D-minimizer (framework) | TE22.ScanCertificate | — (pending Fintype + native_decide on full UniverseParams) | ⏳ tracked in tech-debt registry |
| **GTE Structural Theorems** | | | |
| Mirror orbit size 2 (involution) | GTE.StructuralTheorems | mirror_fiber_two, mirror_pair_induces_loop | ✓ |
| Minimality-duality at n=10 | GTE.StructuralTheorems | minimality_duality_n10, only_survivors_n10 | ✓ |
| **Fingerprint fixed-point (Tarski, Set form)** | GTE.StructuralTheorems | fingerprint_fixed_point_exists | ✓ |
| **Fingerprint fixed-point (bounded Finset form)** | GTE.StructuralTheorems | fingerprint_fixed_point_bounded | ✓ |
| Decidability phase transition | GTE.StructuralTheorems | decidability_phase_transition, local_decidability | ✓ |
| LeptonSeed lex-minimal at n=10 | GTE.StructuralTheorems | leptonSeed_is_lex_min_residual | ✓ |
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
| **GTE Phase (Mar 2026)** | | | |
| Def 2.5 — update map T (odd/even steps) | GTE.UpdateMap | gteQuotient, gteRemainder, oddStepA/B/C, evenStepA/B | ✓ |
| Prop 5.1 — orbit enforced by T, not hardcoded | GTE.UpdateMap | update_map_produces_canonical_orbit, orbit_determined_by_T | ✓ |
| Lem m2 — ridge remainder lock m₂=15 (all n≥5) | GTE.UpdateMap | ridge_remainder_lock_general | ✓ |
| prop:mirror-b1 — b₁ mirror-invariant (all n) | GTE.UpdateMap | mirror_b1_invariance | ✓ |
| prop:mersenne-extremal — b·q=2^k−16 forces c=2^k−1 | GTE.UpdateMap | mersenne_extremal_ridge | ✓ |
| Even-step c-invariance c₃=c₂=2^n−1 (all n≥5) | GTE.UpdateMap | even_step_c_invariance, c3_strict_eq_c2_at_n10 | ✓ |
| Mersenne gcd identity gcd(2^a−1,2^b−1)=2^gcd(a,b)−1 | GTE.MersenneGcd | mersenne_gcd_identity | ✓ |
| Mersenne entanglement: gcd(a,b)>1 → gcd(2^a−1,2^b−1)>1 | GTE.MersenneGcd | mersenne_entanglement_general | ✓ |
| c-value factorizations: 1023=3×11×31, 65535=3×5×17×257 | GTE.PrimeFactorAnalysis | c2_factorization, c3_factorization | ✓ |
| Compositeness growth: c₁ prime, c₂ and c₃ composite | GTE.PrimeFactorAnalysis | compositeness_growth | ✓ |
| Gen 1 isolation: 823 coprime to all Gen 2/3 components | GTE.PrimeFactorAnalysis | gen1_isolated, gen1_mersenne_isolation | ✓ |
| Gen 2↔3 entanglement via shared factors {3,11} | GTE.PrimeFactorAnalysis | gen2_gen3_entangled, c2_c3_not_coprime | ✓ |
| Factor-3 separation: 3∤c₁ but 3∣c₂ and 3∣c₃ | GTE.PrimeFactorAnalysis | three_separates_gen1 | ✓ |
| UGP prime sequence anchors (first two terms) | GTE.PrimeFactorAnalysis | first_ugp_prime, second_ugp_prime | ✓ |
| τ(2^m−1) ≥ τ(m) for m≥1 (injective Mersenne map) | GTE.MirrorDualConjecture | card_divisors_mersenne_ge | ✓ |
| τ(m) unbounded: τ(2^k)=k+1 | GTE.MirrorDualConjecture | tau_unbounded | ✓ |
| τ(2^n−16) unbounded as n→∞ | GTE.MirrorDualConjecture | card_divisors_ridge_unbounded | ✓ |
| **τ(Rₙ) = 5·τ(2^(n−4)−1) exact formula (n≥5)** | GTE.MirrorDualConjecture | tau_ridge_exact | ✓ |
| 2^a and 2^b−1 coprime (b≥1) | GTE.MirrorDualConjecture | coprime_pow2_mersenne | ✓ |
| τ(16) = 5 | GTE.MirrorDualConjecture | tau_16 | ✓ |
| MDL selection at n=10: c₁=823 is minimum | GTE.MirrorDualConjecture | mdl_c1_n10 | ✓ |
| MDL selection at n=13: c₁=9007 is minimum | GTE.MirrorDualConjecture | mdl_c1_n13 | ✓ |
| MDL selection at n=16: c₁=46681 is minimum | GTE.MirrorDualConjecture | mdl_c1_n16 | ✓ |
| MDL c₁ monotone across levels: 823 < 9007 < 46681 | GTE.MirrorDualConjecture | mdl_c1_monotone | ✓ |
| Mirror-dual conjecture (stated, open) | GTE.MirrorDualConjecture | MirrorDualConjecture | open |
| **Resolved Conjectures (7 of 10 proved)** | | | |
| Mirror min-dual: b₁ symmetric | Conjectures | mirror_min_dual_proved | ✓ |
| Fibonacci rigidity: gap = 13 | Conjectures | fib_rigidity_proved | ✓ |
| MDL monotonicity: c₁ increasing in q₂ | Conjectures | c1_monotone_in_q2 | ✓ |
| Robust universality | Conjectures | robust_universality_proved | ✓ |
| Sharp decidability boundary | Conjectures | sharp_boundary_proved | ✓ |
| Kernel compatibility (Quarter-Lock) | Conjectures | kernel_compatibility_proved | ✓ |
| Global c-attractor (one-step) | Conjectures | global_c_attractor_proved | ✓ |
| UGP prime infinitude (stated, open) | GTE.UGPPrimes | UGPPrimeInfinitudeConjecture | open |
| μ-flip distance (stated, open) | Conjectures | MuFlipDistanceConjecture | open |
| **DSI Export (real analysis)** | | | |
| Real-valued c₁ on hyperbola bq=R | GTE.DSIExport | ugpOutputGap | ✓ |
| Valid parameter shell {q ≥ 14, R/q ≥ 16} | GTE.DSIExport | ugpShell | ✓ |
| HasDerivAt: deriv = 13R/q² + 2q − 6 | GTE.DSIExport | ugpOutputGap_deriv | ✓ |
| Derivative positive on shell | GTE.DSIExport | ugpOutputGap_deriv_pos | ✓ |
| Uniform lower bound: deriv ≥ 22 | GTE.DSIExport | ugp_deriv_lower_bound | ✓ |
| Differentiable on (0,∞) | GTE.DSIExport | ugpOutputGap_differentiableOn | ✓ |
| Continuous on compact subsets | GTE.DSIExport | ugpOutputGap_continuousOn_Icc | ✓ |
| Wall 1 export bundle for DSI | GTE.DSIExport | UGPWall1Export | ✓ |
| Five concrete mirror-dual pairs certified (n=10,13,16) | GTE.MirrorDualConjecture | mirror_dual_n10/13/16_a/b/c | ✓ |
| Conjecture implies infinitely many distinct levels | GTE.MirrorDualConjecture | conjecture_implies_many_levels | ✓ |
| **Resonant Factory (twin-prime program)** | | | |
| Branch linearization: c₁ affine in b₂ | GTE.ResonantFactory | branch_linearization | ✓ |
| Factory gap-2: Q₊(t) = Q₋(t) + 2 | GTE.ResonantFactory | factory_gap_two | ✓ |
| D₊ = 119513 is prime | GTE.ResonantFactory | factoryDp_prime | ✓ |
| Local density ρ_F(p) for p ≤ 43 (Hasse check) | GTE.ResonantFactory | localDensity_3..43 | ✓ |
| No local obstruction (singular series S > 0) | GTE.ResonantFactory | hasse_check_no_obstruction | ✓ |
| Product algebra: F(t) = Q₋(t)·Q₊(t), both > 0 | GTE.ResonantFactory | factory_product_factorization | ✓ |
| **Analytic architecture (statements with cited proofs)** | | | |
| Dickman equidistribution in arithmetic progressions | GTE.AnalyticArchitecture | dickman_equidistribution_in_APs | ⚠ sorry (Tenenbaum III.6 — Mathlib infra gap) |
| CRT equidistribution within independence regime | GTE.AnalyticArchitecture | crt_equidistribution_within_regime | ⚠ sorry (Tenenbaum III.6 + CRT — Mathlib infra gap) |
| Q₋(t) ⊥ Q₊(t) coprime (algebraic, proved) | GTE.AnalyticArchitecture | qminus_qplus_coprime | ✓ |
