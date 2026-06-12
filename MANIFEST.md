# ugp-lean Theorem Manifest

**Toolchain:** `leanprover/lean4:v4.29.0-rc6`  
**Mathlib:** v4.29.1 (via `lakefile.lean`)  
**Build:** `lake build` from this directory  
**Root import:** `UgpLean.lean`  
**Last verified:** 2026-06-11 — 376 `.lean` files across 27 layers; 0 sorry on core proof path.

**Companion:** The formalization paper (`paper/ugp_lean_formalization.tex`) provides the complete theorem-indexed table mapping every definition and theorem to ugp-lean modules. Use it as the definitive paper-level reference. The curated highlights in `docs/THEOREMS.md` cover the most important theorems by layer.

| Paper / Source | Lean Module | Lean Theorem | Status |
|----------------|-------------|--------------|--------|
| Coarse entropy non-monotone on 8→9 step prefix (Lepton GTE sim, n=10) | GTE.GTESimulation; GTE.EntropyNonMonotone | gte_entropy_prefix8_gt_prefix9; Hpred8_gt_Hpred9 | ✓ |
| UWCA + history stack, backward ∘ forward = id | Universality.UWCAHistoryReversible | uwca_augmented_left_inverse; uwca_history_lane_step_reversible | ✓ |
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
| **Claim C (formal): TT = Weyl·2^g** | MassRelations.ClaimCBridge | claim_C_formal, claim_C_via_su3_const, claim_C_increment_is_weyl_scaled | ✓ (zero hyp, zero sorry; 2026-04-20) |
| **k_gen2 encodes doubled Weyl bisector** | MassRelations.ClaimCBridge | k_gen2_encodes_double_weyl_bisector, k_gen2_is_neg_phi_cos_double_TT_coeff | ✓ (zero hyp, zero sorry; 2026-04-20) |
| **Unified Pentagon–Hexagon–TT bridge** | MassRelations.ClaimCBridge | pentagon_hexagon_TT_unified_bridge | ✓ (zero hyp, zero sorry; 2026-04-20) |
| **THM-UCL-2 (k_gen): k_gen = φ·cos(π/10)** | ElegantKernel.Unconditional.KGenFullClosure | thm_ucl2_fully_unconditional | ✓ (zero hyp, zero sorry; 2026-04-20) |
| k_gen2 = −φ/2 | ElegantKernel.KGen2 | k_gen2_eq_neg_phi_half | ✓ |
| **Pentagon–Hexagon Bridge: k_gen + k_gen2 = φ·(cos π/10 − cos π/3)** | ElegantKernel.Unconditional.KGenFullClosure | k_gen_pentagon_hexagon_bridge, k_gen_pentagon_hexagon_bridge_half | ✓ (zero hyp, zero sorry; 2026-04-20) |
| THM-UCL-1 (k_gen2 from Fibonacci Hessian) | ElegantKernel.Unconditional.FibonacciPentagonBridge | thm_ucl1_unconditional, fibonacci_hessian_determines_value | ✓ |
| GTE canonical orbit | GTE.Evolution, GTE.Orbit | canonical_orbit_triples, canonical_orbit_three_steps | ✓ |
| Sieve Extended n∈[5,30] | Compute.SieveExtended | mirrorDualCount_10 | ✓ |
| **Ridge Minimality: n=10 smallest** | Compute.SieveBelow10 | ridgeSurvivors_{5..9}_empty, n10_is_minimal_admissible_ridge, ridge_minimality_and_existence | ✓ |
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
| **RC Tier Structure (Paper 24)** | | | |
| Tier-1/tier-2 boundary 1023 = 2^10 - 1 (Mersenne) | GTE.MersenneLadder | tier12_boundary_is_mersenne_10 | ✓ |
| Tier-2/tier-3 boundary 65535 = 2^16 - 1 (Mersenne) | GTE.MersenneLadder | tier23_boundary_is_mersenne_16 | ✓ |
| Tier boundaries strictly ordered: 1023 < 65535 | GTE.MersenneLadder | tier_boundaries_strictly_ordered | ✓ |
| Both tier boundaries are Mersenne numbers 2^k − 1 | GTE.MersenneLadder | tier_boundaries_are_mersenne | ✓ |
| Tier-2/tier-3 boundary = 2^(n+2·Nc)−1 (n=10, Nc=3) | GTE.MersenneLadder | tier23_boundary_from_ridge_and_Nc | ✓ |
| Lepton c-cascade spans all three tiers | GTE.MersenneLadder | lepton_c_values_span_all_tiers | ✓ |
| **Full tier structure conjunction** (all 7 facts, zero sorry) | GTE.MersenneLadder | ugp_rc_tier_structure | ✓ |
| **Composite Braid c-Rule (Paper 24 Category A upgrade)** | | | |
| Antiquark winding = −W(quark) (CPT reversal) | BraidAtlas.CompositeTriples | antiquark_winding_is_negation | ✓ |
| Meson winding = 0: W(q) + W(q̄) = 0 | BraidAtlas.CompositeTriples | meson_winding_zero | ✓ |
| H(0) = 0 → c is real+positive for mesons | BraidAtlas.CompositeTriples | meson_c_real_positive | ✓ |
| Baryon c real+positive for Q ≥ 0 | BraidAtlas.CompositeTriples | baryon_c_real_of_nonneg_charge | ✓ |
| Proton winding: W(u)+W(u)+W(d) = 3 = N_c·Q | BraidAtlas.CompositeTriples | proton_winding_eq_Nc_times_Q | ✓ |
| Neutron winding: W(u)+W(d)+W(d) = 0 = N_c·Q | BraidAtlas.CompositeTriples | neutron_winding_eq_Nc_times_Q | ✓ |
| Confinement tier: 15 = 2^4-1 (new Mersenne level) | BraidAtlas.CompositeTriples | confinement_mersenne_level | ✓ |
| Proton/neutron c=15 in confinement tier (c < 1023) | BraidAtlas.CompositeTriples | proton_neutron_c_eq_15_in_confinement_tier | ✓ |
| **Full composite c-rule conjunction** (zero sorry) | BraidAtlas.CompositeTriples | ugp_composite_braid_c_rule | ✓ |
| **a-component min-rule (proton, neutron)** | BraidAtlas.CompositeTriples | proton_a_eq_min, neutron_a_eq_min | ✓ |
| Correction 61 via two independent paths | BraidAtlas.CompositeTriples | proton_b_correction_from_lepton_seed, proton_b_correction_from_delta, proton_b_correction_agreement | ✓ |
| **b(proton) = N_c²·(a_u·2^{N_c²−1}−δ)+(N_c−1) = 11459** | BraidAtlas.CompositeTriples | proton_b_formula | ✓ |
| b(neutron) = proton_b − 2N_c² = 11441 | BraidAtlas.CompositeTriples | neutron_b_formula | ✓ |
| b(p)−b(n) = 2N_c² = 18 | BraidAtlas.CompositeTriples | proton_neutron_b_diff | ✓ |
| **Full nucleon b-formula conjunction** (zero sorry) | BraidAtlas.CompositeTriples | ugp_nucleon_b_formula | ✓ |
| b(Sigma+) = (b(s)+a_u×seesaw)×(b(s)+a_u×seesaw+(a_u×(Nc²-1))²) = 639161 | BraidAtlas.CompositeTriples | sigma_plus_b_formula | ✓ |
| |S|=1 sector b: Lambda=Sigma0=Sigma-=38236 | BraidAtlas.CompositeTriples | strange_baryon_s1_b_eq_lambda | ✓ |
| |S|=2 sector b: Xi0=Xi-=878434 | BraidAtlas.CompositeTriples | strange_baryon_s2_b_eq_xi | ✓ |
| **All 9 light baryon b-formulas** (full conjunction, zero sorry) | BraidAtlas.CompositeTriples | ugp_all_baryon_b_formulas | ✓ |
| **GTE Orbit Uniqueness and Vacuum** | | | |
| SM orbit is uniquely forced 3-step trajectory from GEN₁ | Universality.CUP3DUniqueness | fmdl_orbit_is_unique_psc_trajectory | ✓ |
| All 16,807 states reach vacuum in ≤7 steps (native_decide) | Universality.CUP3DUniqueness | fmdl_universal_7step_convergence | ✓ |
| Vacuum is unique attractor; no false vacua | Universality.CUP3DUniqueness | fmdl_vacuum_is_unique_attractor | ✓ |
| Rule 110 unique weight-5 orbit satisfier among C(8,5)=56 rules | Universality.CUP4TotalParity | rule110_unique_weight5_orbit_satisfier | ✓ |
| Rule 110 completely isolated on all 1024 orbit pairs | Universality.OrbitPerturbationCatalog | rule110_orbit_complete_isolation | ✓ |
| All 5 cyclic rotations of GEN₁ are Garden-of-Eden states | Universality.GoEStabilityHierarchy | fmdl_gen1_all_rotations_are_goe | ✓ |
| p=5 unique prime for full transitivity of weight-3 vector | Universality.Z5TransitivityUniqueness | z5_transitivity_uniqueness | ✓ |
| d-dim CA satisfying SM orbit must apply Rule 110 on slices | Universality.DimensionalSliceUniqueness | dimensional_slice_uniqueness | ✓ |
| **GTE Compilation and Uniqueness** | | | |
| sigma_gte compilation theorem (by rfl) | Universality.GTECompilation | gte_compilation_theorem | ✓ |
| GTE unique up to bisimulation (no minimality hypothesis) | Universality.GTEUniqueness | gte_uniqueness_up_to_bisimulation | ✓ |
| **Mass Relations (extended)** | | | |
| PMNS: sin²θ₁₂=4/13, sin²θ₂₃=19/42, sinθ₁₃=11/73, δ_CP=8π/7 | MassRelations.NeutrinoSector | (various) | ✓ |
| Higgs quartic λ = φ/(4π)·(1+(IPT−1)/27); 0.12 < λ < 0.14 | MassRelations.HiggsQuartic | (various) | ✓ |
| Neutrino mass ratio R ≈ 0.02936 within 1% of NuFIT 6.0 | MassRelations.NeutrinoMassRatio | neutrino_mass_ratio_within_1pct_of_nufit | ✓ |
| sin²θ₂₃^NLO = 209/441 | MassRelations.PMNSNLOCorrection | (various) | ✓ |
| **η_B and BPS Coupling** | | | |
| η_B = 6.109×10⁻¹⁰ CatAL unconditional (+0.15σ vs PDG) | Physics.FKTTCoupling | kink_top_coupling_eq_eps_FN | ✓ |
| BPS saturation T₁₁=0 by rfl | Physics.FKTTCoupling | phi_mdl_kink_bps_saturation | ✓ |
| **GF(7) Polynomial Explorations** | | | |
| Ground states {0,1,5} (poly_p_uniform_gs_roots, CatAL) | Polynomial.PolyExplorations | poly_p_uniform_gs_roots | ✓ |
| Period-475 certificates (native_decide, CatAL) | Polynomial.PolyExplorations | period_475_returns, period_475_is_minimal | ✓ |
| Vacuum basin = 52; KL divergence p≠f_MDL at (1,1,5) | Polynomial.PolyExplorations | poly_p_vacuum_basin_card_eq_52, kl_divergence_fmdl_p_nonzero | ✓ |
| PSC-projection bundle (CatAL) | Polynomial.PolyExplorations | psc_projection_gives_fmdl | ✓ |
| **GTE Causal Tree** | | | |
| 1023-node binary tree causal graph (ruleGTE, decide) | Polynomial.GTECausalTree | gte_rulegte_ten_generations | ✓ |
| Horton ratio r_B=2 at all levels (CatAL) | Polynomial.GTECausalTree | perfectTree_horton_ratio | ✓ |
| **MDL Three-Level Unification** | | | |
| Cross-module CatAL bundle: theory selection + PSC + orbit | Polynomial.MDLThreeLevelUnification | mdl_three_level_unification | ✓ |
| PSC + closed choice force transputation | Polynomial.MDLThreeLevelUnification | mdl_level23_closed_choice_forces_transputation | ✓ |
| **Algebraic Structure** | | | |
| Fix(T_n) = {vacuum} for all ring sizes (dynamical zeta) | Polynomial.DynamicalZeta | vacuum_unique_temporal_fixed_point_ring | ✓ |
| Zero-energy rings = {0ⁿ,1ⁿ,5ⁿ} for all n≥3 | Polynomial.SpinSevenGroundSpace | gte_ring_ground_states_uniform_general | ✓ |
| cond(K)=15=N_gen·N_fam for K=ℚ(√−3,√5) | Polynomial.BiquadraticCompositum | (various) | ✓ |
| \|AGL(1,7)\|=42; reflection swaps Rule 110 ↔ Rule 124 | Polynomial.AGL17ChiralZ2 | (various) | ✓ |
| p(x,x,x)−x = −x(x²+x−1); SRRG/Rule 110 as ℤ-quadratic fibers | Polynomial.GoldenQuadratic | gte_diagonal_quadratic_factorization | ✓ |
| Z₇ winding conservation ≡ U(1)_EM charge conservation | Universality.GUTStructure | winding_charge_equivalence | ✓ |
| Parity projection forcing maximal (777 + 16,807 forms) | Universality.ParityProjectionForcing | parity_projection_additive_forcing | ✓ |
| **CMCA Physical Point** | | | |
| aM=1/7, am_φ=7/8, Tape Saturation Theorem, M_Pl/Λ_GTE=3¹⁰·7¹⁸/2⁴ | Physics.CMCAPhysicalPoint | (various) | ✓ |
| **Wasserstein Distance** | | | |
| W₁ nonneg, triangle inequality, W₁=0 iff equal, attainment | ContinuumLimit.WassersteinDistance | W1_nonneg, W1_triangle, W1_eq_zero_iff, W1_attained | ✓ |
| **Spin-7 Spectroscopy** | | | |
| Directed wall/bump energies; gap exponent 3/2 (14 theorems) | Polynomial.SpinSevenWallSpectroscopy | spin7_directed_wall_energies | ✓ |
| Zero-energy spectral radius ρ=1; A=1 (10 theorems) | Polynomial.SpinSevenSpectatorAmplitude | spin7_spectator_amplitude | ✓ |
| Perron–Frobenius package for thermal transfer matrix (7 theorems) | Polynomial.SpinSevenTransferPrimitivity | spin7_transfer_pf_hypotheses | ✓ |
