# ugp-lean: Theorem Catalog

What ugp-lean proves. All listed theorems have **0 sorry, 0 axioms** on the core path unless explicitly marked ⚠.

**Sorry audit:** **only two** sorries remain in the codebase,
both openly disclosed with precise citations:
- `dickman_equidistribution_in_APs` and `crt_equidistribution_within_regime`
  in `GTE.AnalyticArchitecture` — classical analytic-NT results (Tenenbaum
  III.6); pending Mathlib analytic-NT infrastructure (Dickman function
  asymptotics).  These are research-level formalization gaps, not
  correctness defects.

**Prior integrity issues fixed:**
- **Tarski `fingerprint_fixed_point_exists`** statement on `Finset ℕ` with
  only monotonicity was **false** (counter-example `F(P) = P ∪ {max(P)+1}`);
  restated on `Set ℕ` and proved via `OrderHom.lfp`; bounded `Finset` variant
  `fingerprint_fixed_point_bounded` also added.
- **TE22 `SM_is_D_minimizer_extended` vacuous theorem** — the original
  statement had conclusion `True` (vacuous) despite its name claiming SM
  D-minimizer uniqueness.  Replaced with a genuine decidable uniqueness
  claim `SM_gauge_uniquely_selected` + `isSMGauge_iff` (both proved by
  `decide`) that captures the decidable fragment.  The original name is
  retained as an alias pointing to `isSMGauge_iff`.  The **full** SM
  D-minimizer theorem (over the 20,160+ universe discretization) remains
  pending Fintype + native_decide and is tracked in the tech-debt registry.

## Core Classification (RSUC)

| Theorem | Module | Statement |
|---------|--------|-----------|
| **theoremA_general** | TheoremA | ∀n, UnifiedAdmissibleAt n t → t ∈ CandidatesAt n |
| **theoremA** | TheoremA | n=10 corollary: UnifiedAdmissible t → t ∈ Candidates |
| **rsuc_theorem** | RSUC | Residual Seed Uniqueness: residual = Candidates; unique up to MirrorEquiv |
| **theoremB** | TheoremB | Residual = Candidates; finite classification |
| **mdl_selects_LeptonSeed** | TheoremB | Lepton Seed is lex-min in Residual |
| **rsuc_formal** | FormalRSUC | (SF₀ ∧ QL₀ ∧ RA₀) t → t ∈ Residual ∧ MDL selects LeptonSeed |
| **rsuc_canon** | FormalRSUC | UnifiedAdmissible t → canon t = LeptonSeed |
| **strengthening_cannot_add_survivors** | MonotonicStrengthening | Strengthening predicates cannot add survivors to Residual |

## Ridge & Sieve

| Theorem | Module | Statement |
|---------|--------|-----------|
| **ridge_10** | RidgeDefs | ridge 10 = 1008 |
| **ridgeSurvivors_10** | Sieve | ridgeSurvivorsFinset 10 = {(24,42), (42,24)} |
| **ridgeSurvivors_5_empty** | SieveBelow10 | ridgeSurvivorsFinset 5 = ∅ |
| **ridgeSurvivors_6_empty** | SieveBelow10 | ridgeSurvivorsFinset 6 = ∅ |
| **ridgeSurvivors_7_empty** | SieveBelow10 | ridgeSurvivorsFinset 7 = ∅ |
| **ridgeSurvivors_8_empty** | SieveBelow10 | ridgeSurvivorsFinset 8 = ∅ |
| **ridgeSurvivors_9_empty** | SieveBelow10 | ridgeSurvivorsFinset 9 = ∅ |
| **n10_is_minimal_admissible_ridge** | SieveBelow10 | ∀ n, 5 ≤ n → n < 10 → ridgeSurvivorsFinset n = ∅ |
| **ridge_minimality_and_existence** | SieveBelow10 | (∀ n, 5≤n → n<10 → survivors=∅) ∧ (survivors at 10 = {(24,42),(42,24)}) |
| **ridge_remainder_lock** | RidgeRigidity | (2^10−1) % b₂ = 15 for b₂∣1008, b₂≥16 |
| **m2_canonical** | RidgeRigidity | (2^10−1) % 42 = 15 |
| **quotient_gap_13** | RidgeRigidity | q₂ − q₁ = 13 when q₂ ≥ 13 |
| **survivor_gap_42_24** | RidgeRigidity | 24 − q1FromQ2 24 = 13 |
| **survivor_gap_24_42** | RidgeRigidity | 42 − q1FromQ2 42 = 13 |
| **remainder_gap_identity** | RidgeRigidity | t=20, s=7, t−s=13 |

## Prime-Lock & Mirror

| Theorem | Module | Statement |
|---------|--------|-----------|
| **prime_823** | PrimeLock | Nat.Prime 823 |
| **prime_2137** | PrimeLock | Nat.Prime 2137 |
| **n10_survivor_c1_primes** | PrimeLock | Both 823 and 2137 prime |
| **mirror_prime_lock** | PrimeLock | (42,24) and (24,42) yield prime c₁ |
| **c1_from_divisor** | PrimeLock | c₁ expressed from b₂,q₂ formula |
| **mirrorC1_ne_leptonC1** | TripleDefs | 2137 ≠ 823 |

## GTE Canonical Orbit

| Theorem | Module | Statement |
|---------|--------|-----------|
| **canonical_orbit_triples** | Evolution | LeptonSeed=(1,73,823), Gen2=(9,42,1023), Gen3=(5,275,65535) |
| **fib13_eq** | Evolution | fib13 = 233 |
| **even_step_rigidity** | Evolution | canonicalGen2.b + fib13 = canonicalGen3.b |
| **worked_orbit_enforced** | Evolution | Same as canonical_orbit_triples |
| **trace_identifiability** | Evolution | G₂=(9,42,1023) ⇒ n=10, b₁=73, c₁∈{823,2137} |
| **c2_canonical** | Evolution | 2^10 − 1 = 1023 |
| **c3_canonical** | Evolution | 2^16 − 1 = 65535 |

## Quarter-Lock & Elegant Kernel

| Theorem | Module | Statement |
|---------|--------|-----------|
| **quarterLockLaw** | QuarterLock | ∃ k_M k_gen2, k_M = k_gen2 + ¼k_L2 |
| **quarterLockStability_holds** | QuarterLock | Defect 0 ⇒ on Quarter-Lock plane |
| **k_L2_eq** | ElegantKernel | k_L2 = 7/512 |
| **k_L2_pos** | ElegantKernel | 0 < k_L2 |
| **L_model_pos** | ElegantKernel | 0 < L_model |
| **L_model_eq_log_residual** | LModelDerivation | L_model = log₂(residualProduct), residual = (2⁴·5³)/3 |
| **L_model_eq_log_wedge_form** | LModelDerivation | L_model = log₂((wedge2Factor · wedge5Factor) / orbitLength) |
| **L_model_from_gauge_structure** | LModelDerivation | L_model = log₂((D₁ · 125) / 3) from D₁, 5³, orbit length 3 |

## Lepton Mass Prediction Pipeline

Module `MassRelations.LeptonMassPrediction`. Zero sorry.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **predictedLeptonMass_zero** | MassRelations.LeptonMassPrediction | predictedLeptonMass m_e θ 0 = m_e |
| **muon_a_value_is_nine** | MassRelations.LeptonMassPrediction | canonicalGen2.a = 9 |
| **koide_angle_equals_two_ninths** | MassRelations.LeptonMassPrediction | koideThetaUGP = 2/9 |
| **koide_angle_equals_two_over_muon_a** | MassRelations.LeptonMassPrediction | koideThetaUGP = 2/canonicalGen2.a |
| **epic_8_lepton_mass_structural_summary** | MassRelations.LeptonMassPrediction | Bundle: angle=2/muon_a ∧ muon_a=9 ∧ Q=2/3 for any θ |

## VV Unified N_c Formula

Module `MassRelations.DownRational` §7 establishes the unified
N_c-derivation of all three VV mass coefficients. Zero sorry.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **alpha_d_from_N_c** | MassRelations.DownRational | α_d = 1+(N_c+1)/N_c² = 13/9 |
| **beta_d_from_N_c** | MassRelations.DownRational | β_d = -(1+1/(2N_c)) = -7/6 |
| **gamma_d_from_N_c** | MassRelations.DownRational | γ_d = -(N_c+2)/(2(N_c²-2)) = -5/14 |
| **VV_unified_from_N_c** | MassRelations.DownRational | All three from N_c: α∧β∧γ = rational(N_c) |

> N_c²-2 = δ = 7, so γ_d = -(N_c+2)/(2δ). Combined with the N_c structural chain,
> both the Koide lepton sector (θ = (N_c²-1)/(4N_c²)) and the VV quark sector
> are controlled by N_c = 3.

---

## VV Coefficient Structural Identifications

Module `MassRelations.DownRational` §§5-6 supplies group-theoretic
identifications of each VV coefficient. Zero sorry.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **beta_d_from_hypercharge** | MassRelations.DownRational | β_d = -(1+Y_Q) = -7/6, Y_Q=1/6 |
| **alpha_d_from_su5_rank** | MassRelations.DownRational | α_d = 1+rank(SU5)/9 = 13/9 |
| **alpha_d_from_su3_weyl** | MassRelations.DownRational | α_d = (\|W(SU3)\|+7)/9 |
| **gamma_d_from_gut_dims** | MassRelations.DownRational | γ_d = -dim(45)/dim(126) = -5/14 |
| **VV_coefficients_structural_summary** | MassRelations.DownRational | Bundle: all 3 VV coefficient identifications |

## Complete N_c Structural Chain

Module `MassRelations.KoideAngle` provides the full N_c structural chain.
All zero sorry, zero hypotheses. N_c = 3 determines all SM fermion structural constants.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **muon_a_eq_color_rank_squared** | MassRelations.KoideAngle | canonicalGen2.a = 3^2 = 9 |
| **lepton_a_values_nc_pattern** | MassRelations.KoideAngle | {a_e,a_μ,a_τ} = {N_c^0,(N_c²+1)/2,N_c²} |
| **lepton_a_values_in_nc_set** | MassRelations.KoideAngle | all lepton a-values ∈ {1,(N_c²+1)/2,N_c²} |
| **max_lepton_a_eq_nc_squared** | MassRelations.KoideAngle | max{a_e,a_μ,a_τ} = N_c² = 9 |
| **lepton_b1_from_N_c** | MassRelations.KoideAngle | leptonB = N_c^4 − (N_c²+1)/2 − N_c = 73 |
| **delta_from_N_c** | MassRelations.KoideAngle | ugp1_s = N_c + (N_c²−1)/2 = 7 |
| **top_a_from_N_c** | MassRelations.KoideAngle | leptonB + 3 = N_c^4 − (N_c²+1)/2 = 76 |
| **delta_b1_eq_511** | MassRelations.KoideAngle | ugp1_s × leptonB = 511 |
| **strand_count_eq_su_nc_adj_div_4** | MassRelations.KoideAngle | (N_c²−1)/4 = 2 = lepton strand count |
| **koide_angle_from_N_c_pure** | MassRelations.KoideAngle | koideThetaUGP = (N_c²−1)/(4N_c²) = 2/9 |
| **koide_angle_three_forms** | MassRelations.KoideAngle | All three formulas equal 2/9 |
| **N_c_determines_everything** | MassRelations.KoideAngle | Full chain: step∧strand∧δ∧b₁∧θ all from N_c |

> **Key identity**: θ = (N_c²−1)/(4N_c²) = dim(SU(N_c))/(4N_c²) = 8/36 = 2/9.  
> Combined with `SM_gauge_uniquely_selected` (N_c=3 from PSC): complete axiom-level derivation.

---

## Koide Angle and β Derivation

Modules `MassRelations.KoideAngle` and `MassRelations.UpLeptonCyclotomic` §5
together derive the Koide angle and the β coefficient.
All zero sorry, zero hypotheses.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **koide_angle_eq_two_ninths** | MassRelations.KoideAngle | koideThetaUGP = 2/9 |
| **koide_angle_from_gte_structure** | MassRelations.KoideAngle | koideThetaUGP = 2/canonicalGen2.a |
| **cos_sum_three_120** | MassRelations.KoideAngle | Σcos(θ+2πg/3)=0 |
| **cos_sq_sum_three_120** | MassRelations.KoideAngle | Σcos²(θ+2πg/3)=3/2 |
| **koide_Q_two_thirds** | MassRelations.KoideAngle | Q=(Σr²)/(Σr)²=2/3 for any θ |
| **beta_eq_alpha_div_c2_su3** | MassRelations.UpLeptonCyclotomic | β = α/C₂(SU3) = (π/6)/(4/3) = π/8 |
| **beta_eq_alpha_times_c2_su2** | MassRelations.UpLeptonCyclotomic | β = α×C₂(SU2) = π/8 |
| **alpha_over_beta_eq_c2_su3** | MassRelations.UpLeptonCyclotomic | α/β = C₂(SU3) = 4/3 |

---

## 13_SPEC Claim C — TT Formula = Weyl Bisector × Binary Cascade

Module `MassRelations.ClaimCBridge` establishes Claim C. All theorems zero sorry, zero hypotheses.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **claim_C_formal** | MassRelations.ClaimCBridge | cascadeState g = angleToAlpha1 omega1 · 2^g + π/8 (formal Claim C: Claim A ⊗ Claim B) |
| **claim_C_via_su3_const** | MassRelations.ClaimCBridge | cascadeState g = su3WeylBisectorAngle · 2^g + π/8 |
| **claim_C_increment_is_weyl_scaled** | MassRelations.ClaimCBridge | step(g→g+1) = Weyl bisector · 2^g |
| **k_gen2_encodes_double_weyl_bisector** | MassRelations.ClaimCBridge | k_gen2 = −φ · cos(2 · Weyl_bisector) = −φ · cos(π/3) |
| **pentagon_hexagon_TT_unified_bridge** | MassRelations.ClaimCBridge | Conjunction of all 5 structural facts: TT ∧ Weyl ∧ k_gen2=−φcos(2Weyl) ∧ k_gen=φcos(π/10) ∧ Pentagon-Hexagon Bridge |
| **k_gen2_is_neg_phi_cos_double_TT_coeff** | MassRelations.ClaimCBridge | k_gen2 = −φ · cos(2·(π/6)) |

> **Note:** "Formal Claim C" proves the TT formula coefficient IS the SU(3) Weyl bisector and the 2^g structure comes from the binary cascade. The physical question (WHY the GTE cascade acts as a Weyl rotation) remains interpretive — the formal mathematical content is now Lean-certified.

---

## UCL Unconditional Closure (k_gen, k_gen2, Pentagon–Hexagon Bridge)

All theorems in this section have **zero hypotheses, zero sorry, Mathlib-only axioms**.  
Module: `ElegantKernel.Unconditional.KGenFullClosure` (§§1–9).

| Theorem | Module | Statement |
|---------|--------|-----------|
| **thm_ucl2_fully_unconditional** | ElegantKernel.Unconditional.KGenFullClosure | k_gen_derived = φ·cos(π/10) = √(φ²−¼) ≈ 1.5388; derived via Quarter-Lock substitution μ=λ²−¼ on Fibonacci char poly |
| **thm_ucl2_sqrt_form** | ElegantKernel.Unconditional.KGenFullClosure | k_gen_derived = √(φ²−¼) (equivalent form) |
| **thm_ucl2_summary** | ElegantKernel.Unconditional.KGenFullClosure | k_gen_derived = φcos(π/10) ∧ = √(φ²−¼) ∧ > 0 ∧ > 1 ∧ k_gen² = φ+¾ |
| **k_gen2_eq_neg_phi_half** | ElegantKernel.KGen2 | k_gen2 = −φ/2 (by definition; also = cos(4π/5)) |
| **thm_ucl1_unconditional** | ElegantKernel.Unconditional.FibonacciPentagonBridge | If k_gen2 = −λ_dom/2 and λ_dom satisfies Fibonacci char poly, then k_gen2 = −φ/2 |
| **k_gen_pentagon_hexagon_bridge** | ElegantKernel.Unconditional.KGenFullClosure | k_gen_derived + k_gen2 = φ·(cos(π/10) − cos(π/3)); bridges D₅ pentagonal (Fibonacci/Quarter-Lock) and D₆ hexagonal (SU(3) Weyl/TT formula α=π/6) symmetries |
| **k_gen_pentagon_hexagon_bridge_half** | ElegantKernel.Unconditional.KGenFullClosure | k_gen_derived + k_gen2 = φ·(cos(π/10) − ½) (equivalent half-angle form) |

> **Note on k_gen = π/2 (KGen.lean):** The file `ElegantKernel.KGen` defines `k_gen := π/2` under a conditional "FibonacciPhaseAxiom" that is tautological. This older path is superseded by `thm_ucl2_fully_unconditional` in `KGenFullClosure`. The value π/2 was also corrected in the SM paper (commit 3762f9e4, ugp-physics) and in `theoretical_coefficients.json`. The canonical value is **φ·cos(π/10) ≈ 1.5388**, not π/2 ≈ 1.5708.

## Exclusion Filters

| Theorem | Module | Statement |
|---------|--------|-----------|
| **exclude_16** | ExclusionFilters | c₁ composite for (16,63) |
| **exclude_18** | ExclusionFilters | c₁ composite for (18,56) |
| **exclude_21** | ExclusionFilters | c₁ composite for (21,48) |
| **exclude_28** | ExclusionFilters | c₁ composite for (28,36) |
| **exclude_36** | ExclusionFilters | c₁ composite for (36,28) |
| **exclude_63** | ExclusionFilters | c₁ composite for (63,16) |

## Universality

| Theorem | Module | Statement |
|---------|--------|-----------|
| **rule110_output_iff_minterm** | Rule110 | Output 1 ↔ neighborhood ∈ S_110 |
| **uwca_simulates_rule110** | UWCAembedsRule110 | UWCA_embeds_Rule110 |
| **ugp_is_turing_universal** | TuringUniversal | UGP_substrate_turing_universal |
| **architecture_bridge** | ArchitectureBridge | uniqueness_of_physical_program |
| **uwca_augmented_left_inverse** | UWCAHistoryReversible | Backward ∘ forward = id on tape × history stack (exact lift) |
| **uwca_history_lane_step_reversible** | UWCAHistoryReversible | Same with empty initial history |
| **gte_entropy_prefix8_gt_prefix9** | EntropyNonMonotone | Coarse Shannon entropy drops from 8- to 9-step macro prefix along simulated GTE orbit (\(n=10\)) |

## Phase 4 (Stubs / Constants)

| Theorem | Module | Statement |
|---------|--------|-----------|
| **leptonB_matches_deltaUGP** | DeltaUGP | deltaUGPFormula leptonB |
| **k_L2_eq** | ElegantKernel | k_L2 = 7/512 (derived from ugp1_s=7, 2^9=512 block scale) |
| **k_L2_from_ugp1_s** | ElegantKernel | k_L2 = ugp1_s / 2^9 (structural link to mirror offset) |
| **block_denom_in_half_ridge_interval** | ElegantKernel | 504 < 2^9 ≤ 1008=ridge(10) (2^9 is unique power of 2 in half-ridge interval) |
| **g1Sq_bare_eq** | GaugeCouplings | g1Sq_bare = 16/125 |
| **g2Sq_bare_eq** | GaugeCouplings | g2Sq_bare = 2329/5400 |
| **g3Sq_bare_eq** | GaugeCouplings | g3Sq_bare = 41075281/27648000 |
| **ugp_coupling_predictions_are_independent** | TE22.ScanCertificate | C15/C16/C4' derived from ugp-lean rationals, not from SM data |
| **ugp_g1g2_prediction_close_to_SM** | TE22.ScanCertificate | UGP g1²/g2² prediction within 2% of SM value at M_Z |
| **SM_gauge_uniquely_selected** | TE22.ScanCertificate | Among all 60 (GaugeGroup, Dimension) pairs, exactly `(SU3xSU2xU1, 4D)` satisfies `isSMGauge` (decided) |
| **isSMGauge_iff** | TE22.ScanCertificate | `isSMGauge g d = true ↔ g = SU3xSU2xU1 ∧ dim_val d = 4` (decided) |
| **SM_is_D_minimizer_extended** | TE22.ScanCertificate | Alias of `isSMGauge_iff` (decidable fragment of full D-minimizer claim; full claim over 20,160+ universes still pending Fintype+native_decide) |

## GTE Number Theory

| Theorem | Module | Statement |
|---------|--------|-----------|
| **tau_ridge_exact** | MirrorDualConjecture | τ(2^n−16) = 5·τ(2^(n−4)−1) for n≥5 |
| **coprime_pow2_mersenne** | MirrorDualConjecture | Coprime(2^a, 2^b−1) for b≥1 |
| **mdl_c1_n10/n13/n16** | MirrorDualConjecture | MDL-selected c₁ at each level |
| **branch_linearization** | ResonantFactory | c₁(b₂,q₂) = b₂·(q₂−13) + B(q₂) |
| **factory_gap_two** | ResonantFactory | Q₊(t) = Q₋(t) + 2 for all t |
| **factoryDp_prime** | ResonantFactory | D₊ = 119513 is prime |
| **localDensity_3..43** | ResonantFactory | ρ_F(p) for good primes p ≤ 43 |
| **hasse_check_no_obstruction** | ResonantFactory | ρ_F(p) < p for all checked primes |

## Analytic Architecture (documented statements)

Statements supporting the Selberg–Delange architecture for the one-factor sum.
Classical analytic-NT results from Tenenbaum III.6; Lean proofs pending
Mathlib analytic-NT infrastructure (Dickman function asymptotics, character
sum estimates).

| Theorem | Module | Status |
|---------|--------|--------|
| **qminus_qplus_coprime** | AnalyticArchitecture | ✓ algebraic, proved zero-sorry |
| **dickman_equidistribution_in_APs** | AnalyticArchitecture | ⚠ sorry — Tenenbaum III.6, Mathlib infra gap |
| **crt_equidistribution_within_regime** | AnalyticArchitecture | ⚠ sorry — depends on Dickman + CRT |

## Resolved Conjectures (7 of 10)

| Theorem | Module | Statement |
|---------|--------|-----------|
| **mirror_min_dual_proved** | Conjectures | b₁(b₂,q₂) = b₁(q₂,b₂) — commutativity of + |
| **fib_rigidity_proved** | Conjectures | q₂ − q₁ = 13 — definitional from q₁ = q₂ − 13 |
| **c1_monotone_in_q2** | Conjectures | c₁ strictly increasing in q₂ (corrected MDL direction) |
| **robust_universality_proved** | Conjectures | = ugp_is_turing_universal (unconditional) |
| **sharp_boundary_proved** | Conjectures | Decidable + RE-hard, both proved |
| **kernel_compatibility_proved** | Conjectures | Quarter-Lock is unconditional algebraic identity |
| **global_c_attractor_proved** | Conjectures | c reaches 2^n−1 in one step via even_step_c_invariance |

## GTE Structural Theorems

| Theorem | Module | Statement |
|---------|--------|-----------|
| **mirror_fiber_two** | StructuralTheorems | \|{(b₂,q₂),(q₂,b₂)}\| = 2 when b₂ ≠ q₂ |
| **mirror_pair_induces_loop** | StructuralTheorems | Mirror-dual pair induces orbit of size 2 under involution |
| **minimality_duality_n10** | StructuralTheorems | At n=10, MDL pair is {(24,42), (42,24)} |
| **only_survivors_n10** | Compute.ExclusionFilters | Prime-locked ridge survivors at n=10 are exactly {(24,42), (42,24)} |
| **fingerprint_fixed_point_exists** | StructuralTheorems | Monotone F : Set ℕ → Set ℕ has a fixed point (Tarski via `OrderHom.lfp`) |
| **fingerprint_fixed_point_bounded** | StructuralTheorems | Monotone F : Finset ℕ → Finset ℕ bounded by B has fixed point P ⊆ B (Knaster-Tarski on finite Boolean sublattice) |
| **decidability_phase_transition** | StructuralTheorems | Local decidability ∧ global (Turing) universality |
| **leptonSeed_is_lex_min_residual** | StructuralTheorems | LeptonSeed lex-minimal c in residual triples at n=10 |

## Open Conjectures (3 of 10)

| Conjecture | Module | Statement |
|------------|--------|-----------|
| **MirrorDualConjecture** | MirrorDualConjecture | Infinitely many mirror-dual pairs (twin-prime analog) |
| **UGPPrimeInfinitudeConjecture** | UGPPrimes | Infinitely many UGP primes (follows from Mirror-Dual) |
| **MuFlipDistanceConjecture** | Conjectures | Bounded μ-flip waiting time on linear progressions |

## Real Analysis / DSI Export

| Theorem | Module | Statement |
|---------|--------|-----------|
| **ugpOutputGap** | DSIExport | Real-valued c₁ on hyperbola: g_R(q) = (R/q+q+7)(q-13)+20 |
| **ugpShell** | DSIExport | Valid parameter domain {q ≥ 14, R/q ≥ 16, q > 0} |
| **ugpOutputGap_deriv** | DSIExport | HasDerivAt: g'(q) = 13R/q² + 2q − 6 |
| **ugpOutputGap_deriv_pos** | DSIExport | Derivative positive for q ≥ 14, R > 0 |
| **ugp_deriv_lower_bound** | DSIExport | Uniform bound: g'(q) ≥ 22 on shell |
| **ugpOutputGap_differentiableOn** | DSIExport | Differentiable on (0,∞) |
| **ugpOutputGap_continuousOn_Icc** | DSIExport | Continuous on compact subsets |
| **UGPWall1Export** *(structure)* | DSIExport | Packaged export for DSI SmallSymmetricMVTBundle |

## RC Tier Structure (Paper 24: Substrate Depth and Self-Generated Mass)

These theorems certify the arithmetic tier boundaries of the reflexive-closure
analysis (Spivack 2026, Paper 24). Status: **Category A** (arithmetic bounds
derived from Lean-certified GTE cascade); **Category A/D** for the empirical
RC correlation (computational COMP-EP18 backed, r = −0.944 p = 6.7×10⁻¹⁹
n = 38; RC predicate not yet formalized in Lean).

| Theorem | Module | Statement |
|---------|--------|-----------|
| **tier12_boundary_is_mersenne_10** | GTE.MersenneLadder | 1023 = 2^10 − 1 |
| **tier23_boundary_is_mersenne_16** | GTE.MersenneLadder | 65535 = 2^16 − 1 |
| **tier_boundaries_strictly_ordered** | GTE.MersenneLadder | 1023 < 65535 |
| **tier_boundaries_are_mersenne** | GTE.MersenneLadder | ∃k₁ k₂, 1023 = 2^k₁−1 ∧ 65535 = 2^k₂−1 |
| **tier23_boundary_from_ridge_and_Nc** | GTE.MersenneLadder | 65535 = 2^(10+2·3)−1 (N_c=3) |
| **lepton_c_values_span_all_tiers** | GTE.MersenneLadder | LeptonSeed.c < 1023, c₂ = 1023, c₃ = 65535 |
| **ugp_rc_tier_structure** | GTE.MersenneLadder | Full conjunction of all 7 tier facts (zero sorry) |

## Composite Braid c-Rule (Paper 24 — Category A upgrade)

Module `BraidAtlas.CompositeTriples` formalizes the composition law for
composite hadron GTE triples. Status: **Category A** for writhe/chirality/tier
theorems and the **full proton/neutron (a,b,c) derivation** (all zero sorry);
**Category A/D** for the sector assignment rule (empirically validated).

### c-component theorems

| Theorem | Module | Statement |
|---------|--------|-----------|
| **antiquark_winding_is_negation** | BraidAtlas.CompositeTriples | W(q̄) = −W(q) (CPT reversal) |
| **meson_winding_zero** | BraidAtlas.CompositeTriples | W(q) + W(q̄) = 0 for all quark types |
| **meson_c_real_positive** | BraidAtlas.CompositeTriples | H(0) = 0, so c is real+positive for mesons |
| **baryon_c_real_of_nonneg_charge** | BraidAtlas.CompositeTriples | c real+positive for baryons with Q ≥ 0 |
| **proton_winding_eq_Nc_times_Q** | BraidAtlas.CompositeTriples | W(u)+W(u)+W(d) = 3 = N_c·Q(proton) |
| **neutron_winding_eq_Nc_times_Q** | BraidAtlas.CompositeTriples | W(u)+W(d)+W(d) = 0 = N_c·Q(neutron) |
| **confinement_mersenne_level** | BraidAtlas.CompositeTriples | 15 = 2^4−1 (lowest composite Mersenne level) |
| **proton_neutron_c_eq_15_in_confinement_tier** | BraidAtlas.CompositeTriples | 15 < 1023 (proton/neutron in tier 1) |
| **ugp_composite_braid_c_rule** | BraidAtlas.CompositeTriples | Full composite c-rule conjunction (zero sorry) |

### a-component (min-rule) and b-component (Wolfram Alpha breakthrough)

The Wolfram Alpha representation 11459 = 5 × 2^8 × 3^2 − 61 exposes the
structural law b(proton) = N_c²·(a_u·2^{N_c²−1} − δ) + (N_c−1), where every
factor is a Lean-certified UGP constant. The correction 61 has TWO independent
derivations: `b₁ − N_c(N_c+1) = 73 − 12 = 61` and `δ·N_c² − (N_c−1) = 7·9−2 = 61`.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **proton_a_eq_min** | BraidAtlas.CompositeTriples | min(5,5,9) = 5 (a-rule: min of constituents) |
| **neutron_a_eq_min** | BraidAtlas.CompositeTriples | min(5,9,9) = 5 |
| **proton_b_correction_from_lepton_seed** | BraidAtlas.CompositeTriples | 73 − N_c(N_c+1) = 61 |
| **proton_b_correction_from_delta** | BraidAtlas.CompositeTriples | δ·N_c² − (N_c−1) = 61 |
| **proton_b_correction_agreement** | BraidAtlas.CompositeTriples | Both paths equal 61 |
| **proton_b_formula** | BraidAtlas.CompositeTriples | N_c²·(a_u·2^{N_c²−1}−δ)+(N_c−1) = 11459 |
| **neutron_b_formula** | BraidAtlas.CompositeTriples | Same − 2N_c² = 11441 |
| **proton_neutron_b_diff** | BraidAtlas.CompositeTriples | 11459 − 11441 = 2N_c² = 18 |
| **ugp_nucleon_b_formula** | BraidAtlas.CompositeTriples | Full (a,b,c) conjunction for p and n (zero sorry) |
| **sigma_plus_b_formula** | BraidAtlas.CompositeTriples | b(Σ+)=(b(s)+a_u×seesaw)×(…)=639161 |
| **strange_baryon_s1_b_eq_lambda** | BraidAtlas.CompositeTriples | |S|=1 sector b: Lambda=Sigma0=Sigma-=38236 |
| **strange_baryon_s2_b_eq_xi** | BraidAtlas.CompositeTriples | |S|=2 sector b: Xi0=Xi-=878434 |
| **ugp_all_baryon_b_formulas** | BraidAtlas.CompositeTriples | All 9 light baryon b-values (full conjunction, zero sorry) |

## Asymptotic Sparsity (P25)

Module `Phase4.AsymptoticSparsity` proves the Asymptotic Sparsity Theorem (P25 §4):

| Theorem | Module | Statement |
|---------|--------|-----------|
| **ridge_ge_8176** | Phase4.AsymptoticSparsity | ridge n ≥ 8176 for n ≥ 13 |
| **stage2_survivor_10** | Phase4.AsymptoticSparsity | (24,42) is Stage-1 survivor at n=10 with b₁=73 |
| **no_stage2_at_4..12** | Phase4.AsymptoticSparsity | For each n ∈ {4,5,6,7,8,9,11,12}, no element of ridgeSurvivorsFinset n has b₁=73 (native_decide) |
| **no_stage2_large_n** | Phase4.AsymptoticSparsity | For n ≥ 13, AM-GM → b₁ = b₂+q₂+7 ≥ 187 ≠ 73 (nlinarith over ℤ) |
| **asymptotic_sparsity_universal** | Phase4.AsymptoticSparsity | **For ALL n : ℕ**, (n=10,b₁=73) is the UNIQUE Stage-2 survivor. Single ∀n theorem combining finite check + AM-GM + trivial small-n case. |
| **no_survivor_small_n** | Phase4.AsymptoticSparsity | For n < 4, isMirrorDualSurvivorAt is False (ridge n = 0, no valid pairs) |

## Positive Root Theorem (P25)

Module `Phase4.PositiveRootTheorem` proves T6 (P25 §5):

| Theorem | Module | Statement |
|---------|--------|-----------|
| **g1_num_val** | Phase4.PositiveRootTheorem | g₁² numerator = 16 (native_decide) |
| **g2_num_val** | Phase4.PositiveRootTheorem | g₂² numerator = 2329 (native_decide) |
| **g3_num_val** | Phase4.PositiveRootTheorem | g₃² numerator = 41075281 (native_decide) |
| **g2_factor** | Phase4.PositiveRootTheorem | 2329 = 17 × 137 (norm_num) |
| **g3_perfect_sq** | Phase4.PositiveRootTheorem | 41075281 = (13×17×29)² (norm_num) |
| **su14,su18,su30** | Phase4.PositiveRootTheorem | c(SU(14)₁)=13, c(SU(18)₁)=17, c(SU(30)₁)=29 |
| **positive_root_theorem** | Phase4.PositiveRootTheorem | SU(N)₁ factor count in numerator(g²_G) = |Φ⁺(G)| for all G |
| **prime_29_cross_sector** | Phase4.PositiveRootTheorem | 4·N_c²−δ = 29 = c(SU(30)₁): same integer in seesaw and gauge sectors |

## Galois Layer Stability (P25)

Module `GaloisStructure.CyclotomicLayers` proves the Galois Stability Theorem (P25 §7):

| Theorem | Module | Statement |
|---------|--------|-----------|
| **two_cos_pi12_sq** | GaloisStructure.CyclotomicLayers | (2·cos(π/12))² = 2 + √3 |
| **two_cos_pi10_sq** | GaloisStructure.CyclotomicLayers | (2·cos(π/10))² = 2 + φ |
| **p10_at_cos_pi12** | GaloisStructure.CyclotomicLayers | p₁₀(2cos(π/12)) = 2−√3 exactly |
| **p12_at_cos_pi10** | GaloisStructure.CyclotomicLayers | p₁₂(2cos(π/10)) = φ−2 exactly |
| **two_minus_sqrt3_ne_zero** | GaloisStructure.CyclotomicLayers | 2−√3 ≠ 0 |
| **goldenRatio_minus_two_ne_zero** | GaloisStructure.CyclotomicLayers | φ−2 ≠ 0 |
| **galois_layer_stability** | GaloisStructure.CyclotomicLayers | p₁₀(2cos(π/12))≠0 ∧ p₁₂(2cos(π/10))≠0: layers in different Galois orbits |
| **galois_cross_eval_values** | GaloisStructure.CyclotomicLayers | Exact evaluation values (2−√3, φ−2) |
| **strand_count_eq_two** | GaloisStructure.CyclotomicLayers | (N_c²−1)/4 = 2 = strand_count |

## Minimal Cyclotomic Field + Fibonacci-Ridge Structure (P25)

Module `GaloisStructure.MinimalCyclotomic` formalises the minimal cyclotomic
conductor and the Fibonacci-ridge structural identities:

| Theorem | Module | Statement |
|---------|--------|-----------|
| **c2_mersenne_exponent** | GaloisStructure.MinimalCyclotomic | 1023 = 2^(2*F(5)) - 1: n_ridge is the c₂ Mersenne exponent |
| **mersenne_ladder_structure** | GaloisStructure.MinimalCyclotomic | {4,10,16} = {2F(3),2F(5),2F(6)}, step=2Nc (native_decide) |
| **n_ridge_structural_position** | GaloisStructure.MinimalCyclotomic | 10 = 2F(5) = (4+16)/2; F(6)-F(5)=F(4)=Nc; Nc^2-1=F(6) |
| **lcm_20_24_eq_120** | GaloisStructure.MinimalCyclotomic | LCM(20,24) = 120 (minimal cyclotomic conductor) |
| **lcm_minimality** | GaloisStructure.MinimalCyclotomic | ∀ N, 20\|N ∧ 24\|N → 120\|N |
| **prime_set_120_matches_gauge** | GaloisStructure.MinimalCyclotomic | {2,3,5} prime set shared by 120 and gauge denominators |
| **prime_137_bitset** | GaloisStructure.MinimalCyclotomic | 137 = 2^0 + 2^3 + 2^7 (bit-set {0, Nc, delta}) |
| **delta_from_Nc** | GaloisStructure.MinimalCyclotomic | delta = 7 = Nc + (Nc^2-1)/2, derived from Nc=3 |
| **prime_137_from_Nc** | GaloisStructure.MinimalCyclotomic | 137 = 2^Nc * (2Nc^2-1) + 1 (structural formula) |
| **prime_137_structural_origin** | GaloisStructure.MinimalCyclotomic | 137 is the bit-set prime {0,Nc,delta} fully determined by Nc=3 (closes P25 §10.2) |

## Unconditional Rigidity

### b1=73 Forced at n=10 + δ_target as Structural Prediction

| Theorem | Module | Statement |
|---------|--------|-----------|
| **b1_unique_at_n10** | Phase4.AsymptoticSparsity | ∀ survivors at n=10: b2+q2+7=73 (both pairs give 73, native_decide) |
| **b1_forced_eq_73** | Phase4.AsymptoticSparsity | isMirrorDualSurvivorAt 10 b2 q2 → b2+q2+7=73 |
| **delta_structural_prediction** *(def)* | Phase4.DeltaUGP | b1=73 arithmetically forced → δ_structural = C_alg/73 is a structural prediction |
| **b1_in_delta_is_sieve_forced** | Phase4.DeltaUGP | leptonB = 73 (certified, supports prediction interpretation) |

### VV All Coefficients from N_c = 3 — Module MassRelations.VVAllCoefficientsFromNc

| Theorem | Module | Statement |
|---------|--------|-----------|
| **dim_45_su_Nc_plus_2** | MassRelations.VVAllCoefficientsFromNc | 45 = (Nc+2)(2Nc+3) for Nc=3 (norm_num) |
| **dim_126_so_2Nc_plus_4** | MassRelations.VVAllCoefficientsFromNc | 126 = C(2(Nc+2),Nc+2)/2 for Nc=3 (native_decide) |
| **vv_gamma_from_Nc** | MassRelations.VVAllCoefficientsFromNc | γ_d = -5/14 = -(Nc+2)(2Nc+3)/[C(2Nc+4,Nc+2)/2] (norm_num) |
| **vv_all_coefficients_from_Nc** | MassRelations.VVAllCoefficientsFromNc | All 3 VV exponents (13/9, -7/6, -5/14) from Nc=3 alone (zero sorry) |

## VV Mechanism (P25)

Module `MassRelations.VVMechanism` formalises the VV mass mechanism as a
log-linear law derived from the SU(5)/SO(10) GUT power law:

| Theorem | Module | Statement |
|---------|--------|-----------|
| **vv_exponents** | MassRelations.VVMechanism | (13/9)=1+4/9, (-7/6)=-(1+1/6), (-5/14)=-45/126: group-theory identities |
| **log_of_power_law** | MassRelations.VVMechanism | If f=C·u^α·l^β then log(f)=α·log(u)+β·log(l)+log(C) (pure algebra) |
| **vv_mechanism_algebraic** | MassRelations.VVMechanism | GUT power law + UCL log map → log-linear VV relation (zero sorry) |
| **dim_126_eq_two_Nc_sq_delta** | MassRelations.VVMechanism | 126 = 2·Nc²·δ (connects VV to seesaw structure) |

## Neutrino Froggatt-Nielsen Texture — Module MassRelations.NeutrinoFroggattNielsen

Module `MassRelations.NeutrinoFroggattNielsen` selects the structural FN
texture for the b^(29/9) seesaw exponent under UGP axiom A3 (Compression / MDL).

Setup: two-flavon U(1)_1 x U(1)_2 with M_R(g) ~ b_g^(q1 + q2/Nc^2).
The b^(29/9) law requires q1 + q2/Nc^2 = 29/9; at Nc=3 this admits
exactly four non-negative integer solutions in [0,6] x [0,30]:
{(0,29), (1,20), (2,11), (3,2)}.

A charge is "singleton-atomic in Nc" if it equals one of
{Nc, Nc-1, Nc+1, Nc^2, Nc^2-1, strand=(Nc^2-1)/4}.
Pair singleton-atomic = both components singleton-atomic.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **fnEqAtNc3** *(def)* | MassRelations.NeutrinoFroggattNielsen | FN charge equation 9 q1 + q2 = 29 (the form of q1 + q2/Nc^2 = 29/9 at Nc=3) |
| **fn_solutions_satisfy_eq** | MassRelations.NeutrinoFroggattNielsen | Each pair in {(0,29),(1,20),(2,11),(3,2)} satisfies the equation |
| **fn_solutions_are_complete** | MassRelations.NeutrinoFroggattNielsen | Every non-negative integer solution with q1<=6, q2<=30 is in the list (interval_cases + omega + decide) |
| **texture_3_2_is_singleton_atomic** | MassRelations.NeutrinoFroggattNielsen | (3, 2) has both charges singleton-atomic |
| **texture_0_29_not_singleton_atomic** | MassRelations.NeutrinoFroggattNielsen | (0, 29) lacks singleton-atomic charge q2 = 29 |
| **texture_1_20_not_singleton_atomic** | MassRelations.NeutrinoFroggattNielsen | (1, 20) lacks singleton-atomic charge q2 = 20 |
| **texture_2_11_not_singleton_atomic** | MassRelations.NeutrinoFroggattNielsen | (2, 11) lacks singleton-atomic charge q2 = 11 |
| **fn_texture_3_2_is_unique_singleton_atomic** | MassRelations.NeutrinoFroggattNielsen | Among the four FN solutions, exactly (q1, q2) = (3, 2) is singleton-atomic |
| **fn_structural_texture_existence_and_uniqueness** | MassRelations.NeutrinoFroggattNielsen | Bundled exists-unique form |

This converts the FN texture choice from aesthetic preference to a
Lean-certified MDL theorem: among the four arithmetic solutions, only
(q1, q2) = (Nc, strand) = (3, 2) has both charges as elementary UGP atoms.

## Galois-Protection Non-Renormalization — Module Phase4.GaloisProtection

Module `Phase4.GaloisProtection` formalises the Galois-protection one-loop cancellation theorem.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **c_alg_nonzero_shift** | Phase4.GaloisProtection | If A ≠ 0 and t ≠ 0, then C + A*t ≠ C (linarith + mul_eq_zero) |
| **galois_protection_coefficient_forced_zero** | Phase4.GaloisProtection | If C + A*t = C and A ≠ 0 then t = 0 (linarith + mul_eq_zero) |
| **T_Tdagger_cancellation** | Phase4.GaloisProtection | L + (-L) = 0 (linarith) |
| **L_zero_from_T_Tdagger** | Phase4.GaloisProtection | If L = -L then L = 0 (linarith) |
| **delta_C_vanishes_from_T_Tdagger** | Phase4.GaloisProtection | C + A*(L with L=-L) = C (rw mul_zero) |
| **one_loop_correction_zero** | Phase4.GaloisProtection | A*L = 0 under T/T† pairing (rw mul_zero) |
| **residual_is_positive** | Phase4.GaloisProtection | The 2.39 ppm residual is positive (norm_num) |
| **residual_below_one_loop_scale** | Phase4.GaloisProtection | 2.39 ppm < alpha/pi (norm_num bound) |
| **galois_protection_master_theorem** | Phase4.GaloisProtection | Master: C + A*L = C under A≠0 and T/T† pairing (zero sorry) |

The physical content: C_alg ∈ Q(sqrt(5)) ⊂ Q(zeta_120); A ≠ 0; the loop
transcendental L = sum n_i log(m_i/mu) ∉ Q(sqrt(5)) (Baker's theorem); Galois
constraint forces A*L = 0; T/T† dual-operator pairing implements L = -L → L = 0.
Residual R_real = 2.39 ppm = 0.886 × alpha^2/(2*pi^2) is at two-loop magnitude.

## Two-Loop Color Coefficient — Module Phase4.TwoLoopCoefficient

Module `Phase4.TwoLoopCoefficient` certifies the structural identification of
the two-loop coefficient in the UGP precision residual.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **C2_fund_at_Nc3** | Phase4.TwoLoopCoefficient | C2(SU(3),fund) = (9-1)/(2×3) = 4/3 (norm_num) |
| **two_loop_coeff_eq_Nc_ratio** | Phase4.TwoLoopCoefficient | C2×2/Nc = (Nc²-1)/Nc² (field_simp + ring) |
| **two_loop_coefficient_eq_8_over_9** | Phase4.TwoLoopCoefficient | At Nc=3: coefficient = 8/9 (norm_num) |
| **gluon_count_eq_Nc_sq_minus_1** | Phase4.TwoLoopCoefficient | 3²-1 = 8 = gluon count (norm_num) |
| **two_loop_coeff_between_zero_and_one** | Phase4.TwoLoopCoefficient | 0 < 8/9 < 1 (norm_num) |
| **o3_full_identification** | Phase4.TwoLoopCoefficient | Bundled: C2=4/3, coeff=8/9, bounds (zero sorry) |

Physical identification: R_real = [(Nc²-1)/Nc²] × α_EM²/(2π²) = (8/9) × α_EM²/(2π²).
The (Nc²-1) = 8 = dim(su(3)_adj) is the gluon count; the coefficient arises
from symmetric T/T†-two-loop diagrams (one-loop cancels by GaloisProtection).
Verified numerically at 0.33% (within double-precision accuracy of b1_required chain).

## RCC Infinite Families — Module PSC.RCCInfiniteFamilies

Module `PSC.RCCInfiniteFamilies` closes RCC over all four
infinite classical Lie families: B_n, C_n, D_n, A_n.

Key fact: For B_n = SO(2n+1) and C_n = Sp(2n), the longest Weyl element acts
as negation (w0 = -id). Therefore -w0(lam) = lam for every dominant weight lam,
so every irrep is self-dual (real or pseudoreal, never complex). No chiral
fermions possible -> PSC Layer I fail for ALL n.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **bn_all_irreps_self_dual** | PSC.RCCInfiniteFamilies | For all n, all B_n dominant weights: -(w0 lam) = lam (funext + simp) |
| **cn_all_irreps_self_dual** | PSC.RCCInfiniteFamilies | Same for C_n = Sp(2n) (identical Weyl group) |
| **bn_cn_no_complex_reps_all_n** | PSC.RCCInfiniteFamilies | Bundled: all B_n and C_n irreps self-dual for all n (zero sorry) |
| **dn_even_all_irreps_self_dual** | PSC.RCCInfiniteFamilies | D_n even: -id in W(D_n) since even many sign changes -> all irreps self-dual |
| **dn_odd_spinorDim_exceeds_threshold** | PSC.RCCInfiniteFamilies | D_n odd, n>=5: spinorDim n = 2^(n-1) >= 16 (Nat.pow_le_pow_right) |
| **spinorDim_doubles** | PSC.RCCInfiniteFamilies | spinorDim(n+1) = 2 * spinorDim(n) for n>=1 (ring) |
| **an_adjDim_ge_15** | PSC.RCCInfiniteFamilies | A_n, n>=3: anAdjDim n = (n+1)^2-1 >= 15 (nlinarith) |
| **an_adjDim_strictly_grows** | PSC.RCCInfiniteFamilies | anAdjDim is strictly increasing for n>=1 (zify + nlinarith) |
| **dissonanceLB_exceeds_one** | PSC.RCCInfiniteFamilies | dim/12 > 1 when dim >= 13 (linarith over Q) |
| **an_dissonanceLB_exceeds_one** | PSC.RCCInfiniteFamilies | A_n (n>=3): D_lb > 1 (Layer II fail) |
| **dn_odd_dissonanceLB_exceeds_one** | PSC.RCCInfiniteFamilies | D_n odd (n>=5): D_lb > 1 (Layer II fail) |
| **rcc_all_classical_families** | PSC.RCCInfiniteFamilies | Master theorem: all 5 cases (B_n, C_n, D_n even, D_n odd n>=5, A_n n>=3) |

Combined with TE22.ScanCertificate (computational, 34,560 universes) and the
extended scan certificate (exceptional Lie groups + larger classical shells), RCC is
established as a theorem over ALL compact simple Lie groups.

## Coxeter–Conductor Theorem — Modules BraidAtlas.CoxeterConductor & CoxeterConductorTowerLaw

Modules `BraidAtlas.CoxeterConductor` and `BraidAtlas.CoxeterConductorTowerLaw`
formalise the arithmetic core of the Coxeter–conductor theorem: the affine Toda
mass spectrum of a simple Lie algebra G lies in Q(ζ₁₂₀) iff its Coxeter number
h(G) divides 120, and prove the **E7 falsifier** via the Tower Law obstruction.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **phi_120** | BraidAtlas.CoxeterConductor | Euler totient φ(120) = 32 = [Q(ζ₁₂₀):Q] (native_decide) |
| **phi_18** | BraidAtlas.CoxeterConductor | Euler totient φ(18) = 6 = [Q(ζ₁₈):Q] (native_decide) |
| **q_zeta18_real_degree** | BraidAtlas.CoxeterConductor | [Q(ζ₁₈)⁺ : Q] = φ(18)/2 = 3 (native_decide) |
| **three_not_dvd_32** | BraidAtlas.CoxeterConductor | 3 ∤ 32 (key Tower Law obstruction, norm_num) |
| **e8_coxeter_dvd, e6_coxeter_dvd, f4_coxeter_dvd, g2_coxeter_dvd, b4_coxeter_dvd** | BraidAtlas.CoxeterConductor | Coxeter numbers of E8 (30), E6/F4 (12), G2 (6), B4 (8) all divide 120 (norm_num) |
| **e7_coxeter_not_dvd** | BraidAtlas.CoxeterConductor | **KEY FALSIFIER**: E7 Coxeter number 18 ∤ 120 (norm_num) |
| **nine_dvd_18_not_120** | BraidAtlas.CoxeterConductor | Root cause: 9 \| 18 but 9 ∤ 120 (norm_num) |
| **full_lcm_all_coxeter** | BraidAtlas.CoxeterConductor | lcm(30, 12, 8, 6, 3, 2, 1) = 120 (native_decide) |
| **min_poly_cos_pi9_no_rational_roots** | BraidAtlas.CoxeterConductor | 8X³−6X−1 has no rational roots (8 candidate checks via rcases + norm_num) |
| **e7_coxeter_conductor_obstruction** | BraidAtlas.CoxeterConductor | Composite arithmetic obstruction (zero sorry) |
| **positive_coxeter_conductor** | BraidAtlas.CoxeterConductor | Composite Q(ζ₁₂₀) containment for E8/E6/F4/G2/B4 (zero sorry) |
| **p_int_natDegree** | BraidAtlas.CoxeterConductorTowerLaw | natDegree of 8X³−6X−1 over ℤ = 3 (compute_degree!) |
| **p_rat_natDegree** | BraidAtlas.CoxeterConductorTowerLaw | natDegree over ℚ = 3 (natDegree_map_of_leadingCoeff_ne_zero) |
| **p_rat_no_roots** | BraidAtlas.CoxeterConductorTowerLaw | No rational root via num/den_dvd_of_is_root + 8 candidate checks |
| **p_rat_irreducible** | BraidAtlas.CoxeterConductorTowerLaw | Irreducible over ℚ (irreducible_of_degree_le_three_of_not_isRoot) |
| **p_rat_q_natDegree** | BraidAtlas.CoxeterConductorTowerLaw | Quotient-form polynomial natDegree = 3 (compute_degree!) |
| **finrank_p_rat_quot** | BraidAtlas.CoxeterConductorTowerLaw | [ℚ[X]/(8X³−6X−1) : ℚ] = 3 (zero sorry) |
| **tower_obstruction** | BraidAtlas.CoxeterConductorTowerLaw | ∀ k:ℕ, 3·k ≠ 32 (arithmetic Tower Law obstruction) |
| **e7_arithmetic_evidence** | BraidAtlas.CoxeterConductorTowerLaw | Composite: irreducibility + degree + φ(120) = 32 + 3∤32 |
| **e7_tower_law_complete** | BraidAtlas.CoxeterConductorTowerLaw | Complete Tower Law theorem (zero sorry, all five components) |

The Tower Law step uses `finrank_quotient_span_eq_natDegree` on the quotient
ring `ℚ[X] ⧸ Ideal.span {p_rat_q}`, bypassing the `AdjoinRoot`-instance
synthesis obstruction (Mathlib `AdjoinRoot` is `def` not `abbrev`).

## Electroweak Boson c-Values — Module BraidAtlas.EWBosons

Module `BraidAtlas.EWBosons` derives the EW massive boson c-values
{c(W), c(Z), c(H)} = {11, 12, 13} from two structural identities at the canonical
ridge level n = 10, closing the last Category B item in the Braid Atlas (P17).

| Theorem | Module | Statement |
|---------|--------|-----------|
| **ridge_10_canonical_factorisation** | BraidAtlas.EWBosons | 42 × 24 = 1008 = R₁₀ (canonical factorisation, native_decide) |
| **ridge_10_mirror_factorisation** | BraidAtlas.EWBosons | 24 × 42 = 1008 = R₁₀ (mirror factorisation, native_decide) |
| **q₂_canonical_eq_2NcNcPlus1** | BraidAtlas.EWBosons | **Structural Identity I**: q₂(canonical) = 2·N_c·(N_c+1) = 24 |
| **b₂_canonical_eq_2Nc2NcPlus1** | BraidAtlas.EWBosons | b₂(canonical) = 2·N_c·(2N_c+1) = 42 |
| **ridge_10_in_Nc** | BraidAtlas.EWBosons | R₁₀ = 4·N_c²·(N_c+1)·(2N_c+1) |
| **ugp1_g_eq_NcNcPlus1_plus_1** | BraidAtlas.EWBosons | **Structural Identity II**: ugp1_g = N_c·(N_c+1) + 1 = 13 |
| **c_W_eq_11, c_Z_eq_12, c_H_eq_13** | BraidAtlas.EWBosons | Numerical c-values (native_decide) |
| **ew_c_values** | BraidAtlas.EWBosons | Composite: {c(W), c(Z), c(H)} = {11, 12, 13} |
| **c_W_eq_NcNcPlus1_minus_1** | BraidAtlas.EWBosons | c(W) = N_c·(N_c+1) − 1 (structural form) |
| **c_Z_eq_NcNcPlus1** | BraidAtlas.EWBosons | c(Z) = N_c·(N_c+1) (structural form) |
| **c_H_eq_NcNcPlus1_plus_1** | BraidAtlas.EWBosons | c(H) = N_c·(N_c+1) + 1 (structural form) |
| **ew_c_consecutive_window** | BraidAtlas.EWBosons | **Main result**: c(Z) = c(W)+1, c(H) = c(Z)+1 (consecutive triple) |
| **ew_c_set_in_Nc_form** | BraidAtlas.EWBosons | {c(W), c(Z), c(H)} = {N_c(N_c+1)−1, N_c(N_c+1), N_c(N_c+1)+1} |
| **ew_c_primality** | BraidAtlas.EWBosons | c(W)=11 prime ∧ c(Z)=12 not prime ∧ c(H)=13 prime |
| **c_W_eq_q1_canonical** | BraidAtlas.EWBosons | c(W) = q₁(canonical) (cross-domain identification) |
| **c_H_eq_q2_minus_q1** | BraidAtlas.EWBosons | c(H) = q₂ − q₁ (orbital symmetry-breaking gap) |
| **ew_boson_c_value_theorem** | BraidAtlas.EWBosons | Composite: 10 facts including consecutive window + structural identities |
| **orbitalConstants_n10_explicit** | BraidAtlas.EWBosons | Orbital constants at n=10 = {7, 11, 12, 13, 20, 22, 24, 35} (decide) |
| **unique_consecutive3_in_orbital** | BraidAtlas.EWBosons | **Uniqueness**: {11, 12, 13} is the unique consecutive triple drawn from orbital constants (omega) |
| **ew_c_window_unique** | BraidAtlas.EWBosons | MDL-uniqueness corollary: composite proof of EW c-window |
| **triangular_Nc** | BraidAtlas.EWBosons | T(N_c) = N_c·(N_c+1)/2 = 6 at N_c=3 (native_decide) |
| **q₂_canonical_eq_4T** | BraidAtlas.EWBosons | q₂(canonical) = 4·T(N_c) (triangular form) |
| **ugp1_g_eq_2T_plus_1** | BraidAtlas.EWBosons | ugp1_g = 2·T(N_c) + 1 (triangular form) |
| **ew_c_centered_on_2T** | BraidAtlas.EWBosons | EW c-window is centred on 2·T(N_c) |
| **ew_triangular_unification** | BraidAtlas.EWBosons | **Deepest derivation**: composite triangular-number unification (zero sorry) |
| **ew_ugp_axiom_derivation** | BraidAtlas.EWBosons | Composite derivation chain from UGP axioms |

This closes the EW boson c-values as Category A: derived from \ugp{} axioms
(asymptotic sparsity → n=10; anomaly cancellation → N_c=3; RSUC → unique fixed
point), not postulated.

## E8 Cyclotomic Divisibility & Mirror Triple — Module GTE.GeneralTheorems

Theorems in `GTE.GeneralTheorems` certify the algebraic foundation
of P24 §7.4 (E8 in Q(ζ₁₂₀)) and the Lean-certified arithmetic backbone of
P02/P17 GTE-P7 mirror dark matter quantum numbers.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **e8_m2_golden_ratio_poly_nat** | GTE.GeneralTheorems | x²−x−1 has integer coefficients summing to 3 (golden-ratio polynomial) |
| **e8_m3_poly_integer_check** | GTE.GeneralTheorems | Degree-8 minimal polynomial of 2cos(π/30) has |coeff| sum = 31 |
| **e8_cyclotomic_divisibility** | GTE.GeneralTheorems | 120 % 10 = 0 ∧ 120 % 60 = 0 (E8 mass ratios containment chain) |
| **e8_all_masses_divisibility** | GTE.GeneralTheorems | 120 % {5, 6, 10, 12, 15, 30, 60} = 0 (all 8 E8 masses in Q(ζ₁₂₀)) |
| **mirror_triple_residue** | GTE.GeneralTheorems | gteRemainder 2137 73 = 20 (mirror prime-lock residue) |
| **mirror_prime_2137** | GTE.GeneralTheorems | 2137 is prime (Lean-certified via native_decide) |
| **mirror_quotient_q1** | GTE.GeneralTheorems | gteQuotient 2137 73 = 29 (mirror q₁) |
| **mirror_triple_prime_lock** | GTE.GeneralTheorems | 73 × 29 + 20 = 2137 (prime-lock arithmetic) |

## Refined Charge Theorem — Module BraidAtlas.ChargeTheorem

Module `BraidAtlas.ChargeTheorem` provides paper-citation aliases for the
GTE-P7 (mirror dark matter) quantum-number derivation.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **sm_charge_leptons** | BraidAtlas.ChargeTheorem | Q = W_g/N_c for leptons and neutrinos (alias bundling charge_from_winding_Nc3 for the colour-singlet sector) |
| **sm_quarks_fractional_charge** | BraidAtlas.ChargeTheorem | Q = W_g/N_c gives fractional charges for up- and down-quarks (3 ∤ 2, 3 ∤ −1) |
| **nc_eq_3_from_fractional_charge** | BraidAtlas.ChargeTheorem | Anomaly cancellation forces N_c = 3 (corollary of anomaly_cancellation_forces_Nc_3) |
| **gmn_color_singlet_neutral** | BraidAtlas.ChargeTheorem | Gell-Mann–Nishijima: T₃=0 ∧ Y=0 → Q = T₃ + Y/2 = 0 (algebraic step for GTE-P7) |
| **mirror_winding_number_zero** | BraidAtlas.ChargeTheorem | **Axiom**: W_g_mirror = 0 (justified by P17 braid topology, faithfully tracked in PROVENANCE) |
| **gte_p7_electric_charge_zero** | BraidAtlas.ChargeTheorem | Q_GTE-P7 = W_g_mirror / N_c = 0 (formal derivation from mirror_winding_number_zero) |
| **gte_p7_quantum_numbers_neutral** | BraidAtlas.ChargeTheorem | Composite: GTE-P7 is electrically neutral, color singlet, sterile (zero sorry beyond the disclosed axiom) |

## CKM θ_23 Structural Ratio — Module MassRelations.CKMTheta23

Module `MassRelations.CKMTheta23` certifies that the specific ratio
τ(R_10)/D_1 = 15/8 appearing in the CKM θ_23 scaling is structurally
forced by UGP (P01 OP(v)). The ridge `R_n = 2^n − 16` admits the structural
Mersenne factorization `R_n = D_1 · M_(n−4)` for `n ≥ 4`, where `D_1 = 16`
is the U(1) discrete invariant and `M_k = 2^k − 1`. At `n = 10` this gives
`τ(R_10)/D_1 = 30/16 = 15/8`, and the ratio is unique to `n = 10` across
the canonical UGP search range `n ∈ [5, 20]`. All theorems zero sorry, zero axioms.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **ridge_eq_D1_mul_mersenne** | MassRelations.CKMTheta23 | For all n ≥ 4: ridge n = D_1 · (2^(n−4) − 1) (master Mersenne factorization) |
| **ridge_10_eq_D1_mul_M6** | MassRelations.CKMTheta23 | At n = 10: ridge 10 = D_1 · (2^6 − 1) (specialization) |
| **D1_mul_M6_eq_1008** | MassRelations.CKMTheta23 | D_1 · (2^6 − 1) = 16 · 63 = 1008 (concrete arithmetic, native_decide) |
| **tau_1008** | MassRelations.CKMTheta23 | τ(1008) = 30 (divisor count, native_decide) |
| **tau_ridge_10** | MassRelations.CKMTheta23 | τ(ridge 10) = 30 (corollary of ridge_10 + tau_1008) |
| **ckm_theta23_ratio_at_n10** | MassRelations.CKMTheta23 | τ(ridge 10) / D_1 = 15/8 in ℚ (OP(v) closed-form ratio) |
| **tau_ridge_ne_30_off_n10** | MassRelations.CKMTheta23 | ∀ n ∈ [5,20], n ≠ 10: τ(ridge n) ≠ 30 (interval_cases + native_decide) |
| **ckm_theta23_ratio_uniqueness** | MassRelations.CKMTheta23 | ∀ n ∈ [5,20], n ≠ 10: τ(ridge n) / D_1 ≠ 15/8 (uniqueness) |
| **op_v_ckm_theta23_closure** | MassRelations.CKMTheta23 | **Bundled OP(v) closure certificate**: ridge 10 = D_1·M_6 ∧ τ(ridge 10) = 30 ∧ ratio = 15/8 ∧ uniqueness across [5,20] (zero sorry) |

> **OP(v) closure narrative**: The Lean certificate decomposes the CKM θ_23
> ratio into structural pieces — the ridge factorization `R_n = D_1 · M_(n−4)`
> exposes the U(1) invariant as a separate factor; the divisor count
> `τ(M_6) = τ(63) = τ(3²·7) = 6` then gives `τ(R_10) = 5·τ(M_6) = 30` and
> `τ(R_10)/D_1 = 30/16 = 15/8`. Combined with the UGP forcing of `n = 10`
> as the unique canonical ridge level (via
> `kprime_is_minimal_double_fib_above_n` in the GTE layer), the CKM θ_23
> scaling ratio is structurally derived from UGP, not data-matched.

## Koide S₃ Discrete Arithmetic-Mean Identity — Module MassRelations.KoideS3DiscreteIdentities

Module `MassRelations.KoideS3DiscreteIdentities` certifies the discrete
shadow of the S₃ equal-norm Koide condition for the GTE lepton orbit's
a-component, contributing to the partial closure of P01 OP(vii). Where
the continuous S₃ equal-norm identity `|v_1|² = |v_2|² = 3` (see
`koide_equal_norm` in `MassRelations.KoideAngle`) holds for every value of
the Koide phase θ, the discrete identity holds exactly on the canonical
Lean-certified orbit a-component sequence (1, 9, 5). Independent of N_c,
of θ = 2/9, and of absolute normalisation. All theorems zero sorry, zero
hypotheses.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **lepton_a_arithmetic_mean** | MassRelations.KoideS3DiscreteIdentities | **Discrete S₃ identity**: 2 · canonicalGen3.a = LeptonSeed.a + canonicalGen2.a (i.e., 2·5 = 1+9 = 10) |
| **lepton_a_tau_is_average** | MassRelations.KoideS3DiscreteIdentities | Equivalent form: canonicalGen3.a · 2 = LeptonSeed.a + canonicalGen2.a |
| **lepton_a_values** | MassRelations.KoideS3DiscreteIdentities | Canonical lepton a-values: LeptonSeed.a = 1 ∧ canonicalGen2.a = 9 ∧ canonicalGen3.a = 5 |
| **lepton_a_sum_eq_ten** | MassRelations.KoideS3DiscreteIdentities | LeptonSeed.a + canonicalGen2.a = 10 |
| **two_tau_a_eq_ten** | MassRelations.KoideS3DiscreteIdentities | 2 · canonicalGen3.a = 10 |
| **lepton_a_arithmetic_mean_explicit** | MassRelations.KoideS3DiscreteIdentities | Explicit numerical form: 2 · 5 = 1 + 9 (decide) |
| **lepton_a_discrete_S3_identity** | MassRelations.KoideS3DiscreteIdentities | **Bundled certificate**: a-values (1,9,5) ∧ sum = 10 ∧ arithmetic-mean identity (zero sorry) |

> **OP(vii) partial-closure narrative**: Together with
> `koide_angle_from_N_c_pure` (which derives θ = 2/9 from N_c = 3 in
> `MassRelations.KoideAngle`), this module supplies the structural-results
> pair on which the partial closure of OP(vii) (Koide S₃ quadric forcing)
> rests in P01. The discrete arithmetic-mean identity is certified here;
> the remaining refined targets (PDG-θ alignment to 7.4×10⁻⁶ rad,
> Koide-cone near-attractor of UCL within 6×10⁻⁴) involve PDG real-valued
> masses and continuous geometric arguments and remain open for full
> OP(vii) closure.

## PSC Three-Route Forcing Capstone — Module PSC.ThreeRouteForcing

Module `PSC.ThreeRouteForcing` records the architectural shape of the
residual P01 OP(i) target as a parametric Lean carrier:

> *Any closed self-referential physical theory satisfying*
> *(i) Gödel–Turing self-reference closure,*
> *(ii) the Reflexive Landauer Bound, and*
> *(iii) the Norfleet holonomy defect δ = Λ − π/12 ≠ 0,*
> *is uniquely characterised by the PSC axiom set (RC, NM\*, TV, SA, PI).*

The substantive content of each route — and the
`PSC ⇔ NEMS + ER + visibility` decomposition — lives upstream in the
`nems-lean` companion library and the MFRR programme (NEMS Papers 02, 03,
05, 08, 14, 23, 51, 56, 88, MFRR Survey, Norfleet 2025). This module
deliberately does **not** re-derive any NEMS theorem and does **not**
define any of `(G, L, N, PSC)` as `True` (which would yield a fake
reflexivity-based proof and constitute smuggling). All four are left as
`Prop` parameters discharged upstream.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **ThreeRouteBundle** *(structure)* | PSC.ThreeRouteForcing | Prop-valued carrier `(G L N : Prop) → Prop` packaging the three forcing routes (Gödel–Turing, Reflexive Landauer, Norfleet) as a single hypothesis |
| **bundle_intro** | PSC.ThreeRouteForcing | From three independent route witnesses, build the bundle: G → L → N → ThreeRouteBundle G L N |
| **bundle_elim** | PSC.ThreeRouteForcing | The bundle entails each of its routes: ThreeRouteBundle G L N → G ∧ L ∧ N |
| **bundle_iff_and** | PSC.ThreeRouteForcing | Bundle ↔ conjunction: ThreeRouteBundle G L N ↔ G ∧ L ∧ N |
| **psc_three_route_capstone** | PSC.ThreeRouteForcing | **Conditional capstone (parametric, no smuggling)**: given upstream NEMS-supplied iff H : ThreeRouteBundle G L N ↔ PSC, conclude ThreeRouteBundle G L N ↔ PSC |
| **psc_three_route_capstone_conj** | PSC.ThreeRouteForcing | Unbundled-conjunction form: given the same H, conclude (G ∧ L ∧ N) ↔ PSC |

> **OP(i) partial-closure narrative**: P01 OP(i) (PSC-axiom deeper structural
> justification) is partially resolved via the NEMS programme through
> three convergent results: (a) axiom reduction (NM\* derives from
> PSC ⇒ RC ⇒ NM\* in `NemS.Physics.Rigidity`); (b) architectural
> equivalence (PSC = NEMS + ER + visibility, theorem-derived in
> `NemS.MFRR.PSCBundle`; PSC ⇔ BICS in NEMS Hub); (c) three independent
> forcing routes (Gödel–Turing logical, Reflexive Landauer energetic,
> Norfleet holonomy defect geometric, with the Foundational Finality
> theorem in NEMS 23 ruling out any external "deeper framework" route).
> A single Lean capstone fusing the three routes into a zero-axiom iff
> with the PSC axiom set remains the residual structural target; this
> module records the architectural shape pending the full upstream
> NEMS-Lean integration.

## External Citations (Not Formalized)

| ID | Claim | Source |
|----|-------|--------|
| C1 | Rule 110 Turing-universal | Cook (2004) |
| C2 | Continued-fraction Fibonacci lift | UGP Paper Updates |
| C3 | delta_UGP formula, b1=73 unique | JMP Math Foundations |
| C4 | g1^2, g2^2, g3^2 from invariants | JMP Math Foundations |
