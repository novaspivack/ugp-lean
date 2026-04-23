# ugp-lean: Theorem Catalog

What ugp-lean proves. All listed theorems have **0 sorry, 0 axioms** on the core path unless explicitly marked ⚠.

**Sorry audit (2026-04-20):** **only two** sorries remain in the codebase,
both openly disclosed with precise citations:
- `dickman_equidistribution_in_APs` and `crt_equidistribution_within_regime`
  in `GTE.AnalyticArchitecture` — classical analytic-NT results (Tenenbaum
  III.6); pending Mathlib analytic-NT infrastructure (Dickman function
  asymptotics).  These are research-level formalization gaps, not
  correctness defects.

**Prior integrity issues fixed 2026-04-18:**
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

## 13_SPEC Claim C — TT Formula = Weyl Bisector × Binary Cascade

All theorems zero sorry, zero hypotheses. Module: `MassRelations.ClaimCBridge`. Committed 2026-04-20.

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
Module: `ElegantKernel.Unconditional.KGenFullClosure` (§§1–9). Committed 2026-04-20.

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
| **only_survivors_n10** | StructuralTheorems | Prime-locked ridge survivors at n=10 are exactly {(24,42), (42,24)} |
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
| **UGPWall1Export** | DSIExport | Packaged export for DSI SmallSymmetricMVTBundle |

## External Citations (Not Formalized)

| ID | Claim | Source |
|----|-------|--------|
| C1 | Rule 110 Turing-universal | Cook (2004) |
| C2 | Continued-fraction Fibonacci lift | UGP Paper Updates |
| C3 | δ_UGP formula, b₁=73 unique | JMP Math Foundations |
| C4 | g₁²,g₂²,g₃² from invariants | JMP Math Foundations |
