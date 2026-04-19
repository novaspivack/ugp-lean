# ugp-lean: Theorem Catalog

What ugp-lean proves. All listed theorems have **0 sorry, 0 axioms** on the core path unless explicitly marked ⚠.

**Sorry audit (2026-04-18):** three documented sorries remain, all openly
disclosed with citations:
- `dickman_equidistribution_in_APs` and `crt_equidistribution_within_regime`
  in `GTE.AnalyticArchitecture` — classical analytic-NT results (Tenenbaum
  III.6); pending Mathlib analytic-NT infrastructure.
- `SM_is_D_minimizer_extended` in `TE22.ScanCertificate` — finite-enumeration
  claim pending `native_decide` over a `Fintype` instance on the universe
  description product type.

Prior integrity issue fixed 2026-04-18: the Tarski `fingerprint_fixed_point_exists`
statement on `Finset ℕ` with only monotonicity was **false** (counter-example
`F(P) = P ∪ {max(P)+1}`); restated on `Set ℕ` and proved via `OrderHom.lfp`;
bounded `Finset` variant `fingerprint_fixed_point_bounded` also added.

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
| **SM_is_D_minimizer_extended** (framework) | TE22.ScanCertificate | SM unique D-minimizer over 34,560 universes — sorry pending native_decide |

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

## Mass Relations (Round 12 + Rounds 13–18 research)

Charged-fermion mass-relation modules formalising the TT (up-to-lepton cyclotomic)
and VV (down-type rational) structural identities discovered 2026-04-19.
All theorems below are zero-sorry; axiom signatures = standard Mathlib
{propext, Classical.choice, Quot.sound} unless noted.  See ugp-physics
Lab Notes 11, 17, 18, 19, 20, 21, 22 for full dialectical derivation.

### TT — Up-Lepton Cyclotomic Identity (`UgpLean.MassRelations.UpLeptonCyclotomic`)

| Theorem | Module | Statement |
|---------|--------|-----------|
| **interGenerationIdentity_1_to_2** | UpLeptonCyclotomic | UpLeptonFormula 2 β − UpLeptonFormula 1 β = π/3 (β-free, by `ring`) |
| **interGenerationIdentity_2_to_3** | UpLeptonCyclotomic | UpLeptonFormula 3 β − UpLeptonFormula 2 β = 2π/3 (β-free, by `ring`) |
| **interGenerationIdentity_1_to_3** | UpLeptonCyclotomic | UpLeptonFormula 3 β − UpLeptonFormula 1 β = π (Gelfond, by `linarith`) |
| **alpha_equals_su3_weyl_bisector** | UpLeptonCyclotomic | su3WeylBisectorAngle = π/6 (`rfl`) |
| **beta_equals_pi_over_8** | UpLeptonCyclotomic | betaCandidate1 = π/8 (`rfl`) |

### VV — Down-Rational Mass Identity (`UgpLean.MassRelations.DownRational`)

| Theorem | Module | Statement |
|---------|--------|-----------|
| **gammaFreeIdentity_delta_1** | DownRational | γ-free formula across g=1 → g=2 (by `linarith`) |
| **combined_lepton_exponent_equals_5_18** | DownRational | 13/9 − 7/6 = 5/18 (by `norm_num`) |
| **combined_cyclotomic_coefficient** | DownRational | (13/9)·(π/6) = 13π/54 (by `ring`) |
| **combined_constant_139_630** | DownRational | (13/9)·(2/5) + (−5/14) = 139/630 (by `norm_num`) |

### Claim A — A_2 / SU(3) Cartan Geometry (`UgpLean.MassRelations.SU3FlavorCartan`) — Round 13 Phase 1

| Theorem | Module | Statement |
|---------|--------|-----------|
| **omega1_slope_eq_inv_sqrt_three** | SU3FlavorCartan | (√3/6) / (1/2) = (√3)⁻¹ (algebraic lemma) |
| **angle_alpha1_omega1_eq_pi_div_six** | SU3FlavorCartan | **Claim A:** angle between A_2 simple root α_1 and fundamental weight ω_1 = π/6 |
| **a2_weyl_chamber_half_opening** | SU3FlavorCartan | Half-opening angle of A_2 fundamental Weyl chamber = π/6 (alias of Claim A) |
| **omega1_in_weyl_chamber_interior** | SU3FlavorCartan | ω_1 lies strictly in the interior of the fundamental Weyl chamber (0 < π/6 < π/3) |

### Binary Phase Cascade — Claim B candidate (`UgpLean.MassRelations.BinaryCascade`) — Round 19

Constructive realisation of the "binary cascade of π/6 phase shifts" mechanism
preferred by MDL after Round 16's rule-out of compact-SU(3) character theory.
This module proves the **mathematical** equivalence of the cascade and TT;
**physical** realisation (which UV mechanism implements the cascade) is
flagged as Claim C, an open Round-19+ research question.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **cascade_increment** | BinaryCascade | cascadeState (g+1) − cascadeState g = 2^g · (π/6) (per-step increment doubles per generation) |
| **cascadeState_closed_form** | BinaryCascade | cascadeState g = (π/6)·2^g + π/8 (closed-form by induction) |
| **cascadeState_eq_TT** | BinaryCascade | **cascade reproduces TT exactly:** cascadeState g = UpLeptonFormula g (π/8) |
| **cascade_increment_doubles** | BinaryCascade | (g+2 − g+1) increment = 2 · (g+1 − g) increment (signature of 2^g structure) |
| **cascade_delta_1_to_2** | BinaryCascade | cascadeState 2 − cascadeState 1 = π/3 (β-free identity) |
| **cascade_delta_2_to_3** | BinaryCascade | cascadeState 3 − cascadeState 2 = 2π/3 (β-free identity) |
| **cascade_delta_1_to_3** | BinaryCascade | cascadeState 3 − cascadeState 1 = π (Gelfond's β-free identity) |

### Froggatt-Nielsen UV completion — Claim C (`UgpLean.MassRelations.FroggattNielsen`) — Round 21

First concrete UV-physics-model realisation of the binary cascade. Two
U(1)_FN flavor symmetries with flavon VEVs ε_1 = e^(−π/3), ε_2 = e^(−π/8)
(both < 1, FN-natural) and integer FN charges with **doubling pattern**
on lepton FN_1: charges (1, 2, 4) per generation; up-type FN_1 = (0, 0, 0);
constant FN_2 difference = 1.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **fnLogYukawaRatio_eq_TT** | FroggattNielsen | **Claim C theorem:** FN log-Yukawa-ratio prediction = UpLeptonFormula g (π/8) for g ≥ 1 (algebraic exact match) |
| **fnLogYukawaRatio_eq_cascade** | FroggattNielsen | FN-predicted log-Yukawa = binary cascade state for g ≥ 1 (FN as UV completion of cascade) |
| **fn_naturalness** | FroggattNielsen | ε_1 < 1 and ε_2 < 1 (standard FN naturalness condition `<Φ>/Λ < 1`) |
| **epsRatio_eq** | FroggattNielsen | ε_1 / ε_2 = e^(−5π/24) (falsifiable structural prediction for any UV completion) |

**Honest open questions for Round 22+:**
- Why doubled FN charges (1, 2, 4) instead of standard (0, 1, 2, 3)?
- Why transcendental flavon VEVs e^(−π/3), e^(−π/8) instead of rational ratios?
  (π/3 = 2·π/6 ties to Claim A's SU(3) Cartan-bisector angle — possible structural link)
- Why exactly 2 flavons, not 1 or 3?

### GUT Clebsch-Gordan Structure (`UgpLean.MassRelations.ClebschGordan`)

Includes Round 12 baseline + Rounds 17–18 VV three-factor extensions.

| Theorem | Module | Statement |
|---------|--------|-----------|
| **gut_ratio_45_over_126** | ClebschGordan | 45 · 14 = 126 · 5 (i.e., dim(45_SU5)/dim(126_SO10) = 5/14) |
| **nine_eq_gluon_plus_photon_dim** | ClebschGordan | dim(SU(3)_C adjoint) + dim(U(1)_Y) = 9 (= number of gauge bosons coupling to d_R, s_R, b_R as SU(2)_L singlets) |
| **alpha_VV_structural** | ClebschGordan | **VV α:** 1 + rank(SU(5))/(dim SU(3)_C adjoint + dim U(1)_Y) = 13/9 |
| **beta_VV_structural** | ClebschGordan | **VV β:** −(1 + Y_Q_doublet) = −7/6  (Y_Q = 1/6) |
| **so10_126_branching_sum** | ClebschGordan | 1 + 5 + 10 + 15 + 45 + 50 = 126 (SO(10) 126 → SU(5) branching arithmetic; confirms 45_SU5 is a subrep of 126_SO10) |
| **gamma_VV_structural** | ClebschGordan | **VV γ:** −dim(45_SU5)/dim(126_SO10) = −5/14 |
| **alpha_gamma_shared_gcd** | ClebschGordan | **Round 18:** Nat.gcd(45, 126) = dim(SU(3)_C adjoint) + dim(U(1)_Y) = 9 (no axioms, by `decide`) |
| **VV_coefficients_rational** | ClebschGordan | (13/9, −7/6, −5/14) packaged with structural identifications |

**Status of physical-bridge "FormulaHolds" theorems:** Both `UpLeptonFormulaHolds` and (analogous) "VV holds on physical masses" theorems remain `True → trivial` placeholders in their respective modules, pending Lean formalization of E_base→physical-mass conversion.  See ugp-physics 02_SPEC §D.4.

**Track D status (TT mechanism):** Compact-SU(3) character interpretation of the TT 2^g structure was definitively ruled out in Round 16 (algebraic integers vs transcendental targets); GUT CG rep-dim search ruled out in Round 15 (density-dominated null).  Best remaining candidate: binary cascade of π/6 phase shifts with 2^g accumulation per generation (under construction).
