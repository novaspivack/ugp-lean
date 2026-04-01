# ugp-lean: Theorem Catalog

What ugp-lean proves. All listed theorems have **0 sorry, 0 axioms** on the core path unless noted.

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

## Phase 4 (Stubs / Constants)

| Theorem | Module | Statement |
|---------|--------|-----------|
| **leptonB_matches_deltaUGP** | DeltaUGP | deltaUGPFormula leptonB |
| **g1Sq_bare_eq** | GaugeCouplings | g1Sq_bare = 16/125 |
| **g2Sq_bare_eq** | GaugeCouplings | g2Sq_bare = 2329/5400 |
| **g3Sq_bare_eq** | GaugeCouplings | g3Sq_bare = 41075281/27648000 |

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

## Open Conjectures (3 of 10)

| Conjecture | Module | Statement |
|------------|--------|-----------|
| **MirrorDualConjecture** | MirrorDualConjecture | Infinitely many mirror-dual pairs (twin-prime analog) |
| **UGPPrimeInfinitudeConjecture** | UGPPrimes | Infinitely many UGP primes (follows from Mirror-Dual) |
| **MuFlipDistanceConjecture** | Conjectures | Bounded μ-flip waiting time on linear progressions |

## External Citations (Not Formalized)

| ID | Claim | Source |
|----|-------|--------|
| C1 | Rule 110 Turing-universal | Cook (2004) |
| C2 | Continued-fraction Fibonacci lift | UGP Paper Updates |
| C3 | δ_UGP formula, b₁=73 unique | JMP Math Foundations |
| C4 | g₁²,g₂²,g₃² from invariants | JMP Math Foundations |
