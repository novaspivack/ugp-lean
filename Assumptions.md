# ugp-lean Premise Ledger

Every premise that is not definitional truth. Tag: `definition` | `lemma` | `axiom` | `imported` | `citation`.

This ledger covers the **full library** as of 2026-05-12 (117 modules). The RSUC core proof path has 0 sorry and 0 custom axioms. See `docs/DESIGN.md` for the non-circularity contract.

---

## Definitions (semantic — core RSUC predicates)

| ID | Premise | Where Used | Tag |
|----|---------|------------|-----|
| D1 | `SemanticFloor t := t.a ∈ {1,5,9} ∧ t.b ≥ 40 ∧ t.c ≥ 800` | SievePredicates, TheoremA | definition |
| D2 | `QuarterLockRigidAt n t := ∃ b₂ q₂, isMirrorDualSurvivorAt n b₂ q₂ ∧ (t.b, t.c) from that pair` | SievePredicates | definition |
| D3 | `RelationalAnchorAt n t := ∃ b₂ q₂, isMirrorDualSurvivorAt n b₂ q₂ ∧ t.b = b₁ ∧ c ∈ {c₁, c₂}` | SievePredicates | definition |
| D4 | `UnifiedAdmissibleAt n := SemanticFloor ∧ QuarterLockRigidAt n ∧ RelationalAnchorAt n` | RSUC | definition |
| D4a | `QuarterLockRigid := QuarterLockRigidAt 10`; `RelationalAnchor := t.b=73 ∧ t.c∈{823,2137}`; `UnifiedAdmissible := UnifiedAdmissibleAt 10` | SievePredicates | definition |
| D5 | `MirrorEquiv t₁ t₂ := same (a,b), c ∈ {823, 2137} swapped` | TripleDefs, Disconfirmation | definition |

---

## Lemmas (proved in ugp-lean — selected key results)

### RSUC chain

| ID | Lean name | Module | Tag |
|----|-----------|--------|-----|
| L1 | `ridgeSurvivors_10` — at n=10, survivors = {(24,42),(42,24)} | Compute.Sieve | lemma |
| L1a | `isMirrorDualSurvivorAt_iff` — Prop ↔ Finset membership at any n | Compute.Sieve | lemma |
| L2 | `theoremA_general` — UnifiedAdmissibleAt n t → t ∈ CandidatesAt n | Classification.TheoremA | lemma |
| L2a | `theoremA` — n=10 corollary | Classification.TheoremA | lemma |
| L3 | `theoremB` — Residual = Candidates | Classification.TheoremB | lemma |
| L4 | `mdl_selects_LeptonSeed` — Lepton Seed is lex-min in Residual | Classification.TheoremB | lemma |
| L5 | `decUnifiedAdmissible_correct` — decidable version matches Prop | Compute.DecidablePredicates | lemma |
| L5a | `RelationalAnchorAt_10_iff` — RelationalAnchorAt 10 t ↔ RelationalAnchor t | Compute.DecidablePredicates | lemma |

### GTE orbit and structure

| ID | Lean name | Module | Tag |
|----|-----------|--------|-----|
| L10 | `canonical_orbit_triples` — (1,73,823)→(9,42,1023)→(5,275,65535) | GTE.Evolution | lemma |
| L11 | `update_map_produces_canonical_orbit` — orbit forced by T, not hardcoded | GTE.UpdateMap | lemma |
| L12 | `ridge_remainder_lock_general` — m₂ = 15 for all n ≥ 5 | GTE.UpdateMap | lemma |
| L13 | `mersenne_gcd_identity` — gcd(2^a−1, 2^b−1) = 2^(gcd a b)−1 | GTE.MersenneGcd | lemma |
| L14 | `tau_ridge_exact` — τ(2^n−16) = 5·τ(2^(n−4)−1) for n≥5 | GTE.MirrorDualConjecture | lemma |

### Structural / Elegant Kernel

| ID | Lean name | Module | Tag |
|----|-----------|--------|-----|
| L20 | `quarterLockLaw` — k_M = k_gen2 + ¼k_L² | QuarterLock | lemma |
| L21 | `k_L2_eq` — k_L² = 7/512 | ElegantKernel | lemma |
| L22 | `thm_ucl2_fully_unconditional` — k_gen = φ·cos(π/10) | ElegantKernel.KGen | lemma |
| L23 | `k_gen2_eq_neg_phi_half` — k_gen2 = −φ/2 | ElegantKernel.KGen2 | lemma |
| L24 | `L_model_from_gauge_structure` — L_model = log₂((D₁·5³)/3) | LModelDerivation | lemma |

### Mass relations

| ID | Lean name | Module | Tag |
|----|-----------|--------|-----|
| L30 | `koide_iff_twoS_sq_eq_threeN` — Koide ↔ (2S)²=3N | MassRelations.KoideClosedForm | lemma |
| L31 | `newton_flow_fixes_null_cone` — Newton flow fixes Koide null cone | MassRelations.KoideNewtonFlow | lemma |
| L32 | `alpha_d_from_N_c` — α_d = 13/9 from N_c=3 | MassRelations.DownRational | lemma |
| L33 | `cabibbo_vev_formula` — \|V_us\|_CDM = exp(−13π/27) ≈ 0.2203 | MassRelations.CKMMixing | lemma |
| L34 | `claim_C_formal` — cascadeState g = angleToAlpha1(ω₁)·2^g + π/8 | MassRelations.ClaimCBridge | lemma |

### Universality and self-reference

| ID | Lean name | Module | Tag |
|----|-----------|--------|-----|
| L40 | `uwca_sweep_implements_rule110` — UWCA sweep exactly implements Rule 110 | Universality.UWCASimulation | lemma |
| L41 | `ugp_is_turing_universal` — UGP substrate Turing-universal | Universality.TuringUniversal | lemma |
| L42 | `uwca_augmented_left_inverse` — backward ∘ forward = id on tape×history | Universality.UWCAHistoryReversible | lemma |
| L43 | `ugp_lawvere_fixed_point` / `ugp_rice_theorem` / `ugp_halting_undecidable` | SelfRef.* | lemma |

### Cyclotomic / Galois / Phase4

| ID | Lean name | Module | Tag |
|----|-----------|--------|-----|
| L50 | `galois_protection_master_theorem` — one-loop QED correction vanishes | Phase4.GaloisProtection | lemma |
| L51 | `o3_full_identification` — two-loop colour coefficient = 8/9 | Phase4.TwoLoopCoefficient | lemma |
| L52 | `coxeter_biconditional_summary` — h\|60 ↔ Q(ζ_{2h}) ⊂ Q(ζ₁₂₀) arithmetic | CyclotomicCompleteness.CoxeterBiconditional | lemma |
| L53 | `cyclotomic_field_embedding` — Q(ζ_{2h}) →ₐ[ℚ] Q(ζ₁₂₀) when h\|60 | CyclotomicCompleteness.CyclotomicContainment | lemma |

---

## Documented Axioms (not sorry; explicit dependency)

| ID | Lean name | Justification | Module |
|----|-----------|---------------|--------|
| A1 | `dickman_equidistribution_in_APs` | Tenenbaum III.6; pending Mathlib analytic-NT infrastructure | GTE.AnalyticArchitecture |
| A2 | `crt_equidistribution_within_regime` | Tenenbaum III.6; same dependency | GTE.AnalyticArchitecture |

Neither axiom appears in the closure of any physics or classification theorem.

---

## Imported (Mathlib / standard)

| ID | Premise | Source | Tag |
|----|---------|--------|-----|
| I1 | `Nat.Prime`, `Nat.fib`, `Nat.Coprime` | Mathlib | imported |
| I2 | `Finset`, `divisorsAntidiagonal`, `Nat.card_divisors` | Mathlib | imported |
| I3 | `Real.logb`, `Real.rpow`, `Real.log_pos` | Mathlib | imported |
| I4 | `IsCyclotomicExtension`, `IsPrimitiveRoot` | Mathlib | imported |
| I5 | `OrderHom.lfp` (Tarski fixed-point) | Mathlib | imported |

---

## External citations (not formalized in this library)

| ID | Claim | Used in | Tag |
|----|-------|---------|-----|
| C1 | Rule 110 is Turing-universal (Cook 2004) | Universality.Rule110 | citation |
| C2 | Fibonacci lift F_g from continued-fraction geometry | GTE.UpdateMap | citation |
| C3 | δ_UGP formula, b₁=73 unique (UGP Main Paper) | Phase4.DeltaUGP | citation |
| C4 | g₁², g₂², g₃² from invariants; SU(2) harmonic mean, SU(3) Vandermonde | Phase4.GaugeCouplings | citation |
| C5 | IPT threshold physical validation across five domains | IPT (in ugp-physics-lean) | citation |
| C6 | FN SVD diagonalization: \|V_us\|_SM = ε₁^(α_d)·(1+O(ε²)) | MassRelations.CKMMixing (open) | citation |

---

## Non-negotiable credibility constraints

- RSUC proof path (TheoremA + TheoremB) has **0 sorry, 0 custom axioms**
- **Core/ does not import Compute/** (non-circularity enforced by module structure)
- All sieve predicates defined without referencing the answer (anti-smuggling rule)
- The two `axiom` entries (A1, A2) are **outside** the physics theorem closure
- Every `native_decide` call reduces to kernel-checkable arithmetic
