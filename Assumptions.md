# ugp-lean Premise Ledger

Every premise that is not definitional truth. Tag: `definition` | `lemma` | `axiom` | `imported` | `citation`.

This ledger covers the **full library** (392 modules across 27 layers). The RSUC core proof path has 0 sorry and 0 custom axioms. See `docs/DESIGN.md` for the non-circularity contract.

---

## Definitions (semantic — core RSUC predicates)

| ID | Premise | Where Used | Tag |
|---|---|---|---|
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
|---|---|---|---|
| L1 | `ridgeSurvivors_10` — at n=10, survivors = {(24,42),(42,24)} | Compute.Sieve | lemma |
| L1a | `isMirrorDualSurvivorAt_iff` — Prop ↔ Finset membership at any n | Compute.Sieve | lemma |
| L2 | `theoremA_general` — UnifiedAdmissibleAt n t → t ∈ CandidatesAt n | Classification.TheoremA | lemma |
| L3 | `theoremB` — Residual = Candidates | Classification.TheoremB | lemma |
| L4 | `mdl_selects_LeptonSeed` — Lepton Seed is lex-min in Residual | Classification.TheoremB | lemma |
| L5 | `decUnifiedAdmissible_correct` — decidable version matches Prop | Compute.DecidablePredicates | lemma |

### GTE orbit and structure

| ID | Lean name | Module | Tag |
|---|---|---|---|
| L10 | `canonical_orbit_triples` — (1,73,823)→(9,42,1023)→(5,275,65535) | GTE.Evolution | lemma |
| L11 | `update_map_produces_canonical_orbit` — orbit forced by T, not hardcoded | GTE.UpdateMap | lemma |
| L12 | `ridge_remainder_lock_general` — m₂=15 for all n≥5 | GTE.UpdateMap | lemma |
| L13 | `mersenne_gcd_identity` — gcd(2ᵃ−1, 2ᵇ−1) = 2^gcd(a,b)−1 | GTE.MersenneGcd | lemma |
| L14 | `fmdl_orbit_is_unique_psc_trajectory` — GEN₁→GEN₂→GEN₃→vacuum uniquely forced | Universality.CUP3DUniqueness | lemma |
| L15 | `fmdl_vacuum_is_unique_attractor` — all 16,807 states → vacuum; no false vacua | Universality.CUP3DUniqueness | lemma |

### Structural / Elegant Kernel

| ID | Lean name | Module | Tag |
|---|---|---|---|
| L20 | `quarterLockLaw` — k_M = k_gen2 + ¼k_L² | QuarterLock | lemma |
| L21 | `k_L2_eq` — k_L² = 7/512 | ElegantKernel | lemma |
| L22 | `thm_ucl2_fully_unconditional` — k_gen = φ·cos(π/10) | ElegantKernel.Unconditional.KGenFullClosure | lemma |
| L23 | `k_gen2_eq_neg_phi_half` — k_gen2 = −φ/2 | ElegantKernel.KGen2 | lemma |
| L24 | `full_closure_summary` — all 5 UCL constraints simultaneously satisfiable | ElegantKernel.Unconditional.FullClosure | lemma |

### Mass relations

| ID | Lean name | Module | Tag |
|---|---|---|---|
| L30 | `koide_iff_twoS_sq_eq_threeN` — Koide ↔ (2S)²=3N | MassRelations.KoideClosedForm | lemma |
| L31 | `newton_flow_fixes_null_cone` — Newton flow S₃-equivariant; fixes Koide null cone | MassRelations.KoideNewtonFlow | lemma |
| L32 | `cabibbo_vev_formula` — \|V_us\|_CDM = exp(−13π/27) ≈ 0.2203 | MassRelations.CKMMixing | lemma |
| L33 | `neutrino_mass_ratio_within_1pct_of_nufit` — R within 1% of NuFIT 6.0 | MassRelations.NeutrinoMassRatio | lemma |
| L34 | `claim_C_formal` — TT = Weyl·2^g (zero hyp, zero sorry) | MassRelations.ClaimCBridge | lemma |
| L35 | `kink_top_coupling_eq_eps_FN` — η_B = 6.109×10⁻¹⁰ CatAL unconditional | Physics.FKTTCoupling | lemma |
| L36 | `cmca_physical_point_dictionary` — aM=1/7, am_φ=7/8, ξ*=7 | Physics.CMCAPhysicalPoint | lemma |

### Universality and self-reference

| ID | Lean name | Module | Tag |
|---|---|---|---|
| L40 | `uwca_sweep_implements_rule110` — UWCA sweep exactly implements Rule 110 | Universality.UWCASimulation | lemma |
| L41 | `ugp_is_turing_universal` — UGP substrate Turing-universal | Universality.TuringUniversal | lemma |
| L42 | `uwca_augmented_left_inverse` — backward ∘ forward = id | Universality.UWCAHistoryReversible | lemma |
| L43 | `gte_uniqueness_up_to_bisimulation` — unique lawful UWCA program | Universality.GTEUniqueness | lemma |
| L44 | `parity_projection_additive_forcing` — all 777 additive forms; Rule 110 forcing maximal | Universality.ParityProjectionForcing | lemma |
| L45 | `ugp_lawvere_fixed_point` / `ugp_rice_theorem` / `ugp_halting_undecidable` | SelfRef.* | lemma |

### Algebraic structure

| ID | Lean name | Module | Tag |
|---|---|---|---|
| L50 | `vacuum_unique_temporal_fixed_point_ring` — Fix(T_n)={vacuum} for all ring sizes | Polynomial.DynamicalZeta | lemma |
| L51 | `gte_ring_ground_states_uniform_general` — zero-energy rings = {0ⁿ,1ⁿ,5ⁿ} for all n≥3 | Polynomial.SpinSevenGroundSpace | lemma |
| L52 | `winding_charge_equivalence` — Z₇ winding conservation ≡ U(1)_EM charge conservation | Universality.GUTStructure | lemma |
| L53 | `coxeter_biconditional_summary` — h\|60 ↔ Q(ζ_{2h}) ⊂ Q(ζ₁₂₀) | CyclotomicCompleteness.CoxeterBiconditional | lemma |
| L54 | `cyclotomic_field_embedding` — Q(ζ_{2h}) →ₐ[ℚ] Q(ζ₁₂₀) when h\|60 | CyclotomicCompleteness.CyclotomicContainment | lemma |

### Continuum and substrate

| ID | Lean name | Module | Tag |
|---|---|---|---|
| L60 | `W1_triangle`, `W1_eq_zero_iff`, `W1_attained` | ContinuumLimit.WassersteinDistance | lemma |
| L61 | `planck_eft_blocking_ratio` — M_Pl/Λ_GTE = 3¹⁰·7¹⁸/2⁴ | Physics.CMCAPhysicalPoint | lemma |

---

## Documented Axioms (not sorry; explicit dependency)

| ID | Lean name | Module | Justification |
|---|---|---|---|
| A1 | `dickman_equidistribution_in_APs` | GTE.AnalyticArchitecture | Tenenbaum III.6; pending Mathlib analytic-NT |
| A2 | `crt_equidistribution_within_regime` | GTE.AnalyticArchitecture | Tenenbaum III.6 + CRT; same dependency |
| A3 | `sech_overlap_mesh_to_integral` | Substrate.SechOverlapIntegralBounds_bridge | Mesh→integral bridge; CatA class |
| A4 | `sech_overlap_bridge_r5` | Substrate.SechOverlapIntegralBounds_bridge | Second mesh→integral bridge; CatA class |

None of A1–A4 appear in the axiom closure of any physics or classification theorem.

---

## Imported (Mathlib / standard)

| ID | Premise | Source | Tag |
|---|---|---|---|
| I1 | `Nat.Prime`, `Nat.fib`, `Nat.Coprime` | Mathlib | imported |
| I2 | `Finset`, `divisorsAntidiagonal`, `Nat.card_divisors` | Mathlib | imported |
| I3 | `Real.logb`, `Real.rpow`, `Real.log_pos` | Mathlib | imported |
| I4 | `IsCyclotomicExtension`, `IsPrimitiveRoot` | Mathlib | imported |
| I5 | `OrderHom.lfp` (Tarski fixed-point) | Mathlib | imported |
| I6 | `MeasureTheory` (integrals, L² space) | Mathlib | imported |
| I7 | `LinearAlgebra.Matrix` | Mathlib | imported |

---

## External citations (not formalized in this library)

| ID | Claim | Used in | Tag |
|---|---|---|---|
| C1 | Rule 110 is Turing-universal (Cook 2004) | Universality.Rule110 | citation |
| C2 | Fibonacci lift F_g from continued-fraction geometry | GTE.UpdateMap | citation |
| C3 | δ_UGP formula, b₁=73 unique (UGP Main Paper) | Phase4.DeltaUGP | citation |
| C4 | g₁², g₂², g₃² from invariants (UGP Main Paper) | Phase4.GaugeCouplings | citation |
| C5 | IPT threshold physical validation across five domains | IPT (in ugp-physics-lean) | citation |
| C6 | FN SVD diagonalization: \|V_us\|_SM = ε₁^(α_d)·(1+O(ε²)) | MassRelations.CKMMixing | citation |
| C7 | Pöschl–Teller spectral completeness | Substrate.PhiMDLFluctuationSpectrum | citation |
| C8 | Wald entropy formula S = Area/(4G) | Gravity.WaldEntropy | citation |
| C9 | Cartan–Killing classification: compact semisimple Lie algebras classified by root system (Cartan 1894; Killing 1888); used to identify dim-14/rank-≤2 algebra as g₂ and dim-8 stabilizer as su(3) from certified dimension and rank witnesses | Algebra.G2StabilizerCertificate | citation |

---

## Non-negotiable credibility constraints

- RSUC proof path (TheoremA + TheoremB) has **0 sorry, 0 custom axioms**
- **Core/ does not import Compute/** (non-circularity enforced by module structure)
- All sieve predicates defined without referencing the answer (anti-smuggling rule)
- The four `axiom` entries (A1–A4) are **outside** the physics theorem closure
- Every `native_decide` call reduces to kernel-checkable arithmetic
