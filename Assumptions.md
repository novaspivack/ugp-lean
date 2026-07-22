# ugp-lean Premise Ledger

Every premise that is not definitional truth. Tag: `definition` | `lemma` | `axiom` | `imported` | `citation`.

This is a curated selection of the premises behind the library's key results — it is not
exhaustive. The library is 442 modules across 27 layers and references **98** named axioms
in total, counted via `grep -rhoE "^axiom [a-zA-Z0-9_']+" UgpLean --include="*.lean" | sort -u | wc -l`
(top-level `axiom` declarations, deduplicated by name; excludes the standard Lean/Mathlib
logical axioms `propext`/`Classical.choice`/`Quot.sound`, which are not disclosed
physics/mathematics premises in the sense meant here); for the complete, current axiom
inventory see the formalization paper's axiom-inventory table
(`paper/ugp_lean_formalization.tex`, Table `tab:axiom-inventory`). This ledger's purpose is
narrower: it documents the RSUC core proof path (0 sorry, 0 custom axioms) and the handful of
axioms and citations most relevant to spot-checking that path and the Universality chain. See
`docs/DESIGN.md` for the non-circularity contract.

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
| L41 | `ugp_is_turing_universal` — UGP substrate Turing-universal (conditional on A5) | Universality.TuringUniversal | lemma |
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

### Fock-space particle realization

**No new axioms.** This module (`Universality.PhiMDLFockSpaceParticles`) is built entirely
from previously-certified lemmas/axioms (`FockSpaceKink`, `BeableWindingPartitionInstance`,
`CMCAHilbertFockBridge`, `algebraic_lifting_theorem`) — it introduces zero new `axiom`
declarations and does not add to the 98-axiom count above.

| ID | Lean name | Module | Tag |
|---|---|---|---|
| L70 | `psc_admissible_sector_has_normalizable_fock_state` — every PSC-admissible Z₇ sector has a normalizable one-particle Fock-sector state or unit-weight sector amplitude | Universality.PhiMDLFockSpaceParticles | lemma |
| L71 | `fock_state_realizes_algebraic_lifting` — every [D]-weighted physical beable's Fock lift realizes the Algebraic Lifting Theorem's physical realization | Universality.PhiMDLFockSpaceParticles | lemma |
| L72 | `phimdl_fock_particle_master_bundle` — master bundle: sector totality, beable lift, algebraic-Fock-only construction, mass/stability/hierarchy on Fock-orbit states | Universality.PhiMDLFockSpaceParticles | lemma |

### Intrinsic area-scaling cut measure (causal graph and three-tape CMCA)

**No new axioms.** These two modules (`Spacetime.SpacelikeCutAreaScaling`,
`Spacetime.ThreeTapeCutAreaScaling`) are built entirely from previously-certified
infrastructure (`GTE.Spacetime.CausalGraph`'s `SpacelikeAdj`/`FinAdj`,
`Spacetime.HolographicScaling`'s `three_tape_state_card`, `Algebra.ChargeFromPolynomial`'s
`gtePolynomial`) plus `Finset`/`Fintype` combinatorics from Mathlib — they introduce zero
new `axiom` declarations and do not add to the 98-axiom count above (verified by
`grep -rhoE "^axiom [a-zA-Z0-9_']+" UgpLean/Spacetime/SpacelikeCutAreaScaling.lean
UgpLean/Spacetime/ThreeTapeCutAreaScaling.lean`, zero matches).

| ID | Lean name | Module | Tag |
|---|---|---|---|
| L90 | `cut_crossing_finset_card_eq_L_sq` — spacelike edges crossing a coordinate cut in the certified causal graph number exactly L² | Spacetime.SpacelikeCutAreaScaling | lemma |
| L91 | `three_tape_config_card_confirms_reading_A` — the three-tape ℤ₇ configuration space has cardinality exactly 7^(3L), confirming the one-coordinate-per-tape reading of the source-density formula | Spacetime.ThreeTapeCutAreaScaling | lemma |
| L92 | `three_tape_cut_crossing_card_eq_L_sq` — spacelike edges crossing a coordinate cut in the three-tape CMCA's emergent 3D lattice number exactly L² | Spacetime.ThreeTapeCutAreaScaling | lemma |

### GTP-3 uniqueness, winding superselection, and cyclotomic Galois certificates

**No new axioms.** These four modules (`Universality.GTP3Uniqueness`,
`Universality.WindingSectorSuperselection`, `Algebra.CyclotomicZ7GaloisGroup`,
`Algebra.CyclotomicFieldDisjointness`) are built entirely from previously-certified
results and Mathlib (`fmdl_step5`, `BeableWindingPartitionInstance`,
`IsCyclotomicExtension.autEquivPow`, cyclotomic irreducibility over ℚ) — they introduce
zero new `axiom` declarations and do not add to the 98-axiom count above.

| ID | Lean name | Module | Tag |
|---|---|---|---|
| L80 | `sm_orbit_unique_gtp3` — a state starts a GTP-3 chain iff it is a cyclic rotation of gen₁ (exhaustive over 16,807 states) | Universality.GTP3Uniqueness | lemma |
| L81 | `sm_orbit_gtp3_count` — exactly 5 GTP-3 start states exist | Universality.GTP3Uniqueness | lemma |
| L82 | `winding_sector_superselection` — winding-preserving injective evolution never maps a nonzero sector-w state into sector w' ≠ w | Universality.WindingSectorSuperselection | lemma |
| L83 | `topological_kink_stability` — nonzero non-trivial-winding states cannot evolve into the vacuum sector | Universality.WindingSectorSuperselection | lemma |
| L84 | `galois_z7_cyclic_order_6` — Gal(Q(ζ₇)/Q) is cyclic of order 6 (actual Galois group, via `autEquivPow`) | Algebra.CyclotomicZ7GaloisGroup | lemma |
| L85 | `galois_z7_cpt_generator` / `galois_z7_generation_subgroup_order_3` — conjugation has order 2, Frobenius σ₂ has order 3: Z₆ = Z₂ × Z₃ | Algebra.CyclotomicZ7GaloisGroup | lemma |
| L86 | `cyclotomic_z7_not_embeddable_in_z120` — no ℚ-algebra embedding Q(ζ₇) ↪ Q(ζ₁₂₀) (degree obstruction 6 ∤ 32) | Algebra.CyclotomicFieldDisjointness | lemma |

---

## Documented Axioms (not sorry; explicit dependency)

| ID | Lean name | Module | Justification |
|---|---|---|---|
| A1 | `dickman_equidistribution_in_APs` | GTE.AnalyticArchitecture | Tenenbaum III.6; pending Mathlib analytic-NT |
| A2 | `crt_equidistribution_within_regime` | GTE.AnalyticArchitecture | Tenenbaum III.6 + CRT; same dependency |
| A3 | `sech_overlap_mesh_to_integral` | Substrate.SechOverlapIntegralBounds_bridge | Mesh→integral bridge; CatA class |
| A4 | `sech_overlap_bridge_r5` | Substrate.SechOverlapIntegralBounds_bridge | Second mesh→integral bridge; CatA class |
| A5 | `minsky_counter_machine_turing_complete_1967` | Universality.RegisterMachine | Minsky 1967, classical counter-machine Turing-completeness; absent from Mathlib. **Load-bearing** for the Universality chain (`ugp_is_turing_universal`, L41). |
| A6 | `cook_rule110_simulates_computable` | Universality.CookComputableBridge | Composition of Cook's proven operational Stage 3 readback theorem (`cook_operational_stage3_tm_microstep_readback` in `rule110-lean`, formerly `rule110_turing_universal_from_cook`; zero-sorry modulo 5 classical Cook bridge axioms — real, established mathematics, but itself only a conditional readback certificate for already-supplied compilations, not a Turing-universality theorem) with classical TM/Partrec compilation; axiom only because this specific composition step is not yet re-derived within `ugp-lean-exp` itself, not because the underlying mathematics is in doubt. **Load-bearing** for `phimdl_turing_universal` (Universality.PhiMDLUniversality). |

None of A1–A4 appear in the axiom closure of any physics or classification theorem; they are
outside the RSUC core proof path entirely. A5 and A6 are different: they ARE load-bearing, but
specifically and only for the Universality chain (`ugp_is_turing_universal`,
`phimdl_turing_universal`) — they do not appear in the RSUC core, GTE orbit, mass-relations, or
algebraic-structure results listed above.

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
- A1–A4 are **outside** the physics theorem closure entirely (analytic-NT and mesh-bridge axioms, unrelated to RSUC or Universality)
- A5–A6 are **load-bearing, but only for the Universality chain** (`ugp_is_turing_universal`, `phimdl_turing_universal`) — they do not affect RSUC, GTE orbit, or mass-relations results
- Every `native_decide` call reduces to kernel-checkable arithmetic
