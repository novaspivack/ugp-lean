# ugp-lean: Theorem Highlights

**This is a curated selection of the most important theorems by layer.** It is not exhaustive — the library contains thousands of theorems across 361 modules. For the complete inventory, see `paper/ugp_lean_formalization.tex` (Table 1) and browse the source in `UgpLean/`.

All listed theorems have **0 sorry, 0 custom axioms** on the core path unless marked ⚠.

---

## RSUC — Residual Seed Uniqueness

The foundational chain from which all physics derives.

| Theorem | Lean name | Module |
|---|---|---|
| At n=10, ridge survivors = {(24,42),(42,24)} | `ridgeSurvivors_10` | Compute.Sieve |
| ∀n, UnifiedAdmissibleAt n t → t ∈ CandidatesAt n | `theoremA_general` | Classification.TheoremA |
| Residual = Candidates (classification) | `theoremB` | Classification.TheoremB |
| MDL selects (1,73,823) as lex-min | `mdl_selects_LeptonSeed` | Classification.TheoremB |
| **RSUC: unique residual up to MirrorEquiv** | `rsuc_theorem` | Classification.RSUC |
| n=10 is the minimal admissible ridge level | `n10_is_minimal_admissible_ridge` | Compute.SieveBelow10 |

---

## GTE Orbit and Update Map

| Theorem | Lean name | Module |
|---|---|---|
| Canonical orbit: (1,73,823)→(9,42,1023)→(5,275,65535) | `canonical_orbit_triples` | GTE.Evolution |
| Orbit forced by T; not hardcoded | `update_map_produces_canonical_orbit` | GTE.UpdateMap |
| Ridge remainder lock m₂=15 for all n≥5 | `ridge_remainder_lock_general` | GTE.UpdateMap |
| gcd(2ᵃ−1, 2ᵇ−1) = 2^gcd(a,b)−1 | `mersenne_gcd_identity` | GTE.MersenneGcd |
| τ(Rₙ) = 5·τ(2^(n−4)−1) exact formula | `tau_ridge_exact` | GTE.MirrorDualConjecture |
| RC tier structure: 1023, 65535 Mersenne boundaries | `ugp_rc_tier_structure` | GTE.MersenneLadder |
| Fingerprint fixed-point (Tarski, Set form) | `fingerprint_fixed_point_exists` | GTE.StructuralTheorems |
| Resonant factory Q₊=Q₋+2; no local obstruction | `factory_gap_two`, `hasse_check_no_obstruction` | GTE.ResonantFactory |

---

## Orbit Uniqueness and Vacuum Structure

| Theorem | Lean name | Module |
|---|---|---|
| SM orbit is the *uniquely forced* 3-step trajectory from GEN₁ | `fmdl_orbit_is_unique_psc_trajectory` | Universality.CUP3DUniqueness |
| GEN₁ is a Garden-of-Eden state (0 predecessors) | `fmdl_gen1_is_goe` | Universality.GoEHierarchy |
| All 5 cyclic rotations of GEN₁ are GoE states | `fmdl_gen1_all_rotations_are_goe` | Universality.GoEStabilityHierarchy |
| GEN₂ and GEN₃ each have exactly 1 predecessor | `fmdl_gen2_unique_predecessor` | Universality.GoEStabilityHierarchy |
| All 16,807 states reach vacuum in ≤7 steps | `fmdl_universal_7step_convergence` | Universality.CUP3DUniqueness |
| **No false vacua**: vacuum is unique fixed point | `fmdl_unique_fixed_point` | Universality.CUP3DUniqueness |
| Z₇/Z₂ incompatibility: φ: Z₇→Z₂ is not a ring hom | `z7_binary_not_ring_homomorphism` | Universality.CUP3DUniqueness |
| Photon is the unique uniform fixed point of f_MDL | `fmdl_unique_uniform_fixed_point` | Universality.CUP3DUniqueness |
| Z₇ sum conservation unique to gen₁ | `cup11b_z7_sum_conservation_unique` | Universality.CUP3DUniqueness |

---

## Rule 110 / Universality

| Theorem | Lean name | Module |
|---|---|---|
| Rule 110 is the unique weight-5 SM orbit satisfier | `rule110_unique_weight5_orbit_satisfier` | Universality.CUP4TotalParity |
| Rule 110 completely isolated on all 1024 orbit pairs | `rule110_orbit_complete_isolation` | Universality.OrbitPerturbationCatalog |
| d-dim CA with SM orbit must apply Rule 110 on slices | `dimensional_slice_uniqueness` | Universality.DimensionalSliceUniqueness |
| p=5 uniquely transitive for weight-3 vectors among primes ≤23 | `z5_transitivity_uniqueness` | Universality.Z5TransitivityUniqueness |
| UWCA sweep implements Rule 110 exactly | `uwca_sweep_implements_rule110` | Universality.UWCASimulation |
| **UGP substrate is Turing-universal** | `ugp_is_turing_universal` | Universality.TuringUniversal |
| UWCA history-lane reversibility: backward ∘ forward = id | `uwca_augmented_left_inverse` | Universality.UWCAHistoryReversible |
| GTE compilation: sigma_gte by `rfl` | `gte_compilation_theorem` | Universality.GTECompilation |
| **GTE uniqueness**: unique lawful UWCA program up to bisimulation | `gte_uniqueness_up_to_bisimulation` | Universality.GTEUniqueness |
| Parity-projection forcing maximal (777 + 16,807 forms) | `parity_projection_additive_forcing` | Universality.ParityProjectionForcing |
| Orbit + vacuum force unique GF(7) interpolant (7⁸ census) | `ugp_orbit_interpolation_lift` | Universality.TriangleLiftTheorem |
| Z₇ winding conservation ≡ U(1)_EM charge conservation | `winding_charge_equivalence` | Universality.GUTStructure |
| D_top = exp(−1/N_c) via Z₇ transitivity (CatAL, zero sorry) | `d_top_derivation_chain_catal` | Universality.GUTStructure |

---

## Elegant Kernel / Quarter-Lock

| Theorem | Lean name | Module |
|---|---|---|
| k_M = k_gen2 + ¼k_L² | `quarterLockLaw` | QuarterLock |
| k_L² = 7/512 | `k_L2_eq` | ElegantKernel |
| **k_gen = φ·cos(π/10)** (zero hypotheses, zero sorry) | `thm_ucl2_fully_unconditional` | ElegantKernel.Unconditional.KGenFullClosure |
| k_gen2 = −φ/2 (unique negative root of pentagon quadratic) | `k_gen2_eq_neg_phi_half` | ElegantKernel.KGen2 |
| Pentagon–Hexagon Bridge: k_gen + k_gen2 = φ·(cos π/10 − cos π/3) | `k_gen_pentagon_hexagon_bridge` | ElegantKernel.Unconditional.KGenFullClosure |
| All 5 UCL constraints simultaneously satisfiable | `full_closure_summary` | ElegantKernel.Unconditional.FullClosure |
| UCL master cert: all 9 EK coefficients CatAL | `elegant_kernel_full_certification` | ElegantKernel.Unconditional.MasterCertification |

---

## Mass Relations

| Theorem | Lean name | Module |
|---|---|---|
| **Claim C (formal)**: TT = Weyl·2^g (zero hyp, zero sorry) | `claim_C_formal` | MassRelations.ClaimCBridge |
| Pentagon–Hexagon–TT unified bridge | `pentagon_hexagon_TT_unified_bridge` | MassRelations.ClaimCBridge |
| Koide ↔ (2S)² = 3N algebraic normal form | `koide_iff_twoS_sq_eq_threeN` | MassRelations.KoideClosedForm |
| Newton flow fixes Koide null cone; S₃-equivariance | `newton_flow_fixes_null_cone` | MassRelations.KoideNewtonFlow |
| CKM θ₂₃ ratio = 15/8 unique at n=10 | `op_v_ckm_theta23_closure` | MassRelations.CKMTheta23 |
| \|V_us\|_CDM = exp(−13π/27) ≈ 0.2203 (1.9% off PDG) | `cabibbo_vev_formula` | MassRelations.CKMMixing |
| VV GUT coefficient shifts bare FN charge additively | `fn_vv_correction_additive` | MassRelations.CKMMixing |
| Neutrino mass ratio R ≈ 0.02936; within 1% of NuFIT 6.0 | `neutrino_mass_ratio_within_1pct_of_nufit` | MassRelations.NeutrinoMassRatio |
| PMNS: sin²θ₁₂=4/13, sin²θ₂₃=19/42, δ_CP=8π/7, J<0 | (various) | MassRelations.NeutrinoSector |
| Higgs quartic 0.12 < λ < 0.14 | (various) | MassRelations.HiggsQuartic |
| sin²θ₂₃^NLO = 209/441 | (various) | MassRelations.PMNSNLOCorrection |
| 2·a_τ = a_e + a_μ (discrete S₃ shadow, zero sorry) | `lepton_a_discrete_S3_identity` | MassRelations.KoideS3DiscreteIdentities |

---

## BraidAtlas

| Theorem | Lean name | Module |
|---|---|---|
| Q = W_g/N_c; anomaly cancellation forces N_c=3 | `charge_theorem` | BraidAtlas.ChargeTheorem |
| EW boson c-values: c(W)=11, c(Z)=12, c(H)=13 | (various) | BraidAtlas.EWBosons |
| All 9 light baryon b-formulas (full conjunction) | `ugp_all_baryon_b_formulas` | BraidAtlas.CompositeTriples |
| b(proton)=11459, b(neutron)=11441, b(p)−b(n)=2N_c²=18 | `ugp_nucleon_b_formula` | BraidAtlas.CompositeTriples |
| E₇ falsifier: h=18 ∤ 120 | `e7_double_failure` | BraidAtlas.CoxeterConductor |

---

## GF(7) Polynomial Explorations

| Theorem | Lean name | Module |
|---|---|---|
| Ground states = {0,1,5} for poly p (CatAL) | `poly_p_uniform_gs_roots` | Polynomial.PolyExplorations |
| Period-475 certificates (CatAL) | `period_475_returns`, `period_475_is_minimal` | Polynomial.PolyExplorations |
| Vacuum basin = 52; KL divergence p≠f_MDL | `poly_p_vacuum_basin_card_eq_52` | Polynomial.PolyExplorations |
| PSC-projection bundle (CatAL) | `psc_projection_gives_fmdl` | Polynomial.PolyExplorations |
| MDL Three-Level Unification (cross-module CatAL bundle) | `mdl_three_level_unification` | Polynomial.MDLThreeLevelUnification |
| GTE causal tree: 1023 nodes, Horton r_B=2 | `gte_causal_tree_summary` | Polynomial.GTECausalTree |
| p(x,x,x)−x = −x(x²+x−1); SRRG and Rule 110 as ℤ-quadratic fibers | `gte_diagonal_quadratic_factorization` | Polynomial.GoldenQuadratic |
| **Ground-space rigidity**: {0ⁿ,1ⁿ,5ⁿ} for ALL ring lengths n≥3 | `gte_ring_ground_states_uniform_general` | Polynomial.SpinSevenGroundSpace |
| cond(K)=15=N_gen·N_fam for K=ℚ(√−3,√5) | (various) | Polynomial.BiquadraticCompositum |
| Fix(T_n)={vacuum} for all ring sizes; period-475 ζ factorization | `vacuum_unique_temporal_fixed_point_ring` | Polynomial.DynamicalZeta |
| \|AGL(1,7)\|=42; reflection swaps Rule 110 ↔ Rule 124 | (various) | Polynomial.AGL17ChiralZ2 |
| F₂₁ ≅ (ℤ[ω]/(3+ω))⁺⋊μ₃; Φ₆ ladder identity web | `f21_eisenstein_residue_model` | Polynomial.EisensteinIdentities |
| Directed wall energies; gap exponent 3/2 (14 theorems) | `spin7_directed_wall_energies` | Polynomial.SpinSevenWallSpectroscopy |
| Zero-energy spectral radius ρ=1; gap-law A=1 (10 theorems) | `spin7_spectator_amplitude` | Polynomial.SpinSevenSpectatorAmplitude |
| Perron–Frobenius hypothesis package, uniform in β (7 theorems) | `spin7_transfer_pf_hypotheses` | Polynomial.SpinSevenTransferPrimitivity |

---

## Physics / Substrate / Gravity

| Theorem | Lean name | Module |
|---|---|---|
| **η_B = 6.109×10⁻¹⁰ CatAL unconditional** (+0.15σ vs PDG) | `kink_top_coupling_eq_eps_FN` | Physics.FKTTCoupling |
| BPS saturation T₁₁=0 by `rfl` | `phi_mdl_kink_bps_saturation` | Physics.FKTTCoupling |
| aM=1/7, am_φ=7/8, ξ*=7; Tape Saturation Theorem | `cmca_physical_point_dictionary` | Physics.CMCAPhysicalPoint |
| M_Pl/Λ_GTE = 3¹⁰·7¹⁸/2⁴ (CatAL) | `planck_eft_blocking_ratio` | Physics.CMCAPhysicalPoint |
| V_coupling breaks Z₇ shift symmetry; bias minimum at k=0 | `vcoupling_breaks_z7_shift` | Physics.ZSevenVacuumSelection |
| Coset-charge spectrum t_V=3, c_coset=−1 | (various) | Physics.BurnsideCosetCharges |
| ∫sech³ = π/2 (0 sorry) | (various) | Substrate.SechOverlapIntegralBounds |
| Sech overlap finite-r bounds (0 sorry; 2 CatA bridge axioms) | (various) | Substrate.SechOverlapIntegralBounds_bridge |
| α = N_c−1 = 2 sech bracket (CatAL-conditional on bridge axioms) ⚠ | `alpha_eq_Nc_minus_1` | Gravity.YukawaOverlapExponent |
| W₁ nonneg, triangle, W₁=0 iff equal, attainment (all 0 sorry) | `W1_nonneg`, `W1_triangle`, `W1_eq_zero_iff` | ContinuumLimit.WassersteinDistance |

---

## Spacetime / Mass Gap

| Theorem | Lean name | Module |
|---|---|---|
| Positive mass gap Δ > 0 for all non-vacuum beables | `gte_mass_gap` | Spacetime.MassGap |
| Δ ≥ 1.8 MeV (PDG up-quark lower bound) | `gte_mass_formula_physical` | Spacetime.MassGap |
| gen₃ mass > gen₂ mass > gen₁ mass > 0 (all SM sectors) | `orbit_generation_ordering` | Spacetime.OrbitMassHierarchy |
| Preferred-direction geodesic via D-weighted centroid (CatAD) | `geodesic_theorem` | Spacetime.GeodesicTheorem |
| Spatial centroid invariant along timelike worldline | `geodesic_preferred_direction` | Spacetime.GeodesicTheorem |

---

## Cyclotomic / Galois

| Theorem | Lean name | Module |
|---|---|---|
| h\|60 ↔ 2h\|120; E₇ falsifier (h=18 ∤ 120 AND ∤ 60) | `coxeter_biconditional_summary` | CyclotomicCompleteness.CoxeterBiconditional |
| Q(ζ_{2h}) →ₐ[ℚ] Q(ζ₁₂₀) when h\|60 (zero sorry) | `cyclotomic_field_embedding` | CyclotomicCompleteness.CyclotomicContainment |
| One-loop QED correction vanishes | `galois_protection_master_theorem` | Phase4.GaloisProtection |
| Two-loop colour coefficient = 8/9 | `o3_full_identification` | Phase4.TwoLoopCoefficient |

---

## Self-Reference

| Theorem | Lean name | Module |
|---|---|---|
| Lawvere fixed-point theorem | `ugp_lawvere_fixed_point` | SelfRef.LawvereKleene |
| Kleene recursion theorem | `ugp_kleene_recursion_thm` | SelfRef.LawvereKleene |
| Rice's theorem | `ugp_rice_theorem` | SelfRef.RiceHalting |
| Halting problem undecidable | `ugp_halting_undecidable` | SelfRef.RiceHalting |

---

## Nuclear Structure

| Theorem | Lean name | Module |
|---|---|---|
| Proton b-seed 11459 is odd; neutron b-seed 11441 is odd | `proton_b_seed_is_odd`, `neutron_b_seed_is_odd` | GTE.NuclearPairing |
| b_eff parity = mass-number A mod 2 | `beff_parity` | GTE.NuclearPairing |
| GTE nuclear parity rule (full conjunction, 0 sorry) | `gte_nuclear_parity_rule` | GTE.NuclearPairing |
| 5^(3/2) = √125 (pairing constant identity) | `pairing_sqrt_identity` | GTE.NuclearPairing |

---

## GTE Derivation Modules (EPIC-091 — GT-001 through GT-013)

| Theorem | Lean name | Module |
|---|---|---|
| Ridge constant 16 = 2^(1+ord₇(2)) is the unique power of 2 compatible with Z₇×Z₃ divisibility at n=10 (GT-001/GT-009 bundle) | `gt001_gt009_ridge_closed` | GTE.RidgeDerivation |
| Ridge constant derived from GF(7)×Z₃ structure | `ridge_constant_from_gf7_z3` | GTE.RidgeDerivation |
| Divisibility condition certified at ridge n=10 | `ridge_divisibility_at_n10` | GTE.RidgeDerivation |
| Ridge offset is uniquely a power of 2 | `ridge_offset_unique_power_of_2` | GTE.RidgeDerivation |
| q₂ = N_c × 2^ord₇(2) from Z₇ multiplicative order and colour rank (GT-010) | `gt010_q2_from_z7_nc` | GTE.FibonacciDerivation |
| Ridge offset d = π(7) = 16 equals Pisano period of 7 (GT-011) | `gt011_ridge_offset_eq_pisano_7` | GTE.FibonacciDerivation |
| Generation gap = F_{ord₇(2)+N_c+1} derived from Z₇×Z₃ (GT-012) | `gt012_gap_from_z7_z3` | GTE.FibonacciDerivation |
| SemanticFloor set {1,9,5} is orbit projection of a′ = m−(n+2−t) | `semantic_floor_a_condition_from_cascade` | GTE.SemanticFloorDerivation |
| Canonical a-orbit values {1,9,5} at ridge n=10 certified | `a_orbit_values_at_n10` | GTE.SemanticFloorDerivation |
| Even-step c′ = 2^(n+2Nc)−1 uniquely selected by double-Fibonacci minimality | `mersenne_ladder_uniqueness_proved` | GTE.MersenneLadder |
| N_c = 3 forced by PSC with Frobenius prime and FGCI identities (GT-013 bundle) | `gt013_psc_nc_bundle` | GTE.PSCColorRankBundle |
| PSC enumeration forces N_gen = colorRank | `psc_implies_ngen_eq_colorRank` | GTE.PSCColorRankBundle |

---

## GTE-NEMS Framework

| Theorem | Lean name | Module |
|---|---|---|
| GTE substrate as `NemS.Framework`; NEMS + PSC bundle | `gte_nems` | Framework.GTEFrameworkInstance |
| Transputation classification on GTE substrate | `gte_tpc_from_nems_classification` | Framework.GTEFrameworkInstance |
| GTE final coalgebra | (various) | Framework.GTEFinalCoalgebra |
| PR-5 Independence | `pr5_independence` | Framework.PR5Independence |
| PSC measure uniformity | `psc_measure_uniformity` | Framework.PSCMeasureUniformity |

---

## PSL(2,7) Unification, Golden Fiber, and Algebraic Extensions

| Theorem | Lean name | Module |
|---|---|---|
| F₂₁ ≅ PSL(2,7) is the automorphism group of the Fano plane | `psl27_is_automorphism_group_fano_plane` | Polynomial.PSL27Unification |
| Borel-measurability of the F₂₁ action | `f21_action_borel_measurable` | Polynomial.F21SU2Bridge |
| Fano regular action well-defined | (various) | Algebra.FanoRegularAction |
| Golden-fiber states at q=7 classified | `golden_fiber_taxonomy_at_q7` | Polynomial.GoldenFiberTaxonomy |
| Golden-quadratic arithmetic certified | (various) | Polynomial.GoldenQuadratic |
| Eisenstein norm-product \|F₂₁\| = Φ₆(2)Φ₆(3) | `eisenstein_norm_product` | Algebra.EisensteinFunctor |
| A₄ structure from inert-2 ramification | `a4_from_inert_two_ramification` | Algebra.EisensteinFunctor |
| Eisenstein mass identities | (various) | MassRelations.EisensteinIdentities |
| Admissible prime set certification | (various) | Polynomial.AdmissiblePrimes |
| Gaussian face arithmetic | (various) | Polynomial.GaussianFaceLemma |
| N_gen = 3 is unique | `ngen_uniqueness` | Classification.NgenUniqueness |
| N_gen = 3 universality: 7 constraints jointly certified | `ngen_universality_seven_constraints` | Classification.NgenUniqueness |
| N_gen = 3 universality: 8th constraint (bracket orientation) conditional on OQ-QG-1b/c | `ngen_universality_eight_conditional` | Classification.NgenUniqueness |
| N_gen = 3 universality master (7/8 CatAL, 8th conditional) | `ngen_universality_master` | Classification.NgenUniqueness |
| Cosmological constant vanishes at all algebraic orders | `lambda_all_order_zero` | Gravity.LambdaAllOrderZero |
| **Vacuum CMCA spatial GH convergence to flat 3D space** | **`vacuum_cmca_gh_converges_to_flat_space`** | **Spacetime.VacuumGHConvergence** |
| **GH distance bound: ghDist(FinGrid L, UnitCube) ≤ 1/L** | **`fin_grid_gh_dist_bound`** | **Spacetime.VacuumGHConvergence** |
| **FinGrid GH family is totally bounded (matter-present sequences have GH-convergent subsequences)** | **`finGrid_family_totally_bounded`** | **Spacetime.MatterGHPrecompactness** |
| **Single kink of width W: ghDist(KinkGrid L, UnitCube) ≤ (W/2+1)/L → 0; GH limit is flat R³** | **`single_kink_gh_converges_to_flat`** | **Spacetime.MatterGHPrecompactness** |
| **SU(2)_L doublet Hilbert space: T₃ eigenvalues ±½, W± operators, su(2) algebra machine-certified** | **`su2l_doublet_hilbert_certified`** | **Substrate.SU2LDoubletHilbert** |
| T₃ eigenvalue: +½ (neutrino) and −½ (charged lepton) on standard basis | `t3_eigenvalue` | Substrate.SU2LDoubletHilbert |
| su(2) algebra: [T₊,T₋]=2T₃ and [T₃,T±]=±T± all certified | `su2l_algebra_closes` | Substrate.SU2LDoubletHilbert |
| VA quantization bundle | (various) | Substrate.VAQuantBundle |
| Chiral current L² structure | (various) | Substrate.ChiralCurrentL2 |
| Coherence-measure uniqueness | (various) | Substrate.CoherenceMeasureUniqueness |
| Solovay completeness of UWCA | `solovay_completeness` | Universality.SolovayCompleteness |
| Bi-immunity of the orbit | `orbit_bi_immune` | Universality.BiImmunity |
| Complex amplitude forcing | `complex_amplitude_forced` | Universality.ComplexAmplitudeForced |
| CMCA record filtration | (various) | Foundations.CMCARecordFiltration |
| CMCA thermodynamic bridge | (various) | Foundations.CMCAThermodynamicBridge |
| Cosmological constant bracket (Hurwitz) | (various) | Cosmology.CCBracketHurwitz |

---

## Finding More Theorems

- **Complete inventory**: `paper/ugp_lean_formalization.tex` Table 1
- **Module-level overview**: [docs/MODULES.md](MODULES.md)
- **Source**: `UgpLean/<Layer>/<Module>.lean` — all theorems, lemmas, and definitions
- **Full theorem search**: `grep -r "^theorem\|^lemma" UgpLean/ --include="*.lean" | wc -l`
