# ugp-lean: Theorem Highlights

**This is a curated selection of the most important theorems by layer.** It is not exhaustive — the library contains thousands of theorems across 436 modules. For the complete inventory, see `paper/ugp_lean_formalization.tex` (Table 1) and browse the source in `UgpLean/`.

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
| Cook operational Stage 3 TM-microstep readback (5 named bridge axioms; conditional certificate for already-supplied compilations, not itself a Turing-universality theorem) ⚠ | `cook_operational_stage3_tm_microstep_readback` (formerly `rule110_turing_universal_from_cook`) | rule110-lean (`CookUniversalityTop`) |
| Rule 110 at center-1 realizes any finite 2-input Boolean function (Sheffer 1913; not Turing universality) | `rule110_center1_is_nand`, `z7_bool3_finite_functional_completeness` | Universality.PhiMDLUniversality |
| Minsky two-counter machines simulate every computable function (1 named axiom) ⚠ | `counter_machine_simulates_computable` | Universality.RegisterMachine |
| UWCA CRT register file simulates counter machines (zero sorry) | `uwca_substrate_simulates_computable` | Universality.UWCARegisterUniversality |
| $k$ UWCA sweeps = $k$ Rule 110 steps (zero sorry, zero axioms) | `uwca_rounds_C_eq_ringRule110` | Universality.UWCARegisterSweep |
| Cook operational universality composed with TM compilation (1 named axiom) ⚠ | `cook_rule110_simulates_computable` | Universality.CookComputableBridge |
| $\Phi_{\rm MDL}$ is Turing-universal (Cook route, 1 named axiom) ⚠ | `phimdl_turing_universal` | Universality.PhiMDLUniversality |
| **UGP substrate is Turing-universal** (register-machine route, 1 named axiom) ⚠ | `ugp_is_turing_universal` | Universality.TuringUniversal |
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
| M_W^GTE = 80364 MeV in PDG band (80351, 80377) | `m_W_pdg_interval` | Universality.EWBosonNumericalCerts |
| M_Z^GTE = M_W·√(13/10) (Weinberg identity) | `m_Z_gte_from_weinberg` | Universality.EWBosonNumericalCerts |
| M_Z^GTE(tree) ∈ (91600, 91660) MeV | `m_Z_pdg_interval` | Universality.EWBosonNumericalCerts |
| sin²θ_W(2-loop) ∈ (0.23128, 0.23131) | `sin2_theta_W_threshold_interval` | Universality.EWBosonNumericalCerts |
| M_Z^GTE(ρ̂-corrected, GTE m_t=172610 MeV) ∈ (91190, 91220) MeV | `m_Z_rho_corrected_interval` | Universality.EWRhoCorrectedMZ |

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
| **Classical cosmological constant is zero (V(0)=0 at Z₇ vacuum)** | **`classical_lambda_zero`** | **Gravity.ClassicalLambda** |
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

## Archival Identity and Structural Classification

| Theorem | Lean name | Module |
|---|---|---|
| b₁ = 2^φ(7) + N_gen² (φ(7) route to lepton seed) | `b1_totient7_ngen_identity` | Universality.AlphaEMArchivalIdentities |
| b₁ + 1/α_em = primorial(7) = 210 | `primorial7_alpha_b1_identity` | Universality.AlphaEMArchivalIdentities |
| Two routes to 1/α_em are equivalent: 2×73−9 = 2⁷+9 | `alpha_inv_routes_equivalent` | Universality.AlphaEMArchivalIdentities |
| URC scale: 200 = 2³×5² (GTE structural identification) | `urc_scale_200_gte_identity` | Universality.AlphaEMArchivalIdentities |
| ord₇(2) = N_gen = 3 (color subgroup order) | `ord7_2_eq_ngen` | Universality.Phi7UnificationTheorem |
| φ(7) = 2 × N_gen = 6 | `phi7_eq_two_ngen` | Universality.Phi7UnificationTheorem |
| φ(7) unification: b₁, b₂, α_em as corollaries of \|GF(7)*\| = 2N_gen | `phi7_structural_unification_theorem` | Universality.Phi7UnificationTheorem |
| φ(7) = 6 uniquely among primes (null test) | `phi7_uniqueness_among_primes` | Universality.Phi7UnificationTheorem |
| Electron triple is unique lepton with Möbius product +1 | `electron_triple_mobius_unique_lepton` | GTE.MobiusTripleClassification |
| Lepton c-values ≡ 7 (mod 8): {823, 1023, 65535} | `lepton_c_values_mod8_seven` | GTE.MobiusTripleClassification |
| Electron triple (1,73,823): all three components squarefree | `electron_all_squarefree` | GTE.MobiusTripleClassification |
| Bottom quark triple (5,8191,65535): all three squarefree | `bottom_all_squarefree` | GTE.MobiusTripleClassification |
| Electron and bottom are the unique all-squarefree fermion pair | `fermion_triples_all_squarefree_pair` | GTE.MobiusTripleClassification |
| b₂ = φ(7) × 7 = 42 (group-order identity) | `b2_equals_phi7_times_7` | GTE.MobiusTripleClassification |
| b₂ divides ridge R₁₀ (ridge divisibility) | `b2_phi7_divides_ridge` | GTE.MobiusTripleClassification |
| c₁ = 823 is prime (MDL minimality argument) | `c1_prime` | GTE.MobiusTripleClassification |
| GTE polynomial Lipschitz constant = 3 over GF(7) symmetric metric | `gte_lipschitz_constant_eq_3` | GTE.PolynomialLipschitz |
| Bilinear-D unitarity obstruction: row sum zero for any unitary U | `bduo_row_sum_zero` | QM.BilinearNeutrinoNoGo |
| Unitarity forces interference matrix to be singular | `bduo_interference_sum_zero` | QM.BilinearNeutrinoNoGo |
| Unitary conjugation preserves trace | `trace_invariant_under_unitary` | QM.KahlerStateManifold |
| Unitary conjugation preserves density matrix condition | `unitary_preserves_density_matrix` | QM.KahlerStateManifold |
| GTE state manifold is Kähler (CatAD; Mathlib blocker) | `gte_state_space_kaehler_property` | QM.KahlerStateManifold |
| Pure-state bipartite entanglement: rank-one projector with unit trace | `pure_state_bipartite_rank_one` | Spacetime.EntanglementAreaLaw |
| Wald entropy cross-reference to WaldEntropy.lean | `bekenstein_hawking_wald_crossref` | Spacetime.EntanglementAreaLaw |
| Minkowski metric ≠ Euclidean (indefinite signature certified) | `minkowski_has_indefinite_signature` | Spacetime.LorentzianCausalityNecessity |
| Minkowski supports causal cone (timelike and spacelike sectors) | `minkowski_supports_causal_cone` | Spacetime.LorentzianCausalityNecessity |
| PSC → Lorentzian signature (CatAD; PDE Mathlib blocker) | `lorentzian_sig_from_causal_propagation` | Spacetime.LorentzianCausalityNecessity |
| IMT gen-1/phase pair: g₁ + 2w_phase = 2^N_fam − π/2^n_ridge (e cancels) | `imt_gen1_phase_structural_pair` | Universality.IMTStructuralPair |
| IMT binding weight: w_bind = −1/(4×11) − 1/2^11 | `imt_binding_weight_structural` | Universality.IMTStructuralPair |

---

## Octonion Certificate Cluster (QR(7) → G₂ → Spin(8) triality)

All modules in this cluster: zero sorry, zero custom axioms.

### OctonionShadowInterface

| Theorem | Lean name | Module |
|---|---|---|
| UGP `weights` IS the octonion difference set QR(7) = {1,2,4} | `weights_eq_D` | Algebra.OctonionShadowInterface |
| QR(7) is a (7,3,1) difference set: all nonzero differences appear exactly once | `qr7_is_difference_set` | Algebra.OctonionShadowInterface |
| Exactly 3 Fano lines through each point (pencil count = N_c) | `pencil_count_eq_three` | Algebra.OctonionShadowInterface |
| F₂₁ translation preserves the oriented octonion product | `translation_preserves_oriented_product` | Algebra.OctonionShadowInterface |
| F₂₁ doubling (ℤ₃) preserves the oriented octonion product | `doubling_preserves_oriented_product` | Algebra.OctonionShadowInterface |
| UGP ℤ₃ = cyclic color rotation cycles the pencil ladder pairs (1,3)→(2,6)→(4,5) | `z3_cycles_pencil_ladder_pairs` | Algebra.OctonionShadowInterface |
| 6 pairwise weight differences = 6 nonzero residues (λ=1): all distinct gluon vectors | `weight_differences_all_nonzero` | Algebra.OctonionShadowInterface |
| Pencil cardinality = 3 = N_c (not an independent input) | `pencil_card_eq_Nc` | Algebra.OctonionShadowInterface |

### HurwitzCosetCertificate

| Theorem | Lean name | Module |
|---|---|---|
| permA is an involution on 168 cosets | `permA_involution` | Algebra.HurwitzCosetCertificate |
| permB has order 3 | `permB_order_three` | Algebra.HurwitzCosetCertificate |
| **\|⟨a,b \| a², b³, (ab)⁷, [a,b]⁴⟩\| = 168** (Hurwitz presentation) | `hurwitz_group_order_168` | Algebra.HurwitzCosetCertificate |

### G2StabilizerCertificate

| Theorem | Lean name | Module |
|---|---|---|
| **Derivation algebra dimension exactly 14** (Bareiss rank, zero sorry) | `derivation_dimension_exactly_14` | Algebra.G2StabilizerCertificate |
| Apex stabilizer (D(e₀)=0) dimension exactly 8 | `stabilizer_dimension_exactly_8` | Algebra.G2StabilizerCertificate |
| 14 derivation witnesses satisfy the Leibniz rule on all 64 basis pairs | `derivation_witnesses_valid` | Algebra.G2StabilizerCertificate |
| 14×14 Bareiss determinant ≠ 0: witness set is linearly independent | `derivation_witnesses_independent` | Algebra.G2StabilizerCertificate |
| 50×50 rank minor ≠ 0: nullspace dimension exactly 14 | `derivation_nullspace_rank` | Algebra.G2StabilizerCertificate |
| All 91 commutators [Dᵢ,Dⱼ] equal certified linear combinations of the basis | `derivation_bracket_closed` | Algebra.G2StabilizerCertificate |
| **Killing form negative definite** (Sylvester, all principal minors positive, Bareiss) | `derivation_killing_negative_definite` | Algebra.G2StabilizerCertificate |
| Centralizer rank bound: dim centralizer(x) ≤ 2 for generic element x (excludes rank-4 alternative) | `centralizer_dim_bound` | Algebra.G2StabilizerCertificate |

### TrialityInterface (Theorems G1–G6)

| Theorem | Lean name | Module |
|---|---|---|
| **G1**: Z(Spin(8)) = V₄ (Klein four-group); 4 scalar-related patterns certified | `G1_klein_center_card` | Algebra.TrialityInterface |
| **G2**: Triality ρ acts as a 3-cycle on {V, S⁺, S⁻} | `G2_rho_triality_action` | Algebra.TrialityInterface |
| **G3**: σ swaps S⁺ and S⁻ (outer involution), fixes V | `G3_sigma_swaps_spinors` | Algebra.TrialityInterface |
| **G4**: gen₁ ↔ V slot pinning (Eisenstein selection) | `G4_gen1_vector_slot_pinning` | Algebra.TrialityInterface |
| **G5**: gen₂ and gen₃ occupy the two spinor slots S⁺ and S⁻ | `G5_gen23_spinor_slots` | Algebra.TrialityInterface |
| **G6**: S₃ = ⟨ρ,σ⟩ acts faithfully on the 3-element generation set | `G6_triality_s3_action_faithful` | Algebra.TrialityInterface |

### OctonionColorFlavorDisambiguation

| Theorem | Lean name | Module |
|---|---|---|
| Color Z₃ (×2 on ℤ₇) acts on Fano points; flavor Z₃ (θ↦θ+2π/3) acts on Koide cone | `color_action_on_fano_points`, `flavor_action_on_koide_phase` | Algebra.OctonionColorFlavorDisambiguation |
| **Color and flavor Z₃ are not formally identified** (no import relation) | `color_action_not_flavor_action` | Algebra.OctonionColorFlavorDisambiguation |
| Color Z₃ order 3 on ℤ₇ (certified) | `color_z3_order_three` | Algebra.OctonionColorFlavorDisambiguation |
| Inner/outer split master: color = inner G₂, flavor = outer triality | `z3_disambig_master` | Algebra.OctonionColorFlavorDisambiguation |

### KinkSigmaParityAction

| Theorem | Lean name | Module |
|---|---|---|
| σ swaps Q_φ=4 and Q_φ=3 kink labels (ℤ₇ charge conjugation) | `sigma_swaps_q4_q3` | Algebra.KinkSigmaParityAction |
| σ action not realized by any non-identity Aut(F₂₁) element | `sigma_not_f21_automorphism` | Algebra.KinkSigmaParityAction |
| Kink sigma parity master bundle | `kink_sigma_parity_master` | Algebra.KinkSigmaParityAction |

### KinkSectorTrialityAction

| Theorem | Lean name | Module |
|---|---|---|
| S₃ acts faithfully on {gen₁, gen₂, gen₃} as degree-3 permutation rep | `s3_acts_faithfully_on_generation_sectors` | Algebra.KinkSectorTrialityAction |
| ρ acts as the 3-cycle gen₁→gen₂→gen₃→gen₁ | `rho_triality_on_sectors` | Algebra.KinkSectorTrialityAction |
| σ acts as the transposition gen₂↔gen₃ | `sigma_triality_on_sectors` | Algebra.KinkSectorTrialityAction |

### PhiMDLZeroModeIndex

| Theorem | Lean name | Module |
|---|---|---|
| cos(7φₖ) = 1 at every Z₇ vacuum φₖ = 2πk/7 | `cosine_yukawa_equals_one_at_vacua` | Spacetime.PhiMDLZeroModeIndex |
| Dirac mass g·cos(7φ) = g at all Z₇ vacua (same sign at both kink ends) | `cosine_yukawa_equals_g_at_all_vacua` | Spacetime.PhiMDLZeroModeIndex |
| **Callias index vanishes for Z₇-periodic cosine Yukawa** (Case A, zero sorry) | `callias_index_vanishes` | Spacetime.PhiMDLZeroModeIndex |

### BraidAtlasPhaseEquivariance

| Theorem | Lean name | Module |
|---|---|---|
| σ maps the fermionic sector (Q_φ=4, phase −1) to the bosonic W⁺ sector (Q_φ=3, phase +1) | `sigma_maps_fermion_to_boson` | Algebra.BraidAtlasPhaseEquivariance |
| Exchange phase not equivariant under S₃ (non-equivariance certified) | `braid_phase_not_s3_equivariant` | Algebra.BraidAtlasPhaseEquivariance |
| **Phase structure carries ℤ₂ = {e, σρ²} but no larger proper subgroup of S₃** | `braid_phase_z2_but_not_s3` | Algebra.BraidAtlasPhaseEquivariance |

### SeesawTrialityPinning

| Theorem | Lean name | Module |
|---|---|---|
| RH braid seeds: b_{R,1}=5, b_{R,2}=11, b_{R,3}=19 | `b_R1_eq_5`, `b_R2_eq_11`, `b_R3_eq_19` | MassRelations.SeesawTrialityPinning |
| Strict seed ordering 5 < 11 < 19 | `seed_ordering_strict` | MassRelations.SeesawTrialityPinning |
| **b_{R,3}=19 is the unique Eisenstein norm** among {5,11,19} | `b_R3_unique_eisenstein_norm` | MassRelations.SeesawTrialityPinning |
| 5 and 11 are not Eisenstein norms | `b_R1_not_eisenstein`, `b_R2_not_eisenstein` | MassRelations.SeesawTrialityPinning |
| Seesaw map m(b)=C·b^{29/9} is strictly monotone for C>0 | `seesaw_map_strict_monotone` | MassRelations.SeesawTrialityPinning |
| **Normal mass ordering m_{ν,1} < m_{ν,2} < m_{ν,3}** conditional on corpus seesaw formula | `normal_ordering_from_seeds` | MassRelations.SeesawTrialityPinning |

---

### PhiMDLFockSpaceParticles

| Theorem | Lean name | Module |
|---|---|---|
| Every PSC-admissible Z₇ sector {0,2,3,4,6} has a normalizable one-particle Fock-sector state | `psc_admissible_sector_has_normalizable_fock_state` | Universality.PhiMDLFockSpaceParticles |
| Fock lift realizes the Algebraic Lifting Theorem's physical realization for every [D]-weighted beable | `fock_state_realizes_algebraic_lifting` | Universality.PhiMDLFockSpaceParticles |
| Each GTE kink-mode Fock one-particle state carries the certified (Q_Φ, Q_χ) pair | `kink_mode_fock_carries_certified_quantum_numbers` | Universality.PhiMDLFockSpaceParticles |
| The four canonical PSC-orbit beables (vacuum, gen₁, gen₂, gen₃) each have a normalized Fock-sector lift | `psc_admissible_beable_has_normalized_fock_lift` | Universality.PhiMDLFockSpaceParticles |
| **Master bundle**: sector totality + beable lift + algebraic-Fock-only construction + gen₁ mass/stability + three-generation mass ordering | `phimdl_fock_particle_master_bundle` | Universality.PhiMDLFockSpaceParticles |

Physical meaning: Φ_MDL particles are second-quantized Fock-space excitations within
topological superselection sectors, certified by an extended (never spatially-compact)
classical background — the Fock-space realization the Algebraic Lifting Theorem
(`Spacetime.LiftingTheorem`) promises. Zero sorry, zero new axioms.

---

## Finding More Theorems

- **Complete inventory**: `paper/ugp_lean_formalization.tex` Table 1
- **Module-level overview**: [docs/MODULES.md](MODULES.md)
- **Source**: `UgpLean/<Layer>/<Module>.lean` — all theorems, lemmas, and definitions
- **Full theorem search**: `grep -r "^theorem\|^lemma" UgpLean/ --include="*.lean" | wc -l`
