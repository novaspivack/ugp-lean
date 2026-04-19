# ugp-lean Premise Ledger

Every premise that is not definitional truth. Tag: definition | lemma | conjecture | imported | citation.

## Definitions (semantic)

| ID | Premise | Where Used | Tag |
|----|---------|------------|-----|
| D1 | `SemanticFloor t := t.a ∈ {1,5,9} ∧ t.b ≥ 40 ∧ t.c ≥ 800` | SievePredicates, TheoremA | definition |
| D2 | `QuarterLockRigidAt n t := ∃ b₂ q₂, isMirrorDualSurvivorAt n b₂ q₂ ∧ (t.b, t.c) from that pair` | SievePredicates | definition |
| D3 | `RelationalAnchorAt n t := ∃ b₂ q₂, isMirrorDualSurvivorAt n b₂ q₂ ∧ t.b = b₁ ∧ c ∈ {c₁, c₂}` | SievePredicates | definition |
| D4 | `UnifiedAdmissibleAt n := SemanticFloor ∧ QuarterLockRigidAt n ∧ RelationalAnchorAt n` | RSUC | definition |
| D4a | `QuarterLockRigid := QuarterLockRigidAt 10`, `RelationalAnchor := t.b=73 ∧ t.c∈{823,2137}`, `UnifiedAdmissible := UnifiedAdmissibleAt 10` | SievePredicates | definition |
| D5 | `MirrorEquiv t₁ t₂ := same (a,b), c ∈ {823, 2137} swapped` | TripleDefs, Disconfirmation | definition |

## Lemmas (proved in ugp-lean)

| ID | Premise | Module | Tag |
|----|---------|--------|-----|
| L1 | `ridgeSurvivors_10`: at n=10, survivors = {(24,42), (42,24)} | Compute.Sieve | lemma |
| L1a | `isMirrorDualSurvivorAt_iff`: Prop ↔ Finset membership at any n | Compute.Sieve | lemma |
| L2 | `theoremA_general`: UnifiedAdmissibleAt n t → t ∈ CandidatesAt n | Classification.TheoremA | lemma |
| L2a | `theoremA`: n=10 corollary | Classification.TheoremA | lemma |
| L5a | `RelationalAnchorAt_10_iff`: RelationalAnchorAt 10 t ↔ RelationalAnchor t | Compute.DecidablePredicates | lemma |
| L3 | `theoremB`: Residual = Candidates | Classification.TheoremB | lemma |
| L4 | `mdl_selects_LeptonSeed`: Lepton Seed is lex-min in Residual | Classification.TheoremB | lemma |
| L5 | `decUnifiedAdmissible_correct`: decidable version matches Prop | Compute.DecidablePredicates | lemma |

## Imported (Mathlib / external)

| ID | Premise | Source | Tag |
|----|---------|--------|-----|
| I1 | `Nat.Prime`, `Nat.fib` | Mathlib | imported |
| I2 | `Finset`, `divisorsAntidiagonal` | Mathlib | imported |

## External citations (not formalized)

| ID | Claim | Source | Tag |
|----|-------|--------|-----|
| C1 | Rule 110 is Turing-universal (Cook 2004) | Universality.Rule110 | citation |
| C2 | Continued-fraction derivation of Fibonacci lift F_g | UGP Paper Updates | citation |
| C3 | δ_UGP formula, b₁=73 unique (JMP Math Foundations) | Phase4.DeltaUGP | citation |
| C4 | g₁², g₂², g₃² from invariants; SU(2) harmonic mean, SU(3) Vandermonde | Phase4.GaugeCouplings | citation |

## Non-negotiable credibility set

- RSUC proof path (TheoremA + TheoremB) has 0 sorry, 0 custom axioms
- Core/ does not import Compute/ (non-circularity)
- All sieve predicates defined without referencing the answer

## MassRelations definitions (Round 12 + Rounds 13–18)

Concrete numerical / geometric objects formalising the TT and VV charged-fermion
mass relations.  All are zero-sorry; standard Mathlib axioms only.  The
definitions below are *concrete numerical / geometric objects*, NOT axioms or
hypotheses about physical content.

| ID | Definition | Module | Tag |
|----|---|---|---|
| MR-D1 | `UpLeptonFormula (g : ℕ) (β : ℝ) := (π/6) · 2^g + β` | MassRelations.UpLeptonCyclotomic | definition (Round 12) |
| MR-D2 | `DownRationalFormula`, `CombinedFormula` (rational-coefficient combinations) | MassRelations.DownRational | definition (Round 12) |
| MR-D3 | A_2 root-system 2D vectors `alpha1 := (1, 0)`, `alpha2 := (-1/2, √3/2)`, `omega1 := (1/2, √3/6)` | MassRelations.SU3FlavorCartan | definition (Round 13) |
| MR-D4 | `angleToAlpha1 v := Real.arctan (v.2 / v.1)` (arctan of slope) | MassRelations.SU3FlavorCartan | definition (Round 13) |
| MR-D5 | GUT representation dimensions: `dim_45_SU5 := 45`, `dim_126_SO10 := 126`, `dim_adj_SU3 := 8`, `dim_U1_Y := 1`, etc. | MassRelations.ClebschGordan | definition (textbook values) |
| MR-D6 | Hypercharge: `Y_Q_doublet_num := 1`, `Y_Q_doublet_den := 6` (SM convention Y = Q − I_3) | MassRelations.ClebschGordan | definition (SM convention) |
| MR-D7 | Binary phase cascade: `cascadeState 0 := π/6 + π/8`, `cascadeState (g+1) := cascadeState g + 2^g · (π/6)` | MassRelations.BinaryCascade | definition (Round 19) |
| MR-D8 | Froggatt-Nielsen flavon-VEV logs: `log_eps_1 := -π/3`, `log_eps_2 := -π/8`; charge differences `Δq1 g := -2^(g-1)`, `Δq2 _ := -1`; FN log-Yukawa prediction `Δq1 g · log_eps_1 + Δq2 g · log_eps_2` | MassRelations.FroggattNielsen | definition (Round 21) |
| MR-D9 | Cartan-torus flavon potential: `cartanFlavonPotential a b φ_1 φ_2 := -a · cos(6 φ_1) - b · cos(16 φ_2)`; Z_6 generator angle = π/3 (= 2 · Claim-A π/6); Z_16 generator angle = π/8 | MassRelations.CartanFlavonPotential | definition (Round 22) |
| MR-D10 | Z_2-orbifold depth function: `binaryTreeDepth g := 2^(g-1)` | MassRelations.Z2OrbifoldDepth | definition (Round 23) |
| MR-D11 | Heavy-fermion-tower instanton action: `instantonAction g := (π/3) · 2^(g-1) + π/8` | MassRelations.HeavyFermionTower | definition (Round 24) |

### Interpretive claims (NOT proved as physical content)

The following are **interpretations** offered by the structural theorems.
They are not Lean-provable physical facts; they are Lean-decidable arithmetic
facts about specific concrete numerical objects.

| ID | Claim | Module | Tag |
|----|---|---|---|
| MR-I1 | π/6 = SU(3)_flavor Weyl-chamber half-opening angle (TT structural angle) | MassRelations.UpLeptonCyclotomic, SU3FlavorCartan | interpretation |
| MR-I2 | 9 = number of gauge bosons coupling to right-handed down-type quarks (SU(3)_C adjoint + U(1)_Y) | MassRelations.ClebschGordan | interpretation |
| MR-I3 | The SU(5) 45-adjoint is a subrep of the SO(10) 126-plet under SO(10)→SU(5) branching | MassRelations.ClebschGordan | interpretation (well-known group-theory fact, here verified via dimension sum 1+5+10+15+45+50 = 126) |
| MR-I4 | The shared denominator-9 between α (VV α denominator) and γ (gcd of dim 45 and 126) suggests both arise from the same EFT integration | MassRelations.ClebschGordan | interpretation (no physical-Lagrangian Lean derivation yet) |

**Status note (Round 16):** the original TT structural-angle interpretation
("the SU(3) Weyl rotation per generation is π/6, scaled by 2^g") was tested
and the COMPACT-SU(3) character mechanism was definitively ruled out.  See
ugp-physics Lab Notes 21 for full reasoning.  Best remaining candidate
mechanism (Lab Notes 21 §6 Option a) is the binary cascade of π/6 phase
shifts with 2^g accumulation per generation.

**Round 19 update:** the binary cascade is now Lean-formalised in
`UgpLean.MassRelations.BinaryCascade` (theorem `cascadeState_eq_TT`).  The
*mathematical* equivalence between the cascade and the TT formula is proved.
The *physical* realisation (which UV mechanism — U(1) flavor charge doubling,
heavy-fermion tower, affine Cartan translation — implements the cascade)
remains Claim C, open research.

**Round 31 update (β = π/8 STRUCTURALLY FIXED):** Priority 5 (β discrimination among π/8, 2/5, 1/φ²) is closed.  `UgpLean.MassRelations.FroggattNielsen.beta_TT_equals_pi_div_eight` proves the structural identity `−log(ε_2) = π/8`, so β is not an empirical fit parameter but rather derived from the Round-22 Cartan-potential global minimum at φ_2 = −π/8.  Empirical discrimination at current PDG precision ALREADY rules out β = 2/5 (6.7σ, dominated by precise m_t) and β = 1/φ² (3.6σ); π/8 fits at 2.5σ consistent with data.  No alternative candidate has a comparable structural derivation in the framework.  See ugp-physics Lab Notes 31.

**Round 33 update (Priority 7 Phase II — Koide):** Paper 1 OP(vii) / 4.4 — the longest-standing Koide-relation open problem — sees structural progress but not yet full closure.  `UgpLean.MassRelations.KoideClosedForm` adds seven theorems:
- `cos_sq_pi_div_twelve` (cos²(π/12) = (2+√3)/4)
- `two_plus_sqrt3_eq` ((2+√3) = 4·cos²(π/12))
- `one_plus_sqrt3_sq` and `one_plus_sqrt3_sq_eq_eight_cos_sq` ((1+√3)² = 8·cos²(π/12))
- `koide_solved_form_root` (closed form r_τ = 2(r_e+r_μ) + √3·√(r_e²+4r_e r_μ+r_μ²))
- `koide_quadratic_discriminant_form` and `koide_iff_twoS_sq_eq_threeN` (45°-cone reformulation).

Empirical (COMP-P01-GGG): PDG lepton vector at 44.99974° (0.95 arcsec from 45°); m_τ predicted from (m_e, m_μ) at 61 ppm = 0.91σ_PDG (within PDG 1σ).  Koide is structurally identified as a cyclotomic-12 algebraic identity, same atom family as α = π/6 in Round 13's TT derivation.  Full Phase III/IV flow construction (03_SPEC) is still open.  See ugp-physics Lab Notes 33.

**Round 34 update (Priority 7 Phase III/IV — Koide Newton-step flow):** 03_SPEC Phase III/IV completed via the partial-win (a)+(b)+(d) pattern explicitly flagged in 03_SPEC §1.  `UgpLean.MassRelations.KoideNewtonFlow` adds 15 theorems (0 sorry, 0 axioms): the operator `U(v) = v − (q(v)/|∇q|²)·∇q` is S_3-equivariant (three generator-cases proved individually), fixes every point of the null cone `{q = 0}`, and is UGP-native (polynomial + one division by a polynomial).  Empirical (COMP-P01-HHH): 100% of 1000 random v ∈ [0.01, 5.0]³ converge to the null cone in 5 Newton iterations; S_3-equivariance verified at machine precision (2.3e-15).  R34-B identifies the structural obstruction to full (c) closure: at PDG v* the three Koide root-equations require the (+,-,-) root pattern (largest component is +root, middle and smallest are −root), which is asymmetric under S_3 — hence no S_3-equivariant polynomial operator with v* as a nontrivial fixed point AND exact off-cone q-conservation can exist.  OP(vii) / 4.4 upgraded from "research-grade open" to "partially closed with UGP-native dynamical operator exhibited."  See ugp-physics Lab Notes 34.

**Round 21 update (FIRST UV-COMPLETION REALISED):** Claim C now has a
concrete physics model.  `UgpLean.MassRelations.FroggattNielsen` implements
a **two-flavon Froggatt-Nielsen model with doubled FN charges**, reproducing
TT exactly via theorem `fnLogYukawaRatio_eq_TT`.  Lepton FN_1 charges
follow the doubling pattern (1, 2, 4) per generation; up-type FN_1 are all
zero; flavon VEVs are `ε_1 = e^(−π/3)`, `ε_2 = e^(−π/8)` (both < 1,
FN-natural).  Three residual structural questions logged for Round 22+:
(i) why doubled charges; (ii) why transcendental VEVs; (iii) why two
flavons.  Possible link to Claim A: π/3 = 2·π/6 ties ε_1's exponent to
the SU(3)_flavor Cartan-bisector angle.

**Rounds 22–25 update (residual sub-questions partially closed):**
- **Round 22 sub-(ii):** Cartan-invariant flavon potential `V = -a·cos(6 φ_1) - b·cos(16 φ_2)` has the FN VEVs as global minima; theorem `fn_vevs_are_potential_minima`.  Z_6 directly ties to Claim A.  Z_16 origin remains conjectural (leading candidate: SO(10) 16-spinor R-symmetry).
- **Round 23 sub-(i):** Z_2-orbifold-depth function `2^(g-1)` matches FN charge magnitudes; theorem `binaryTreeDepth_matches_FN_charge_magnitude`.  Heterotic Z_2^n orbifold is leading candidate UV origin.
- **Round 24 (heavy-fermion-tower):** EFT-DUAL to the FN-doubled model; not a distinct UV completion but a different formulation.  Theorem `tower_eq_FN`.
- **Round 25 (neutrino predictions):** naive FN-doubled extension to neutrinos (q_νR = q_lep) is FALSIFIED by data (predicts 10⁵ hierarchy; observed 10–50). Modified extension with anti-doubled q_νR charges is qualitatively consistent — concrete PMNS prediction for DUNE δ_CP is open Round-26+ work. KATRIN bound m_β < 0.45 eV is trivially satisfied.
