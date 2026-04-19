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
