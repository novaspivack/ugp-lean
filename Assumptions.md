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
