# ugp-lean: Design and Architecture

## Non-Circularity Contract

**RSUC must not be proved by definitions that encode the answer.**

### Rule

- **Core/** contains all predicate *definitions* (SemanticFloor, QuarterLockRigid, RelationalAnchor).
- **Compute/** contains all *algorithms* and computational evidence (sieve, `native_decide`).
- **Core/ may not import Compute/** — enforced by module structure.

### Why It Matters

If we defined `UnifiedAdmissible t := t = LeptonSeed`, RSUC would be trivial. Instead:

1. **SemanticFloor** is defined by bounds: a ∈ {1,5,9}, b ≥ 40, c ≥ 800 — no reference to survivors.
2. **QuarterLockRigidAt n** requires `∃ b₂ q₂, isMirrorDualSurvivorAt n b₂ q₂ ∧ ...` — survivors come from a proved lemma (`ridgeSurvivors_10` at n=10), not from the predicate definition.
3. **RelationalAnchorAt n** requires `∃ b₂ q₂, isMirrorDualSurvivorAt n b₂ q₂ ∧ t.b = b₁ ∧ ...` — purely structural. At n=10 this is equivalent to t.b=73 ∧ t.c∈{823,2137}.

### Correctness Chain

- `isMirrorDualSurvivorAt n b₂ q₂ ↔ (b₂,q₂) ∈ ridgeSurvivorsFinset n` (Sieve.isMirrorDualSurvivorAt_iff)
- `ridgeSurvivors_10`: survivors = {(24,42), (42,24)}
- `RelationalAnchorAt_10_iff`: RelationalAnchorAt 10 t ↔ RelationalAnchor t
- `decUnifiedAdmissible_correct`: decidable version matches Prop

## Two-Theorem RSUC Architecture

| Theorem | Role |
|---------|------|
| **Theorem A** | Structural: UnifiedAdmissible t → t ∈ Candidates. Non-computational; shows predicates imply membership in explicit finite set. |
| **Theorem B** | Classification: Residual = Candidates; MDL selects LeptonSeed. Uses `native_decide` to enumerate and filter. |

**RSUC** combines both: unique residual up to MirrorEquiv; MDL selects (1,73,823).

## Proof Tactics

- **native_decide**: Concrete arithmetic (ridgeSurvivors_10, Nat.Prime, Finset equality).
- **simp**, **omega**: Case splits, inequalities.
- **ring**: Quarter-Lock identity.
- **linarith**: Linear reasoning in ℚ.

## Bounded Certification

- `CandidatesAt n` is the biUnion over ridgeSurvivorsFinset n; at n=10, `Candidates = CandidatesAt 10` is an explicit `Finset Triple` of 6 triples.
- `Residual := Candidates.filter (fun t => decide (UnifiedAdmissible t))`.
- Equality proved by `native_decide` — no hand computation.

## Stubs and Deferred Work

Some modules contain **structural stubs** (Prop := True) for paper statements not fully formalized:

- **Phase4.UCL**, **Phase4.PR1**: Informational stubs
- **Universality**: Cook (2004) cited; full reduction not formalized
- **DeltaUGP**: Formula present; full Stage 2 sieve not computed

These do not affect the soundness of RSUC or the core classification.
