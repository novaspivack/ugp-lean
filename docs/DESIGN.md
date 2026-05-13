# ugp-lean: Design and Architecture

## Non-Circularity Contract

**RSUC must not be proved by definitions that encode the answer.**

### Rule

- **Core/** contains all predicate *definitions* (SemanticFloor, QuarterLockRigid, RelationalAnchor).
- **Compute/** contains all *algorithms* and computational evidence (sieve, `native_decide`).
- **Core/ may not import Compute/** — enforced by module structure.

### Why It Matters

If we defined `UnifiedAdmissible t := t = LeptonSeed`, RSUC would be trivial. Instead:

1. **SemanticFloor** is defined by bounds: `a ∈ {1,5,9}`, `b ≥ 40`, `c ≥ 800` — no reference to survivors.
2. **QuarterLockRigidAt n** requires `∃ b₂ q₂, isMirrorDualSurvivorAt n b₂ q₂ ∧ ...` — survivors come from a proved lemma (`ridgeSurvivors_10` at n=10), not from the predicate definition.
3. **RelationalAnchorAt n** requires `∃ b₂ q₂, isMirrorDualSurvivorAt n b₂ q₂ ∧ t.b = b₁ ∧ ...` — purely structural. At n=10 this is equivalent to `t.b=73 ∧ t.c∈{823,2137}`.

### Correctness Chain

- `isMirrorDualSurvivorAt n b₂ q₂ ↔ (b₂,q₂) ∈ ridgeSurvivorsFinset n` (`Sieve.isMirrorDualSurvivorAt_iff`)
- `ridgeSurvivors_10`: survivors = {(24,42), (42,24)}
- `RelationalAnchorAt_10_iff`: `RelationalAnchorAt 10 t ↔ RelationalAnchor t`
- `decUnifiedAdmissible_correct`: decidable version matches Prop

## Two-Theorem RSUC Architecture

| Theorem | Role |
|---------|------|
| **Theorem A** | Structural: `UnifiedAdmissible t → t ∈ Candidates`. Non-computational; shows predicates imply membership in explicit finite set. |
| **Theorem B** | Classification: `Residual = Candidates`; MDL selects LeptonSeed. Uses `native_decide` to enumerate and filter. |

**RSUC** combines both: unique residual up to `MirrorEquiv`; MDL selects (1, 73, 823).

## Proof Tactics

- **`native_decide`**: Concrete arithmetic (`ridgeSurvivors_10`, `Nat.Prime`, `Finset` equality).
- **`simp`**, **`omega`**: Case splits, inequalities.
- **`ring`**: Quarter-Lock identity and algebraic identities throughout.
- **`linarith`**: Linear reasoning in ℚ/ℝ.
- **`decide`**: Small decidable propositions (TE22 gauge-group labelling, parity checks).
- **`norm_num`**: Arithmetic ground truths (conductor values, divisibility).
- **`field_simp`**: IPT self-consistency, gauge-coupling identities.

## Bounded Certification

- `CandidatesAt n` is the `biUnion` over `ridgeSurvivorsFinset n`; at n=10, `Candidates = CandidatesAt 10` is an explicit `Finset Triple` of 6 triples.
- `Residual := Candidates.filter (fun t => decide (UnifiedAdmissible t))`.
- Equality proved by `native_decide` — no hand computation.

## Documented Axioms (outside core RSUC path)

Two theorems in `GTE.AnalyticArchitecture` are declared `axiom` (not `sorry`):

| Axiom | Lean name | Justification |
|-------|-----------|---------------|
| Dickman equidistribution in APs | `dickman_equidistribution_in_APs` | Tenenbaum III.6; pending Mathlib analytic-NT |
| CRT equidistribution within regime | `crt_equidistribution_within_regime` | Tenenbaum III.6; same dependency |

Declaring them as `axiom` rather than `sorry` makes the dependency explicit and auditable. Neither appears in the axiom closure of any physics theorem (`#print axioms` on any charged-lepton or coupling theorem reaches only `propext`, `Classical.choice`, `Quot.sound`).

## Completeness Status by Layer (as of 2026-05-12)

| Layer | Status |
|-------|--------|
| Core / Compute / Classification | ✓ Complete; 0 sorry |
| GTE orbit, UpdateMap, MersenneGcd, etc. | ✓ Complete; 0 sorry |
| GTE.AnalyticArchitecture | Two documented axioms (see above); not on physics path |
| Structural (QuarterLock, ElegantKernel) | ✓ Complete; 0 sorry |
| MassRelations (Koide, VV, CDM, CKM) | ✓ Complete; 0 sorry (one physical-bridge step open, tracked externally) |
| BraidAtlas | ✓ Complete; 0 sorry |
| GaloisStructure / CyclotomicCompleteness | ✓ Complete; 0 sorry |
| Phase4 (GaloisProtection, TwoLoopCoefficient, GaugeCouplings, …) | ✓ Complete on stated theorems; UCL/PR1 modules are informational stubs |
| TE22 (ScanCertificate) | ✓ Zero sorry; full 34,560-universe native_decide pending Fintype instance |
| Universality | ✓ **Fully proved**: UWCA sweeps Rule 110 (`uwca_sweep_implements_rule110`); Turing-universal (`ugp_is_turing_universal`); history-lane inverse (`uwca_augmented_left_inverse`) |
| SelfRef | ✓ Complete; 0 sorry |
| GTE.GTESimulation / EntropyNonMonotone (ML-9) | ✓ Complete; 0 sorry |

## What "Stub" Means in This Library

A **stub** is a Lean declaration whose statement is a genuine mathematical claim but whose proof body is `True` (placeholder) or deferred to companion work. The only active informational stubs are:

- `Phase4.UCL` — UCL formula presentation (companion algebraic derivation in ugp-physics-lean)
- `Phase4.PR1` — PR-1 table stub

These do not affect RSUC, Universality, or any physics theorem on the zero-sorry path.
