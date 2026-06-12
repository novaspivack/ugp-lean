# ugp-lean: Design and Architecture

## Non-Circularity Contract

**RSUC must not be proved by definitions that encode the answer.**

### Rule

- **Core/** contains all predicate *definitions* (SemanticFloor, QuarterLockRigid, RelationalAnchor).
- **Compute/** contains all *algorithms* and computational evidence (sieve, `native_decide`).
- **Core/ may not import Compute/** — enforced by module structure; `lake build` fails if violated.

### Why It Matters

If we defined `UnifiedAdmissible t := t = LeptonSeed`, RSUC would be trivial. Instead:

1. **SemanticFloor** is defined by bounds: `a ∈ {1,5,9}`, `b ≥ 40`, `c ≥ 800` — no reference to survivors.
2. **QuarterLockRigidAt n** requires `∃ b₂ q₂, isMirrorDualSurvivorAt n b₂ q₂ ∧ ...` — survivors come from a proved lemma, not the predicate definition.
3. **RelationalAnchorAt n** is purely structural. At n=10 it is equivalent to `t.b=73 ∧ t.c∈{823,2137}`.

### Correctness Chain

- `isMirrorDualSurvivorAt n b₂ q₂ ↔ (b₂,q₂) ∈ ridgeSurvivorsFinset n`
- `ridgeSurvivors_10`: survivors = {(24,42), (42,24)}
- `RelationalAnchorAt_10_iff`: `RelationalAnchorAt 10 t ↔ RelationalAnchor t`
- `decUnifiedAdmissible_correct`: decidable version matches Prop

---

## Two-Theorem RSUC Architecture

| Theorem | Role |
|---|---|
| **Theorem A** | Structural: `UnifiedAdmissible t → t ∈ Candidates`. Non-computational; shows predicates imply membership in an explicit finite set. |
| **Theorem B** | Classification: `Residual = Candidates`; MDL selects LeptonSeed. Uses `native_decide` to enumerate and filter. |

**RSUC** combines both: unique residual up to `MirrorEquiv`; MDL selects (1, 73, 823).

---

## Proof Tactics

| Tactic | Uses |
|---|---|
| `native_decide` | Concrete arithmetic (ridgeSurvivors_10, Nat.Prime, Finset equality, orbit uniqueness) |
| `decide` | Small decidable propositions (TE22 gauge-group labelling, parity checks, Z₇⁵ enumeration) |
| `simp` / `omega` | Case splits, inequalities |
| `ring` | Quarter-Lock identity and algebraic identities throughout |
| `linarith` | Linear reasoning in ℚ/ℝ |
| `norm_num` | Arithmetic ground truths (conductor values, divisibility, mass bounds) |
| `field_simp` | IPT self-consistency, gauge-coupling identities |
| `rfl` | Definitional equalities (BPS saturation, GTE compilation) |

---

## Bounded Certification

- `CandidatesAt n` is the `biUnion` over `ridgeSurvivorsFinset n`; at n=10, `Candidates = CandidatesAt 10` is an explicit `Finset Triple` of 6 triples.
- `Residual := Candidates.filter (fun t => decide (UnifiedAdmissible t))`.
- Equality proved by `native_decide` — no hand computation.

---

## Documented Axioms (not sorry; explicit dependencies)

| Axiom | Lean name | Module | Justification |
|---|---|---|---|
| A1 | `dickman_equidistribution_in_APs` | GTE.AnalyticArchitecture | Tenenbaum III.6; pending Mathlib analytic-NT |
| A2 | `crt_equidistribution_within_regime` | GTE.AnalyticArchitecture | Tenenbaum III.6 + CRT; same dependency |
| A3 | `sech_overlap_mesh_to_integral` | Substrate.SechOverlapIntegralBounds_bridge | Mesh→integral bridge (CatA, documented) |
| A4 | `sech_overlap_bridge_r5` | Substrate.SechOverlapIntegralBounds_bridge | Second mesh→integral bridge (CatA, documented) |

Declaring as `axiom` rather than `sorry` makes the dependency explicit and auditable. None of A1–A4 appear in the axiom closure of any physics or classification theorem (`#print axioms` on any core theorem reaches only `propext`, `Classical.choice`, `Quot.sound`).

---

## Remaining sorry Stubs

| Location | Count | Reason |
|---|---|---|
| `Gravity/WaldEntropy` | 3 | Pending Mathlib manifold integrals for Wald entropy formula |
| `Substrate/CogwheelDynamicsG21` | 3 | Pending Mathlib matrix-exponential API |
| `Physics/KinkPoleMassSpectralCore` | partial | Pöschl–Teller integrals, full Mathlib API deferred |
| `Physics/CCOneJumpResidual` | 1 | Computable convergence modulus deferred |

All are documented stubs outside the core proof path. None affect RSUC, universality, or any mass/coupling theorem on the zero-sorry path.

---

## Completeness Status by Layer

| Layer | Status |
|---|---|
| Core / Compute / Classification | ✓ Complete; 0 sorry |
| GTE orbit, UpdateMap, MersenneGcd | ✓ Complete; 0 sorry |
| GTE.AnalyticArchitecture | Two documented axioms (A1, A2); not on physics path |
| ElegantKernel / QuarterLock | ✓ Complete; 0 sorry |
| MassRelations (Koide, VV, CDM, CKM, PMNS, Higgs) | ✓ Complete; 0 sorry |
| BraidAtlas | ✓ Complete; 0 sorry |
| Universality (Rule 110, UWCA, GTE compilation) | ✓ Complete; 0 sorry |
| Polynomial (GF(7) explorations, spin-7, MDL unification) | ✓ Complete; 0 sorry |
| Physics (kink, Z₇ vacuum, CMCA physical point) | ✓ Complete except KinkPoleMassSpectralCore (partial) |
| Substrate (sech bounds, PhiMDL) | ✓ Complete; 0 sorry (2 CatA bridge axioms documented) |
| Gravity | ✓ Mostly complete; 3 sorry in WaldEntropy (Mathlib gap) |
| Spacetime (geodesic, mass gap, orbit hierarchy, QEC) | ✓ Complete; 0 sorry on stated theorems |
| Algebra (Z₇/F₂₁ Galois, SM gauge) | ✓ Complete; 0 sorry |
| Framework / ContinuumLimit | ✓ Complete; 0 sorry |
| QFT / VEVProof / VEVNoGo | ✓ Complete; 0 sorry |
| GaloisStructure / CyclotomicCompleteness | ✓ Complete; 0 sorry |
| Phase4 (GaloisProtection, TwoLoopCoefficient) | ✓ Complete on stated theorems; UCL/PR1 are informational stubs |
| TE22 (ScanCertificate) | ✓ Decidable fragment; full 34,560-universe scan pending Fintype |
| SelfRef | ✓ Complete; 0 sorry |

---

## What "Stub" Means

A **stub** is a declaration whose statement is a genuine mathematical claim but whose proof body is `True` or deferred to companion work. Active informational stubs:

- `Phase4.UCL` — UCL formula presentation (companion derivation in ugp-physics-lean)
- `Phase4.PR1` — PR-1 table

These do not affect any theorem on the zero-sorry path.
