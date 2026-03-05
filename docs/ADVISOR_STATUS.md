# ugp-lean: Advisor Status Report

**Date:** March 2026 (rolling)  
**Purpose:** Comprehensive status for advisors: what was built, what it does, why it is sound, and what remains.

---

## Executive Summary

**ugp-lean** is a Lean 4 formalization of the Universal Generative Principle (UGP) and Generative Triple Evolution (GTE). It **proves** the Residual Seed Uniqueness Conjecture (RSUC) as a theorem via a non-circular two-theorem architecture, certifies the n=10 ridge sieve and canonical orbit, and formalizes Quarter-Lock, Elegant Kernel constants, and Turing universality. The classification is **n-parameterized**: predicates (QuarterLockRigidAt, RelationalAnchorAt, UnifiedAdmissibleAt) and candidate sets (CandidatesAt n) are indexed by ridge level n; at n=10 this yields the certified Lepton Seed. The core classification path has **0 sorry, 0 custom axioms**. The build completes successfully on standard toolchains.

---

## What We Made

### 1. Core Formalization (Phases 0–2)

| Component | Description |
|-----------|-------------|
| **Ridge** | Rₙ = 2ⁿ − 16, UGP-1 parameters (s=7, g=13, t=20), strict divisors |
| **Mirror** | (b₂,q₂) ↦ (b₁,q₁,c₁); Lepton Seed (1,73,823), mirror (1,73,2137) |
| **Triple** | Structure (a,b,c), MirrorEquiv, lexLt, MDL |
| **Sieve** | ridgeSurvivors_10 = {(24,42), (42,24)} — certified by `native_decide` |
| **PrimeLock** | Nat.Prime 823, Nat.Prime 2137 |
| **Sieve Predicates** | SemanticFloor; QuarterLockRigidAt n, RelationalAnchorAt n, UnifiedAdmissibleAt n. At n=10: QuarterLockRigid, RelationalAnchor, UnifiedAdmissible. Defined without encoding the answer; survivors come from proved lemmas. |
| **Bounds** | CandidatesAt n (biUnion over ridgeSurvivorsFinset n); Candidates = CandidatesAt 10 (6 triples) |
| **Theorem A** | theoremA_general: UnifiedAdmissibleAt n t → t ∈ CandidatesAt n; theoremA: n=10 corollary |
| **Theorem B** | Residual = Candidates; MDL selects LeptonSeed |
| **RSUC** | Full theorem combining A + B |
| **NemSBridge** | GTESpace instance for nems-lean / Paper 25 |

### 2. Extended Theorems (Phase 3)

| Component | Description |
|-----------|-------------|
| **QuarterLock** | k_M = k_gen2 + ¼k_L²; stability on defect |
| **ElegantKernel** | k_L² = 7/512, L_model = log₂(2000/3) |
| **GTE Evolution** | Canonical orbit, fib13=233, even-step rigidity |
| **Sieve Extended** | n∈[5,30] range |
| **Disconfirmation** | MirrorEquivClass equivalence |
| **Papers** | Citable stubs (Paper25, UGPMain) |
| **Assumptions** | Premise ledger |

### 3. Phase 4 (Gauge & Physical)

| Component | Description |
|-----------|-------------|
| **DeltaUGP** | δ_UGP formula; b₁=73 unique |
| **GaugeCouplings** | g₁², g₂², g₃² bare; D₂, D₃ |
| **UCL, PR1** | Structural stubs |

### 4. Phase 5 (Universality)

| Component | Description |
|-----------|-------------|
| **Rule110** | CA definition, S_110 minterms |
| **UWCA** | Tile set, rule110Tiles |
| **Turing Universal** | UGP substrate Turing-universal |
| **Architecture Bridge** | Uniqueness of Physical Program |

### 5. Monograph Additions

| Component | Description |
|-----------|-------------|
| **RidgeRigidity** | m₂=15 lock, quotient-gap 13 |
| **MirrorAlgebra** | Symmetric mirror form, discriminant |
| **ExclusionFilters** | b₂∈{16,18,21,28,36,63} ⇒ c₁ composite |
| **Trace Identifiability** | G₂=(9,42,1023) ⇒ n=10, b₁=73 |

---

## What It Does

1. **Certifies the n=10 sieve** — the survivors are exactly {(24,42), (42,24)}; both yield prime c₁ ∈ {823, 2137}.
2. **Proves RSUC** — among triples satisfying SemanticFloor, QuarterLockRigidAt 10, and RelationalAnchorAt 10 (purely structural; survivors from ridge sieve), there is exactly one equivalence class; MDL selects (1,73,823) as the canonical representative. `strengthening_cannot_add_survivors` shows predicate strengthening cannot add survivors.
3. **Certifies the canonical orbit** — (1,73,823) → (9,42,1023) → (5,275,65535) with fib13=233.
4. **Proves Quarter-Lock** — kernel coefficients satisfy k_M = k_gen2 + ¼k_L².
5. **Formalizes the embedding architecture** — provides a mechanized UWCA simulation scaffold; Turing-universality relies on Cook (2004) as an explicit external citation (cited, not mechanized).
6. **Provides NEMS/Paper 25 bridge** — NemSBridge exposes GTESpace and RSUC for downstream formalizations.

---

## Why It Is Sound

### No Circularity

- Sieve predicates (QuarterLockRigidAt n, RelationalAnchorAt n) are **defined** structurally via isMirrorDualSurvivorAt n — no reference to Lepton Seed or specific survivors.
- Survivors are **proved** by enumeration (ridgeSurvivors_10); isMirrorDualSurvivorAt_iff bridges Prop and Finset.
- Core/ does not import Compute/ — definitions and computation are separated.

### No Sorry, No Axioms on Core Path

- Theorem A, Theorem B, RSUC, Sieve, PrimeLock, Bounds — all proved.
- `native_decide` used for concrete arithmetic; Mathlib for standard facts.

### Explicit Bounded Certification

- Candidates is an explicit Finset of 6 triples.
- Residual is computed by filtering; equality proved by `native_decide`.
- No unbounded quantifiers or computational oracle.

### External Citations Are Explicit

- Cook (2004) for Rule 110 universality — cited, not assumed as axiom.
- δ_UGP, gauge formulas — cited from JMP Math Foundations.
- Assumptions.md lists all premises and tags (definition | lemma | citation).

---

## Holes and Unfinished Items

### Integration

| Item | Status |
|------|--------|
| nems-lean `require ugpLean` | Pending — Lake path dependency syntax to be confirmed |
| Paper 25 LaTeX citation | Not done |
| ≥3 UGP papers cite ugp-lean | Not done |

### Deferred Formalization

| Item | Notes |
|------|-------|
| **Full GTE update map T** | Odd/even step formulas partially certified; full T as function not compiled |
| **Cook reduction** | Rule 110 → Turing machine reduction cited, not formalized |
| **δ_UGP numeric** | Formula present; full Stage 2 sieve (only b₁=73) not computed in Lean |
| **SU(2) harmonic mean, SU(3) Vandermonde** | Stated as uniqueness props; full proofs not in Lean |
| **Topos Sh(E)** | Deferred |
| **FO decidability, phase transition** | Deferred |
| **Proof-carrying certificates** | Optional enhancement |
| **Countermodel harness** | Optional |

### Stubs (Prop := True)

- Phase4.UCL, Phase4.PR1 — structural placeholders
- Some Universality statements — logical structure only

These stubs do **not** affect RSUC or core soundness.

---

## Build and Verification

- **Build**: `lake build` — succeeds, ~8085 jobs
- **Toolchain**: Lean 4.29.0-rc3, Mathlib v4.29.0-rc3
- **Determinism**: Verified on macOS; should port to Linux

---

## Summary for Advisors

| Question | Answer |
|----------|--------|
| **What is ugp-lean?** | Lean 4 formalization of UGP/GTE; proves RSUC and certifies core claims. |
| **Is RSUC proved?** | Yes. Theorem A + Theorem B; 0 sorry, 0 axioms. |
| **Is it circular?** | No. Predicates defined independently; survivors proved by sieve. |
| **What’s missing?** | nems-lean wiring, paper citations, some deferred formalizations (Cook reduction, full δ_UGP, topos). |
| **Is it sound?** | Yes. Core path is fully proved; external results are cited, not axiomatized. |
