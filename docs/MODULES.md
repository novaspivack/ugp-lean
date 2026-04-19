# ugp-lean: Module Reference

## Dependency Rule

**Core/ may not import Compute/** — enforced to prevent circularity in RSUC.

## Module Graph (Simplified)

```
UgpLean.lean
├── Core (no Compute)
│   ├── RidgeDefs
│   ├── MirrorDefs
│   ├── TripleDefs
│   ├── SievePredicates
│   ├── Disconfirmation
│   ├── RidgeRigidity
│   └── MirrorAlgebra
├── Compute
│   ├── PrimeLock (RidgeDefs, MirrorDefs)
│   ├── Sieve (RidgeDefs, MirrorDefs, SievePredicates, PrimeLock)
│   ├── SieveExtended
│   ├── ExclusionFilters
│   └── DecidablePredicates
├── Classification
│   ├── Bounds
│   ├── TheoremA
│   ├── TheoremB
│   ├── RSUC
│   ├── FormalRSUC
│   └── MonotonicStrengthening
├── GTE
│   ├── Evolution
│   └── Orbit
├── QuarterLock, ElegantKernel
├── Phase4 (DeltaUGP, GaugeCouplings, UCL, PR1)
├── Universality (Rule110, UWCA, UWCAembedsRule110, TuringUniversal, ArchitectureBridge)
├── Papers (Paper25, UGPMain)
└── Instance (NemSBridge)
```

## Module Descriptions

### Core Layer

| Module | Purpose |
|--------|---------|
| **RidgeDefs** | Rₙ = 2ⁿ − 16, strictRidgeMin=16, UGP-1 params (s=7, g=13, t=20) |
| **MirrorDefs** | b₁=b₂+q₂+7, q₁=q₂−13, c₁=b₁q₁+20; leptonB=73, leptonC1=823, mirrorC1=2137 |
| **TripleDefs** | `Triple` structure, LeptonSeed, LeptonMirror, MirrorEquiv, lexLt |
| **SievePredicates** | SemanticFloor; QuarterLockRigidAt n, RelationalAnchorAt n, UnifiedAdmissibleAt n; legacy n=10: QuarterLockRigid, RelationalAnchor, UnifiedAdmissible |
| **Disconfirmation** | MirrorEquivClass equivalence, lexLt_seed_mirror |
| **RidgeRigidity** | Ridge remainder lock (m₂=15), quotient-gap 13 |
| **MirrorAlgebra** | mirrorS, discSq, symmetric mirror form, discriminant |

### Compute Layer

| Module | Purpose |
|--------|---------|
| **PrimeLock** | Nat.Prime 823, 2137; mirror_prime_lock; c1_from_divisor |
| **Sieve** | ridgeSurvivorsFinset, ridgeSurvivors_10 = {(24,42),(42,24)} |
| **SieveExtended** | n∈[5,30] sieve range, mirrorDualCount_10 |
| **ExclusionFilters** | exclude_16..63 — composite c₁ for listed divisors |
| **DecidablePredicates** | decUnifiedAdmissible, correctness lemmas |

### Classification Layer

| Module | Purpose |
|--------|---------|
| **Bounds** | CandidatesAt n : Finset Triple (biUnion over ridgeSurvivorsFinset n); Candidates = CandidatesAt 10 |
| **TheoremA** | theoremA_general: UnifiedAdmissibleAt n t → t ∈ CandidatesAt n; theoremA: n=10 corollary |
| **TheoremB** | ResidualAt n, Residual = ResidualAt 10; Residual = Candidates; MDL selects LeptonSeed |
| **RSUC** | rsuc_theorem (combines A + B) |
| **FormalRSUC** | rsuc_formal, rsuc_canon (two-layer RSUC with interpretation) |
| **MonotonicStrengthening** | strengthening_cannot_add_survivors |

### GTE Layer

| Module | Purpose |
|--------|---------|
| **Evolution** | fib13=233, canonicalGen2/3, canonical_orbit_triples, even_step_rigidity |
| **Orbit** | canonical_orbit_three_steps |

### Structural / Phase 4 / Universality

| Module | Purpose |
|--------|---------|
| **QuarterLock** | quarterLockLaw, kernelDefect, quarterLockStability |
| **ElegantKernel** | k_L2=7/512, L_model=log₂(2000/3) |
| **DeltaUGP** | deltaUGPFormula, leptonB_matches_deltaUGP |
| **GaugeCouplings** | g1Sq_bare, g2Sq_bare, g3Sq_bare; D₂, D₃ |
| **UCL, PR1** | Structural stubs |
| **Rule110** | rule110Output, rule110Minterms, Cook citation |
| **UWCA** | UWCATile, rule110Tiles |
| **UWCAembedsRule110** | uwca_simulates_rule110 |
| **TuringUniversal** | ugp_is_turing_universal |
| **ArchitectureBridge** | uniqueness_of_physical_program |

### Papers & Instance

| Module | Purpose |
|--------|---------|
| **Paper25** | Citable stubs for Paper 25 |
| **UGPMain** | Citable stubs for UGP Main |
| **NemSBridge** | GTESpace instance, RSUC for nems-lean |

### Mass Relations Layer (Round 12 + Rounds 13–18)

Charged-fermion mass-relation modules formalising the TT (up-to-lepton cyclotomic)
and VV (down-type rational) structural identities discovered 2026-04-19.
Hub module `MassRelations` re-exports the formulas; submodules contain the
specific theorems.  All zero-sorry; standard Mathlib axioms only.

| Module | Purpose |
|--------|---------|
| **MassRelations** | Hub: re-exports `UpLeptonFormula`, `DownRationalFormula`, `CombinedFormula`. Imports all four submodules. |
| **MassRelations.UpLeptonCyclotomic** | TT formula `log(m_{u,g}/m_{l,g}) = (π/6)·2^g + β`; three β-free inter-generational identities (Δg=1,2,3 → π/3, 2π/3, π); β candidates (π/8, 2/5, 1/φ²). |
| **MassRelations.DownRational** | VV formula `log(m_{d,g}) = (13/9)·log(m_{u,g}) + (−7/6)·log(m_{l,g}) + (−5/14)`; γ-free Δg=1 identity; combined-formula arithmetic identities. |
| **MassRelations.ClebschGordan** | GUT representation-dimension table (SU(2), SU(3), SU(5), SO(10) ranks, fundamental dims, adjoint dims, key Higgs reps). Round 12 `gut_ratio_45_over_126`. **Rounds 17–18 extension:** VV three-factor structural theorems — α (rank/d_R-channels), β (hypercharge), γ (45-in-126 subrep), shared-gcd link, packaged `VV_coefficients_rational`. |
| **MassRelations.SU3FlavorCartan** (Round 13 Phase 1) | **Claim A theorem:** angle between A_2 simple root α_1 and fundamental weight ω_1 = π/6.  Direct 2D Euclidean construction bypassing abstract Mathlib RootSystem infrastructure.  Includes chamber-interior bonus theorem. |
| **MassRelations.BinaryCascade** (Round 19 Claim B candidate) | Discrete dynamical system on ℝ implementing the binary phase cascade `state(g) = state(g-1) + 2^(g-1)·(π/6)` with initial condition `state(0) = π/6 + π/8`.  Proves closed-form `cascadeState g = (π/6)·2^g + π/8 = UpLeptonFormula g (π/8)`.  Per-step increment doubles each generation.  **Physical realisation (which UV mechanism implements the cascade) flagged as Claim C — open research.** |
| **MassRelations.FroggattNielsen** (Round 21 Claim C — first UV completion) | Concrete two-flavon Froggatt-Nielsen model realising the binary cascade.  Flavon VEVs `ε_1 = e^(−π/3)`, `ε_2 = e^(−π/8)`; FN charges with doubling pattern on lepton FN_1: `(1, 2, 4)` per generation; up-type FN_1 = `(0, 0, 0)`; constant FN_2 difference = 1.  Theorem `fnLogYukawaRatio_eq_TT` proves the FN model reproduces TT exactly; `fnLogYukawaRatio_eq_cascade` connects to the BinaryCascade module.  Open structural questions catalogued (why doubled charges? why transcendental VEVs? why two flavons?). |
