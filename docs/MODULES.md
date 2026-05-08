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

### BraidAtlas Layer (P17 algebraic substrate)

| Module | Purpose |
|--------|---------|
| **ChargeTheorem** | Theorem C-W (Q = W_g/N_c); anomaly cancellation forces N_c=3; SM charge derivation; GTE-P7 mirror dark matter quantum numbers (Q=0, color singlet) |
| **CompositeTriples** | Composite c-rule; baryon (a, b, c) derivation including proton/neutron and full strange-baryon octet; meson constraints |
| **ChiralitySquaring** | Arithmetic signature of V−A chiral structure: (13×17×29)² perfect square; 17×137 not perfect square |
| **ChargeDerivation** | SM winding pattern derived from N_c; Y_QL = 1/(2N_c) unifies VV slope and braid winding |
| **CoxeterConductor** | Arithmetic backbone of the Coxeter–conductor theorem; **E7 falsifier** (h=18 ∤ 120); φ(120)=32, 3∤32; lcm(30,12,8,6,3,2,1)=120 |
| **CoxeterConductorTowerLaw** | Tower-Law step: 8X³−6X−1 irreducible over ℚ via rational-root theorem; finrank ℚ[X]/(p) = 3 (zero sorry, resolves SPEC_033_BTL) |
| **EWBosons** | Electroweak boson c-values c(W)=11, c(Z)=12, c(H)=13 derived from canonical ridge factorisation + Higgs gap identity at n=10; consecutive triple centred on 2·T(N_c); triangular-number unification |
