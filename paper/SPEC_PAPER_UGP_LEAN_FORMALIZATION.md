# SPEC — ugp-lean Formalization Paper (arXiv)

**Target:** arXiv cs.LO (Logic in Computer Science) with cross-list math.LO  
**Format:** LaTeX, ~12–16 pages  
**Paper directory:** `/Users/nova/ugp-lean/paper/`  
**Main file:** `paper/ugp_lean_formalization.tex`  
**Artifact:** https://github.com/novaspivack/ugp-lean  
**Status:** IN-PROCESS

---

## Working Title

**ugp-lean: A Machine-Checked Formalization of the Universal Generative Principle**

*Subtitle candidate:* "Lean 4 Formalization of a Number-Theoretic Framework for Physics"

---

## Abstract (draft)

We present **ugp-lean**, a Lean 4 formalization of the Universal Generative Principle (UGP),
a deterministic arithmetic framework proposed as a foundation for generating structured universes.
The formalization covers the complete mathematical content of the UGP paper: the ridge sieve,
prime-lock criterion, Residual Seed Uniqueness Conjecture (RSUC), Quarter-Lock symmetry,
GTE canonical orbit, UWCA Turing universality, and a suite of new general-level theorems
not explicitly stated in the paper. The artifact comprises 43 Lean modules, 8106 build jobs,
and maintains a strict zero-sorry, zero-custom-axiom policy throughout. Novel contributions
include: a machine-checked proof that the GTE update map T forces the canonical orbit
(rather than postulating it), a general ridge remainder lock theorem for all n ≥ 5,
an even-step c-invariance theorem clarifying the paper's illustrative figure, and a precise
formal statement of the mirror-dual conjecture with computational evidence. The self-reference
theorems (Lawvere fixed-point, Kleene recursion, Rice's theorem) are imported from companion
Lean libraries. All open conjectures from the paper are formally stated as Lean propositions.

---

## Sections

### 1. Introduction (~1.5 pages)
- What UGP is: a deterministic number-theoretic framework, not a physical theory per se
- Why formalize it: (a) the paper makes strong claims that benefit from machine-checking,
  (b) the number-theoretic core is independently interesting, (c) serves as a citable artifact
  for the physics papers
- What's novel in the formalization vs. the paper
- Structure of the paper

### 2. The UGP Framework (~2 pages)
- Ridge definition R_n = 2^n − 16
- UGP-1 prime-locked ridge: divisor pairs, prime-lock condition
- GTE update map T (Def 2.5): odd/even steps, formal definition
- Canonical orbit at n=10: (1,73,823) → (9,42,1023) → (5,275,65535)
- Key invariants: m₂=15 (ridge remainder lock), q₂−q₁=13 (quotient gap), b₁ mirror-invariant

### 3. Architecture and Design Decisions (~1.5 pages)
- Module structure (43 modules across Core, Compute, Classification, GTE, SelfRef, Universality, Phase4)
- Zero-sorry, zero-custom-axiom policy — what this means and why it matters
- Dependency graph: Mathlib v4.29.0-rc3, nems-lean (SelfReference), aps-rice-lean (APS)
- `native_decide` for computational facts vs. algebraic proofs for general theorems
- The orbit-from-T upgrade: orbit values as corollaries of T, not postulates

### 4. Core Classification Results (~2 pages)
- RSUC (Residual Seed Uniqueness Conjecture): statement and proof structure
- Theorem A (general): ∀n, UnifiedAdmissibleAt n t → t ∈ CandidatesAt n
- Theorem B: Residual = Candidates; MDL selects LeptonSeed
- FormalRSUC and MonotonicStrengthening
- n=10 sieve: ridgeSurvivors_10 = {(24,42),(42,24)}
- Exclusion filters: 6 composite cases explicitly ruled out

### 5. GTE Orbit and Update Map (~2 pages)
- Formalizing the update map T (first time in any Lean artifact)
- Odd-step formulas: a_{t+1}, b_{t+1}, c_{t+1} = 2^n−1
- Even-step formulas: a_{t+1}, b_{t+1} = b_t + F_{|q_t−q_{t-1}|}, c_{t+1} = b_t·q_t+15
- `orbit_determined_by_T`: the three orbit triples as computed outputs of T
- **Novel theorem:** `even_step_c_invariance` — under the strict rule, c₃ = c₂ = 2^n−1
  for all n ≥ 5. Clarifies the paper's illustrative figure (c₃=65535 is a Mersenne target,
  not the strict per-step output)
- Linear b-growth: b_{2t+1} = b₂ + t·F₁₃ (thm:j35-growth)

### 6. General-Level Theorems (~1.5 pages)
These theorems hold at ALL ridge levels n, not just n=10:
- `ridge_remainder_lock_general`: m₂ = 15 for all n ≥ 5, all valid b₂
- `quotient_gap_all`: q₂ − q₁ = 13 for all n ≥ 10 (definitional but not stated generally in paper)
- `mirror_b1_invariance`: b₁ = b₂+q₂+7 is mirror-symmetric for all n
- `mersenne_gcd_identity`: gcd(2^a−1, 2^b−1) = 2^gcd(a,b)−1 (from Mathlib)
- `card_divisors_ridge_unbounded`: τ(2^n−16) → ∞ as n → ∞ (new theorem)
- `alpha_echo`: 2·b₁ − a₂ = 137 (fine-structure constant echo)

### 7. Quarter-Lock and Elegant Kernel (~1 page)
- Quarter-Lock law: k_M = k_G + ¼·k_L² (proved)
- Stability of Quarter-Lock under perturbation
- Elegant Kernel: k_L² = 7/512, L_model = log₂(2000/3)
- L_model derived from D₁, 5³, orbit length 3

### 8. Universality and Self-Reference (~1.5 pages)
- UWCA simulation of Rule 110 (Cook 2004 cited, not mechanized)
- Turing universality: ugp_is_turing_universal
- Lawvere fixed-point theorem (imported from nems-lean): ugp_lawvere_fixed_point
- Kleene recursion theorem (imported from nems-lean): ugp_kleene_recursion_theorem
- Rice's theorem (imported from aps-rice-lean): ugp_rice_theorem
- Halting undecidability: ugp_halting_undecidable
- FO decidability on finite windows vs. RE-hardness of general reachability

### 9. Mirror-Dual Conjecture (~1 page)
- Definition: mirror-dual pair at level n
- Computational evidence: 30 pairs found for n ≤ 50
- Formal statement: `MirrorDualConjecture` as a Lean `def`
- `card_divisors_ridge_unbounded`: the raw material for pairs is always available
- Relationship to twin prime conjecture (structural analogy)
- Heuristic analysis: expected count finite but growing

### 10. Open Conjectures (~0.5 pages)
All 8 open conjectures from the paper, formally stated:
- MirrorMinDualConjecture, FibRigidityConjecture, RobustUniversalityConjecture
- SharpDecidabilityBoundaryConjecture, MDLSelectionConjecture
- KernelCompatibilityConjecture, GlobalCAttractorConjecture, MuFlipDistanceConjecture

### 11. Related Work (~0.5 pages)
- Other physics formalization efforts in Lean/Coq/Isabelle
- Comparison with Mathlib's number theory coverage
- The companion SelfReference library (nems-lean, Paper 26)
- The B₃ prime theorem (primes-in-greedy-B3, companion result)

### 12. Conclusion (~0.5 pages)
- Summary of contributions
- What remains open (classifying topos, Dirichlet, Markov mixing)
- Future directions

---

## Theorem Inventory Table (for paper §4–8)

To include as a table in the paper:

| Theorem | Module | Paper ref | Novel? |
|---------|--------|-----------|--------|
| rsuc_theorem | Classification.RSUC | RSUC | No |
| theoremA_general | Classification.TheoremA | Thm A | No |
| mdl_selects_LeptonSeed | Classification.TheoremB | Thm B | No |
| ridgeSurvivors_10 | Compute.Sieve | §5 | No |
| quarterLockLaw | QuarterLock | §3 | No |
| ugp_is_turing_universal | Universality.TuringUniversal | §4 | No |
| orbit_determined_by_T | GTE.UpdateMap | §5 | **Yes** |
| ridge_remainder_lock_general | GTE.UpdateMap | Lem m2 | **Yes (general)** |
| even_step_c_invariance | GTE.UpdateMap | — | **Yes (new)** |
| quotient_gap_all | GTE.GeneralTheorems | thm:gap13-all | **Yes (general)** |
| mersenne_gcd_identity | GTE.MersenneGcd | — | **Yes (from Mathlib)** |
| card_divisors_ridge_unbounded | GTE.MirrorDualConjecture | — | **Yes (new)** |
| MirrorDualConjecture | GTE.MirrorDualConjecture | — | **Yes (new)** |
| ugp_lawvere_fixed_point | SelfRef.LawvereKleene | thm:lawvere-ugp | No (from nems-lean) |
| ugp_kleene_recursion_theorem | SelfRef.LawvereKleene | thm:ugp-recursion | No (from nems-lean) |
| ugp_rice_theorem | SelfRef.RiceHalting | thm:rice-ugp | No (from aps-rice-lean) |
| alpha_echo | GTE.GeneralTheorems | prop:alpha-echo | **Yes (machine-checked)** |

---

## Files to Create

```
paper/
  ugp_lean_formalization.tex   ← main paper
  refs.bib                     ← bibliography
  figures/
    module_graph.tex           ← dependency graph (TikZ)
    theorem_table.tex          ← full theorem inventory
  README.md                    ← how to compile
```

---

## Key Citations Needed

- Lean 4 / Mathlib: `leanprover-community/mathlib4`
- UGP paper: `SpivackUGP2025` (the main UGP paper)
- ugp-lean artifact: `SpivackUGPFormalization` (this repo)
- nems-lean: Paper 26 (SelfReference library)
- aps-rice-lean: APS Rice/Recursion library
- primes-in-greedy-B3: companion B₃ result
- Cook (2004): Rule 110 Turing universality
- Lean 4: de Moura et al.

---

## Style Notes

- Audience: Lean/ITP community, not physicists
- Physics is *motivation*, not *content* — one paragraph in intro, then pure math/CS
- Emphasize: zero-sorry policy, the orbit-from-T upgrade, the general theorems
- The mirror-dual conjecture section is the most novel — give it space
- Keep the self-reference section concise — these are imports, not new proofs

---

## Timeline

1. Draft §1 (Introduction) and §3 (Architecture) first — these frame everything
2. Draft theorem inventory table — this is the core of the paper
3. Fill in §4–8 from the table
4. §9 (Mirror-dual) and §10 (Conjectures) are the novel sections — write carefully
5. Polish and submit to arXiv
