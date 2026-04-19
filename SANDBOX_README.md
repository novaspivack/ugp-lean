# ugp-lean-exp — Experimental Sandbox for SPEC_028_TP1

**Status:** SANDBOX — experimental Lean work for the Theoretical Path Closure program.
**Created:** 2026-04-17
**Base repo:** `~/ugp-lean`
**Baseline SHA:** `ae64d3a44bcace40c64064db988929478ca37e21` ("Remove rejected OEIS A394412 reference from UGP primes")
**Branch:** `theoretical_path_closure_sandbox`

## Purpose

This is a working sandbox for experimental Lean theorem work on the remaining non-certified UCL coefficients of Paper 1.  See `SPEC_028_TP1_THEORETICAL_PATH_CLOSURE.md` in the ugp-physics repo for the full research program.

**The main `~/ugp-lean` repository is NOT modified by work in this sandbox.**  Only proven, defensibility-passed theorems are ported back.

## Why this exists as a separate directory

Saturation null (COMP-P01-S3) showed that Lean-proving a chain whose premise is post-hoc is indistinguishable from rigorous numerology.  To avoid contaminating the main Lean library with experimental or potentially-post-hoc theorems, all work happens here first and is validated per the defensibility protocol before port-back.

## Scope

Target theorems (see SPEC_028_TP1 §3):
- **THM-UCL-1:** `k_gen2_eq_neg_phi_over_2` (k_gen² = −φ/2 via D₅ pentagonal RG symmetry)
- **THM-UCL-2:** `k_gen_eq_pi_over_2` (k_gen = π/2 via quarter-turn gauge normalization)
- **THM-UCL-3:** `mu_triple_unique_mdl` (Möbius triple (1/8, −3/2, 4/3) via MDL uniqueness) — **FIRST TARGET**
- **THM-UCL-4:** `k_L_base_independent_form` (linear-L coefficient via GTE equilibrium)
- **THM-UCL-5:** `k_const_structural_form` (after historical investigation of −0.15203 vs −1/(2π) discrepancy)

### Round 12 + Rounds 13–18 additional scope (charged-fermion mass relations)

Added 2026-04-19 alongside the original UCL-coefficient program (see ugp-physics
spec EPIC_CLUSTER7_RESEARCH_GRADE for full programme):

- **TT formula** (`UgpLean.MassRelations.UpLeptonCyclotomic`): `log(m_{u,g}/m_{l,g}) = (π/6)·2^g + β`; three β-free inter-generational identities proved.
- **VV formula** (`UgpLean.MassRelations.DownRational`): `log(m_{d,g}) = (13/9)·log(m_{u,g}) + (-7/6)·log(m_{l,g}) + (-5/14)`; γ-free identity + combined-formula arithmetic proved.
- **Claim A — Round 13 Phase 1** (`UgpLean.MassRelations.SU3FlavorCartan`): angle between A_2 simple root α_1 and fundamental weight ω_1 = π/6. **Machine-proved**, zero sorry, only standard Mathlib axioms.
- **VV three-factor structural decomposition — Rounds 17–18** (`UgpLean.MassRelations.ClebschGordan` extension): all three VV coefficients identified with exact structural rationals (`alpha_VV_structural`, `beta_VV_structural`, `gamma_VV_structural`); `alpha_gamma_shared_gcd` (axiom-free, `decide`-only) proves the non-trivial Round-18 link `gcd(45, 126) = 9 = dim(SU(3)_C adj) + dim(U(1)_Y)`.
- **Hub** (`UgpLean.MassRelations`): re-exports formulas; documents status of each submodule.

These follow the same port-back protocol as the UCL targets above.  Currently
**not yet ported back** to `~/ugp-lean` — port-back planned bundled with the
next consolidated Paper 1 update pass per ugp-physics 02_SPEC §I.

**Status of Track D (TT mechanism, Claims B/C):** compact-SU(3) character interpretation definitively ruled out (Round 16); GUT CG rep-dim search density-dominated (Round 15). Best remaining candidate: binary cascade of π/6 phase shifts. Under construction.

**Status of Track F (VV three-factor decomposition):** structurally complete in Lean (Rounds 17–18); awaiting unified-Lagrangian derivation for full landmark integration.

## Protocol

### Before any Lean proof work on a target

1. Execute Phase 1.5 defensibility pre-check per SPEC_028_TP1 §5.
2. File defensibility ledger: `docs/DEFENSIBILITY_<TARGET>.md` in this repo, and `defensibility_<TARGET>.json` in `~/ugp-physics/papers/01_SM/canonical_run/`.
3. User review of the defensibility outcome.
4. User GO/NO-GO decision before proceeding to Lean work.

### During Lean proof work

- Each target gets its own file under `UgpLean/ElegantKernel/`.
- `sorry` is permitted during work but must be eliminated before port-back.
- Temporary `axiom` introductions must be documented in `EXP_AXIOMS.md` in this repo root.  **No axioms port back.**
- If modifying existing modules is needed, keep changes minimal and prefer adding lemmas in new files.
- `lake build` must pass after every commit.

### Port-back criteria

A theorem is ready to port back to `~/ugp-lean` only when:
- [ ] Passed Phase 1.5 defensibility.
- [ ] Zero `sorry` in the proof chain.
- [ ] Zero experimental `axiom` in the proof chain.
- [ ] `lake build` passes in the sandbox.
- [ ] Statement matches the claim in Paper 1 §3 (or paper has been updated to match the Lean statement).
- [ ] Defensibility ledger hash cited in the theorem's doc-comment.
- [ ] User has reviewed.

### Port-back procedure

1. In `~/ugp-lean`, create a new branch `port/<target-name>`.
2. Copy the relevant `UgpLean/ElegantKernel/*.lean` files from the sandbox.
3. Adjust imports if needed (should not be necessary if sandbox and main are on same Mathlib pin).
4. Run `lake build` in `~/ugp-lean`. Must succeed with no new warnings.
5. Review one final time: read the theorem statement in isolation; confirm it matches the paper claim.
6. Commit to `~/ugp-lean` with message referencing the SPEC and the sandbox commit SHA.
7. Update `MANIFEST.md` in `~/ugp-lean` to add the new theorem.

### Sandbox retention

This sandbox is retained as a historical record after port-back.  Do not delete.
Abandoned or reformulated targets: document in `EXP_ABANDONED.md`.

## Files in this sandbox

- `UgpLean/ElegantKernel/` — original UCL target-theorem files (one per target).
- `UgpLean/MassRelations/` — Round 12 + Rounds 13–18 charged-fermion mass-relation modules:
  - `MassRelations.lean` (hub, re-exports)
  - `MassRelations/UpLeptonCyclotomic.lean` (TT formula + β-free identities)
  - `MassRelations/DownRational.lean` (VV formula + γ-free identity + combined-formula arithmetic)
  - `MassRelations/SU3FlavorCartan.lean` (Claim A: π/6 from A_2 geometry)
  - `MassRelations/ClebschGordan.lean` (GUT dimension table + Round 17–18 VV three-factor structural theorems)
  - `MassRelations/BinaryCascade.lean` (Round 19 Claim B candidate: TT as binary phase cascade with 2^g doubling)
  - `MassRelations/FroggattNielsen.lean` (Round 21 Claim C: two-flavon FN model with doubled charges reproduces TT exactly)
- `docs/DEFENSIBILITY_*.md` — defensibility ledgers.
- `docs/THEOREMS.md` — full theorem catalog (kept in sync with Lean modules).
- `docs/MODULES.md` — module reference (kept in sync).
- `MANIFEST.md` — paper-to-Lean-theorem mapping (kept in sync).
- `Assumptions.md` — premise ledger including MassRelations definitions and interpretive flags.
- `EXP_AXIOMS.md` — any temporary experimental axioms (must be empty before port-back; currently empty).
- `EXP_ABANDONED.md` — documentation of targets that failed defensibility or Lean proof attempts.
- `SANDBOX_README.md` — this file.

**Doc-sync rule (added 2026-04-19):** every Lean module addition or theorem addition in this sandbox MUST be reflected in `MANIFEST.md`, `docs/THEOREMS.md`, `docs/MODULES.md`, and `Assumptions.md` (where applicable) in the SAME COMMIT.  Backlog of un-documented theorems is unacceptable; if discovered, fix immediately.

## Relationship to main ugp-lean

The sandbox diverges from `~/ugp-lean` starting at the baseline SHA above.  Periodically rebase onto main if main advances independently, BUT only rebase new main changes that do not touch UCL-coefficient-related modules.

Do NOT push this branch to any remote.  This sandbox is local-only.
