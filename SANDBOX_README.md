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

- `UgpLean/ElegantKernel/` — target-theorem files (one per target).
- `docs/DEFENSIBILITY_*.md` — defensibility ledgers.
- `EXP_AXIOMS.md` — any temporary experimental axioms (must be empty before port-back).
- `EXP_ABANDONED.md` — documentation of targets that failed defensibility or Lean proof attempts.
- `SANDBOX_README.md` — this file.

## Relationship to main ugp-lean

The sandbox diverges from `~/ugp-lean` starting at the baseline SHA above.  Periodically rebase onto main if main advances independently, BUT only rebase new main changes that do not touch UCL-coefficient-related modules.

Do NOT push this branch to any remote.  This sandbox is local-only.
