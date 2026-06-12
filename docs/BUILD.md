# ugp-lean: Build Guide

## Prerequisites

- **Lean 4** with **elan**: `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf | sh`
- **Lake**: bundled with Lean 4; no separate install needed
- **Git LFS**: not required for source builds

## Toolchain

| Component | Version |
|---|---|
| Lean | 4.29.0-rc6 |
| Mathlib | v4.29.1 |

The `lean-toolchain` file pins the Lean version. Mathlib is fetched automatically by Lake.

## Build Commands

```bash
# Clone
git clone https://github.com/novaspivack/ugp-lean.git
cd ugp-lean

# Fetch dependencies (Mathlib, transputation-lean, etc.)
lake update

# Full build
lake build

# Clean and rebuild from scratch
lake clean && lake build
```

## Expected Output

```
✔ Built UgpLean
Build completed successfully.
```

- **0 errors**
- **0 sorry** on the core proof path
- Linter warnings (unused variables, deprecated names) are non-blocking

## Build Time

- First build: ~3–8 minutes (Mathlib compilation; varies by hardware)
- Incremental: ~15–60 seconds for typical edits
- Full clean rebuild: ~5–15 minutes

Some modules with large `native_decide` proofs build slower:
- `Universality/Z5TransitivityUniqueness` — §8 primes, ~440s cold
- `Universality/ParityProjectionBattery` — 16,807 mod-2 recodings, several minutes
- `Polynomial/SpinSevenGroundSpace` — pair digraph, ~30s

## Sorry Audit

The core proof path has **0 sorry**. The full library has:

| Location | Count | Reason |
|---|---|---|
| `Gravity/WaldEntropy` | 3 | Pending Mathlib manifold integrals |
| `Substrate/CogwheelDynamicsG21` | 3 | Pending Mathlib matrix-exponential API |
| `Physics/KinkPoleMassSpectralCore` | partial | Pöschl–Teller integrals deferred |
| `Physics/CCOneJumpResidual` | 1 partial | Computable modulus deferred |

Two analytic inputs in `GTE/AnalyticArchitecture` are declared as `axiom` (not `sorry`) with precise citations — see [DESIGN.md](DESIGN.md).

Two mesh→integral bridge steps in `Substrate/SechOverlapIntegralBounds_bridge.lean` are declared as `axiom` (CatA class, documented).

## Axiom Closure

A clean build satisfies:

```lean
#print axioms rsuc_theorem
-- propext, Classical.choice, Quot.sound
```

These are the standard Mathlib axioms. No custom axioms appear in the closure of any physics or classification theorem on the core path.

## Verification

```bash
# Spot-check no sorry in core modules
lake env lean UgpLean/Classification/RSUC.lean
# (no output = OK)

# Check axiom closure of RSUC
lake env lean --run <<'EOF'
import UgpLean.Classification.RSUC
#print axioms rsuc_theorem
EOF
```

## Core Path

`RidgeDefs` → `MirrorDefs` → `TripleDefs` → `SievePredicates` → `Sieve` → `DecidablePredicates` → `Bounds` → `TheoremA` → `TheoremB` → `RSUC`

## Troubleshooting

**Mathlib fails to fetch**
```bash
lake exe cache get   # use prebuilt Mathlib cache
lake update
```

**Out of memory during build**
```bash
ulimit -s 65536   # increase stack (Linux/macOS)
```
Lean 4 can use several GB during a full build with large `native_decide` proofs.

**Wrong Lean version**
```bash
elan show                                          # see current default
elan override set leanprover/lean4:v4.29.0-rc6    # pin to this directory
```

**Build hangs on a specific module**
Large `native_decide` modules (Z5TransitivityUniqueness §8, ParityProjectionBattery) can take several minutes — this is expected, not a hang.
