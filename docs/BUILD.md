# ugp-lean: Build Guide

## Prerequisites

- **Lean 4**: v4.29.0-rc3 (or compatible)
- **elan** (recommended): `curl https://raw.githubusercontent.com/leanprover/elan/master/elan-init.sh -sSf \| sh`
- **Lake**: Bundled with Lean 4; no separate install needed

## Toolchain

| Component | Version |
|-----------|---------|
| Lean | 4.29.0-rc3 |
| Mathlib | v4.29.0-rc3 |

The `lean-toolchain` file pins the Lean version. Mathlib is fetched automatically by Lake.

## Build Commands

```bash
# Clone or navigate to ugp-lean
cd /path/to/ugp-lean

# Fetch dependencies (Mathlib, etc.)
lake update

# Full build
lake build

# Clean and rebuild
lake clean && lake build
```

## Expected Output

```
✔ Built UgpLean (8–10s)
Build completed successfully (8085 jobs).
```

- **0 errors**
- **0 sorry** on the core RSUC path (Theorem A, Theorem B, RSUC, Sieve, PrimeLock, etc.)
- Optional: some linter warnings (e.g. unused variables) — non-blocking

## Build Time

- First build: ~2–5 minutes (Mathlib compilation)
- Incremental: ~10–30 seconds for typical edits

## Troubleshooting

### Mathlib fails to build
- Ensure `lake update` completed; check network
- Try `lake exe cache get` if using Mathlib cache

### Out of memory
- Increase stack: `ulimit -s 65536` (Linux/macOS)
- Lean 4 can use several GB during full build

### Wrong Lean version
- Run `elan show` to see current default
- `elan override set leanprover/lean4:v4.29.0-rc3` in the repo directory

## Verification

After a successful build:

```bash
# Check no sorry in core modules (optional)
lake env lean UgpLean/Classification/RSUC.lean -- no output = OK
```

Core path: `RidgeDefs` → `MirrorDefs` → `TripleDefs` → `SievePredicates` → `Sieve` → `DecidablePredicates` → `Bounds` → `TheoremA` → `TheoremB` → `RSUC`.
