/-!
# DEPRECATED — `UgpLean.ElegantKernel.KGen` (conditional π/2 route)

**Not imported** from `UgpLean.lean`. This path is retained only as a module-path
marker in git history.

## Supersession

The unconditional closure is
`UgpLean.ElegantKernel.Unconditional.KGenFullClosure`:

- `thm_ucl2_fully_unconditional` — `k_gen = φ * cos (π / 10)`
- `thm_ucl2_summary` — packaged UCL₂ block

The former file proved `k_gen = π / 2` from a tautological `FibonacciPhaseAxiom`
(identifying the UCL linear coefficient with `arg ψ`). That value disagrees with
P01, the SM verifier theoretical coefficients, and `theoretical_coefficients.json`.

## Where related facts live now

| Former name (KGen) | Canonical location |
|--------------------|--------------------|
| `psi_minimal_poly` | `UgpLean.GTE.StructuralTheorems.neg_inv_golden_ratio_minimal_poly` |
| `elegant_kernel_Lg_block` | `KGenFullClosure.thm_ucl2_summary` (with `FullClosure` for UCL₁) |
| `k_gen_eq_pi_div_two` | **removed** — use `thm_ucl2_fully_unconditional` |

Chirality and Fibonacci–Hessian structure: `FibonacciHessian`, `KGen2`, `D5StructuralAxiom`.
-/
