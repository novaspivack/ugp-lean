# ugp-lean Formalization Paper

Machine-checked Lean 4 formalization of the Universal Generative Principle (UGP), comprising **143 modules** across 13 architectural layers with a strict zero-sorry, zero-custom-axiom policy on the core proof path.

**Key results formalized:**
- Algebraic uniqueness: canonical seed $(1,73,823)$ is the unique lexicographic minimum at $n=10$
- Computational universality: UWCA bisimulates Rule 110 (`uwca_sweep_implements_rule110`)
- CUP-4: SM generation orbit uniquely forces Rule 110 (`cup4_parity_uniqueness`)
- Two-way convergence: Rule 110 forced from UWCA substrate AND SM orbit independently (`rule110_two_layer_confluence`)
- Tape-level unification: both SM charge and mass cascade sectors run on one Rule 110 tape (`hypothesis_b_tape_level`)
- Garden of Eden: gen₁ has zero predecessors under f_MDL (`fmdl_gen1_is_garden_of_eden`)
- PSC chain: PSC → SM gauge → orbit → Rule 110 → Turing-universal (`hypothesis_c_psc_forces_universality`)
- GTE-NEMS framework: GTE substrate as `NemS.Framework` with transputation classification (`gte_tpc_from_nems_classification`)
- Dark sector certificate: Q=0 for all dark particles, SU(3)_dark gauge group (`dark_braid_atlas_certificate`)
- MassRelations: Koide closed form, S₃-equivariant Newton flow, full fermion mass spectrum

**Bridge axioms (partial certification):**
- Six axioms in `CUP3DPhysicalIncompleteness` (fMDL APS / vacuum encoding)
- `gte_partrec_eval_iff_fmdl_phi` in `GTEFrameworkInstance` (Cook Partrec ↔ fMDL halting)
- `rcc_physics_ax` — RCC, backed by `rcc_analytical_complete`
- `rule110_simulates_computable` — Cook's universality theorem (2004/2009)
- `simultaneous_dual_tape_ax` — dual-sector tape coherence

## Compilation

```bash
cd paper/
pdflatex ugp_lean_formalization
bibtex ugp_lean_formalization
pdflatex ugp_lean_formalization
pdflatex ugp_lean_formalization
```

## Files

```
paper/
  ugp_lean_formalization.tex   ← main paper
  refs.bib                     ← bibliography
  figures/
    theorem_table.tex          ← full theorem inventory (Table 2)
    module_graph.tex           ← detailed dependency graph (Figure 2)
  README.md                    ← this file
```

## Status

**Branch:** `theoretical_path_closure_sandbox` on `ugp-lean-exp` (experimental).  
Graduation to canonical `ugp-lean` requires explicit user approval.

## Target

arXiv cs.LO (Logic in Computer Science) with cross-list math.LO.
