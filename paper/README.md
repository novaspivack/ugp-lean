# ugp-lean Formalization Paper

## Compilation

Requires a standard LaTeX distribution (TeX Live 2023+ or equivalent) with:
- `pdflatex`
- `bibtex`
- TikZ (`tikz`, `backgrounds`, `fit`, `positioning`, `calc`)
- Standard AMS packages (`amsmath`, `amssymb`, `amsthm`)
- `cleveref`, `hyperref`, `booktabs`, `listings`, `microtype`

### Build

```bash
cd paper/
pdflatex ugp_lean_formalization
bibtex ugp_lean_formalization
pdflatex ugp_lean_formalization
pdflatex ugp_lean_formalization
```

Or with `latexmk`:

```bash
cd paper/
latexmk -pdf ugp_lean_formalization.tex
```

### Clean

```bash
latexmk -C
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

## Target

arXiv cs.LO (Logic in Computer Science) with cross-list math.LO.
