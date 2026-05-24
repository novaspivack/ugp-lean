import Lake
open Lake DSL

package «ugp-lean» where
  -- UGP (Universal Generative Principle) and GTE (Generative Triple Evolution)
  -- Formalization for UGP papers, Paper 25, and MFRR

-- nems-lean (Lawvere/Kleene fixed-point theorems, Paper 26; SelfReference is a lean_lib within it)
-- Using «nems-lean» as package name to avoid duplicate-module conflicts when transputation
-- also resolves nems-lean as a transitive dependency.
require «nems-lean» from git
  "https://github.com/novaspivack/nems-lean.git" @ "main"

-- transputation-lean (NEMS Transputation / TPC framework; NemS.Category.PSCSys / FPSC)
-- Required by UgpLean.Framework.GTEFrameworkInstance, GTEOptimalityInstance, GTEFinalCoalgebra.
require «transputation» from git
  "https://github.com/novaspivack/transputation-lean.git" @ "main"

-- APS Rice/Recursion theorems (Rice's theorem, halting undecidability, recursion theorem)
require APS from git
  "https://github.com/novaspivack/aps-rice-lean.git" @ "main"

/-- Mathlib **last**: lets Lake align transitive tool deps (plausible, aesop, …) with Mathlib's pins. -/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

/-- Cook Rule 110 pipeline (cyclic tag prelude, ether background, A-glider verification). -/
require «Rule110» from git
  "https://github.com/novaspivack/rule110-lean.git" @ "13811a3"

@[default_target]
lean_lib «UgpLean» where
  -- Ridge, Sieve, Triple, QuarterLock, Classification, RSUC
