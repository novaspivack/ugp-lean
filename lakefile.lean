import Lake
open Lake DSL

package «ugp-lean» where
  -- UGP (Universal Generative Principle) and GTE (Generative Triple Evolution)
  -- Formalization for UGP papers, Paper 25, and MFRR

-- nems-lean (Lawvere/Kleene fixed-point theorems, Paper 26; package name «nems-lean»)
-- SelfReference is a lean_lib within nems-lean; imports like `import SelfReference.Core.*`
-- remain valid regardless of the package alias used in require.
require «nems-lean» from git
  "https://github.com/novaspivack/nems-lean.git" @ "main"

-- transputation-lean (NEMS Transputation / TPC framework, Paper 34 GTE substrate)
require «transputation» from git
  "https://github.com/novaspivack/transputation-lean.git" @ "main"

-- APS Rice/Recursion theorems (Rice's theorem, halting undecidability, recursion theorem)
require APS from git
  "https://github.com/novaspivack/aps-rice-lean.git" @ "main"

/-- Mathlib **last**: lets Lake align transitive tool deps (plausible, aesop, …) with Mathlib's pins. -/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.1"

/-- Cook Rule 110 pipeline (cyclic tag prelude, ether background). -/
require «Rule110» from git
  "https://github.com/novaspivack/rule110-lean.git" @ "9ac43e3"

@[default_target]
lean_lib «UgpLean» where
  -- Ridge, Sieve, Triple, QuarterLock, Classification, RSUC
