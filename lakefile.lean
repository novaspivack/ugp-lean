import Lake
open Lake DSL

package «ugp-lean» where
  -- UGP (Universal Generative Principle) and GTE (Generative Triple Evolution)
  -- Formalization for UGP papers, Paper 25, and MFRR

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc3"

-- SelfReference (Lawvere/Kleene fixed-point theorems, Paper 26)
require SelfReference from "../nems-lean"

-- APS Rice/Recursion theorems (Rice's theorem, halting undecidability, recursion theorem)
require APS from "../aps-rice-lean"

@[default_target]
lean_lib «UgpLean» where
  -- Ridge, Sieve, Triple, QuarterLock, Classification, RSUC
