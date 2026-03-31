import Lake
open Lake DSL

package «ugp-lean» where
  -- UGP (Universal Generative Principle) and GTE (Generative Triple Evolution)
  -- Formalization for UGP papers, Paper 25, and MFRR

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

-- SelfReference (Lawvere/Kleene fixed-point theorems, Paper 26)
require SelfReference from git
  "https://github.com/novaspivack/nems-lean.git" @ "d1379b2d6d01b1c652ae65b65e1fab97b9b6b6b3"

-- APS Rice/Recursion theorems (Rice's theorem, halting undecidability, recursion theorem)
require APS from git
  "https://github.com/novaspivack/aps-rice-lean.git" @ "368cf90ef0a07d96feb88dfd4915aa4e7f6e4389"

@[default_target]
lean_lib «UgpLean» where
  -- Ridge, Sieve, Triple, QuarterLock, Classification, RSUC
