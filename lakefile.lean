import Lake
open Lake DSL

package «ugp-lean» where
  -- UGP (Universal Generative Principle) and GTE (Generative Triple Evolution)
  -- Formalization for UGP papers, Paper 25, and MFRR

require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

-- SelfReference (Lawvere/Kleene fixed-point theorems, Paper 26)
-- Local dev: override by placing nems-lean at ../nems-lean (Lake prefers local path if present)
require SelfReference from git
  "https://github.com/novaspivack/nems-lean.git" @ "d1379b2d6d01b1c652ae65b65e1fab97b9b6b6b3"

-- APS Rice/Recursion theorems (Rice's theorem, halting undecidability, recursion theorem)
require APS from git
  "https://github.com/novaspivack/aps-rice-lean.git" @ "19fd18ad250bf83cb4fb6c3b2067975c0faaac4b"

@[default_target]
lean_lib «UgpLean» where
  -- Ridge, Sieve, Triple, QuarterLock, Classification, RSUC
