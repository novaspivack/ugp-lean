import Lake
open Lake DSL

package «ugp-lean» where
  -- UGP (Universal Generative Principle) and GTE (Generative Triple Evolution)
  -- Formalization for UGP papers, Paper 25, and MFRR

-- SelfReference (Lawvere/Kleene fixed-point theorems, Paper 26)
-- Pin `c60a844` so downstream packages (e.g. DSI) can `require «ugp-lean»` alongside the same
-- nems checkout without duplicate `SelfReference.*` modules (`d1379b2` is an ancestor).
require SelfReference from git
  "https://github.com/novaspivack/nems-lean.git" @ "c60a84438782071e88fcf07d2f263727d2499b7a"

-- APS Rice/Recursion theorems (Rice's theorem, halting undecidability, recursion theorem)
require APS from git
  "https://github.com/novaspivack/aps-rice-lean.git" @ "368cf90ef0a07d96feb88dfd4915aa4e7f6e4389"

/-- Mathlib **last**: lets Lake align transitive tool deps (plausible, aesop, …) with Mathlib's pins. -/
require mathlib from git
  "https://github.com/leanprover-community/mathlib4.git" @ "v4.29.0-rc6"

@[default_target]
lean_lib «UgpLean» where
  -- Ridge, Sieve, Triple, QuarterLock, Classification, RSUC
