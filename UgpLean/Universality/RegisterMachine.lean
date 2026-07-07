import Mathlib.Computability.Partrec

/-!
# Minsky counter machines and Turing completeness

Formalizes a standard Minsky-style counter machine (Minsky 1967, *Computation: Finite
and Infinite Machines*): finitely many registers holding natural numbers, with
`INC`, `DEC`-with-branch, and `HALT` instructions.

## What is proved here (zero sorry)

- `CounterState`, `CounterInstr`, `CounterProgram`, `counter_step`, `counter_run`
- `counter_encode_input` / `counter_decode_output` for I/O on register 0
- `counter_step_total` — one step always produces a definite successor state

## Named axiom (classical, not smuggled)

- `minsky_counter_machine_turing_complete_1967` — every total computable `ℕ → ℕ` function is
  computed by some counter program with a fuel function.  This is Minsky's theorem
  (equivalence of counter machines and Turing machines / partial recursive functions).

  **Mathlib audit (2026):** no counter-machine, register-machine, URM, or Minsky formalization
  in `Mathlib.Computability.*` (`Partrec`, `PartrecCode`, `TuringMachine`, `PartrecToTM2`, …).
  Discharge path: Minsky 1967 two-counter construction, or `PartrecToTM2` + counter↔TM compilation.

The UWCA register-machine universality route (`UWCARegisterUniversality.lean`) uses this
axiom together with a zero-sorry UWCA register-file interpreter.
-/

namespace UgpLean.Universality.RegisterMachine

/-- Number of counter registers.  Minsky (1967): two counters suffice for Turing
    completeness; we use two as the canonical witness size. -/
def numRegs : Nat := 2

/-- Register index type for the canonical 2-counter machine. -/
abbrev RegIdx := Fin 2

/-- Counter-machine state: register file, program counter, halt flag. -/
structure CounterState where
  regs : RegIdx → ℕ
  pc : ℕ
  halted : Bool

/-- Counter-machine instruction set (Minsky-style). -/
inductive CounterInstr where
  | inc (r : RegIdx) (next : ℕ) : CounterInstr
  | dec (r : RegIdx) (zeroDest succDest : ℕ) : CounterInstr
  | halt : CounterInstr

/-- A counter program is a finite instruction list indexed by the program counter. -/
abbrev CounterProgram := List CounterInstr

/-- Fetch the instruction at `pc`, if in range. -/
def fetch (prog : CounterProgram) (pc : ℕ) : Option CounterInstr :=
  prog[pc]?

/-- One counter-machine step. -/
def counter_step (prog : CounterProgram) (st : CounterState) : CounterState :=
  if st.halted then st else
  match fetch prog st.pc with
  | none => { st with halted := true }
  | some CounterInstr.halt => { st with halted := true }
  | some (CounterInstr.inc r next) =>
    { regs := Function.update st.regs r (st.regs r + 1),
      pc := next,
      halted := false }
  | some (CounterInstr.dec r zeroDest succDest) =>
    let v := st.regs r
    if v = 0 then
      { st with pc := zeroDest }
    else
      { regs := Function.update st.regs r (v - 1),
        pc := succDest,
        halted := false }

/-- `fuel`-bounded iteration of `counter_step`. -/
def counter_run (prog : CounterProgram) : ℕ → CounterState → CounterState
  | 0, st => st
  | fuel + 1, st => counter_run prog fuel (counter_step prog st)

/-- Encode input `n` in register 0, other registers zero, at program counter 0. -/
def counter_encode_input (n : ℕ) : CounterState :=
  { regs := fun i => if i = (0 : RegIdx) then n else 0,
    pc := 0,
    halted := false }

/-- Decode output from register 0 after execution. -/
def counter_decode_output (st : CounterState) : ℕ := st.regs 0

theorem counter_step_total (prog : CounterProgram) (st : CounterState) :
    ∃ st', counter_step prog st = st' :=
  ⟨_, rfl⟩

theorem counter_run_zero (prog : CounterProgram) (st : CounterState) :
    counter_run prog 0 st = st := rfl

/-- **Axiom (Minsky 1967: counter machines are Turing complete).**

    Every total computable function `f : ℕ → ℕ` is computed by some counter program:
    there exist a finite program and a fuel function such that running from
    `counter_encode_input n` and decoding register 0 yields `f n`.

    **Classical source:** Minsky, *Computation: Finite and Infinite Machines* (1967), Ch. 8–9.
    Equivalent to Turing-machine / partial-recursive computability.

    **Assumed, not derived:** Mathlib has no counter-machine development as of v4.29.1.
    Full formalization of Minsky's 2-counter Turing simulation is out of scope here; this
    records a textbook-standard, uncontroversial classical result. -/
axiom minsky_counter_machine_turing_complete_1967 (f : ℕ → ℕ) (hf : Computable f) :
    ∃ (prog : CounterProgram) (fuel : ℕ → ℕ),
      ∀ n, counter_decode_output (counter_run prog (fuel n) (counter_encode_input n)) = f n

/-- Backward-compatible alias for the Minsky 1967 axiom. -/
theorem counter_machine_simulates_computable (f : ℕ → ℕ) (hf : Computable f) :
    ∃ (prog : CounterProgram) (fuel : ℕ → ℕ),
      ∀ n, counter_decode_output (counter_run prog (fuel n) (counter_encode_input n)) = f n :=
  minsky_counter_machine_turing_complete_1967 f hf

end UgpLean.Universality.RegisterMachine
