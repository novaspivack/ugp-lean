import Mathlib.Data.List.Basic
import Mathlib.Data.Fin.Basic

/-!
# UgpLean.Universality.CUP11ModSeven — CUP-11c: Orbit and Rule 110 Constraints are Conflict-Free

## Statement

For the `phi_a7` standard branch, canonical ordering `[e⁻, u, d, νR, νL]`,
the **10 orbit constraints** (from the gen1→gen2→gen3 CA step) and the **8 Rule 110
binary sublayer constraints** (restricting the rule to agree with Rule 110 on `{0,1}³`)
together define 18 **conflict-free** neighborhoods: no neighborhood has two different
required outputs.

This proves (constructively) that there exists a function `f : Fin 7 → Fin 7 → Fin 7 → Fin 7`
satisfying all 18 constraints simultaneously, i.e., that a computationally universal mod-7
CA rule realizing the SM generation orbit EXISTS.

## Background

- CUP-11b: the 10 orbit neighborhoods for `phi_a7` standard canonical ordering
  have no conflicts with each other (each neighborhood is unique in the orbit).
- CUP-11c: the 8 Rule 110 binary neighborhoods `{0,1}³` are disjoint from
  the 10 orbit neighborhoods for `phi_a7` (verified computationally for all 1730 orderings).
- Here we give a machine-verified proof for the specific canonical ordering via `decide`.

## Constraint Data

Orbit constraints (phi_a7, standard branch, canonical ordering [e⁻, u, d, νR, νL]):
- Sourced from `t_cup11b_sat_results.json`, first zero-conflict ordering.

Rule 110 binary constraints (identity encoding, {0,1} ⊂ Fin 7):
- Rule 110 number 110 = 01101110₂: (L,C,R) → output for all (L,C,R) ∈ {0,1}³.

## Proof Method

The conflict-freeness claim is decidable (finite list intersection over `Fin 7³`).
We use `decide` to verify it. The computation is small: 10 × 8 = 80 pair checks.
All theorems in this file are proved by `decide` with zero axioms beyond propositional logic.
-/

namespace CUP11ModSeven

/-- A neighborhood is a triple (L, C, R) of mod-7 cell values. -/
abbrev Nbhd := Fin 7 × Fin 7 × Fin 7

/-- A CA constraint is a (neighborhood, output) pair. -/
abbrev Constraint := Nbhd × Fin 7

/-- The 10 orbit constraints for phi_a7 standard branch, canonical ordering [e⁻, u, d, νR, νL].
    Sourced from SAT analysis of orbit neighborhoods (first zero-conflict ordering). -/
def orbitConstraints : List Constraint :=
  [ ((1, 1, 5), 2),
    ((1, 5, 2), 5),
    ((5, 2, 2), 2),
    ((2, 2, 1), 0),
    ((2, 1, 1), 2),
    ((2, 2, 5), 5),
    ((2, 5, 2), 6),
    ((5, 2, 0), 5),
    ((2, 0, 2), 3),
    ((0, 2, 2), 5) ]

/-- The 8 Rule 110 binary sublayer constraints.
    Rule 110 (Cook 2004, Turing-complete): output bit = (110 >> (4L+2C+R)) & 1
    for all (L,C,R) ∈ {0,1}³ ⊂ (Fin 7)³ (identity encoding). -/
def rule110BinaryConstraints : List Constraint :=
  [ ((0, 0, 0), 0),
    ((0, 0, 1), 1),
    ((0, 1, 0), 1),
    ((0, 1, 1), 1),
    ((1, 0, 0), 0),
    ((1, 0, 1), 1),
    ((1, 1, 0), 1),
    ((1, 1, 1), 0) ]

/-- Check whether a list of constraints is conflict-free (as a `Bool`).
    A list is conflict-free if no two constraints share a neighborhood with different outputs. -/
def conflictFreeBool (cs : List Constraint) : Bool :=
  cs.all fun c1 =>
    cs.all fun c2 =>
      !(c1.1 == c2.1) || (c1.2 == c2.2)

/-- Check whether two constraint lists are cross-conflict-free (as a `Bool`).
    Cross-conflict-free: no constraint from cs1 and cs2 share a neighborhood with different outputs. -/
def crossConflictFreeBool (cs1 cs2 : List Constraint) : Bool :=
  cs1.all fun c1 =>
    cs2.all fun c2 =>
      !(c1.1 == c2.1) || (c1.2 == c2.2)

/-- The orbit constraints have no internal conflicts. -/
theorem orbitConstraints_conflictFree : conflictFreeBool orbitConstraints = true := by decide

/-- The Rule 110 binary constraints have no internal conflicts. -/
theorem rule110BinaryConstraints_conflictFree : conflictFreeBool rule110BinaryConstraints = true := by
  decide

/-- **CUP-11c core theorem**: The orbit constraints and Rule 110 binary constraints
    are cross-conflict-free for phi_a7 standard canonical ordering.

    This means: no orbit neighborhood is also a binary neighborhood with a different
    required output. Equivalently: the 10 + 8 = 18 constraints can all be satisfied
    simultaneously by a single function f : Fin 7 → Fin 7 → Fin 7 → Fin 7.

    Proof: by `decide`. The neighborhoods are from a finite type `(Fin 7)³` with 343
    elements; we check 10 × 8 = 80 pairs. -/
theorem cup11c_orbit_rule110_no_conflicts :
    crossConflictFreeBool orbitConstraints rule110BinaryConstraints = true := by decide

/-- The combined constraint list (orbit ++ Rule 110) is conflict-free as a whole. -/
theorem cup11c_combined_conflictFree :
    conflictFreeBool (orbitConstraints ++ rule110BinaryConstraints) = true := by decide

/-- The orbit and Rule 110 constraint neighborhoods are disjoint.
    No neighborhood appears in both lists. -/
theorem cup11c_neighborhood_disjoint :
    (orbitConstraints.all fun c1 =>
      rule110BinaryConstraints.all fun c2 => !decide (c1.1 = c2.1)) = true := by decide

/-- The number of constraints in the combined list is exactly 18. -/
theorem cup11c_n_fixed_neighborhoods :
    (orbitConstraints ++ rule110BinaryConstraints).length = 18 := by decide

/-- The orbit neighborhood set has exactly 10 distinct elements. -/
theorem orbitConstraints_length : orbitConstraints.length = 10 := by decide

/-- The Rule 110 constraint set has exactly 8 distinct elements. -/
theorem rule110BinaryConstraints_length : rule110BinaryConstraints.length = 8 := by decide

/-- **Existence theorem**: There is a function f : Fin 7 → Fin 7 → Fin 7 → Fin 7
    satisfying all orbit constraints. -/
theorem orbit_f_exists :
    ∃ f : Fin 7 → Fin 7 → Fin 7 → Fin 7,
      f 1 1 5 = 2 ∧ f 1 5 2 = 5 ∧ f 5 2 2 = 2 ∧ f 2 2 1 = 0 ∧ f 2 1 1 = 2 ∧
      f 2 2 5 = 5 ∧ f 2 5 2 = 6 ∧ f 5 2 0 = 5 ∧ f 2 0 2 = 3 ∧ f 0 2 2 = 5 := by
  -- The MDL-minimal witness f_MDL: use constraint values, 0 elsewhere.
  -- We use the constant-0 function patched at the 10 orbit neighborhoods.
  -- Lean's classical function-extension: define piecewise.
  refine ⟨fun l c r =>
    if l = 1 ∧ c = 1 ∧ r = 5 then 2
    else if l = 1 ∧ c = 5 ∧ r = 2 then 5
    else if l = 5 ∧ c = 2 ∧ r = 2 then 2
    else if l = 2 ∧ c = 2 ∧ r = 1 then 0
    else if l = 2 ∧ c = 1 ∧ r = 1 then 2
    else if l = 2 ∧ c = 2 ∧ r = 5 then 5
    else if l = 2 ∧ c = 5 ∧ r = 2 then 6
    else if l = 5 ∧ c = 2 ∧ r = 0 then 5
    else if l = 2 ∧ c = 0 ∧ r = 2 then 3
    else if l = 0 ∧ c = 2 ∧ r = 2 then 5
    else 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- **Existence theorem (combined)**: There is a function f satisfying all orbit constraints
    AND all Rule 110 binary constraints simultaneously.
    This is the machine-verified existence of a universal mod-7 CA with SM generation orbit. -/
theorem cup11c_universal_mod7_CA_exists :
    ∃ f : Fin 7 → Fin 7 → Fin 7 → Fin 7,
      -- Orbit constraints
      f 1 1 5 = 2 ∧ f 1 5 2 = 5 ∧ f 5 2 2 = 2 ∧ f 2 2 1 = 0 ∧ f 2 1 1 = 2 ∧
      f 2 2 5 = 5 ∧ f 2 5 2 = 6 ∧ f 5 2 0 = 5 ∧ f 2 0 2 = 3 ∧ f 0 2 2 = 5 ∧
      -- Rule 110 binary sublayer constraints
      f 0 0 0 = 0 ∧ f 0 0 1 = 1 ∧ f 0 1 0 = 1 ∧ f 0 1 1 = 1 ∧
      f 1 0 0 = 0 ∧ f 1 0 1 = 1 ∧ f 1 1 0 = 1 ∧ f 1 1 1 = 0 := by
  -- Witness: piecewise function, orbit values + Rule 110 values + 0 elsewhere.
  -- All 18 neighborhoods are distinct (proved by cup11c_neighborhood_disjoint).
  refine ⟨fun l c r =>
    -- Orbit neighborhoods
    if l = 1 ∧ c = 1 ∧ r = 5 then 2
    else if l = 1 ∧ c = 5 ∧ r = 2 then 5
    else if l = 5 ∧ c = 2 ∧ r = 2 then 2
    else if l = 2 ∧ c = 2 ∧ r = 1 then 0
    else if l = 2 ∧ c = 1 ∧ r = 1 then 2
    else if l = 2 ∧ c = 2 ∧ r = 5 then 5
    else if l = 2 ∧ c = 5 ∧ r = 2 then 6
    else if l = 5 ∧ c = 2 ∧ r = 0 then 5
    else if l = 2 ∧ c = 0 ∧ r = 2 then 3
    else if l = 0 ∧ c = 2 ∧ r = 2 then 5
    -- Rule 110 binary neighborhoods (no conflicts with orbit by cup11c_neighborhood_disjoint)
    else if l = 0 ∧ c = 0 ∧ r = 0 then 0
    else if l = 0 ∧ c = 0 ∧ r = 1 then 1
    else if l = 0 ∧ c = 1 ∧ r = 0 then 1
    else if l = 0 ∧ c = 1 ∧ r = 1 then 1
    else if l = 1 ∧ c = 0 ∧ r = 0 then 0
    else if l = 1 ∧ c = 0 ∧ r = 1 then 1
    else if l = 1 ∧ c = 1 ∧ r = 0 then 1
    else if l = 1 ∧ c = 1 ∧ r = 1 then 0
    -- All other neighborhoods: 0 (MDL-minimal canonical completion)
    else 0,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_,
    ?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

end CUP11ModSeven
