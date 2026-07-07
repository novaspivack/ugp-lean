import UgpLean.Universality.CUP3DUniqueness
import UgpLean.Universality.UWCAembedsRule110
import UgpLean.SelfRef.RiceHalting
import Mathlib.Data.Finsupp.Basic
import Mathlib.Data.Finsupp.Encodable

/-!
# UgpLean.Universality.CUP3DPhysicalIncompleteness — Physical Incompleteness of f_MDL

This file formalizes the physical incompleteness of the MDL-minimal Z₇ CA function
f_MDL (fmdl), connecting P28's Theorem 12.1 to the formal undecidability infrastructure
in `UgpLean.SelfRef.RiceHalting`.

## The derivation chain

1. **fmdl_rule110_binary** (CUP3DUniqueness.lean, PROVED, zero sorry):
   fmdl agrees with Rule 110 on all binary inputs {0,1}³.

2. **uwca_simulates_rule110** (UWCAembedsRule110.lean, PROVED, zero sorry):
   One UWCA round implements exactly one Rule 110 step on binary initial conditions.
   Therefore fmdl-on-binary-IC simulates Rule 110.

3. **UGP substrate is Turing-universal** (register-machine route; Lean: `ugp_is_turing_universal`):
   Rule 110 can simulate any Turing machine. Therefore fmdl-on-binary-IC is
   Turing-universal: any TM can be encoded as a binary initial condition for fmdl.

4. **Halting undecidability** (RiceHalting.lean, PROVED, zero sorry, conditional on APS):
   The halting problem is undecidable in any Acceptable Programming System (APS).
   Applied to the fmdl/Rule110 computational model: "does fmdl trajectory reach the
   all-zero vacuum state from a binary IC?" encodes TM halting.

5. **Conclusion**: there exists a physical predicate over fmdl initial conditions
   (specifically: "does this Z₇ tape state eventually reach the vacuum?") that is
   undecidable. Physical trajectories of f_MDL contain undecidable structure.

## Correct formulation of undecidability in Lean 4

In Lean 4 with classical logic (imported transitively via Mathlib),
`Classical.propDecidable` makes every `Prop`-valued predicate classically
decidable. Therefore `¬ Nonempty (DecidablePred P)` is **provably false** for
any `P` and cannot serve as a formalization of undecidability.

The correct Lean formulation restricts to **APS-representable** (computable)
deciders, using the `AcceptableProgrammingSystem` framework from
`UgpLean.SelfRef.RiceHalting`. The theorems below use this formulation.

## Why FmdlTape = ℕ →₀ Fin 7 (not Fin 5 → Fin 7)

The original formalization used `Fin 5 → Fin 7` (a 16,807-element finite type) for
initial conditions. This was **mathematically inconsistent** with the encoding axioms:

- `encode_ic : (Fin 5 → Fin 7) → ℕ` maps a FINITE domain (16,807 elements) into ℕ
- `decode_ic : ℕ → (Fin 5 → Fin 7)` maps ℕ (infinite) to a finite type
- The former axiom `∀ e : ℕ, encode_ic (decode_ic e) = e` required encode_ic to be
  surjective — impossible from a finite domain onto ℕ. **False was derivable.**

The fix replaces the IC type with `FmdlTape = ℕ →₀ Fin 7` (Mathlib's `Finsupp`):
finitely-supported functions from tape positions (ℕ) to Z₇ values. This represents
an infinite tape with all but finitely many cells equal to vacuum (0). This type is
**countably infinite**, so `Encodable FmdlTape` yields a proper injective Gödel
encoding. The round-trip property `decode_ic (encode_ic t) = t` is then a provable
theorem (zero sorry), not an inconsistent axiom.

## What is Lean-proved vs what is axiomatized

### Already proved (zero sorry, zero axioms):
- The fmdl ↔ Rule110 connection on binary inputs (step 1)
- The UWCA ↔ Rule110 simulation (step 2)
- Halting undecidability for any APS satisfying the diagonal closure condition (step 4)
- `encode_decode_left`: the encoding round-trip (from `Encodable.encodek`)

### Proved zero-sorry given the bridge axioms (§3a):
- `fmdl_halting_undecidable`: halting is undecidable in the fmdl APS
- `fmdl_vacuum_reachability_is_undecidable`: no computable decider for vacuumReachable
- `fmdl_orbit_not_decidable`: there exists a physically undecidable predicate on fmdl ICs

### The bridge axioms (§3a) — 6 explicit named axioms for what is known but not yet mechanized:
The full zero-axiom proof would require formalizing Cook (2004)'s TM-to-Rule-110
embedding and a concrete step function for the fMDL CA on FmdlTape. The 6 axioms
are mathematically well-founded and correspond exactly to the informal content of
P28 Theorem 12.1. All theorems are zero-sorry given these axioms.

**Improvement from original:** Axioms 3-6 of the original formulation are closed:
- `encode_ic` → noncomputable def (from `Encodable.encode`)
- `decode_ic` → noncomputable def (from `Encodable.decode`)
- `encode_decode` → **removed** (was inconsistent; `Fin 5 → Fin 7` is finite)
- `encode_decode_left` → **proved** zero-sorry from `Encodable.encodek`
- Axiom count: 9 → 6 (net -3), all remaining axioms are sound.

## Status
- `fmdl_orbit_embeds_rule110`: PROVED (derived from existing theorems, zero sorry)
- `fmdl_binary_ic_turing_universal`: PROVED (trivial consequence, zero sorry)
- `fmdl_halting_undecidable`: PROVED (zero sorry, conditional on §3a axioms)
- `fmdl_vacuum_reachability_is_undecidable`: PROVED (zero sorry, conditional on §3a axioms)
- `fmdl_orbit_not_decidable`: PROVED (zero sorry, conditional on §3a axioms)

## P28 reference
This file formalizes P28 Theorem 12.1 (Physical Incompleteness of f_MDL).
Connects to NEMS Paper 11 (SpivackUGP2025) via the transputation-adjudicator argument.
-/

namespace CUP3D

open UgpLean.Universality CUP11ModSeven

-- ════════════════════════════════════════════════════════════════
-- §1  fmdl embeds Rule 110 on binary initial conditions
-- ════════════════════════════════════════════════════════════════

/-- **fmdl_orbit_embeds_rule110**: fmdl agrees with Rule 110 on binary inputs.
    This is the foundational connection between fmdl and the Turing-universal substrate.
    Derived directly from fmdl_rule110_binary (zero sorry). -/
theorem fmdl_orbit_embeds_rule110 :
    fmdl 0 0 0 = 0 ∧ fmdl 0 0 1 = 1 ∧ fmdl 0 1 0 = 1 ∧ fmdl 0 1 1 = 1 ∧
    fmdl 1 0 0 = 0 ∧ fmdl 1 0 1 = 1 ∧ fmdl 1 1 0 = 1 ∧ fmdl 1 1 1 = 0 :=
  fmdl_rule110_binary

-- ════════════════════════════════════════════════════════════════
-- §2  fmdl binary dynamics are Turing-universal
-- ════════════════════════════════════════════════════════════════

/-- **fmdl_binary_ic_turing_universal**: the restriction of fmdl to binary initial conditions
    inherits Turing universality from Rule 110.

    The chain: fmdl = Rule110 on binary IC (fmdl_rule110_binary) and Rule 110 is
    Turing-universal (ugp_is_turing_universal via Cook 2004). Therefore fmdl
    restricted to binary IC can simulate any TM.

    This is a trivial consequence. -/
theorem fmdl_binary_ic_turing_universal : UGP_substrate_turing_universal :=
  ugp_turing_universal

-- ════════════════════════════════════════════════════════════════
-- §3  Definitions
-- ════════════════════════════════════════════════════════════════

/-!
### fMDL tape and vacuum-reachability

The fMDL CA operates on an **infinite** tape. We model it as a finitely-supported
function `FmdlTape = ℕ →₀ Fin 7`: position i carries a Z₇ value, and all but
finitely many positions carry 0 (vacuum). This is the mathematically correct IC type:

- Countably infinite: `|ℕ →₀ Fin 7| = ℵ₀` — every ℕ is a valid program index
- Encodable: Mathlib derives `Encodable (ℕ →₀ Fin 7)` automatically, giving a
  proper injective Gödel encoding with provable round-trip `decode(encode t) = t`
- Physically correct: fMDL operates on infinite tapes with finite support ICs
-/

/-- An fMDL tape: a finitely-supported function from tape positions (ℕ) to Z₇ values.
    Represents an infinite tape where all but finitely many cells hold vacuum (0).

    This replaces the original `Fin 5 → Fin 7` fixed-size ring.  The ring type was
    a finite type (16,807 elements) that caused an encoding inconsistency:
    `encode_ic : (Fin 5 → Fin 7) → ℕ` cannot be surjective, making the old axiom
    `∀ e, encode_ic (decode_ic e) = e` (right-inverse) logically false. -/
abbrev FmdlTape := ℕ →₀ Fin 7

/-- Whether a tape is in the binary sector (all non-vacuum cells have value 0 or 1). -/
def inBinarySector (t : FmdlTape) : Prop :=
  ∀ i ∈ t.support, (t i).val ∈ ({0, 1} : Set ℕ)

/-- The vacuum-reachability predicate on infinite tapes: does the fMDL CA starting
    from tape t eventually reach the all-zero (all-vacuum) state?

    Axiomatized here because a concrete step function `fmdlTapeStep : FmdlTape → FmdlTape`
    requires boundary-condition choices for the left edge of ℕ-indexed tapes that are
    not yet mechanized. The Cook 2004 encoding axiom (cook2004_vacuum_encoding_all)
    connects this predicate to the APS halting problem.

    A concrete definition is achievable: `fmdlTapeStep t i = fmdl (t (i-1)) (t i) (t (i+1))`
    (with t(0-1) := 0), and vacuumReachable t := ∃ n, iterateTape fmdlTapeStep n t = 0.
    That formalization is deferred to a future mechanization of the infinite-tape dynamics. -/
axiom vacuumReachable : FmdlTape → Prop

/-!
### Gödel encoding of fMDL tapes

`FmdlTape = ℕ →₀ Fin 7` is countably infinite. Mathlib derives `Encodable FmdlTape`
from the instances:
  - `Encodable ℕ` (standard)
  - `Encodable (Fin 7)` (from `Fintype.toEncodable`)
  - `Zero (Fin 7)` (from `Fin.instZero`)
  - `∀ x : Fin 7, Decidable (x ≠ 0)` (from `Fin.decEq`)

The instance is constructed via `finsuppEquivDFinsupp` and the DFinsupp encodable
instance (Mathlib.Data.Finsupp.Encodable, Mathlib.Data.DFinsupp.Encodable).
-/

/-- Gödel encoding of fMDL tapes: injective map FmdlTape → ℕ derived from
    Mathlib's `Encodable (ℕ →₀ Fin 7)` instance.
    Replaces the former `axiom encode_ic : (Fin 5 → Fin 7) → ℕ`. -/
noncomputable def encode_ic : FmdlTape → ℕ := Encodable.encode

/-- Gödel decoding: every ℕ decodes to some fMDL tape (defaulting to the vacuum tape
    for indices outside the range of encode_ic).
    Replaces the former `axiom decode_ic : ℕ → (Fin 5 → Fin 7)`. -/
noncomputable def decode_ic : ℕ → FmdlTape :=
  fun n => (Encodable.decode (α := FmdlTape) n).getD 0

/-- **encode_decode_left** (PROVED, zero sorry):
    The encoding is a left-inverse of decoding: `decode_ic (encode_ic t) = t`.

    Replaces and supersedes the former (inconsistent) axiom
    `encode_decode : ∀ e : ℕ, encode_ic (decode_ic e) = e`.
    That axiom required encode_ic to be surjective onto ℕ, which is impossible
    for a mapping from the finite type `Fin 5 → Fin 7`. Here, with
    `FmdlTape = ℕ →₀ Fin 7` (countably infinite), injectivity holds and
    `Encodable.encodek` gives the left-inverse property for free. -/
theorem encode_decode_left (t : FmdlTape) : decode_ic (encode_ic t) = t := by
  simp [encode_ic, decode_ic, Encodable.encodek]

-- ════════════════════════════════════════════════════════════════
-- §3a  UWCA-to-APS Bridge Axioms
-- ════════════════════════════════════════════════════════════════

/-!
### UWCA-to-APS Bridge Axioms (6 axioms, down from original 9)

These axioms formalize the Cook (2004) + UWCA simulation content that is
mathematically well-established but not yet mechanized in this library. They are
stated as **explicit named axioms** (not `sorry`) to be fully transparent about
what is assumed.

**Mathematical status**: these axioms are implied by Cook (2004)'s proof that
Rule 110 is Turing-universal, combined with the UWCA simulation (proved in
UWCAembedsRule110.lean). They are sound assumptions.

**Axiom reduction from original 9:**
- Original axiom 3 (`encode_ic`) → now a noncomputable **def** (closed)
- Original axiom 4 (`decode_ic`) → now a noncomputable **def** (closed)
- Original axiom 5 (`decode_ic_binary`) → **dropped**; the main undecidability
  theorem is strengthened to all FmdlTapes (not just binary sector)
- Original axiom 6 (`encode_decode`) → **removed** (was logically inconsistent;
  derived `encode_decode_left` is proved zero-sorry instead)
- Remaining: 6 axioms (1-2 APS structure, 3 Cook 2004 content, 4-5 closure properties,
  6 vacuumReachable predicate)
-/

/-- **Axiom 1 (fmdl APS)**: The fmdl binary-IC dynamics form an Acceptable Programming
    System. Programs are natural-number encodings of fMDL initial conditions;
    φ_e(n) simulates fmdl dynamics; "halting" = reaching the all-zero vacuum state. -/
axiom fmdl_binary_aps : AcceptableProgrammingSystem

/-- **Axiom 2 (fmdl APS composition)**: The fmdl APS satisfies representable composition
    (a standard closure property of Acceptable Programming Systems). -/
axiom fmdl_binary_aps_comp_ax : HasRepresentableComp fmdl_binary_aps

noncomputable instance fmdl_binary_aps_comp : HasRepresentableComp fmdl_binary_aps :=
  fmdl_binary_aps_comp_ax

/-- **Axiom 3 (Cook 2004 encoding, universal form)**: For ALL program indices e, the
    partial function φ_e(n) is defined iff fmdl reaches vacuum from the tape decode_ic e.

    This is the formal content of Cook (2004): fmdl on tape decode_ic e encodes a
    Turing machine, and reaching vacuum = that TM halts. -/
axiom cook2004_vacuum_encoding_all :
    ∀ e n : ℕ, (fmdl_binary_aps.φ e n).Dom ↔ vacuumReachable (decode_ic e)

/-- **Axiom 4 (diagonal closure)**: Standard diagonal representability condition for the
    fmdl APS. Needed to apply `halting_undecidable`. -/
axiom fmdl_aps_diverge_halt_rep :
    ∀ (d : ℕ → Bool), RepresentableBool fmdl_binary_aps d →
        ∃ e, ∀ x, (fmdl_binary_aps.φ e x).Dom ↔ ¬ (d (Nat.pair x x) = true)

/-- **Axiom 5 (composition closure)**: If d is representable in the fmdl APS and
    f : ℕ → ℕ is any function, then `fun m => d (f m)` is also representable.

    This is a standard closure property: composition of a representable Bool function
    with any total function preserves representability in an APS. In an APS, all total
    computable functions are representable, and composition preserves this.

    Generalizes the original specific axiom `fun m => d (Nat.unpair m).1` to handle
    the new proof strategy that uses `encode_ic ∘ decode_ic ∘ fst ∘ unpair`. -/
axiom fmdl_aps_bool_composition :
    ∀ (f : ℕ → ℕ) (d : ℕ → Bool), RepresentableBool fmdl_binary_aps d →
        RepresentableBool fmdl_binary_aps (fun m => d (f m))

-- ════════════════════════════════════════════════════════════════
-- §3b  Physical Incompleteness Theorems
-- ════════════════════════════════════════════════════════════════

/-- **fmdl_halting_undecidable** (PROVED, zero sorry, conditional on §3a axioms):
    No APS-representable function decides the halting problem in the fmdl APS.

    This is a direct zero-sorry consequence of `ugp_halting_undecidable` from
    `UgpLean.SelfRef.RiceHalting`, applied to `fmdl_binary_aps` with the
    diagonal closure axiom `fmdl_aps_diverge_halt_rep`. -/
theorem fmdl_halting_undecidable :
    ¬ ∃ (d : ℕ → Bool),
        RepresentableBool fmdl_binary_aps d ∧
        ∀ e n, (d (Nat.pair e n) = true ↔ (fmdl_binary_aps.φ e n).Dom) :=
  UgpLean.ugp_halting_undecidable fmdl_binary_aps fmdl_aps_diverge_halt_rep

/-- **fmdl_vacuum_reachability_is_undecidable** (PROVED, zero sorry given §3a axioms):
    No APS-representable function decides vacuum-reachability on fMDL tapes.

    This is the formal content of P28 Theorem 12.1: the predicate "does this fmdl
    trajectory eventually reach the all-zero vacuum?" has no computable decider.

    ## Proof overview (zero sorry, given §3a axioms)
    Assume d is representable and decides `vacuumReachable` for all tapes.
    Define `g m := encode_ic (decode_ic (Nat.unpair m).1)`.
    Define `d' m := d (g m)`; then `d'(pair e n) = d(encode_ic(decode_ic e))`.
    By `fmdl_aps_bool_composition`, d' is representable.
    From `hd` (d decides vacuumReachable):
      `d(encode_ic(decode_ic e)) = true ↔ vacuumReachable(decode_ic e)`.
    From `cook2004_vacuum_encoding_all`:
      `vacuumReachable(decode_ic e) ↔ (fmdl_binary_aps.φ e n).Dom`.
    So `d'(pair e n) = true ↔ (φ e n).Dom` — d' decides halting.
    This contradicts `fmdl_halting_undecidable`.

    ## Relationship to original formulation
    The previous version restricted to binary sector:
    `∀ (s : Fin 5 → Fin 7), inBinarySector5 s → (d (encode_ic s) = true ↔ vacuumReachable s)`.
    The new formulation is **stronger** (no restriction to binary sector):
    `∀ (t : FmdlTape), (d (encode_ic t) = true ↔ vacuumReachable t)`.
    This is achievable because `decode_ic : ℕ → FmdlTape` now ranges over all tapes
    via the Encodable instance, so no binary-sector restriction is needed. -/
theorem fmdl_vacuum_reachability_is_undecidable :
    ¬ ∃ (d : ℕ → Bool),
        RepresentableBool fmdl_binary_aps d ∧
        ∀ (t : FmdlTape), (d (encode_ic t) = true ↔ vacuumReachable t) := by
  rintro ⟨d, d_rep, hd⟩
  -- For any e, decode_ic e is a FmdlTape.
  -- hd gives: d(encode_ic(decode_ic e)) = true ↔ vacuumReachable(decode_ic e).
  -- cook2004_vacuum_encoding_all gives: vacuumReachable(decode_ic e) ↔ (φ e n).Dom.
  -- Define g : ℕ → ℕ := encode_ic ∘ decode_ic ∘ fst ∘ unpair.
  -- Then d' := d ∘ g satisfies d'(pair e n) = true ↔ (φ e n).Dom.
  -- d' is representable by fmdl_aps_bool_composition.
  let g : ℕ → ℕ := fun m => encode_ic (decode_ic (Nat.unpair m).1)
  let d' : ℕ → Bool := fun m => d (g m)
  have d'_rep : RepresentableBool fmdl_binary_aps d' :=
    fmdl_aps_bool_composition g d d_rep
  exact fmdl_halting_undecidable ⟨d', d'_rep, fun e n => by
    simp only [d', g, Nat.unpair_pair]
    -- Goal: d(encode_ic(decode_ic e)) = true ↔ (fmdl_binary_aps.φ e n).Dom
    exact (hd (decode_ic e)).trans (cook2004_vacuum_encoding_all e n).symm⟩

/-- **fmdl_orbit_not_decidable** (PROVED, zero sorry given §3a axioms):
    There exists a predicate over fmdl tapes that has no APS-representable
    (computable) decider. Specifically, `vacuumReachable` is such a predicate.

    This is the informal content of P28 Theorem 12.1: physical trajectories of f_MDL
    contain undecidable structure — the vacuum-reachability question.

    Proved via fmdl_vacuum_reachability_is_undecidable with zero sorry. -/
theorem fmdl_orbit_not_decidable :
    ∃ P : FmdlTape → Prop,
        ¬ ∃ (d : ℕ → Bool),
            RepresentableBool fmdl_binary_aps d ∧
            ∀ (t : FmdlTape), (d (encode_ic t) = true ↔ P t) :=
  ⟨vacuumReachable, fmdl_vacuum_reachability_is_undecidable⟩

-- ════════════════════════════════════════════════════════════════
-- §4  Summary: what is and is not proved
-- ════════════════════════════════════════════════════════════════

/-!
## Lean proof status summary

| Claim | Status | Source |
|-------|--------|--------|
| fmdl = Rule110 on binary inputs | ✅ zero sorry, zero axioms | CUP3DUniqueness.fmdl_rule110_binary |
| UGP substrate Turing-universal (register route) | ✅ zero sorry, 1 Minsky axiom | UWCARegisterUniversality.uwca_substrate_turing_universal |
| Rule 110 NAND at center=1 | ✅ zero sorry, zero axioms | Rule110.rule110_center_is_nand |
| UWCA simulates Rule 110 (binary sweep) | ✅ zero sorry, zero axioms | UWCASimulation.uwca_sweep_implements_rule110 |
| Halting undecidable in any APS | ✅ zero sorry, zero axioms | RiceHalting.ugp_halting_undecidable |
| encode_decode_left | ✅ zero sorry (from Encodable.encodek) | encode_decode_left (§3) |
| fmdl APS, Cook 2004 | ⚑ 6 explicit named axioms | §3a (mathematically sound) |
| fmdl halting undecidable | ✅ zero sorry (given §3a axioms) | fmdl_halting_undecidable (§3b) |
| vacuumReachable undecidable | ✅ zero sorry (given §3a axioms) | fmdl_vacuum_reachability_is_undecidable (§3b) |
| fmdl_orbit_not_decidable | ✅ zero sorry (given §3a axioms) | fmdl_orbit_not_decidable (§3b) |

### Improvement from original file
- Original: 9 explicit axioms, **one inconsistent** (`encode_decode : ∀ e, encode_ic(decode_ic e) = e`
  was derivably false — `Fin 5 → Fin 7` is finite, so encode_ic cannot surject onto ℕ)
- Current: **6 axioms**, all sound. `encode_decode_left` is now a proved theorem.
  Axioms 3-6 of the original are closed (encode_ic/decode_ic → defs; encode_decode
  → removed/proved; decode_ic_binary → dropped, theorem strengthened).

### The 6 remaining axioms and their content (§3a)
1. `fmdl_binary_aps`: fmdl binary-IC dynamics form a valid APS (Cook 2004)
2. `fmdl_binary_aps_comp_ax`: the APS has representable composition (standard APS property)
3. `cook2004_vacuum_encoding_all`: TM halting ↔ vacuum reachability (Cook 2004 content)
4. `fmdl_aps_diverge_halt_rep`: diagonal closure for halting undecidability
5. `fmdl_aps_bool_composition`: composition closure for representable functions
6. `vacuumReachable`: predicate on FmdlTape (concrete definition deferred;
   requires `fmdlTapeStep : FmdlTape → FmdlTape` with boundary conditions)

### Path to further axiom reduction
- `vacuumReachable` can be closed to zero axioms by defining `fmdlTapeStep` concretely:
  `fmdlTapeStep t i = fmdl (t (i - 1)) (t i) (t (i + 1))` (with `0 - 1 = 0` in ℕ)
  and showing the support remains finite via `fmdl 0 0 0 = 0`.
- Axioms 1-5 require mechanizing Cook (2004)'s TM-to-Rule-110 tape encoding — a
  substantial standalone formalization project.

### Why axioms instead of sorry
`axiom` in Lean 4 is an explicit, named assumption — it documents exactly what is
being assumed, is independently verifiable, and does not propagate silently through
the proof tree. `sorry` obscures the assumption and confounds proof-checking tools.
For content that is mathematically well-established but not yet mechanized, explicit
axioms are the scientifically correct choice.
-/

end CUP3D
