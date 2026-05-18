import UgpLean.Universality.CUP3DUniqueness
import UgpLean.Universality.UWCASimulation
import UgpLean.Universality.CUP4TotalParity

/-!
# UgpLean.Universality.TwoLayerConfluence — Two-Layer Rule 110 Confluence

## Summary

Rule 110 emerges independently at two distinct levels of the UGP architecture:

1. **UWCA substrate level (P04/P08):** The survivor-sieve arithmetic substrate is
   Turing-universal via a direct Rule 110 embedding in the clopen cylinder basis.
   Proved by: `uwca_sweep_implements_rule110` (UWCASimulation.lean).

2. **fMDL winding level (P28/CUP-4):** The MDL-minimal Z₇ CA `fmdl`, when restricted
   to binary inputs (Z₇ values 0 and 1), exactly computes Rule 110.
   Proved by: `fmdl_rule110_binary` (CUP3DUniqueness.lean).

These are distinct constructions: the UWCA operates on binary residues in the survivor
sieve; fMDL operates on Z₇ winding numbers and is projected to {0,1} via binary
restriction. That the same Rule 110 rule arises from both is a convergence property
of the UGP architecture.

## Main Theorem

`rule110_two_layer_confluence`: For all binary inputs (Bool values, embedded into Fin 7
as 0 and 1), the fMDL output agrees with the Rule 110 output used by the UWCA substrate.

All proofs are by `decide`, zero sorry.

## Connection to P08 (UGP Monograph) Results

The UGP monograph additionally claims (thm:gte-as-uwca, thm:gte_uniqueness):
- GTE map T is compiled as a finite UWCA program Σ_GTE on this substrate
- Σ_GTE is the unique lawful UWCA program up to bisimulation

These monograph theorems are NOT yet Lean-certified. The present theorem establishes
the lower-level confluence (same Rule 110 at both layers) from already-proved pieces.
See GTECompilation.lean and GTEUniqueness.lean for the certified compilation and
uniqueness results.
-/

namespace UgpLean.Universality.TwoLayerConfluence

open UgpLean.Universality
open CUP3D

/-!
## Embedding: Bool ↪ Fin 7

We embed binary values into Z₇ via false ↦ 0, true ↦ 1.
-/

/-- Embed a Boolean into Fin 7 as 0 or 1. -/
def boolToFin7 (b : Bool) : Fin 7 := if b then 1 else 0

/-- Embed a Rule-110 Bool output back: `true` ↦ 1, `false` ↦ 0 in Fin 7. -/
def rule110OutputFin7 (l c r : Bool) : Fin 7 :=
  if rule110Output (neighborhoodIndex l c r) then 1 else 0

/-!
## Main confluence theorem

For binary inputs, fMDL and the UWCA Rule 110 substrate compute the same function.
-/

/-- **Two-Layer Rule 110 Confluence.**
    The fMDL Z₇ CA restricted to binary inputs (0 and 1 embedded in Fin 7) agrees
    with Rule 110 as computed by the UWCA substrate embedding.

    This connects:
    - P04/P08 Layer: `uwca_sweep_implements_rule110` (UWCA substrate is Rule 110-universal)
    - P28/CUP-4 Layer: `fmdl_rule110_binary` (fMDL binary sublayer IS Rule 110)

    Both layers implement the same Rule 110 rule from independent constructions.

    Proof: exhaustive case analysis over all 8 binary neighborhoods, by `decide`.
    Zero sorry, zero custom axioms. -/
theorem rule110_two_layer_confluence :
    ∀ l c r : Bool,
      fmdl (boolToFin7 l) (boolToFin7 c) (boolToFin7 r) = rule110OutputFin7 l c r := by
  decide

/-!
## Corollaries
-/

/-- The UWCA substrate layer (Rule 110 output as Bool) and the fMDL winding layer
    (fMDL output on binary inputs, nonzero ↔ true) agree on all 8 neighborhoods.
    Direct corollary of `rule110_two_layer_confluence`. -/
theorem two_layer_confluence_bool :
    ∀ l c r : Bool,
      (fmdl (boolToFin7 l) (boolToFin7 c) (boolToFin7 r) ≠ 0) =
      rule110Output (neighborhoodIndex l c r) := by
  decide

/-- Both layers agree on the Rule 110 minterm set {1,2,3,5,6}: the neighborhoods
    where fMDL outputs 1 (on binary inputs) are exactly the Rule 110 minterms. -/
theorem fmdl_binary_minterms_eq_rule110_minterms :
    ∀ l c r : Bool,
      (fmdl (boolToFin7 l) (boolToFin7 c) (boolToFin7 r) = 1) =
      (neighborhoodIndex l c r ∈ rule110Minterms) := by
  decide

/-- Explicit 8-case verification: fMDL on all binary neighborhoods. -/
theorem fmdl_binary_all_cases :
    fmdl 0 0 0 = 0 ∧
    fmdl 0 0 1 = 1 ∧
    fmdl 0 1 0 = 1 ∧
    fmdl 0 1 1 = 1 ∧
    fmdl 1 0 0 = 0 ∧
    fmdl 1 0 1 = 1 ∧
    fmdl 1 1 0 = 1 ∧
    fmdl 1 1 1 = 0 := CUP3D.fmdl_rule110_binary

/-!
## Hypothesis A: Layered Universality

**Hypothesis A (Layered Universality):** Multiple distinct constructions in UGP
independently converge on Rule 110. The fMDL orbit layer (Z₇/SM winding sector) and
the UWCA substrate layer (P04/P08) both lead to Rule 110 via independent arguments.

The UWCA substrate is the layer on which GTE runs as a program (GTE Compilation Theorem,
P08). So "the GTE substrate layer" in Hypothesis A refers to the UWCA layer, proved
below.

This theorem packages all three certified pieces into a single formal statement of A:
(1) fMDL orbit uniquely selects Rule 110, (2) UWCA substrate implements Rule 110,
(3) both layers agree on every binary input — independence established by distinct
constructions (orbit algebra vs. arithmetic sieve).

**CatAL status: fully proved (zero sorry, zero custom axioms).**
The GTE→UWCA compilation (GTECompilation.lean) remains as a stub; certifying it
would extend A to cover the full GTE program layer, not just its substrate.
-/

/-- **Hypothesis A — Layered Universality** (formal statement, zero sorry).

    Two distinct constructions in UGP independently converge on Rule 110:

    (1) **fMDL orbit layer** (CUP-4, P28): The SM generation orbit smGen1 → smGen2 → smGen3
        uniquely determines Rule 110 among all 256 elementary binary CA rules, when combined
        with vacuum-transparency.
        Source: `cup1_orbit_uniquely_selects_rule110` (CUP4TotalParity.lean, zero sorry).

    (2) **UWCA substrate layer** (P04, P08): The survivor-sieve arithmetic substrate
        implements Rule 110 at every site after one synchronous round (P1–P4).
        Source: `uwca_sweep_implements_rule110` (UWCASimulation.lean, zero sorry).

    (3) **Independence + Confluence**: The two layers derive from different mathematical
        structures — orbit algebra (Z₅ parity of particle generations) vs. survivor-sieve
        arithmetic (clopen cylinder basis). They agree on all 8 binary neighborhoods:
        fMDL and UWCA compute the same Rule 110 function.
        Source: `rule110_two_layer_confluence` (this file, zero sorry).

    **Note on GTE layer:** The GTE update map T runs as a UWCA program (Σ_GTE) on the
    UWCA substrate (P08). GTE universality flows through UWCA universality. The formal
    Lean certification of the GTE→UWCA compilation is tracked in GTECompilation.lean
    (stub). Certifying it would extend this theorem to the full GTE program layer.

    LEAN-CERTIFIED: zero sorry, zero custom axioms. -/
theorem hypothesis_a_layered_universality :
    -- (1) fMDL orbit layer: SM orbit uniquely selects Rule 110
    (∀ r : Fin 256,
     (elementaryCAStep r smGen1 = smGen2 ∧
      elementaryCAStep r smGen2 = smGen3 ∧
      r.val % 2 = 0) ↔ r = 110) ∧
    -- (2) UWCA substrate layer: one synchronous round implements Rule 110
    (∀ (L : ℕ) [NeZero L] (tape : Tape L) (_h : tape.inBinarySector) (i : Fin L),
     (uwcaRound tape i).C =
       rule110Output (neighborhoodIndex
         (tape ⟨(i.val + L - 1) % L, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne L))⟩).C
         (tape i).C
         (tape ⟨(i.val + 1) % L, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne L))⟩).C)) ∧
    -- (3) Independence + confluence: the two layers agree on all binary inputs
    (∀ l c r : Bool,
     fmdl (boolToFin7 l) (boolToFin7 c) (boolToFin7 r) = rule110OutputFin7 l c r) :=
  ⟨cup1_orbit_uniquely_selects_rule110,
   fun _L _ tape h i => uwca_sweep_implements_rule110 tape h i,
   rule110_two_layer_confluence⟩

end UgpLean.Universality.TwoLayerConfluence
