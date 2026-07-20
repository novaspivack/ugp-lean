import UgpLean.Spacetime.SpacelikeCutAreaScaling
import UgpLean.Spacetime.HolographicScaling
import UgpLean.Algebra.ChargeFromPolynomial

/-!
# Intrinsic Area-Scaling of a Spacelike Cut in the Three-Tape ℤ₇ CMCA

Ports `SpacelikeCutAreaScaling`'s intrinsic, area-scaling (`L^2`) cut-crossing-link
count from the binary `GTE.Spacetime.CausalGraph` proof-of-concept to the **actual**
three-tape ℤ₇-valued CMCA substrate (`HolographicScaling.lean`'s
`(Fin L → ZMod 7) × (Fin L → ZMod 7) × (Fin L → ZMod 7)`) named by the epic's Stage A
audit. This is EPIC_103's `LT-103-06`.

## Grounding in the corpus (read before trusting any claim below)

- **P45 §"The Dimensional Protocol Principle" (`sec:dpp`), "Derivation of 3+1D Minkowski
  Structure":** *"Each spatial coordinate `j ∈ {x,y,z}` is the cell index along tape
  `j`... The metric is `ds² = −c²(dτc)² + ℓc²(dx²+dy²+dz²)`."* This is the corpus's own
  stated coordinate assignment: a spatial point is a triple `(x,y,z)` with each
  coordinate an independent index into ONE tape — i.e. the spatial lattice is
  `Fin L × Fin L × Fin L`, exactly `GTE.Spacetime.CausalGraph.CausalNode`'s spatial part.
- **P45 §"Gravitational Coupling" (`sec:gravity`), eq. `pmdl-action`,
  "Step A (Local)":** the gravitational source density is
  `ρ(x) = p(w_x(x), w_y(x), w_z(x))/6`, with `p` the GTE polynomial
  (`ChargeFromPolynomial.gtePolynomial`).

## A genuine ambiguity in the corpus, resolved here by an explicit, checked choice

P45's own prose is **not fully precise** about what `w_j(x)` means when `x` is written
as ranging over `ℤ³` (eq. `pmdl-action`: `Σ_{x∈ℤ³} p(w_x(x), w_y(x), w_z(x))`). Two
readings are possible:

- **(A) Each tape's value at a 3D point depends only on that axis's own 1D coordinate**
  — i.e. `w_x : Fin L → ZMod 7` is genuinely 1D, and `w_x` "evaluated at `x=(x₁,x₂,x₃)`"
  really means `w_x(x₁)` (the first component only). Total independent input data:
  `3` functions `Fin L → ZMod 7`, i.e. `7^(3L)` configurations.
- **(B) Each tape is itself a genuinely 3D scalar field** `w_j : Fin L × Fin L × Fin L →
  ZMod 7` (three independent fields on the same 3D lattice — "tape" meaning "flavor
  component," not "1D array"). Total independent input data: `7^(3·L^3)` configurations.

**These are NOT equivalent, and the corpus's own certified cardinality decides between
them.** `HolographicScaling.three_tape_state_card` (imported here) certifies the
three-tape configuration space has cardinality **exactly `7^(3L)`** — matching reading
**(A)**, not (B) (`7^(3·L^3)` would flatly contradict this certified count, and would
also contradict the entire point of §"Holographic structure": (B)'s field content is
*larger* than the naive `7^(L^3)` lattice, the opposite of holographic compression).
**Reading (A) is adopted here as the only reading consistent with the corpus's own
Lean-certified state-space cardinality; this is stated as an explicit, checked design
choice, not an unstated assumption** — see `three_tape_config_card_confirms_reading_A`
below.

## What this module establishes

Given reading (A): the spatial lattice `SpatialPoint L := Fin L × Fin L × Fin L` (one
coordinate per tape, per the DPP citation above) inherits the *exact same* intrinsic,
zero-metric, area-scaling (`L²`) cut-crossing-link count already proved for
`GTE.Spacetime.CausalGraph` in `SpacelikeCutAreaScaling.lean` — because it is, after
unfolding definitions, **the identical type with the identical adjacency structure**
(`CausalNode L T`'s spatial part is definitionally `Fin L × Fin L × Fin L`, and
`SpacelikeAdj` restricted to a fixed time is definitionally the adjacency defined here).
This is confirmed by `spatialPoint_eq_causalNode_spatial_part` and
`spatialAdj_eq_spacelikeAdj_at_shared_time` below — the
"sanity check" against the binary-graph proof-of-concept requested for this port.

## Honest scope statement

This closes the **spatial-lattice/area-scaling** half of Stage A's "not yet defined"
gap for the real three-tape substrate, under the checked reading-(A) interpretation. It
does **not** yet: (i) formalize the ρ-reconstruction map's role as the physical boundary
entropy of a causal *diamond* (only the flat spatial-lattice cut is treated here, not a
genuine causal-diamond cross-section with a horizon/null-congruence structure as H1's
Raychaudhuri-based derivation needs); (ii) compute an actual entropy `S` or slope `η`
(Stage B's job, not this one). See the epic lab note for the precise boundary of what
is and is not established.
-/

namespace GTE.Spacetime.ThreeTape

open HolographicScaling
open ChargeFromPolynomial
open GTE.Spacetime

variable {L : ℕ}

/-- The three-tape ℤ₇ CMCA configuration: one ℤ₇-valued 1D tape per spatial axis,
    exactly `HolographicScaling`'s (unnamed) state type, named here for clarity. -/
abbrev ThreeTapeConfig (L : ℕ) := (Fin L → ZMod 7) × (Fin L → ZMod 7) × (Fin L → ZMod 7)

/-- **Reading-(A) confirmation.** The three-tape configuration space has cardinality
    exactly `7^(3L)` — matching `HolographicScaling.three_tape_state_card` verbatim
    (restated here on the named `ThreeTapeConfig` type for direct reference). This is
    the check that selects reading (A) over reading (B) in the module docstring: under
    (B) the cardinality would be `7^(3*L^3)`, not `7^(3L)`. -/
theorem three_tape_config_card_confirms_reading_A (L : ℕ) :
    Fintype.card (ThreeTapeConfig L) = 7 ^ (3 * L) :=
  HolographicScaling.three_tape_state_card L

/-- A spatial point in the emergent 3D lattice: a triple of tape-cell indices, one per
    axis, per the DPP's own coordinate assignment (P45 §sec:dpp: "each spatial
    coordinate `j` is the cell index along tape `j`"). -/
abbrev SpatialPoint (L : ℕ) := Fin L × Fin L × Fin L

/-- The gravitational source density at a spatial point, reconstructed from the three
    tapes' own values at that point's respective coordinate — P45 eq. `pmdl-action`,
    "Step A (Local)": `ρ(x) = p(w_x(x), w_y(x), w_z(x))/6`. The `/6` normalization is
    omitted here (this module is about the lattice/cut structure, not the physical
    normalization); this is the un-normalized GTE polynomial value. -/
def sourceDensity (cfg : ThreeTapeConfig L) (pt : SpatialPoint L) : ZMod 7 :=
  gtePolynomial (cfg.1 pt.1) (cfg.2.1 pt.2.1) (cfg.2.2 pt.2.2)

/-- **Sanity check against the binary-graph proof-of-concept, part 1 (type identity).**
    `SpatialPoint L` unfolds to exactly `Fin L × Fin L × Fin L` — literally the spatial
    part of `GTE.Spacetime.CausalGraph.CausalNode L T` (`:= Fin (T+1) × Fin L × Fin L ×
    Fin L`) for any `T`: dropping the leading time factor leaves the identical type,
    by `rfl`. Not an analogy; the same type. -/
theorem spatialPoint_eq_causalNode_spatial_part :
    (SpatialPoint L) = (Fin L × Fin L × Fin L) := rfl

/-- Spatial adjacency between two lattice points, reusing `GTE.Spacetime.FinAdj` — the
    same relation `CausalGraph`'s spatial adjacency uses (not redefined, per "verify,
    do not rebuild"): exactly one coordinate differs by
    one tape-cell step (`FinAdj`), the other two coordinates equal. This is the
    fixed-time restriction of `CausalGraph.SpacelikeAdj` — reused in spirit and
    structure, restated here on the bare `SpatialPoint L` type (no time/state
    components needed for the cut-area count). -/
def SpatialAdj (p1 p2 : SpatialPoint L) : Prop :=
  (FinAdj p1.1 p2.1 ∧ p1.2.1 = p2.2.1 ∧ p1.2.2 = p2.2.2) ∨
  (p1.1 = p2.1 ∧ FinAdj p1.2.1 p2.2.1 ∧ p1.2.2 = p2.2.2) ∨
  (p1.1 = p2.1 ∧ p1.2.1 = p2.2.1 ∧ FinAdj p1.2.2 p2.2.2)

/-- **Consistency theorem (the requested sanity check).** `SpatialAdj` on
    `SpatialPoint L` is *exactly* `SpacelikeAdj L T` restricted to nodes sharing a
    common time `t` — the two constructions are not merely analogous, they agree
    verbatim once the (trivial, time-independent) time-equality clause is factored out.
    This confirms the three-tape port is a genuine specialization of the causal-graph
    proof-of-concept, not an independent, possibly-inconsistent redefinition. -/
theorem spatialAdj_eq_spacelikeAdj_at_shared_time (T : ℕ) (t : Fin (T + 1))
    (p1 p2 : SpatialPoint L) :
    SpatialAdj p1 p2 ↔ SpacelikeAdj L T (t, p1) (t, p2) := by
  unfold SpatialAdj SpacelikeAdj
  simp

/-- `cutPred`, `cutEdgeAt`, injectivity, and completeness are reused directly from
    `SpacelikeCutAreaScaling` at a fixed time `t := 0` — the fixed-time restriction is
    literally definitionally faithful to `SpatialAdj` (previous theorem), so the same
    parametrization proof carries over with no new casework. -/
theorem cutEdgeAt_spatial_is_adj (c : Fin L) (hc : 1 ≤ c.val) (yz : Fin L × Fin L) :
    SpatialAdj (cutPred c hc, yz.1, yz.2) (c, yz.1, yz.2) := by
  refine Or.inl ⟨cutPred_finAdj c hc, rfl, rfl⟩

/-- The crossing-edge set for the three-tape spatial lattice: the image of the
    `(y,z)`-parametrization at coordinate cut `x = c`, restated on `SpatialPoint L`. -/
noncomputable def threeTapeCutCrossingFinset (c : Fin L) (hc : 1 ≤ c.val) :
    Finset (SpatialPoint L × SpatialPoint L) :=
  Finset.image (fun yz : Fin L × Fin L => ((cutPred c hc, yz.1, yz.2), (c, yz.1, yz.2)))
    Finset.univ

/-- **Main theorem (three-tape intrinsic area law).** The number of spacelike edges
    crossing the coordinate cut `x = c` in the emergent 3D lattice of the three-tape
    ℤ₇ CMCA — under the reading-(A) coordinate assignment confirmed above — equals
    `L^2` exactly. Zero metric, zero `ℓ_Pl`, zero `G` anywhere in this count: purely
    `Fin`-coordinate combinatorics on the tape-index lattice, exactly mirroring
    `SpacelikeCutAreaScaling.cut_crossing_finset_card_eq_L_sq`. -/
theorem three_tape_cut_crossing_card_eq_L_sq (c : Fin L) (hc : 1 ≤ c.val) :
    (threeTapeCutCrossingFinset (L := L) c hc).card = L ^ 2 := by
  unfold threeTapeCutCrossingFinset
  have hinj : Function.Injective
      (fun yz : Fin L × Fin L => ((cutPred c hc, yz.1, yz.2), (c, yz.1, yz.2))) := by
    intro yz1 yz2 h
    simp only [Prod.mk.injEq] at h
    exact Prod.ext h.1.2.1 h.1.2.2
  rw [Finset.card_image_of_injective _ hinj, Finset.card_univ, Fintype.card_prod,
    Fintype.card_fin]
  ring

end GTE.Spacetime.ThreeTape
