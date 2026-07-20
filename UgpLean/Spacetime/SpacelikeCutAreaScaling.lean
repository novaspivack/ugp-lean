import UgpLean.Spacetime.CausalGraph
import Mathlib.Tactic.Ring

/-!
# Intrinsic Area-Scaling of a Spacelike Coordinate Cut

An intrinsic (no metric, no continuum geometry) combinatorial cut measure for the
3D f_MDL causal graph (`GTE.Spacetime.CausalGraph`), built entirely from `Fin`-coordinate
adjacency. The cut measure counts spacelike causal edges crossing a fixed-coordinate
hyperplane — the same style of construction as the Dou–Sorkin "horizon molecule" count
in causal set theory (the number of causal links piercing a horizon).

## Purpose

Neither `HolographicScaling.three_tape_holographic_L7` (a state-space cardinality
comparison, `3L` vs `L^3`, no notion of a specific cut) nor
`Gravity.GorardRicciFlatVacuum.three_tape_causal_diamond_t4` (a continuum causal-diamond
*volume* `T^4/4`, not a boundary *area*) establishes a literal codimension-2 cut area.
This module supplies that missing object for the (binary, Fin-2-valued) 3D f_MDL causal
graph: the number of spacelike edges crossing a coordinate cut at `x = c` is shown to
equal `L^2` exactly — genuine quadratic (area-like) scaling, in contrast to the linear
(`3L`, holographic ratio) and quartic (`T^4`, causal-diamond volume) scalings already
established elsewhere in the corpus, and in contrast to the cubic (`L^3`) volume scaling
that H1's area-law clause must be shown *not* to follow.

## Scope note (honesty disclosure)

This construction is built on `GTE.Spacetime.CausalGraph`, the existing certified 3D
causal-graph infrastructure (`Fin 2`-valued f_MDL cell states, not the ℤ₇-valued
three-tape CMCA specifically named in the Stage A audit target `three_tape_holographic_L7`).
It demonstrates that an intrinsic, non-metric, area-scaling cut measure **can** be built
for a GTE-style discrete causal graph — a positive existence result — but it is **not**
yet the literal three-tape ℤ₇³ construction the main epic spec's H1/Stage A ask about.
Connecting this construction to the specific three-tape CMCA architecture (or showing
the analogous count there) is future work; see the epic's Stage A lab note for the exact
boundary of what this file does and does not establish.

## Theorems in this file

- `cutEdgeAt_injective` — the parametrization of crossing edges by `(y, z)` positions is
  injective (zero sorry).
- `cutEdgeAt_is_spacelike_adj` — every parametrized edge is a genuine `SpacelikeAdj` edge
  of the causal graph (zero sorry).
- `cutEdgeAt_characterizes_x_crossing` — completeness: every `SpacelikeAdj` pair whose
  nodes sit at `x`-coordinates `c-1` and `c` (in either order) arises from this
  parametrization (zero sorry) — this is what makes the `(y,z)`-indexing exhaustive, not
  merely a lower bound.
- `cut_crossing_finset_card_eq_L_sq` — the crossing-edge `Finset` has cardinality exactly
  `L^2` (zero sorry).
-/

namespace GTE.Spacetime

variable {L T : ℕ}

/-- Given a coordinate `c : Fin L` with `1 ≤ c.val`, the "predecessor" coordinate
    `c.val - 1` as an element of `Fin L`. Well-defined since `c.val - 1 < c.val < L`. -/
def cutPred (c : Fin L) (hc : 1 ≤ c.val) : Fin L :=
  ⟨c.val - 1, by omega⟩

@[simp] theorem cutPred_val (c : Fin L) (hc : 1 ≤ c.val) : (cutPred c hc).val = c.val - 1 := rfl

/-- `cutPred` is spacelike-`FinAdj` to `c`: the two coordinates differ by exactly 1. -/
theorem cutPred_finAdj (c : Fin L) (hc : 1 ≤ c.val) : FinAdj (cutPred c hc) c := by
  left
  simp only [cutPred_val]
  omega

/-- The pair of nodes at fixed time `t`, forming the spacelike edge crossing the
    `x = c` cut at spatial position `(y, z)`: the "left" node at `x = c - 1` and the
    "right" node at `x = c`, both at the same `(y, z)` and time `t`. -/
def cutEdgeAt (t : Fin (T + 1)) (c : Fin L) (hc : 1 ≤ c.val) (yz : Fin L × Fin L) :
    CausalNode L T × CausalNode L T :=
  ((t, cutPred c hc, yz.1, yz.2), (t, c, yz.1, yz.2))

/-- The `(y, z)`-parametrization of crossing edges is injective: distinct `(y,z)`
    positions give distinct edges (distinguished by their second-coordinate values). -/
theorem cutEdgeAt_injective (t : Fin (T + 1)) (c : Fin L) (hc : 1 ≤ c.val) :
    Function.Injective (cutEdgeAt (T := T) t c hc) := by
  intro yz1 yz2 h
  simp only [cutEdgeAt, Prod.mk.injEq] at h
  obtain ⟨⟨_, _, hy1, hz1⟩, ⟨_, _, hy2, hz2⟩⟩ := h
  exact Prod.ext hy1 hz1

/-- Every parametrized edge is a genuine spacelike-adjacent pair in the causal graph:
    same timestep, `x`-coordinates differ by 1 (`cutPred c hc` vs `c`), `y` and `z`
    coordinates equal. -/
theorem cutEdgeAt_is_spacelike_adj (t : Fin (T + 1)) (c : Fin L) (hc : 1 ≤ c.val)
    (yz : Fin L × Fin L) :
    SpacelikeAdj L T (cutEdgeAt (T := T) t c hc yz).1 (cutEdgeAt (T := T) t c hc yz).2 := by
  unfold cutEdgeAt SpacelikeAdj
  exact ⟨rfl, Or.inl ⟨cutPred_finAdj c hc, rfl, rfl⟩⟩

/-- **Completeness (exhaustiveness).** Any spacelike-adjacent pair of nodes at the fixed
    time `t`, with `x`-coordinates exactly `cutPred c hc` (left) and `c` (right), arises
    from `cutEdgeAt` at the shared `(y, z)` position. Combined with injectivity, this
    shows the `(y,z)`-parametrization is an exact bijection onto the set of edges
    crossing this cut — not merely an embedding giving a lower bound. -/
theorem cutEdgeAt_characterizes_x_crossing (t : Fin (T + 1)) (c : Fin L) (hc : 1 ≤ c.val)
    (n1 n2 : CausalNode L T) (ht1 : n1.1 = t) (ht2 : n2.1 = t)
    (hx1 : n1.2.1 = cutPred c hc) (hx2 : n2.2.1 = c) (hadj : SpacelikeAdj L T n1 n2) :
    ∃ yz : Fin L × Fin L, cutEdgeAt (T := T) t c hc yz = (n1, n2) := by
  -- `cutPred c hc ≠ c` since their `.val`s differ by 1; rules out the y/z-crossing branches.
  have hne : cutPred c hc ≠ c := by
    intro heq
    have := congrArg Fin.val heq
    simp only [cutPred_val] at this
    omega
  have hx2' : n1.2.2.1 = n2.2.2.1 ∧ n1.2.2.2 = n2.2.2.2 := by
    rcases hadj.2 with ⟨_, hy, hz⟩ | ⟨hcoord, _, _⟩ | ⟨hcoord, _, _⟩
    · exact ⟨hy, hz⟩
    · exact absurd (hx1.symm.trans (hcoord.trans hx2)) hne
    · exact absurd (hx1.symm.trans (hcoord.trans hx2)) hne
  refine ⟨(n1.2.2.1, n1.2.2.2), ?_⟩
  unfold cutEdgeAt
  have hn1 : (t, cutPred c hc, n1.2.2.1, n1.2.2.2) = n1 := by
    rw [← ht1, ← hx1]
  have hn2 : (t, c, n1.2.2.1, n1.2.2.2) = n2 := by
    rw [hx2'.1, hx2'.2, ← ht2, ← hx2]
  exact congrArg₂ Prod.mk hn1 hn2

/-- The crossing-edge set, as a `Finset`, is the image of `cutEdgeAt` over the full
    `(y,z)`-index set. -/
noncomputable def cutCrossingFinset (t : Fin (T + 1)) (c : Fin L) (hc : 1 ≤ c.val) :
    Finset (CausalNode L T × CausalNode L T) :=
  Finset.image (cutEdgeAt (T := T) t c hc) Finset.univ

/-- **Main theorem (intrinsic area-law count).** The number of spacelike causal edges
    crossing the coordinate cut `x = c` (at fixed time `t`) equals `L^2` exactly.

    This count is built from `FinAdj`/`SpacelikeAdj` alone — pure `Fin`-coordinate
    combinatorics — and reads no metric, no continuum geometry, and no CA update rule
    (cf. `causal_graph_rule_independent`). It scales quadratically in `L`, matching an
    area law, in contrast to `three_tape_holographic_L7`'s linear (`3L`) count and
    `three_tape_causal_diamond_t4`'s quartic (`T^4`) volume. -/
theorem cut_crossing_finset_card_eq_L_sq (t : Fin (T + 1)) (c : Fin L) (hc : 1 ≤ c.val) :
    (cutCrossingFinset (T := T) t c hc).card = L ^ 2 := by
  unfold cutCrossingFinset
  rw [Finset.card_image_of_injective _ (cutEdgeAt_injective t c hc), Finset.card_univ,
    Fintype.card_prod, Fintype.card_fin]
  ring

end GTE.Spacetime
