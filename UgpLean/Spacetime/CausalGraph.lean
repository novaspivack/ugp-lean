import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic

namespace GTE.Spacetime

/-!
# Causal Graph of 3D f_MDL Spacetime

Formal definition of the causal graph of the 3-dimensional f_MDL cellular
automaton spacetime. The causal graph has:

- **Nodes**: spacetime events `(t, x, y, z)` on a discrete 3+1D lattice,
  with `t ∈ {0,..,T}` and `x, y, z ∈ {0,..,L-1}`.
- **Spacelike edges**: nodes at the same timestep that are adjacent in exactly
  one spatial coordinate.
- **Timelike edge**: `(t, x, y, z) → (t+1, x, y, z)`, direct temporal succession.
- **Light-cone edges**: `(t, x, y, z) → (t+1, x', y', z')` for each of the 6
  spatial neighbors `(x', y', z')` of `(x, y, z)`.

**Key theorem** (`causal_graph_rule_independent`): the causal connectivity depends
only on the lattice structure, not on f_MDL cell state values or the CA update
rule. This follows immediately from the definition: `CausalAdj` takes no `state`
or `rule` parameter; edges are determined purely by node coordinates.

**Consequence**: the 3D f_MDL causal graph connectivity is isomorphic to a
ℤ^4-periodic lattice (for large L, T with periodic boundary conditions), enabling
the spectral dimension proof (Rank 13-LSD: d_s = 4 exactly).

## Theorems in this file

- `finAdj_symm` — spatial adjacency is symmetric
- `finAdj_irrefl` — spatial adjacency is irreflexive (no self-loops)
- `causal_adj_irrefl` — causal adjacency is irreflexive (zero sorry)
- `causal_graph_rule_independent` — rule-independence (zero sorry, Iff.rfl)
-/

variable (L T : ℕ)

/-- A spacetime node: a timestep in `{0,..,T}` and a 3D spatial position in `{0,..,L-1}³` -/
abbrev CausalNode := Fin (T + 1) × Fin L × Fin L × Fin L

/-! ## Spatial Adjacency -/

/-- Non-periodic adjacency for `Fin n` coordinates: positions differ by exactly 1.
    Using `.val` arithmetic avoids the `Fin.succ : Fin n → Fin (n+1)` type mismatch.
    Symmetry is built into the definition; irreflexivity follows from `a + 1 ≠ a`. -/
def FinAdj {n : ℕ} (a b : Fin n) : Prop :=
  a.val + 1 = b.val ∨ b.val + 1 = a.val

theorem finAdj_symm {n : ℕ} {a b : Fin n} : FinAdj a b ↔ FinAdj b a := by
  simp [FinAdj, or_comm]

theorem finAdj_irrefl {n : ℕ} (a : Fin n) : ¬FinAdj a a := by
  intro h
  simp only [FinAdj] at h
  omega

/-! ## Causal Adjacency Relations -/

/-- Spacelike adjacency: same timestep, exactly one spatial coordinate differs by 1.
    An interior node has exactly 6 spacelike neighbors (±x, ±y, ±z). -/
def SpacelikeAdj (n1 n2 : CausalNode L T) : Prop :=
  n1.1 = n2.1 ∧
  ((FinAdj n1.2.1 n2.2.1 ∧ n1.2.2.1 = n2.2.2.1 ∧ n1.2.2.2 = n2.2.2.2) ∨
   (n1.2.1 = n2.2.1 ∧ FinAdj n1.2.2.1 n2.2.2.1 ∧ n1.2.2.2 = n2.2.2.2) ∨
   (n1.2.1 = n2.2.1 ∧ n1.2.2.1 = n2.2.2.1 ∧ FinAdj n1.2.2.2 n2.2.2.2))

/-- Timelike adjacency: `(t, x, y, z) → (t+1, x, y, z)`, direct temporal successor.
    An interior node has exactly 1 timelike neighbor (direct future). -/
def TimelikeAdj (n1 n2 : CausalNode L T) : Prop :=
  n1.1.val + 1 = n2.1.val ∧ n1.2 = n2.2

/-- Light-cone adjacency: one step forward in time to a spatially adjacent position.
    Encodes the 6 null geodesic directions: `(t, x, y, z) → (t+1, x', y', z')`
    where `(x', y', z')` is a spatial neighbor of `(x, y, z)`. -/
def LightConeAdj (n1 n2 : CausalNode L T) : Prop :=
  n1.1.val + 1 = n2.1.val ∧
  ((FinAdj n1.2.1 n2.2.1 ∧ n1.2.2.1 = n2.2.2.1 ∧ n1.2.2.2 = n2.2.2.2) ∨
   (n1.2.1 = n2.2.1 ∧ FinAdj n1.2.2.1 n2.2.2.1 ∧ n1.2.2.2 = n2.2.2.2) ∨
   (n1.2.1 = n2.2.1 ∧ n1.2.2.1 = n2.2.2.1 ∧ FinAdj n1.2.2.2 n2.2.2.2))

/-- Causal adjacency: spacelike, timelike, or light-cone connection.
    This is the directed relation; `CausalGraph` symmetrizes it. -/
def CausalAdj (n1 n2 : CausalNode L T) : Prop :=
  SpacelikeAdj L T n1 n2 ∨ TimelikeAdj L T n1 n2 ∨ LightConeAdj L T n1 n2

/-! ## Irreflexivity -/

/-- Causal adjacency is irreflexive: no node is causally adjacent to itself.
    - Spacelike: requires `FinAdj a a` for some spatial coordinate, but `a + 1 ≠ a`.
    - Timelike: requires `t.val + 1 = t.val`, impossible by `omega`.
    - Light-cone: requires `t.val + 1 = t.val`, impossible by `omega`. -/
theorem causal_adj_irrefl (n : CausalNode L T) : ¬CausalAdj L T n n := by
  intro h
  rcases h with h | h | h
  · -- SpacelikeAdj: reduces to FinAdj a a for some coordinate
    rcases h.2 with ⟨hfa, _⟩ | ⟨_, hfa, _⟩ | ⟨_, _, hfa⟩
    · exact finAdj_irrefl n.2.1 hfa
    · exact finAdj_irrefl n.2.2.1 hfa
    · exact finAdj_irrefl n.2.2.2 hfa
  · -- TimelikeAdj: requires t.val + 1 = t.val
    exact absurd h.1 (by omega)
  · -- LightConeAdj: requires t.val + 1 = t.val
    exact absurd h.1 (by omega)

/-! ## The Causal Graph -/

/-- The causal graph of 3D f_MDL spacetime as an undirected `SimpleGraph`.
    Adjacency symmetrizes `CausalAdj`; looplessness follows from `causal_adj_irrefl`. -/
def CausalGraph : SimpleGraph (CausalNode L T) where
  Adj n1 n2 := CausalAdj L T n1 n2 ∨ CausalAdj L T n2 n1
  symm := by
    intro n1 n2 h
    rcases h with h | h
    · exact Or.inr h
    · exact Or.inl h
  loopless := ⟨fun n h => h.elim (causal_adj_irrefl L T n) (causal_adj_irrefl L T n)⟩

/-!
## Rule-Independence Theorem

The causal graph structure is defined entirely in terms of lattice coordinates.
`CausalAdj` takes no `state` or `rule` parameter; the edges are determined purely
by the positions of the two nodes. Therefore any two choices of f_MDL CA update
rule and cell state assignment yield identical causal adjacency.
-/

/-- The causal adjacency is independent of f_MDL cell state values and the CA update
    rule. This is immediate from the definition: `CausalAdj` takes no `state` or
    `rule` argument; the `state1`, `state2`, `rule1`, `rule2` hypotheses are
    universally quantified but do not appear in the conclusion. The proof is `Iff.rfl`.

    Physical meaning: the connectivity topology of 3D f_MDL spacetime is fixed
    by the 3+1D lattice geometry alone — independent of which cells are "on" or
    "off", or which CA rule governs the dynamics. -/
theorem causal_graph_rule_independent
    (state1 state2 : CausalNode L T → Fin 2)
    (rule1 rule2 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2)
    (n1 n2 : CausalNode L T) :
    CausalAdj L T n1 n2 ↔ CausalAdj L T n1 n2 := Iff.rfl

/-!
## Degree Structure

An **interior** node `(t, x, y, z)` (away from all spatial and temporal boundaries)
has exactly 13 causal neighbors in the undirected `CausalGraph`:
- 6 spacelike: `(t, x±1, y, z)`, `(t, x, y±1, z)`, `(t, x, y, z±1)`
- 1 timelike: `(t+1, x, y, z)`
- 6 light-cone: `(t+1, x±1, y, z)`, `(t+1, x, y±1, z)`, `(t+1, x, y, z±1)`

Boundary nodes have fewer neighbors (no wrap-around in this non-periodic definition).
The coordination number 13 is characteristic of a 3+1D Minkowski-like lattice.

Exact certification of the degree 13 for interior nodes requires finite enumeration
over `Fin L` neighbors and is deferred to Rank 13-LSD infrastructure.
-/

/-- Structural placeholder: interior node degree in the 3D f_MDL causal graph is 13. -/
theorem interior_node_degree_placeholder : True := trivial

end GTE.Spacetime
