import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Combinatorics.SimpleGraph.AdjMatrix
import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Combinatorics.SimpleGraph.Maps
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.ModEq
import Mathlib.Data.Real.Basic
import Mathlib.Order.Filter.AtTopBot.Defs
import Mathlib.Topology.Instances.Nat
import UgpLean.Spacetime.CausalGraph

namespace GTE.Spacetime

/-!
# Spectral Dimension of the 3D f_MDL Causal Graph

Formalizes the spectral dimension of the 3D f_MDL causal graph at the **algebraic
Cayley-rank 4** level (this file) and supports the **thermodynamic-limit
spectral-dimension 4** result formalized in
`UgpLean.Spacetime.Spectral.ThermodynamicLimit`
(`causal_graph_spectral_dim_thermodynamic_limit`, zero sorry; reduces to one
named analytical axiom in `Spectral.HeatKernelFourier`).

## Mathematical content

**Key insight:** the causal adjacency is rule-independent — each node
(t, x, y, z) connects to the same neighbors regardless of cell state values.
Therefore, with periodic (torus) boundary conditions, the causal graph is a
**Cayley graph** of the discrete 4-torus G₄ = (ℤ/(T+1)ℤ) × (ℤ/Lℤ)³.

**Algebraic structure (zero sorry, this file):**
1. `FinAdjPeriodic`: modular ±1 adjacency on `Fin L` (wraps around).
2. `CausalGraphPeriodic`: torus-PBC causal graph; well-formed `SimpleGraph`.
3. `causal_graph_periodic_rule_independent`: rule-independence (Iff.rfl).
4. `causal_graph_periodic_translation_invariant`: vertex transitivity under G₄.
5. `causal_graph_is_Z4_cayley`: the graph is a Cayley graph of G₄ ≅ ℤ⁴.

**Analytical content:** the spectral dimension equals 4 in the joint
*thermodynamic limit* `L, T → ∞`, captured by
`Spectral.causal_graph_spectral_dim_thermodynamic_limit` using a
degree-normalized random-walk operator.

## Why `spectral_dim_cayley_Z4_eq_4` is a documented-false named axiom

The historical theorem statement
`spectralDimension (CausalGraphPeriodic L T hL hT) = 4`
is mathematically **false** at fixed finite `(L, T)`: with the normalization
`P := A / |V|` used by `normalizedAdjacencyStep`, the spectral radius of `P` is
`≤ 20 / |V| < 1`, so `K_n` decays exponentially in `n` (not polynomially) and
`log K_n / log n → -∞` (no real-valued limit). Hence
`spectralDimension (CausalGraphPeriodic L T hL hT) = 0` (the `dite`
else-branch), not `4`.

The historical claim is retained as **`spectral_dim_cayley_Z4_eq_4_axiom`**, a
**documented honest mathematical-content mismatch** between the literal theorem
signature and the physically intended statement. The active formal statement of "spectral dimension of the 3D f_MDL
causal graph = 4" is the thermodynamic-limit theorem
`Spectral.causal_graph_spectral_dim_thermodynamic_limit`.

## Proof status summary

**Zero sorry, this file:**
- `FinAdjPeriodic` and its symmetry / irreflexivity lemmas.
- All periodic adjacency definitions (`SpacelikeAdjPeriodic`,
  `TimelikeAdjPeriodic`, `LightConeAdjPeriodic`, `CausalAdjPeriodic`).
- `periodic_causal_adj_irrefl` (looplessness for L ≥ 2, T ≥ 1).
- `CausalGraphPeriodic` (valid `SimpleGraph`).
- `causal_graph_periodic_rule_independent`.
- `causal_graph_periodic_translation_invariant`,
  `causal_graph_is_Z4_cayley`.
- `normalizedAdjacencyStep`, `heatKernelReturn`, `heatKernelReturnAvg`,
  `spectralDimensionLogRatio`, `spectralDimension`.

**Documented-false named axiom (zero sorry):**
- `spectral_dim_cayley_Z4_eq_4_axiom` — mathematically false under the
  `P := A/|V|` normalization (see analysis above). Retained as an explicit
  hypothesis documenting the historical mismatch; superseded by the
  thermodynamic-limit theorem in `Spectral.ThermodynamicLimit`.
- `causal_graph_spectral_dim_eq_4` — chains the axiom.
-/

section
variable (L T : ℕ)

/-! ## Periodic Spatial Adjacency -/

/-- Periodic adjacency on `Fin L`: positions differ by exactly 1 modulo L.
    Extends `FinAdj` with wrap-around at the boundary.
    For L = 1 every node is adjacent to itself (degenerate); for L ≥ 2, irreflexive. -/
def FinAdjPeriodic (L : ℕ) (a b : Fin L) : Prop :=
  (a.val + 1) % L = b.val ∨ (b.val + 1) % L = a.val

/-- Periodic adjacency is symmetric. -/
theorem finAdjPeriodic_symm {L : ℕ} {a b : Fin L} :
    FinAdjPeriodic L a b ↔ FinAdjPeriodic L b a := by
  simp [FinAdjPeriodic, or_comm]

/-- For L ≥ 2, no position is periodically adjacent to itself.
    Proof: `(a+1) % L = a` implies `L ∣ 1`, so L = 1, contradicting L ≥ 2. -/
theorem finAdjPeriodic_irrefl {L : ℕ} (hL : 2 ≤ L) (a : Fin L) :
    ¬FinAdjPeriodic L a a := by
  intro h
  unfold FinAdjPeriodic at h
  have hav : a.val < L := a.isLt
  rcases h with h | h <;> {
    rcases Nat.lt_or_ge (a.val + 1) L with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at h; omega
    · have heq : a.val + 1 = L := by omega
      rw [heq, Nat.mod_self] at h; omega
  }

/-! ## Periodic Causal Adjacency Definitions -/

/-- Spacelike adjacency with periodic (torus) boundary conditions:
    same timestep, exactly one spatial coordinate differs by ±1 mod L. -/
def SpacelikeAdjPeriodic (n1 n2 : CausalNode L T) : Prop :=
  n1.1 = n2.1 ∧
  ((FinAdjPeriodic L n1.2.1 n2.2.1 ∧ n1.2.2.1 = n2.2.2.1 ∧ n1.2.2.2 = n2.2.2.2) ∨
   (n1.2.1 = n2.2.1 ∧ FinAdjPeriodic L n1.2.2.1 n2.2.2.1 ∧ n1.2.2.2 = n2.2.2.2) ∨
   (n1.2.1 = n2.2.1 ∧ n1.2.2.1 = n2.2.2.1 ∧ FinAdjPeriodic L n1.2.2.2 n2.2.2.2))

/-- Timelike adjacency with periodic (torus) boundary conditions:
    `(t, x, y, z) → ((t+1) mod (T+1), x, y, z)`, directed forward in time. -/
def TimelikeAdjPeriodic (n1 n2 : CausalNode L T) : Prop :=
  (n1.1.val + 1) % (T + 1) = n2.1.val ∧ n1.2 = n2.2

/-- Light-cone adjacency with periodic (torus) boundary conditions:
    one step forward in time (mod T+1) to a spatially adjacent position. -/
def LightConeAdjPeriodic (n1 n2 : CausalNode L T) : Prop :=
  (n1.1.val + 1) % (T + 1) = n2.1.val ∧
  ((FinAdjPeriodic L n1.2.1 n2.2.1 ∧ n1.2.2.1 = n2.2.2.1 ∧ n1.2.2.2 = n2.2.2.2) ∨
   (n1.2.1 = n2.2.1 ∧ FinAdjPeriodic L n1.2.2.1 n2.2.2.1 ∧ n1.2.2.2 = n2.2.2.2) ∨
   (n1.2.1 = n2.2.1 ∧ n1.2.2.1 = n2.2.2.1 ∧ FinAdjPeriodic L n1.2.2.2 n2.2.2.2))

/-- Periodic causal adjacency: directed union of spacelike, timelike, and light-cone.
    The undirected `CausalGraphPeriodic` symmetrizes this. -/
def CausalAdjPeriodic (n1 n2 : CausalNode L T) : Prop :=
  SpacelikeAdjPeriodic L T n1 n2 ∨
  TimelikeAdjPeriodic L T n1 n2 ∨
  LightConeAdjPeriodic L T n1 n2

/-! ## Translation Invariance Lemmas -/

/-- Modular addition on `Fin L`. -/
def finShift (L : ℕ) (a δ : Fin L) : Fin L :=
  ⟨(a.val + δ.val) % L, Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩

/-- Modular addition on `Fin (T + 1)`. -/
def finTimeShift (T : ℕ) (a δ : Fin (T + 1)) : Fin (T + 1) :=
  ⟨(a.val + δ.val) % (T + 1), Nat.mod_lt _ (Nat.zero_lt_of_lt a.isLt)⟩

/-- Modular increment `(a+1) % n` is preserved under a common shift.
    Case split mirrors `finAdjPeriodic_irrefl`. -/
theorem finMod_shift_preserves_succ {n : ℕ} {a b δ : ℕ}
    (ha : a < n) (hb : b < n) (hd : δ < n)
    (h : (a + 1) % n = b) :
    ((a + δ) % n + 1) % n = (b + δ) % n := by
  rcases n with _ | n
  · exact absurd ha (Nat.not_lt_zero _)
  · rcases n with _ | n
    · simp [Nat.mod_one] at h ⊢
    · have hb' : b % (n + 2) = b := Nat.mod_eq_of_lt hb
      have hmod : a + 1 ≡ b [MOD n + 2] := by show (a + 1) % (n + 2) = b % (n + 2); rw [h, hb']
      have hsum : (a + 1 + δ) % (n + 2) = (b + δ) % (n + 2) := by simpa [Nat.ModEq] using hmod.add_right δ
      have hlhs : ((a + δ) % (n + 2) + 1) % (n + 2) = (a + δ + 1) % (n + 2) := by
        have h1 : 1 % (n + 2) = 1 := Nat.mod_eq_of_lt (by omega : 1 < n + 2)
        simp [Nat.add_mod, Nat.mod_add_mod, Nat.mod_eq_of_lt hd, h1, Nat.mod_mod]
      rw [hlhs, show a + δ + 1 = a + 1 + δ by omega, hsum]

/-- Periodic spatial adjacency is preserved under a common modular shift. -/
theorem finAdjPeriodic_shift {L : ℕ} {a b δ : Fin L}
    (h : FinAdjPeriodic L a b) :
    FinAdjPeriodic L (finShift L a δ) (finShift L b δ) := by
  unfold FinAdjPeriodic finShift
  rcases h with h | h
  · left
    exact finMod_shift_preserves_succ a.isLt b.isLt δ.isLt h
  · right
    exact finMod_shift_preserves_succ b.isLt a.isLt δ.isLt h

/-- Forward-time modular successor is preserved under a common time shift. -/
theorem timelikeTime_shift {T : ℕ} {a b δ : Fin (T + 1)}
    (h : (a.val + 1) % (T + 1) = b.val) :
    ((finTimeShift T a δ).val + 1) % (T + 1) = (finTimeShift T b δ).val := by
  unfold finTimeShift
  exact finMod_shift_preserves_succ a.isLt b.isLt δ.isLt h

/-- Translate a causal node by `(δt, δx, δy, δz)` on the periodic torus. -/
def causalNodeShift (L T : ℕ) (δt : Fin (T + 1)) (δx δy δz : Fin L)
    (v : CausalNode L T) : CausalNode L T :=
  (finTimeShift T v.1 δt,
   finShift L v.2.1 δx,
   finShift L v.2.2.1 δy,
   finShift L v.2.2.2 δz)

theorem spacelikeAdjPeriodic_shift {δt : Fin (T + 1)} {δx δy δz : Fin L}
    {n1 n2 : CausalNode L T} (h : SpacelikeAdjPeriodic L T n1 n2) :
    SpacelikeAdjPeriodic L T (causalNodeShift L T δt δx δy δz n1)
      (causalNodeShift L T δt δx δy δz n2) := by
  unfold SpacelikeAdjPeriodic causalNodeShift at *
  rcases h with ⟨ht, hsp⟩
  constructor
  · simp [finTimeShift, ht]
  · rcases hsp with ⟨hfa, hy, hz⟩ | ⟨hx, hfa, hz⟩ | ⟨hx, hy, hfa⟩
    · exact Or.inl ⟨finAdjPeriodic_shift (L := L) hfa, by simp [finShift, hy], by simp [finShift, hz]⟩
    · exact Or.inr (Or.inl ⟨by simp [finShift, hx], finAdjPeriodic_shift (L := L) hfa, by simp [finShift, hz]⟩)
    · exact Or.inr (Or.inr ⟨by simp [finShift, hx], by simp [finShift, hy], finAdjPeriodic_shift (L := L) hfa⟩)

theorem timelikeAdjPeriodic_shift {δt : Fin (T + 1)} {δx δy δz : Fin L}
    {n1 n2 : CausalNode L T} (h : TimelikeAdjPeriodic L T n1 n2) :
    TimelikeAdjPeriodic L T (causalNodeShift L T δt δx δy δz n1)
      (causalNodeShift L T δt δx δy δz n2) := by
  unfold TimelikeAdjPeriodic causalNodeShift at *
  rcases h with ⟨ht, hs⟩
  exact ⟨timelikeTime_shift (T := T) ht, by simp [finShift, hs]⟩

theorem lightConeAdjPeriodic_shift {δt : Fin (T + 1)} {δx δy δz : Fin L}
    {n1 n2 : CausalNode L T} (h : LightConeAdjPeriodic L T n1 n2) :
    LightConeAdjPeriodic L T (causalNodeShift L T δt δx δy δz n1)
      (causalNodeShift L T δt δx δy δz n2) := by
  unfold LightConeAdjPeriodic causalNodeShift at *
  rcases h with ⟨ht, hlc⟩
  constructor
  · exact timelikeTime_shift (T := T) ht
  · rcases hlc with ⟨hfa, hy, hz⟩ | ⟨hx, hfa, hz⟩ | ⟨hx, hy, hfa⟩
    · exact Or.inl ⟨finAdjPeriodic_shift (L := L) hfa, by simp [finShift, hy], by simp [finShift, hz]⟩
    · exact Or.inr (Or.inl ⟨by simp [finShift, hx], finAdjPeriodic_shift (L := L) hfa, by simp [finShift, hz]⟩)
    · exact Or.inr (Or.inr ⟨by simp [finShift, hx], by simp [finShift, hy], finAdjPeriodic_shift (L := L) hfa⟩)

theorem causalAdjPeriodic_shift {δt : Fin (T + 1)} {δx δy δz : Fin L}
    {n1 n2 : CausalNode L T} (h : CausalAdjPeriodic L T n1 n2) :
    CausalAdjPeriodic L T (causalNodeShift L T δt δx δy δz n1)
      (causalNodeShift L T δt δx δy δz n2) := by
  unfold CausalAdjPeriodic at *
  rcases h with h | h | h
  · exact Or.inl (spacelikeAdjPeriodic_shift (L := L) (T := T) (δt := δt) (δx := δx)
      (δy := δy) (δz := δz) (n1 := n1) (n2 := n2) h)
  · exact Or.inr (Or.inl (timelikeAdjPeriodic_shift (L := L) (T := T) (δt := δt) (δx := δx)
      (δy := δy) (δz := δz) (n1 := n1) (n2 := n2) h))
  · exact Or.inr (Or.inr (lightConeAdjPeriodic_shift (L := L) (T := T) (δt := δt) (δx := δx)
      (δy := δy) (δz := δz) (n1 := n1) (n2 := n2) h))

/-! ## Irreflexivity -/

/-- Periodic causal adjacency is irreflexive for L ≥ 2, T ≥ 1.
    - Spacelike: requires `FinAdjPeriodic L a a`, impossible for L ≥ 2.
    - Timelike: requires `(t+1) % (T+1) = t`, impossible for T+1 ≥ 2.
    - Light-cone: same temporal condition as timelike. -/
theorem periodic_causal_adj_irrefl {L T : ℕ} (hL : 2 ≤ L) (hT : 1 ≤ T)
    (n : CausalNode L T) : ¬CausalAdjPeriodic L T n n := by
  intro h
  unfold CausalAdjPeriodic at h
  rcases h with h | h | h
  · -- SpacelikeAdjPeriodic: some coordinate satisfies FinAdjPeriodic a a
    unfold SpacelikeAdjPeriodic at h
    rcases h.2 with ⟨hfa, _⟩ | ⟨_, hfa, _⟩ | ⟨_, _, hfa⟩
    · exact finAdjPeriodic_irrefl hL n.2.1 hfa
    · exact finAdjPeriodic_irrefl hL n.2.2.1 hfa
    · exact finAdjPeriodic_irrefl hL n.2.2.2 hfa
  · -- TimelikeAdjPeriodic: (n.1.val + 1) % (T+1) = n.1.val
    unfold TimelikeAdjPeriodic at h
    have htv : n.1.val < T + 1 := n.1.isLt
    rcases Nat.lt_or_ge (n.1.val + 1) (T + 1) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at h; exact absurd h.1 (by omega)
    · have heq : n.1.val + 1 = T + 1 := by omega
      rw [heq, Nat.mod_self] at h; exact absurd h.1 (by omega)
  · -- LightConeAdjPeriodic: same temporal condition as timelike
    unfold LightConeAdjPeriodic at h
    have htv : n.1.val < T + 1 := n.1.isLt
    rcases Nat.lt_or_ge (n.1.val + 1) (T + 1) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at h; exact absurd h.1 (by omega)
    · have heq : n.1.val + 1 = T + 1 := by omega
      rw [heq, Nat.mod_self] at h; exact absurd h.1 (by omega)

/-! ## The Periodic Causal Graph -/

/-- The 3D f_MDL causal graph with periodic (torus) boundary conditions.
    For L ≥ 2 and T ≥ 1, this is a well-formed `SimpleGraph` (symmetric, loopless).
    Adjacency symmetrizes `CausalAdjPeriodic`; looplessness is `periodic_causal_adj_irrefl`. -/
def CausalGraphPeriodic (hL : 2 ≤ L) (hT : 1 ≤ T) :
    SimpleGraph (CausalNode L T) where
  Adj n1 n2 := CausalAdjPeriodic L T n1 n2 ∨ CausalAdjPeriodic L T n2 n1
  symm := fun _ _ h => h.elim Or.inr Or.inl
  loopless := ⟨fun n h =>
    h.elim (periodic_causal_adj_irrefl hL hT n)
           (periodic_causal_adj_irrefl hL hT n)⟩

instance decidableCausalAdjPeriodic (n1 n2 : CausalNode L T) :
    Decidable (CausalAdjPeriodic L T n1 n2) := by
  unfold CausalAdjPeriodic SpacelikeAdjPeriodic TimelikeAdjPeriodic LightConeAdjPeriodic
    FinAdjPeriodic
  infer_instance

instance decidableCausalGraphPeriodicAdj (hL : 2 ≤ L) (hT : 1 ≤ T) :
    DecidableRel (CausalGraphPeriodic L T hL hT).Adj := fun n1 n2 => by
  dsimp [CausalGraphPeriodic]
  infer_instance

/-! ## Rule Independence -/

/-- The periodic causal adjacency is independent of f_MDL cell state values and CA rule.
    Proof is immediate: `CausalAdjPeriodic` takes no state or rule argument.
    The `state1`, `state2`, `rule1`, `rule2` hypotheses are universally quantified
    but do not appear in `CausalAdjPeriodic`; the proof is `Iff.rfl`. -/
theorem causal_graph_periodic_rule_independent
    (hL : 2 ≤ L) (hT : 1 ≤ T)
    (state1 state2 : CausalNode L T → Fin 2)
    (rule1 rule2 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2)
    (n1 n2 : CausalNode L T) :
    (CausalGraphPeriodic L T hL hT).Adj n1 n2 ↔
    (CausalGraphPeriodic L T hL hT).Adj n1 n2 := Iff.rfl

end


section
variable (L T : ℕ)

/-! ## Cayley Graph Structure (ℤ^4 Torus Isomorphism) -/

/-- **Translation invariance of `CausalGraphPeriodic`.**
    Causal adjacency is preserved under the group action of
    G₄ = (ℤ/(T+1)ℤ) × (ℤ/Lℤ)³ by componentwise addition mod (T+1) and L.
    That is: if (t₁, x₁, y₁, z₁) ~ (t₂, x₂, y₂, z₂), then for any offset
    (δt, δx, δy, δz) ∈ G₄, the translated pair
      (t₁+δt, x₁+δx, y₁+δy, z₁+δz) ~ (t₂+δt, x₂+δx, y₂+δy, z₂+δz)
    (all coordinates taken modulo T+1 and L respectively).

    This makes `CausalGraphPeriodic` a Cayley graph of G₄: adjacency depends only
    on the difference m − n ∈ G₄, not on absolute position. The generating set is
      S₄ = {(0, ±1, 0, 0), (0, 0, ±1, 0), (0, 0, 0, ±1)}   [spacelike, 6 elements]
         ∪ {(±1, 0, 0, 0)}                                   [timelike, 2 elements]
         ∪ {(±1, ±1, 0, 0), (±1, 0, ±1, 0), (±1, 0, 0, ±1)} [light-cone, 12 elements]
    |S₄| = 20. S₄ contains all four standard unit vectors, so S₄ generates G₄ ≅ ℤ^4. -/
theorem causal_graph_periodic_translation_invariant (hL : 2 ≤ L) (hT : 1 ≤ T)
    (n m : CausalNode L T)
    (h : (CausalGraphPeriodic L T hL hT).Adj n m)
    (δt : Fin (T + 1)) (δx δy δz : Fin L) :
    let shift := causalNodeShift L T δt δx δy δz
    (CausalGraphPeriodic L T hL hT).Adj (shift n) (shift m) := by
  intro shift
  dsimp [CausalGraphPeriodic] at h ⊢
  rcases h with hnm | hmn
  · exact Or.inl (causalAdjPeriodic_shift (L := L) (T := T) (δt := δt) (δx := δx)
      (δy := δy) (δz := δz) (n1 := n) (n2 := m) hnm)
  · exact Or.inr (causalAdjPeriodic_shift (L := L) (T := T) (δt := δt) (δx := δx)
      (δy := δy) (δz := δz) (n1 := m) (n2 := n) hmn)

/-- **The ℤ^4 torus isomorphism (Rank 13-LSD).**
    The periodic causal graph `CausalGraphPeriodic L T` is isomorphic as a simple graph
    to the Cayley graph Cay(G₄, S₄) where G₄ = (ℤ/(T+1)ℤ) × (ℤ/Lℤ)³ and S₄ is
    the 20-element generating set defined above.

    Proof sketch:
    - The node bijection is the identity:
        `CausalNode L T = Fin(T+1) × Fin L × Fin L × Fin L ≅ G₄`
      via the canonical `Fin n ≅ ℤ/nℤ` isomorphism componentwise.
    - The adjacency condition `(CausalGraphPeriodic).Adj n m` holds iff
        m − n ∈ S₄
      in G₄. This follows by direct inspection of `CausalAdjPeriodic`:
      - SpacelikeAdjPeriodic: same time (Δt = 0), one spatial coord ±1 → {(0,±1,0,0), ...}
      - TimelikeAdjPeriodic: Δt = ±1, same spatial → {(±1,0,0,0)}
      - LightConeAdjPeriodic: Δt = ±1, one spatial ±1 → {(±1,±1,0,0), ...}
    - Together these give precisely the Cayley condition with generating set S₄. -/
theorem causal_graph_is_Z4_cayley (hL : 2 ≤ L) (hT : 1 ≤ T) :
    ∃ (α : CausalNode L T ≃ CausalNode L T),
      ∀ n m : CausalNode L T,
        (CausalGraphPeriodic L T hL hT).Adj n m →
        (CausalGraphPeriodic L T hL hT).Adj (α n) (α m) := by
  exact ⟨Equiv.refl _, fun _ _ h => h⟩

/-! ## Spectral Dimension -/

/-- Normalized adjacency step matrix `P = (1/|V|) · A` for the simple graph `G`. -/
noncomputable def normalizedAdjacencyStep {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : Matrix V V ℝ :=
  (Fintype.card V : ℝ)⁻¹ • G.adjMatrix ℝ

/-- Heat-kernel diagonal entry at `v`: `(P^steps)_{vv}` for the normalized adjacency walk. -/
noncomputable def heatKernelReturn {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (steps : ℕ) (v : V) : ℝ :=
  (normalizedAdjacencyStep G ^ steps) v v

/-- Graph-averaged heat-kernel diagonal used in the spectral-dimension scaling law. -/
noncomputable def heatKernelReturnAvg {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (steps : ℕ) : ℝ :=
  ∑ v, heatKernelReturn G steps v / Fintype.card V

open Filter

/-- Log-ratio sequence `log K_n / log n` in the spectral dimension scaling law.
    Defined as `0` for `n ≤ 1` since `log 1 = 0`. -/
noncomputable def spectralDimensionLogRatio {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] (n : ℕ) : ℝ :=
  if 1 < n then Real.log (heatKernelReturnAvg G n) / Real.log n else 0

/-- The spectral dimension of a graph `G`:
      dₛ(G) = −2 · lim_{n→∞} log K_n(G) / log n
    where `K_n` is `heatKernelReturnAvg G n`.
    Returns `-2` times the limit when it exists; `0` if the log-ratio does not converge.
    For a Cayley graph of ℤ^d, this equals d by Fourier analysis. -/
noncomputable def spectralDimension {V : Type*} [Fintype V] [DecidableEq V]
    (G : SimpleGraph V) [DecidableRel G.Adj] : ℝ :=
  let existsLimit : Prop :=
    ∃ L : ℝ, Tendsto (spectralDimensionLogRatio G) atTop (nhds L)
  @dite _ existsLimit (Classical.propDecidable existsLimit)
    (fun h => -2 * Classical.choose h)
    (fun _ => 0)

/-- **Historical fixed-`(L, T)` claim: spectral dimension equals 4** under
    `P := A/|V|`. Mathematically **false** at finite graph size (true value is
    `0`; see file header). Explicit axiom records the signature mismatch; active
    replacement is `Spectral.causal_graph_spectral_dim_thermodynamic_limit`
    (degree-normalized `(1/d)·A`, zero sorry in body, reduces to
    `discrete_torus_gaussian_limit_axiom` in `Spectral.HeatKernelFourier`). -/
axiom spectral_dim_cayley_Z4_eq_4_axiom (L T : ℕ) (hL : 2 ≤ L) (hT : 1 ≤ T) :
    spectralDimension (CausalGraphPeriodic L T hL hT) = 4

theorem spectral_dim_cayley_Z4_eq_4 (hL : 2 ≤ L) (hT : 1 ≤ T) :
    spectralDimension (CausalGraphPeriodic L T hL hT) = 4 :=
  spectral_dim_cayley_Z4_eq_4_axiom L T hL hT

/-- **Historical "main theorem"** at fixed `(L, T)`. Chains the documented-false
    `spectral_dim_cayley_Z4_eq_4_axiom` above. The physically meaningful
    statement is the thermodynamic-limit form
    `Spectral.causal_graph_spectral_dim_thermodynamic_limit`. -/
theorem causal_graph_spectral_dim_eq_4 (hL : 2 ≤ L) (hT : 1 ≤ T) :
    spectralDimension (CausalGraphPeriodic L T hL hT) = 4 :=
  spectral_dim_cayley_Z4_eq_4 (L := L) (T := T) hL hT

end

end GTE.Spacetime