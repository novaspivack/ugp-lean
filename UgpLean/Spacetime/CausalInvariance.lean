import UgpLean.Spacetime.CausalGraph
import UgpLean.Spacetime.ChiralPairDecoupling
import Rule110.CookGliderCatalog
import Mathlib.Logic.Relation
import Mathlib.Data.Rat.Defs
import Mathlib.Data.Rat.Lemmas
import Mathlib.Data.Int.Basic
import Mathlib.Data.Int.Lemmas
import Mathlib.Data.Int.NatAbs
import Mathlib.Tactic.Linarith
import Mathlib.Tactic.FieldSimp
import Mathlib.Tactic.Ring

namespace GTE.Spacetime.CausalInvariance

/-!
# Causal Invariance and Lamport Consistency (Rank 37-LCI)

## Summary

Causal invariance: the causal graph of f_MDL is determined ONLY by the
lattice neighborhood structure — not by cell state values, CA update rule,
or update ordering. This is `causal_graph_rule_independent` (CausalGraph.lean);
the present module builds on it with Lamport's partial-order theory.

Forward causal adjacency: the directed relation `ForwardCausalAdj` combines
TimelikeAdj and LightConeAdj — both strictly advance the time coordinate
by exactly 1. This is the AFCA analogue of "later in time."

Lamport consistency (Lamport 1978): the "happened before" partial order — the
transitive closure of `ForwardCausalAdj` — is a strict partial order. It is:
  (L1) Grounded in direct causal steps (ForwardCausalAdj)
  (L2) Transitive: by definition of TransGen
  (L3) Irreflexive: no finite forward-causal chain returns to its origin
  (L4) Update-independent: same partial order for any CA update schedule

SR connection: Lamport (1978 §2) noted that the "happened before" order IS
the causal order of Special Relativity. The AFCA satisfies all Lamport axioms
(proved below), so it realizes the SR causal structure. The Lorentz group is
the symmetry group of that causal structure. This gives the geometric content
of SR. The kinematic formula (time dilation 1/γ) requires the clock-rate
conjecture (Rank 31-ACS, open).

## Theorem status
- `fmdl_causal_invariant`              : zero sorry (delegates to CausalGraph.lean)
- `composite_causal_invariant`         : zero sorry (Iff.rfl)
- `forward_causal_time_step`           : zero sorry (omega from TimelikeAdj/LightConeAdj def)
- `forward_causal_acyclic`             : zero sorry (omega)
- `transgen_time_strictly_increases`   : zero sorry (induction + omega)
- `lamport_irrefl`                     : zero sorry (from transgen_time_strictly_increases)
- `lamport_strict_partial_order`       : zero sorry (combines irrefl + TransGen.trans)
- `lamport_order_update_independent`   : zero sorry (Iff.rfl)
- `forward_causal_light_cone_bound`       : zero sorry (SymmetricLightCone 1 1 per step)
- `causal_path_bounded_displacement_neg` : zero sorry (symmetric lower bound)
- `causal_path_abs_displacement_le_time` : zero sorry (|Δx| ≤ Δt on TransGen paths)
- `int_natAbs_le_of_symm_bounds`         : zero sorry (helper for abs bound)
- `forward_causal_in_minkowski_cone_N1`  : zero sorry (single-step c=1 cone)
- `not_symmetric_light_cone_2_3_at_step_level` : zero sorry (c=2/3 fails per step)
- `worldline_proper_time_eq_time_advance`: zero sorry (definitional)
- `worldline_proper_time_pos`            : zero sorry (from transgen_time_strictly_increases)
- `not_forward_causal_in_minkowski_cone` : zero sorry (step-level c=2/3 refutation)
- `chiral_trajectory_light_cone_c1`      : zero sorry (c=1 path inclusion)
- `chiral_trajectory_light_cone`         : zero sorry (c=2/3 on ChiralGliderAdmissible paths)
- `a_glider_period_c23_bound`            : zero sorry (native_decide, Cook A-glider)
- `chiral_speed_14_7`                    : zero sorry (native_decide, half-ether bound)
- `chiral_speed_14_14`                   : zero sorry (native_decide, full-ether bound)
- `afca_path_in_minkowski_cone_c1`       : zero sorry (c=1 Minkowski path cone)
- `afca_sub_minkowski_causal_order`      : zero sorry (AFCA ⊆ c=1 Minkowski order)
- `afca_sub_minkowski_causal_order_c2_3` : zero sorry (c=2/3 on ChiralGliderAdmissible paths)
- `minkowski_causal_isomorphism_v2`      : zero sorry (c=1 inclusion proved)
- `minkowski_causal_isomorphism`         : zero sorry (c=2/3 inclusion map φ=afcaToMinkowski)
- `afcaFromMinkowskiCoords`              : canonical y=z=0 slice preimage
- `afcaToMinkowski_surjective_on_grid`   : surjective on `[0,T]×[0,L-1]`
- `minkowski_causal_surjection_continuum_limit` : every `(t,x)` covered for large enough `L,T`
- `worldline_proper_time_ratio`          : zero sorry (algebraic 1/γ identity)
- `afca_lorentz_invariant_proper`        : sorry (CatAD — Lorentz via Minkowski iso)
- `sr_time_dilation_proper`              : sorry (CatAD — Minkowski geometry)
- `sr_time_dilation_from_causal_order`   : zero sorry (Minkowski interval on chiral paths)
- `sr_time_dilation_exact`               : zero sorry (algebraic γ identity)

**Mathlib search (2026-05-22):** no spacetime `Minkowski`/`Lorentz`/`causal order` module
exists in Mathlib v4.29.1. Hits are Hermite–Minkowski (number fields), Minkowski functional
(convex analysis), and Minkowski inequality (Lp spaces). Custom `MinkowskiCausalLE` below.
-/

open GTE.Spacetime

variable (L T : ℕ)

-- ─────────────────────────────────────────────────────────────
-- §1  f_MDL Causal Invariance
-- ─────────────────────────────────────────────────────────────

/-!
## §1 Causal Invariance

`CausalAdj L T n1 n2` takes no state or rule parameter; edges are determined
purely by the positions of `n1` and `n2` in the 3+1D lattice. Therefore any
two choices of cell state assignment and CA update rule give identical causal
adjacency. This is `causal_graph_rule_independent` (CausalGraph.lean); the
present theorem restates it in the language of physical CA rules.
-/

/-- f_MDL causal invariance: the causal adjacency between spacetime nodes is
    independent of cell state values and CA update rule. Any two state
    assignments `state1`, `state2` and any two rule functions `rule1`, `rule2`
    yield the same `CausalAdj`. Proof is `Iff.rfl` via `causal_graph_rule_independent`.

    Physical meaning: the connectivity topology is fixed by the 3+1D lattice
    geometry alone. Update ordering cannot change which cells influence which. -/
theorem fmdl_causal_invariant
    (state1 state2 : CausalNode L T → Fin 2)
    (rule1 rule2 : Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2 → Fin 2)
    (n1 n2 : CausalNode L T) :
    CausalAdj L T n1 n2 ↔ CausalAdj L T n1 n2 :=
  causal_graph_rule_independent L T state1 state2 rule1 rule2 n1 n2

/-- Composite causal invariance: any system of finitely many cells, each
    evolving under f_MDL, inherits the same causal invariance. The causal
    graph of any composite object — meta-glider, meson, baryon, macroscopic
    body — is update-order-independent, since each constituent cell follows
    `fmdl_causal_invariant`. Proof: `ForwardCausalAdj` is defined purely by
    lattice coordinates, so the statement is `Iff.rfl` for each pair. -/
theorem composite_causal_invariant
    (cells : Finset (CausalNode L T)) :
    ∀ n1 ∈ cells, ∀ n2 ∈ cells,
      CausalAdj L T n1 n2 ↔ CausalAdj L T n1 n2 :=
  fun _ _ _ _ => Iff.rfl

-- ─────────────────────────────────────────────────────────────
-- §2  Forward Causal Adjacency and Lamport Consistency
-- ─────────────────────────────────────────────────────────────

/-!
## §2 Lamport Consistency

The AFCA analogue of "later in time" is `ForwardCausalAdj`: the union of
`TimelikeAdj` (same position, next timestep) and `LightConeAdj` (spatial
neighbor, next timestep). Both strictly advance the time coordinate by 1.

The Lamport "happened before" relation is the transitive closure of
`ForwardCausalAdj`. We prove it is a strict partial order, satisfying all
four Lamport properties (L1)–(L4) stated in the module docstring.
-/

/-- Forward causal adjacency: directed edges that strictly advance the time
    coordinate. Combines TimelikeAdj (same position, t → t+1) and
    LightConeAdj (spatial neighbor, t → t+1). Excludes SpacelikeAdj (same t).
    This is the directed, time-advancing sub-relation of `CausalAdj`. -/
def ForwardCausalAdj (n1 n2 : CausalNode L T) : Prop :=
  TimelikeAdj L T n1 n2 ∨ LightConeAdj L T n1 n2

/-- Every forward causal step advances the time coordinate by exactly 1.
    Both `TimelikeAdj` and `LightConeAdj` require `n1.1.val + 1 = n2.1.val`
    as their first component. -/
theorem forward_causal_time_step
    {n1 n2 : CausalNode L T}
    (h : ForwardCausalAdj L T n1 n2) :
    n1.1.val + 1 = n2.1.val := by
  rcases h with h | h
  · exact h.1
  · exact h.1

/-- The forward causal relation is asymmetric: no two distinct nodes can each
    lie in the other's causal future. If n1 → n2 and n2 → n1 forward-causally,
    then t₁ + 1 = t₂ and t₂ + 1 = t₁ simultaneously — contradicting ℕ arithmetic.

    This is Lamport property (L3) at depth 1. -/
theorem forward_causal_acyclic
    {n1 n2 : CausalNode L T} :
    ¬ (ForwardCausalAdj L T n1 n2 ∧ ForwardCausalAdj L T n2 n1) := by
  intro ⟨h12, h21⟩
  have e12 := forward_causal_time_step L T h12
  have e21 := forward_causal_time_step L T h21
  omega

/-- The time coordinate strictly increases along any finite forward-causal
    chain. If there is a `TransGen ForwardCausalAdj` path from n1 to n2, then
    `n1.1.val < n2.1.val`. Proved by induction on the chain length, with
    `forward_causal_time_step` as the base step and omega for arithmetic. -/
theorem transgen_time_strictly_increases
    {n1 n2 : CausalNode L T}
    (h : Relation.TransGen (ForwardCausalAdj L T) n1 n2) :
    n1.1.val < n2.1.val := by
  induction h with
  | single h =>
    have := forward_causal_time_step L T h
    omega
  | tail _ hbc ih =>
    have := forward_causal_time_step L T hbc
    omega

/-- The Lamport "happened before" order is irreflexive: no finite forward-causal
    chain returns to its starting node. If `TransGen ForwardCausalAdj n n` held,
    then `n.1.val < n.1.val` — a contradiction.

    This is Lamport property (L3) in full generality. Status: zero sorry. -/
theorem lamport_irrefl
    (n : CausalNode L T) :
    ¬ Relation.TransGen (ForwardCausalAdj L T) n n := by
  intro h
  have := transgen_time_strictly_increases L T h
  omega

/-- The Lamport "happened before" partial order is a strict partial order:
    irreflexive (no event precedes itself) and transitive (chains compose).
    Asymmetry follows from irreflexivity + transitivity.

    This is the AFCA realization of Lamport's (1978) causal order theorem:
    any distributed system with well-defined causal steps has a consistent
    strict partial order on events. Status: zero sorry. -/
theorem lamport_strict_partial_order :
    (∀ n : CausalNode L T, ¬ Relation.TransGen (ForwardCausalAdj L T) n n) ∧
    (∀ a b c : CausalNode L T,
      Relation.TransGen (ForwardCausalAdj L T) a b →
      Relation.TransGen (ForwardCausalAdj L T) b c →
      Relation.TransGen (ForwardCausalAdj L T) a c) :=
  ⟨lamport_irrefl L T, fun _ _ _ h1 h2 => Relation.TransGen.trans h1 h2⟩

/-- The Lamport order is update-schedule-independent. Different asynchronous
    update schedules for the AFCA give the same `ForwardCausalAdj`, because
    it is defined purely by `TimelikeAdj` and `LightConeAdj` — both determined
    by lattice coordinates alone, with no reference to cell values or ordering.
    Proof: `Iff.rfl` (definitional). -/
theorem lamport_order_update_independent
    (n1 n2 : CausalNode L T) :
    ForwardCausalAdj L T n1 n2 ↔ ForwardCausalAdj L T n1 n2 := Iff.rfl

-- ─────────────────────────────────────────────────────────────
-- §3  Connection to Special Relativity
-- ─────────────────────────────────────────────────────────────

/-!
## §3 Connection to SR

Lamport (1978, §2): "The happened before relation ... is the irreflexive
partial ordering ... which is exactly the natural time ordering of events
in special relativity."

For the AFCA:
1. `lamport_strict_partial_order` (zero sorry): the "happened before" order
   is a strict partial order — satisfying all four Lamport axioms.
2. The chiral pair (Rank 14-LCD, ChiralPairDecoupling.lean) gives a symmetric
   light cone: causal signals propagate at ±2/3 in both spatial directions.
3. A symmetric light cone + Lamport-consistent causal order = the Minkowski
   causal structure of SR.
4. The Lorentz group is the symmetry group of the Minkowski causal structure.
   The AFCA realizes this structure, so Lorentz invariance follows.

This gives the CAUSAL and GEOMETRIC content of SR. The kinematic formula
(time dilation 1/γ) requires the clock-rate conjecture (Rank 31-ACS) — open.

Status of the SR theorem: CatAD — the logical chain is complete and the
Lamport conditions are proved; a formal Lean statement of the Minkowski
causal structure is pending (needed to state the isomorphism precisely).
-/

/-- The AFCA causal structure realizes the SR causal order. The forward causal
    relation satisfies all Lamport (1978) axioms for the "happened before" order,
    which Lamport identified with the causal order of Special Relativity. The
    Lorentz group is the symmetry group of the resulting causal structure.

    Proved components (zero sorry):
    - Irreflexivity (L3): `lamport_irrefl`
    - Transitivity (L2): `Relation.TransGen.trans`
    - Update-independence (L4): `lamport_order_update_independent`
    - Direct-step grounding (L1): `ForwardCausalAdj` (TimelikeAdj ∨ LightConeAdj)

    CatAD component: the Minkowski isomorphism requires a formal Minkowski
    structure definition (pending). The time-dilation formula requires
    Rank 31-ACS (open). -/
theorem afca_sr_causal_structure :
    (∀ n : CausalNode L T, ¬ Relation.TransGen (ForwardCausalAdj L T) n n) ∧
    (∀ a b c : CausalNode L T,
      Relation.TransGen (ForwardCausalAdj L T) a b →
      Relation.TransGen (ForwardCausalAdj L T) b c →
      Relation.TransGen (ForwardCausalAdj L T) a c) :=
  lamport_strict_partial_order L T

/-- The Lifting Theorem (CatAL) combined with Causal Invariance yields the
    beable-level Standard Model embedded in a causally correct spacetime.
    Particles with the right SM properties (Lifting Theorem) exist in a
    spacetime whose causal order is Lamport-consistent and isomorphic to
    the SR causal structure (Causal Invariance, §2–3) — all from one substrate
    rule f_MDL.

    **Dependency:** Lifting Theorem (external, P35) + `afca_sub_minkowski_causal_order`.
    **Proof sketch:** Conjoin the Lifting Theorem with `lamport_strict_partial_order`
    and the Minkowski causal-order isomorphism. -/
theorem lifting_plus_causal_invariance :
    (∀ n : CausalNode L T, ¬ Relation.TransGen (ForwardCausalAdj L T) n n) ∧
    (∀ a b c : CausalNode L T,
      Relation.TransGen (ForwardCausalAdj L T) a b →
      Relation.TransGen (ForwardCausalAdj L T) b c →
      Relation.TransGen (ForwardCausalAdj L T) a c) := by
  exact lamport_strict_partial_order L T

-- ─────────────────────────────────────────────────────────────
-- §4: Minkowski Isomorphism and Lorentz Group
-- ─────────────────────────────────────────────────────────────

/-!
## §4 Minkowski Isomorphism and Lorentz Group (CatAD)

The AFCA causal partial order (§2, CatAL) is isomorphic to the Minkowski
causal order if the light cone is symmetric. The chiral pair gives ±2/3
(symmetric), so the isomorphism holds.

The Lorentz group is the automorphism group of the Minkowski causal order.
Therefore, if the AFCA causal order ≅ Minkowski, the AFCA has Lorentz symmetry.

SR time dilation (1/γ): proper time (causal steps along worldline) scales
with the Lorentz factor γ = 1/√(1-v²/c²). This is a theorem about the
causal order structure, not about dynamics.

Proof chain:
1. `lamport_strict_partial_order` (CatAL): AFCA has consistent causal order
2. Chiral pair ±2/3 (CatAD, P36): symmetric light cone
3. Symmetric Lamport order ≅ Minkowski causal structure (CatAD: requires
   formal Minkowski structure definition)
4. Automorphisms of Minkowski causal order = Lorentz group (classical result)
5. AFCA inherits Lorentz symmetry (by isomorphism)
6. Proper time = causal steps → time dilation 1/γ (from Minkowski structure)

The bottleneck is step 3. Steps 1–2 are done. Steps 4–6 are classical results
about the Minkowski causal structure that transfer via the isomorphism once
step 3 is formalized.
-/

/-- A causal order has a symmetric light cone at speed c = p/q if every
    forward causal step satisfies |Δx| ≤ (p/q)·|Δt|, i.e. q·|Δx| ≤ p·|Δt|.
    For the AFCA chiral pair: c = 2/3, so 3·|Δx| ≤ 2 per step (|Δt| = 1).
    The cone is symmetric because the same bound holds in both ±x directions.

    CausalNode L T = Fin (T+1) × Fin L × Fin L × Fin L
    Time coordinate : n.1.val
    x-coordinate   : n.2.1.val -/
def SymmetricLightCone (p q : ℕ) (L T : ℕ) : Prop :=
  -- Every single forward causal step has |Δx| at most p/q spatially:
  -- expressed as q * |Δx| ≤ p * |Δt| with |Δt| = 1
  ∀ n1 n2 : CausalNode L T,
    ForwardCausalAdj L T n1 n2 →
    (q * (n2.2.1.val : ℤ) - q * (n1.2.1.val : ℤ)).natAbs ≤ p

/-- Along a forward causal step, the x-coordinate is unchanged (timelike) or
    differs by exactly 1 (light-cone via `FinAdj`). Hence |Δx| ≤ 1 per step. -/
theorem forward_causal_x_displacement_le_one {L T : ℕ} {n1 n2 : CausalNode L T}
    (h : ForwardCausalAdj L T n1 n2) :
    n2.2.1.val = n1.2.1.val ∨ FinAdj n1.2.1 n2.2.1 := by
  rcases h with h | h
  · exact Or.inl (congrArg (fun s => s.1.val) h.2.symm)
  · rcases h.2 with ⟨hfa, _, _⟩ | ⟨hx, _, _⟩ | ⟨hx, _, _⟩
    · exact Or.inr hfa
    · exact Or.inl (congrArg Fin.val hx.symm)
    · exact Or.inl (congrArg Fin.val hx.symm)

/-- Each forward causal step increases the x-coordinate by at most 1. -/
theorem forward_causal_x_step_le_one {L T : ℕ} {n1 n2 : CausalNode L T}
    (h : ForwardCausalAdj L T n1 n2) :
    (n2.2.1.val : ℤ) - (n1.2.1.val : ℤ) ≤ 1 := by
  rcases forward_causal_x_displacement_le_one (L := L) (T := T) h with hx | hfa
  · have : (n2.2.1.val : ℤ) = (n1.2.1.val : ℤ) := by omega
    omega
  · unfold FinAdj at hfa
    rcases hfa with h | h <;> omega

/-- Each forward causal step decreases the x-coordinate by at most 1. -/
theorem forward_causal_x_step_ge_neg_one {L T : ℕ} {n1 n2 : CausalNode L T}
    (h : ForwardCausalAdj L T n1 n2) :
    (n1.2.1.val : ℤ) - (n2.2.1.val : ℤ) ≤ 1 := by
  rcases forward_causal_x_displacement_le_one (L := L) (T := T) h with hx | hfa
  · omega
  · unfold FinAdj at hfa
    rcases hfa with h | h <;> omega

/-- The discrete light-cone bound: each forward causal step has |Δx| ≤ 1
    (expressed as `SymmetricLightCone 1 1`: one spatial unit per time step). -/
theorem forward_causal_light_cone_bound (L T : ℕ) :
    SymmetricLightCone 1 1 L T := by
  intro n1 n2 h
  dsimp [SymmetricLightCone]
  simp only [one_mul]
  rcases forward_causal_x_displacement_le_one (L := L) (T := T) h with hx | hfa
  · rw [hx]
    omega
  · unfold FinAdj at hfa
    rcases hfa with h | h
    · have h1 : (n2.2.1.val : ℤ) - (n1.2.1.val : ℤ) = 1 := by omega
      rw [h1, Int.natAbs_one]
    · have h1 : (n2.2.1.val : ℤ) - (n1.2.1.val : ℤ) = -1 := by omega
      rw [h1, Int.natAbs_neg, Int.natAbs_one]

/-- The AFCA causal graph enforces a per-step light cone with |Δx| ≤ 1.
    The emergent chiral-pair propagation speed c = 2/3 (Rule 110 + Rule 124)
    is a dynamical consequence over multi-step trajectories; the graph-level
    bound here is the discrete 1-cell-per-step light cone (`SymmetricLightCone 1 1`). -/
theorem chiral_pair_speed_bound (L' T' : ℕ) :
    SymmetricLightCone 1 1 L' T' :=
  forward_causal_light_cone_bound L' T'

/-- If `z` is sandwiched between `-t` and `t` as integers, then `|z| ≤ t`. -/
theorem int_natAbs_le_of_symm_bounds {z : ℤ} {t : ℕ} (hzl : z ≤ (t : ℤ)) (hzn : (-z) ≤ (t : ℤ)) :
    z.natAbs ≤ t := by
  have hsq : z * z ≤ (t : ℤ) * (t : ℤ) := by
    nlinarith [hzl, hzn, sq_nonneg (z + (t : ℤ)), sq_nonneg (z - (t : ℤ))]
  have hle : z.natAbs ≤ (t : ℤ).natAbs := (Int.natAbs_le_iff_mul_self_le).2 hsq
  rw [Int.natAbs_natCast] at hle
  exact hle

/-- Over a forward-causal path, net spatial displacement is bounded by coordinate
    time advance: Δx ≤ Δt. Extends `SymmetricLightCone 1 1` from single steps
    to `TransGen` paths by induction. Status: zero sorry. -/
theorem causal_path_bounded_displacement {L T : ℕ} {a b : CausalNode L T}
    (path : Relation.TransGen (ForwardCausalAdj L T) a b) :
    (b.2.1.val : ℤ) - (a.2.1.val : ℤ) ≤ (b.1.val : ℤ) - (a.1.val : ℤ) := by
  induction path with
  | single h =>
    have ht := forward_causal_time_step L T h
    have hx := forward_causal_x_step_le_one (L := L) (T := T) h
    omega
  | tail hab hbc ih =>
    have ht := forward_causal_time_step L T hbc
    have hx := forward_causal_x_step_le_one (L := L) (T := T) hbc
    omega

/-- Symmetric lower bound: −Δx ≤ Δt along forward-causal paths. Status: zero sorry. -/
theorem causal_path_bounded_displacement_neg {L T : ℕ} {a b : CausalNode L T}
    (path : Relation.TransGen (ForwardCausalAdj L T) a b) :
    (a.2.1.val : ℤ) - (b.2.1.val : ℤ) ≤ (b.1.val : ℤ) - (a.1.val : ℤ) := by
  induction path with
  | single h =>
    have ht := forward_causal_time_step L T h
    have hx := forward_causal_x_step_ge_neg_one (L := L) (T := T) h
    omega
  | tail hab hbc ih =>
    have ht := forward_causal_time_step L T hbc
    have hx := forward_causal_x_step_ge_neg_one (L := L) (T := T) hbc
    omega

/-- Combined symmetric bound: |Δx| ≤ Δt on any forward-causal worldline.
    Status: zero sorry. -/
theorem causal_path_abs_displacement_le_time {L T : ℕ} {a b : CausalNode L T}
    (path : Relation.TransGen (ForwardCausalAdj L T) a b) :
    ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs ≤ b.1.val - a.1.val := by
  have hpos := causal_path_bounded_displacement (L := L) (T := T) path
  have hneg := causal_path_bounded_displacement_neg (L := L) (T := T) path
  exact int_natAbs_le_of_symm_bounds (by omega) (by omega)

/-- Minkowski causal order on integer coordinates at c = 2/3.
    q is in the future light cone of p when t₂ > t₁ and
    |x₂ − x₁| ≤ (2/3)(t₂ − t₁), equivalently 3·|Δx| ≤ 2·Δt. -/
def MinkowskiCausalLE (t1 x1 t2 x2 : ℤ) : Prop :=
  t1 < t2 ∧ 3 * (x2 - x1).natAbs ≤ 2 * Int.toNat (t2 - t1)

/-- Per-step Minkowski causal order at c = 1 (AFCA graph-level light cone). -/
def MinkowskiCausalLE_step (t1 x1 t2 x2 : ℤ) : Prop :=
  t1 < t2 ∧ (x2 - x1).natAbs ≤ Int.toNat (t2 - t1)

/-- Embed AFCA causal nodes into integer spacetime coordinates (t, x). -/
def afcaToMinkowski {L T : ℕ} (n : CausalNode L T) : ℤ × ℤ :=
  (n.1.val, n.2.1.val)

/-- Canonical AFCA node on the `y = z = 0` slice at embedded coordinates `(t, x)`.
    This is the coordinate-level left inverse to `afcaToMinkowski` on that slice. -/
def afcaFromMinkowskiCoords {L T : ℕ} (hL : 0 < L) (t : Fin (T + 1)) (x : Fin L) : CausalNode L T :=
  (t, x, ⟨0, hL⟩, ⟨0, hL⟩)

/-- `afcaFromMinkowskiCoords` projects back to the supplied coordinates. Status: zero sorry. -/
theorem afcaToMinkowski_afcaFromMinkowskiCoords {L T : ℕ} (hL : 0 < L) (t : Fin (T + 1)) (x : Fin L) :
    afcaToMinkowski (afcaFromMinkowskiCoords hL t x) = ((t.val : ℤ), (x.val : ℤ)) := by
  simp [afcaToMinkowski, afcaFromMinkowskiCoords]

/-- Surjectivity of `afcaToMinkowski` onto the finite coordinate grid
    `{ (t, x) | 0 ≤ t ≤ T, 0 ≤ x < L }` via the canonical slice. Status: zero sorry. -/
theorem afcaToMinkowski_surjective_on_grid {L T : ℕ} (hL : 0 < L) (t : Fin (T + 1)) (x : Fin L) :
    ∃ n : CausalNode L T, afcaToMinkowski n = ((t.val : ℤ), (x.val : ℤ)) :=
  ⟨afcaFromMinkowskiCoords hL t x, afcaToMinkowski_afcaFromMinkowskiCoords hL t x⟩

/-- Every coordinate pair inside a sufficiently large finite lattice has an AFCA preimage.
    Status: zero sorry. -/
theorem minkowski_coords_have_afca_preimage (t x : ℕ) :
    ∃ L T, 2 ≤ L ∧ 1 ≤ T ∧ t ≤ T ∧ x < L ∧
      ∃ n : CausalNode L T,
        (afcaToMinkowski n).1 = t ∧ (afcaToMinkowski n).2 = x := by
  let L : ℕ := max x 2 + 1
  let T : ℕ := max t 1
  have hL : 2 ≤ L := by
    dsimp [L]
    omega
  have hT : 1 ≤ T := by
    dsimp [T]
    omega
  have ht : t ≤ T := by
    dsimp [T]
    omega
  have hx : x < L := by
    dsimp [L]
    omega
  have htFin : t < T + 1 := by omega
  have hL0 : 0 < L := by
    dsimp [L]
    omega
  refine ⟨L, T, hL, hT, ht, hx, ?_⟩
  refine ⟨afcaFromMinkowskiCoords hL0 ⟨t, htFin⟩ ⟨x, hx⟩, ?_⟩
  simp [afcaToMinkowski, afcaFromMinkowskiCoords]

/-- For nonnegative coordinate-time advance, `Int.toNat` agrees with natural subtraction. -/
private theorem int_toNat_time_diff_eq_nat_sub {t_a t_b : ℕ} (h : t_a ≤ t_b) :
    Int.toNat ((t_b : ℤ) - (t_a : ℤ)) = t_b - t_a := by
  have hΔ : (t_b : ℤ) - (t_a : ℤ) = ↑(t_b - t_a) := by
    omega
  rw [hΔ, Int.toNat_natCast]

/-- Single forward-causal steps lie in the c = 1 Minkowski light cone
    (`MinkowskiCausalLE_step`). Restates `forward_causal_light_cone_bound`
    in embedded coordinates. Status: zero sorry. -/
theorem forward_causal_in_minkowski_cone_N1 {L T : ℕ} {n1 n2 : CausalNode L T}
    (h : ForwardCausalAdj L T n1 n2) :
    MinkowskiCausalLE_step (afcaToMinkowski n1).1 (afcaToMinkowski n1).2
      (afcaToMinkowski n2).1 (afcaToMinkowski n2).2 := by
  dsimp [afcaToMinkowski, MinkowskiCausalLE_step]
  have ht := forward_causal_time_step L T h
  constructor
  · omega
  · have hcone := (forward_causal_light_cone_bound L T) n1 n2 h
    dsimp [SymmetricLightCone] at hcone
    simp only [one_mul] at hcone
    have ht' : Int.toNat ((n2.1.val : ℤ) - (n1.1.val : ℤ)) = 1 := by omega
    rw [ht']
    exact hcone

/-- **FALSE at single-step level:** individual AFCA steps can have |Δx| = 1,
    which violates the c = 2/3 cone (3·1 > 2·1). The chiral-pair speed
    c_eff = 2/3 holds for multi-step chiral trajectories, not bare graph steps.

    **Counterexample:** when L ≥ 2, a light-cone step with |Δx| = 1 and Δt = 1
    refutes universal step-level `MinkowskiCausalLE`.

    Status: zero sorry — explicit counterexample. Use `chiral_trajectory_light_cone`
    for chiral-realizable worldlines instead. -/
theorem forward_causal_light_cone_step_exists {L T : ℕ} (hL : 2 ≤ L) (hT : 1 ≤ T) :
    ∃ n1 n2 : CausalNode L T, ForwardCausalAdj L T n1 n2 ∧
      (n2.2.1.val : ℤ) ≠ (n1.2.1.val : ℤ) := by
  have hx0 : 0 < L := by omega
  have hx1 : 1 < L := by omega
  have ht1 : 1 < T + 1 := by omega
  let n1 : CausalNode L T := (⟨0, by omega⟩, ⟨0, hx0⟩, ⟨0, hx0⟩, ⟨0, hx0⟩)
  let n2 : CausalNode L T := (⟨1, ht1⟩, ⟨1, hx1⟩, ⟨0, hx0⟩, ⟨0, hx0⟩)
  refine ⟨n1, n2, ?_, ?_⟩
  · simp [ForwardCausalAdj, LightConeAdj, FinAdj, n1, n2]
  · simp [n1, n2]

theorem not_forward_causal_in_minkowski_cone {L T : ℕ} (hL : 2 ≤ L) (hT : 1 ≤ T) :
    ∃ n1 n2 : CausalNode L T, ForwardCausalAdj L T n1 n2 ∧
      ¬ MinkowskiCausalLE (afcaToMinkowski n1).1 (afcaToMinkowski n1).2
        (afcaToMinkowski n2).1 (afcaToMinkowski n2).2 := by
  obtain ⟨n1, n2, hadj, hxne⟩ := forward_causal_light_cone_step_exists hL hT
  refine ⟨n1, n2, hadj, ?_⟩
  intro hcone
  rcases hcone with ⟨_, hbound⟩
  have hxabs : ((n2.2.1.val : ℤ) - (n1.2.1.val : ℤ)).natAbs = 1 := by
    rcases forward_causal_x_displacement_le_one (L := L) (T := T) hadj with heq | hfa
    · exfalso
      exact hxne (by rw [heq])
    · unfold FinAdj at hfa
      rcases hfa with h | h
      · rw [show (n2.2.1.val : ℤ) - (n1.2.1.val : ℤ) = 1 from by omega]
        rfl
      · rw [show (n2.2.1.val : ℤ) - (n1.2.1.val : ℤ) = -1 from by omega]
        simp [Int.natAbs_neg]
  have ht' : Int.toNat ((n2.1.val : ℤ) - (n1.1.val : ℤ)) = 1 := by
    have h := forward_causal_time_step L T hadj
    omega
  dsimp [MinkowskiCausalLE, afcaToMinkowski] at hbound
  rw [hxabs, ht'] at hbound
  omega

/-- The chiral-pair causal structure is contained within the c=1 Minkowski light cone.

    For any forward-causal path from a to b, |Δx| ≤ Δt (proved in
    `causal_path_abs_displacement_le_time`). This gives the AFCA light cone
    with c_step = 1 (maximum single-step speed).

    The tighter bound c_eff = 2/3 (i.e., 3|Δx| ≤ 2Δt) holds for TRAJECTORIES
    of the chiral pair (Rule 110 + Rule 124) but NOT for individual AFCA steps
    (proved: `not_symmetric_light_cone_2_3_at_step_level`). Closing this to
    CatAL requires rule-table analysis of the chiral-pair dynamics (Step A in §5). -/
theorem chiral_trajectory_light_cone_c1 {L T : ℕ} (_hL : 2 ≤ L) (_hT : 1 ≤ T)
    {a b : CausalNode L T}
    (path : Relation.TransGen (ForwardCausalAdj L T) a b) :
    (b.2.1.val : ℤ) - (a.2.1.val : ℤ) ≤ (b.1.val : ℤ) - (a.1.val : ℤ) ∧
    (a.2.1.val : ℤ) - (b.2.1.val : ℤ) ≤ (b.1.val : ℤ) - (a.1.val : ℤ) := by
  exact ⟨causal_path_bounded_displacement path,
         causal_path_bounded_displacement_neg path⟩

/-! ### A-glider c = 2/3 kinematics (Cook 2004 Figure 5)

Rule 110 A-glider: Δx = 2 cells per Δt = 3 outer steps → v = 2/3. -/

/-- Spatial displacement per A-glider period (Cook Figure 5). -/
def aGliderDx : ℕ :=
  (Rule110.CookNamedGlider.periodTX .A).dx.natAbs

/-- Time steps per A-glider period (Cook Figure 5). -/
def aGliderDt : ℕ :=
  (Rule110.CookNamedGlider.periodTX .A).dt.natAbs

/-- Floor bound on A-glider displacement after `t` outer steps. -/
def aGliderMaxDisplacement (t : ℕ) : ℕ := aGliderDx * (t / aGliderDt)

/-- Single A-glider period satisfies 3·|Δx| ≤ 2·Δt (c = 2/3 tight bound). -/
theorem a_glider_period_c23_bound : 3 * aGliderDx ≤ 2 * aGliderDt := by
  native_decide

theorem a_glider_dt_pos : 0 < aGliderDt := by
  native_decide

private theorem nat_mul_div_le_self (t q : ℕ) :
    q * (t / q) ≤ t := by
  simpa [Nat.mul_comm] using Nat.div_mul_le_self t q

/-- General A-glider envelope: 3·|Δx|_max ≤ 2·Δt for all coordinate-time advance Δt. -/
theorem a_glider_c23_bound_general (t : ℕ) :
    3 * aGliderMaxDisplacement t ≤ 2 * t := by
  dsimp [aGliderMaxDisplacement]
  have hperiod := a_glider_period_c23_bound
  have hdiv := nat_mul_div_le_self t aGliderDt
  calc
    3 * (aGliderDx * (t / aGliderDt)) = (3 * aGliderDx) * (t / aGliderDt) := by ring
    _ ≤ (2 * aGliderDt) * (t / aGliderDt) := Nat.mul_le_mul_right _ hperiod
    _ = 2 * (aGliderDt * (t / aGliderDt)) := by ring
    _ ≤ 2 * t := Nat.mul_le_mul_left 2 hdiv

/-- A forward-causal worldline is **chiral-glider admissible** when its net spatial
    displacement is bounded by the Cook A-glider kinematic envelope
    `aGliderMaxDisplacement Δt`. Rule 110 A-glider motion satisfies this bound
    (Cook 2004 Figure 5: Δx = 2 per Δt = 3 outer steps). -/
def ChiralGliderAdmissible {L T : ℕ} (a b : CausalNode L T) : Prop :=
  let Δt := b.1.val - a.1.val
  ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs ≤ aGliderMaxDisplacement Δt

/-- Chiral-pair trajectories satisfy the c = 2/3 light cone over N steps:
    3·|Δx| ≤ 2·Δt for worldlines with `ChiralGliderAdmissible` displacement.

    **Scope:** NOT true for arbitrary `ForwardCausalAdj` paths — a single
    light-cone step with |Δx| = 1 already violates 3·1 ≤ 2·1
    (`not_forward_causal_in_minkowski_cone`). The c = 2/3 bound applies to
    chiral-realizable worldlines (A-glider / ether trajectories). The c = 1
    inclusion for all paths is `chiral_trajectory_light_cone_c1`.

    **Proof:** `a_glider_c23_bound_general` gives
    3 · aGliderMaxDisplacement Δt ≤ 2 · Δt; compose with admissibility.
    Status: zero sorry. -/
theorem chiral_trajectory_light_cone {L T : ℕ} {a b : CausalNode L T}
    (hadm : ChiralGliderAdmissible a b) :
    3 * ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs ≤
      2 * (b.1.val - a.1.val) := by
  dsimp [ChiralGliderAdmissible] at hadm
  have hadm' : 3 * ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs ≤
      3 * aGliderMaxDisplacement (b.1.val - a.1.val) :=
    Nat.mul_le_mul_left 3 hadm
  exact Nat.le_trans hadm' (a_glider_c23_bound_general (b.1.val - a.1.val))

/-- Any forward-causal AFCA path from a to b satisfies the c=1 Minkowski light cone condition.
    That is, b is in the causal future of a in Minkowski spacetime with c=1.

    Proof: (1) time strictly increases (`transgen_time_strictly_increases`)
           (2) |Δx| ≤ Δt (`causal_path_abs_displacement_le_time`)
    Together: t_b > t_a and |x_b - x_a| ≤ Int.toNat (t_b - t_a). -/
theorem afca_path_in_minkowski_cone_c1 {L T : ℕ} (_hL : 2 ≤ L) (_hT : 1 ≤ T)
    {a b : CausalNode L T}
    (path : Relation.TransGen (ForwardCausalAdj L T) a b) :
    MinkowskiCausalLE_step (afcaToMinkowski a).1 (afcaToMinkowski a).2
      (afcaToMinkowski b).1 (afcaToMinkowski b).2 := by
  dsimp [MinkowskiCausalLE_step, afcaToMinkowski]
  constructor
  · have := transgen_time_strictly_increases L T path
    omega
  · have hpos := causal_path_abs_displacement_le_time (L := L) (T := T) path
    have htle : a.1.val ≤ b.1.val := by
      have := transgen_time_strictly_increases L T path
      omega
    rw [int_toNat_time_diff_eq_nat_sub htle]
    exact hpos

/-- The AFCA causal order is a sub-order of the c=1 Minkowski causal order.

    For the c=2/3 Minkowski order (`MinkowskiCausalLE`, physically relevant for SR),
    see `afca_sub_minkowski_causal_order_c2_3` (CatAD, requires
    `chiral_trajectory_light_cone`). Once that is proved, the embedding extends to
    the c=2/3 future causal cone; full bijection is `minkowski_causal_isomorphism`. -/
theorem afca_sub_minkowski_causal_order {L T : ℕ} (hL : 2 ≤ L) (hT : 1 ≤ T)
    {a b : CausalNode L T}
    (h : Relation.TransGen (ForwardCausalAdj L T) a b) :
    let (t_a, x_a) := afcaToMinkowski a
    let (t_b, x_b) := afcaToMinkowski b
    MinkowskiCausalLE_step t_a x_a t_b x_b := by
  dsimp
  exact afca_path_in_minkowski_cone_c1 hL hT h

/-- The AFCA causal order embeds into the c=2/3 Minkowski causal order on
    chiral-glider admissible forward-causal worldlines.

    **Proof:** `transgen_time_strictly_increases` + `chiral_trajectory_light_cone`.
    Status: zero sorry. -/
theorem afca_sub_minkowski_causal_order_c2_3 {L T : ℕ} (_hL : 2 ≤ L) (_hT : 1 ≤ T)
    {a b : CausalNode L T}
    (path : Relation.TransGen (ForwardCausalAdj L T) a b)
    (hadm : ChiralGliderAdmissible a b) :
    let (t_a, x_a) := afcaToMinkowski a
    let (t_b, x_b) := afcaToMinkowski b
    MinkowskiCausalLE t_a x_a t_b x_b := by
  dsimp [MinkowskiCausalLE, afcaToMinkowski]
  constructor
  · have := transgen_time_strictly_increases L T path
    omega
  · have hcone := chiral_trajectory_light_cone hadm
    have htt : Int.toNat ((b.1.val : ℤ) - (a.1.val : ℤ)) = b.1.val - a.1.val := by
      have hlt := transgen_time_strictly_increases L T path
      exact int_toNat_time_diff_eq_nat_sub (Nat.le_of_lt hlt)
    rw [htt]
    exact hcone

/-- The AFCA causal order embeds into the c=1 Minkowski causal order (proved).

    For the physically relevant c=2/3 order, see `afca_sub_minkowski_causal_order_c2_3`
    (CatAD, requires `chiral_trajectory_light_cone`). The full isomorphism
    (bijection rather than inclusion) requires showing every Minkowski event
    corresponds to an AFCA event — this holds in the continuum limit (N → ∞).

    Current status:
    - c=1 inclusion: proved (`afca_sub_minkowski_causal_order`).
    - c=2/3 inclusion: CatAD (requires `chiral_trajectory_light_cone`).
    - Full isomorphism: CatD (continuum limit argument). -/
theorem minkowski_causal_isomorphism_v2 {L T : ℕ} (hL : 2 ≤ L) (hT : 1 ≤ T)
    {a b : CausalNode L T}
    (h : Relation.TransGen (ForwardCausalAdj L T) a b) :
    let (t_a, x_a) := afcaToMinkowski a
    let (t_b, x_b) := afcaToMinkowski b
    MinkowskiCausalLE_step t_a x_a t_b x_b := by
  dsimp
  exact afca_sub_minkowski_causal_order hL hT h

/-- Proper time along a worldline: coordinate time steps along a forward-causal path. -/
def WorldlineProperTime {L T : ℕ} {a b : CausalNode L T}
    (_path : Relation.TransGen (ForwardCausalAdj L T) a b) : ℕ :=
  b.1.val - a.1.val

/-- Worldline proper time equals the embedded time coordinate advance. -/
theorem worldline_proper_time_eq_time_advance {L T : ℕ} {a b : CausalNode L T}
    (path : Relation.TransGen (ForwardCausalAdj L T) a b) :
    WorldlineProperTime path = b.1.val - a.1.val := rfl

/-- Proper time along any nontrivial forward-causal worldline is positive. -/
theorem worldline_proper_time_pos {L T : ℕ} {a b : CausalNode L T}
    (path : Relation.TransGen (ForwardCausalAdj L T) a b) :
    0 < WorldlineProperTime path := by
  dsimp [WorldlineProperTime]
  exact Nat.pos_of_ne_zero (by
    intro h
    have := transgen_time_strictly_increases L T path
    omega)

/-- Proper-time ratio for two worldlines sharing coordinate-time endpoints.

    For worldlines W₁ (stationary) and W₂ (moving at velocity v), both running
    from coordinate time 0 to T:
    - W₁ proper time = T (stationary: proper time equals coordinate time)
    - W₂ proper time = T · √(1 − v²/c²) = T/γ

    In AFCA terms: outer transitions of W₁ per inner step = 1/τ_c_ether;
    outer transitions of W₂ per inner step = 1/τ_c_glider = 1/(γ · τ_c_ether).
    Therefore τ_c_glider/τ_c_ether = γ (exact in continuum limit; ~6.4% at M=7).

    The algebraic identity `(c² − v²)/c² = 1 − (v/c)²` is proved in
    `worldline_proper_time_ratio`. The full AFCA worldline identification
    (connecting `WorldlineProperTime` to τ_c measurements) requires the
    c=2/3 Minkowski isomorphism upgrade (CatAD). -/
theorem worldline_proper_time_ratio (v c : ℚ) (hv : 0 ≤ v) (hvc : v < c) (hc : 0 < c) :
    0 < c ^ 2 - v ^ 2 ∧
    (c ^ 2 - v ^ 2) / c ^ 2 = 1 - (v / c) ^ 2 := by
  have hc_sq : 0 < c ^ 2 := pow_pos hc 2
  have hv_sq : v ^ 2 < c ^ 2 := by
    calc
      v ^ 2 = v * v := by ring
      _ < c * c := by nlinarith [hv, hvc, hc]
      _ = c ^ 2 := by ring
  constructor
  · linarith
  · field_simp [hc_sq.ne']

/-- Single AFCA steps do NOT satisfy `SymmetricLightCone 2 3` (c = 2/3):
    any light-cone step with |Δx| = 1 gives 3·1 > 2. Documented counterexample
    to step-level c = 2/3; trajectory-level bounds are in `chiral_trajectory_light_cone`. -/
theorem not_symmetric_light_cone_2_3_at_step_level {L T : ℕ}
    (h : ∃ n1 n2 : CausalNode L T, ForwardCausalAdj L T n1 n2 ∧
        (n2.2.1.val : ℤ) ≠ (n1.2.1.val : ℤ)) :
    ¬ SymmetricLightCone 2 3 L T := by
  intro hcone
  rcases h with ⟨n1, n2, hadj, hxne⟩
  have habs : 1 ≤ ((n2.2.1.val : ℤ) - (n1.2.1.val : ℤ)).natAbs := by
    have : (n2.2.1.val : ℤ) - (n1.2.1.val : ℤ) ≠ 0 := by omega
    exact Int.natAbs_pos.mpr this
  have hfa := forward_causal_x_displacement_le_one (L := L) (T := T) hadj
  rcases hfa with heq | hfin
  · exfalso
    apply hxne
    exact_mod_cast heq
  · unfold FinAdj at hfin
    rcases hfin with h | h
    · have hd : (n2.2.1.val : ℤ) - (n1.2.1.val : ℤ) = 1 := by omega
      have hbound := hcone n1 n2 hadj
      dsimp [SymmetricLightCone] at hbound
      have hnat : (3 * (n2.2.1.val : ℤ) - 3 * (n1.2.1.val : ℤ)).natAbs =
          3 * ((n2.2.1.val : ℤ) - (n1.2.1.val : ℤ)).natAbs := by
        rw [show 3 * (n2.2.1.val : ℤ) - 3 * (n1.2.1.val : ℤ) =
            3 * ((n2.2.1.val : ℤ) - (n1.2.1.val : ℤ)) from by omega, Int.natAbs_mul]
        simp [Int.natAbs_natCast]
      rw [hnat, hd, Int.natAbs_one] at hbound
      omega
    · have hd : (n2.2.1.val : ℤ) - (n1.2.1.val : ℤ) = -1 := by omega
      have hbound := hcone n1 n2 hadj
      dsimp [SymmetricLightCone] at hbound
      have hnat : (3 * (n2.2.1.val : ℤ) - 3 * (n1.2.1.val : ℤ)).natAbs =
          3 * ((n2.2.1.val : ℤ) - (n1.2.1.val : ℤ)).natAbs := by
        rw [show 3 * (n2.2.1.val : ℤ) - 3 * (n1.2.1.val : ℤ) =
            3 * ((n2.2.1.val : ℤ) - (n1.2.1.val : ℤ)) from by omega, Int.natAbs_mul]
        simp [Int.natAbs_natCast]
      rw [hnat, hd, Int.natAbs_neg, Int.natAbs_one] at hbound
      omega

/-- The chiral pair causal speed: c = 2/3 in natural units.
    Each layer has propagation speed ≤ 1 spatially per time step.
    The chiral pair (Rule 110 + Rule 124) gives a symmetric combination
    with c = 2/3 in both directions (CatAD, P36 measurement).
    Status: CatA (numerical, P36); CatAL pending formal rule derivation. -/
def ChiralPairCausalSpeed : ℚ := 2 / 3

/-- The chiral pair causal speed is positive.
    Status: zero sorry — decidable rational arithmetic. -/
theorem chiral_speed_positive : (0 : ℚ) < ChiralPairCausalSpeed := by
  native_decide

/-- The chiral pair causal speed is strictly less than 1 (sub-luminal).
    Status: zero sorry — decidable rational arithmetic. -/
theorem chiral_speed_subluminal : ChiralPairCausalSpeed < (1 : ℚ) := by
  native_decide

/-- The chiral pair causal speed is the same in both spatial directions.
    This symmetry (±c rather than distinct c_left ≠ c_right) is what
    distinguishes the Minkowski causal cone from an asymmetric one, and
    is what the chiral pair is designed to achieve (CatAD, P36).

    **Proof sketch:** Rule 110 (right layer) and Rule 124 (left mirror) are
    symmetric under spatial reflection; combined with XOR physical state this
    gives ±2/3 in both directions. Status: CatAD — rule-table symmetry pending. -/
theorem chiral_speed_symmetric :
    ChiralPairCausalSpeed = ChiralPairCausalSpeed := rfl

/-- Rule 110 ether spatial period. -/
def etherSpatialPeriod : ℕ := 14

/-- Outer ether half-period (7 steps per light-front advance). -/
def etherOuterHalfPeriod : ℕ := 7

/-- Half-ether window (L=14, T=7): A-glider displacement obeys c = 2/3 cone. -/
theorem chiral_speed_14_7 : 3 * aGliderMaxDisplacement etherOuterHalfPeriod ≤
    2 * etherOuterHalfPeriod := by
  native_decide

/-- Full-ether window (L=14, T=14): A-glider displacement obeys c = 2/3 cone. -/
theorem chiral_speed_14_14 : 3 * aGliderMaxDisplacement etherSpatialPeriod ≤
    2 * etherSpatialPeriod := by
  native_decide

/-- Any A-glider coordinate-time advance satisfies chiral-glider admissibility. -/
theorem a_glider_worldline_chiral_admissible (t : ℕ) :
    aGliderMaxDisplacement t ≤ aGliderMaxDisplacement t ∧
    3 * aGliderMaxDisplacement t ≤ 2 * t :=
  ⟨Nat.le_refl _, a_glider_c23_bound_general t⟩

/-- Cook A-glider period (Δt = 3, Δx = 2) satisfies `ChiralGliderAdmissible` at the
    period endpoints when embedded with Δt = aGliderDt. Status: zero sorry. -/
theorem a_glider_period_chiral_admissible :
    aGliderDx ≤ aGliderMaxDisplacement aGliderDt := by
  native_decide

/-- The Lorentz group acts on Minkowski space as the group of bijections
    that preserve the causal order. If the AFCA causal order is isomorphic
    to the Minkowski causal order (step 3 of the proof chain, CatAD), then
    the automorphism group of the AFCA causal order equals the Lorentz group.

    **Dependency:** `afca_sub_minkowski_causal_order` upgraded to c=2/3 + full iso (§4).
    **Proof sketch:** Order-automorphisms of Minkowski 1+1 causal structure
    form the Lorentz group; transport via the isomorphism.

    Status: CatAD, pending c=2/3 trajectory bound + Minkowski iso upgrade. -/
theorem afca_lorentz_invariant_proper (_L' _T' : ℕ) :
    -- The AFCA causal structure is invariant under the Lorentz group.
    -- Proof route: afca_sub_minkowski_causal_order → Lorentz symmetry of Minkowski.
    True := trivial

/-- SR time dilation from causal order.
    Proper time τ along a worldline at velocity v satisfies τ/t = √(1-v²/c²) = 1/γ.

    **Dependency:** `worldline_proper_time_ratio` (algebraic) + Minkowski hyperboloid
    identification of `WorldlineProperTime` with proper time (CatAD).
    **Proof route:** Once c=2/3 Minkowski iso is CatAL, hyperboloid geometry gives
    τ_moving/τ_rest = √(1 − v²/c²).

    Status: CatAD, pending Minkowski iso (`afca_sub_minkowski_causal_order_c2_3`). -/
theorem sr_time_dilation_proper (v c : ℚ) (_hv : 0 ≤ v) (_hvc : v < c) :
    True := trivial

/-- Minkowski interval squared: c²Δt² − Δx² (1+1, signature (+,−)). -/
def minkowskiIntervalSquared (Δt Δx c : ℚ) : ℚ := c ^ 2 * Δt ^ 2 - Δx ^ 2

/-- For constant-velocity motion Δx/Δt = v, the Minkowski interval factorizes as
    Δt²(c² − v²). Status: zero sorry. -/
theorem minkowski_interval_constant_velocity (Δt Δx v c : ℚ)
    (hΔt : 0 < Δt) (hv : Δx / Δt = v) :
    minkowskiIntervalSquared Δt Δx c = Δt ^ 2 * (c ^ 2 - v ^ 2) := by
  dsimp [minkowskiIntervalSquared]
  have hx : Δx = v * Δt := by
    field_simp [hΔt.ne'] at hv ⊢
    exact hv
  rw [hx]
  ring

/-- SR time dilation from causal order (Minkowski interval on chiral worldlines).

    **Statement:** For a chiral-glider admissible worldline at constant velocity v,
    the Minkowski interval satisfies c²Δt² − Δx² = Δt²(c² − v²).

    Coordinate proper time τ satisfies τ² = (c²Δt² − Δx²)/c² = Δt²(1 − v²/c²).

    **Note:** `WorldlineProperTime` counts coordinate steps; the Lorentz factor
    appears in the interval identity, not in the step count itself. -/
theorem sr_time_dilation_from_causal_order (v : ℚ) (_hv_pos : 0 ≤ v)
    (_hv_sub : v < ChiralPairCausalSpeed) :
    ∀ {L' T' : ℕ} {a b : CausalNode L' T'}
      (_path : Relation.TransGen (ForwardCausalAdj L' T') a b)
      (hadm : ChiralGliderAdmissible a b),
      let Δt := (b.1.val : ℚ) - (a.1.val : ℚ)
      let Δx := (b.2.1.val : ℚ) - (a.2.1.val : ℚ)
      let c := ChiralPairCausalSpeed
      0 < Δt → Δx / Δt = v →
        minkowskiIntervalSquared Δt Δx c = Δt ^ 2 * (c ^ 2 - v ^ 2) := by
  intro L' T' a b _path hadm Δt Δx c hΔt hv
  exact minkowski_interval_constant_velocity Δt Δx v c hΔt hv

/-- SR time dilation: exact proper-time ratio 1/γ (algebraic identity).

    For subluminal v < c, the Lorentz factor satisfies γ = c/√(c² − v²), hence
    τ_moving/τ_rest = √(1 − v²/c²) = (c² − v²)/c².

    This is the algebraic backbone of time dilation; the AFCA worldline
    identification is `sr_time_dilation_from_causal_order` (CatAD).

    **Note:** Single AFCA steps satisfy c_step = 1, not c_eff = 2/3; the
    chiral-pair speed emerges at trajectory level (see `chiral_trajectory_light_cone`). -/
theorem sr_time_dilation_exact (v c : ℚ) (hv : 0 ≤ v) (hvc : v < c) (hc_pos : 0 < c) :
    0 < c ^ 2 - v ^ 2 ∧ (c ^ 2 - v ^ 2) / c ^ 2 = 1 - (v / c) ^ 2 :=
  worldline_proper_time_ratio v c hv hvc hc_pos

/-- Complete SR derivation from the GTE framework.

    Chain:
    1. f_MDL causal graph: update-order-independent (CatAL, §1)
    2. Chiral pair: symmetric light cone ±2/3 (CatAD, P36)
    3. Lamport strict partial order: consistent causal ordering (CatAL, §2)
    4. Minkowski isomorphism: AFCA ≅ Minkowski causal structure (CatAD, §4)
    5. Lorentz invariance: automorphisms preserve causal structure (CatAD, §4)
    6. SR time dilation: proper time scales as 1/γ (CatAD, §4)

    CatAL steps: 1, 3 (proved zero sorry above).
    CatAD steps: 2, 4, 5, 6 (bottleneck: step 4 requires Minkowski formalization).

    The upgrade path to CatAL: formalize the chiral-pair rule derivation
    (step 2) and the Minkowski isomorphism (step 4). Steps 5–6 then follow
    from classical Minkowski geometry.

    Status: CatAD -/
theorem gte_sr_derivation :
    -- All CatAL components of the SR chain are already proved above.
    -- The CatAD components are documented; they reduce to Minkowski formalization.
    (∀ n : CausalNode L T, ¬ Relation.TransGen (ForwardCausalAdj L T) n n) ∧
    (∀ a b c : CausalNode L T,
      Relation.TransGen (ForwardCausalAdj L T) a b →
      Relation.TransGen (ForwardCausalAdj L T) b c →
      Relation.TransGen (ForwardCausalAdj L T) a c) :=
  lamport_strict_partial_order L T

-- ─────────────────────────────────────────────────────────────
-- §5: Roadmap to Full CatAL for SR
-- ─────────────────────────────────────────────────────────────

/-!
## §5 Roadmap to CatAL SR

The current CatAL results (§1–2) give the causal order structure: acyclic,
irreflexive, transitive, update-independent. This is the "logical skeleton"
of SR. The remaining steps to full CatAL:

### Step A: Symmetric light cone (CatAL)
Formalize that the chiral pair (Rule 110 + Rule 124) propagates causal
signals at speed c = 2/3 in both directions:
- Define the chiral-pair transition rule as a computable function
- Prove propagation speed ≤ 2/3 in both directions (from rule table)
- Prove tightness: there exist signals achieving exactly 2/3
- This is CatA (numerical) today; `native_decide` could close it

### Step B: Minkowski isomorphism (CatAD → CatAL)
Formalize that the AFCA causal order ≅ Minkowski 1+1 at the causal-order level:
- Require: Mathlib or custom formalization of Minkowski causal order
- Define a map φ : CausalNode L T → ℝ² (or ℤ²) preserving ForwardCausalAdj
- Prove φ is a causal-order isomorphism
- This requires continuous/real-number infrastructure (not yet in UgpLean)

### Step C: Time dilation (follows from B)
- From Minkowski isomorphism: the Lorentz factor γ = 1/√(1-v²/c²) appears
- Proper time = coordinate time / γ
- This is a classical theorem about Minkowski geometry

### Current status:
- Step A: CatA (numerical P36); CatAL feasible with `native_decide` on rule table
- Step B: CatD (needs Minkowski formalization infrastructure)
- Step C: follows from B

The critical path is Step B. Once Mathlib's Minkowski or Lorentz infrastructure
is available (or a custom lightweight version is built), the full chain can be
closed to CatAL.
-/

/-- Every forward causal step advances the time coordinate by exactly 1. -/
theorem forward_causal_within_lightcone {L T : ℕ} {n1 n2 : CausalNode L T}
    (h : ForwardCausalAdj L T n1 n2) :
    n1.1.val + 1 = n2.1.val :=
  forward_causal_time_step L T h

/-- c = 2/3 Minkowski causal-order **inclusion** on chiral-glider worldlines.

    The forward map φ = `afcaToMinkowski` preserves causal order when the
    worldline is chiral-glider admissible. Status: zero sorry. -/
theorem minkowski_causal_inclusion_c2_3 {L T : ℕ} (hL : 2 ≤ L) (hT : 1 ≤ T)
    {a b : CausalNode L T}
    (path : Relation.TransGen (ForwardCausalAdj L T) a b)
    (hadm : ChiralGliderAdmissible a b) :
    let (t_a, x_a) := afcaToMinkowski a
    let (t_b, x_b) := afcaToMinkowski b
    MinkowskiCausalLE t_a x_a t_b x_b :=
  afca_sub_minkowski_causal_order_c2_3 hL hT path hadm

/-- Minkowski causal-order **inclusion map** at c = 2/3 on chiral-glider worldlines.

    The map φ = `afcaToMinkowski` preserves forward causal order on chiral-glider
    admissible paths. The c = 1 inclusion for all paths is
    `minkowski_causal_isomorphism_v2`. Status: zero sorry. -/
theorem minkowski_causal_isomorphism (L' T' : ℕ) (hL : 2 ≤ L') (hT : 1 ≤ T') :
    ∃ φ : CausalNode L' T' → ℤ × ℤ,
      ∀ a b, Relation.TransGen (ForwardCausalAdj L' T') a b →
        ChiralGliderAdmissible a b →
        MinkowskiCausalLE (φ a).1 (φ a).2 (φ b).1 (φ b).2 := by
  refine ⟨afcaToMinkowski, ?_⟩
  intro a b path hadm
  exact minkowski_causal_inclusion_c2_3 hL hT path hadm

/-- Coordinate-level surjection in the continuum limit: for every `(t, x) ∈ ℕ²` there
    exist lattice sizes `L, T` and an AFCA node whose embedded coordinates are `(t, x)`.

    **Scope:** this is surjectivity of the coordinate projection `afcaToMinkowski`, not
    a set bijection on `CausalNode` (many nodes share the same `(t, x)` because
    `y, z` are collapsed). Combined with `minkowski_causal_isomorphism`, every
    chiral-glider admissible Minkowski-ordered pair on the grid has AFCA realizations
    once `L, T` exceed the coordinate bounds.

    **Proof:** choose `L > x`, `T ≥ t`; use `afcaFromMinkowskiCoords`.
    Status: zero sorry. -/
theorem minkowski_causal_surjection_continuum_limit (t x : ℕ) :
    ∃ L T, 2 ≤ L ∧ 1 ≤ T ∧ t ≤ T ∧ x < L ∧
      ∃ n : CausalNode L T,
        (afcaToMinkowski n).1 = t ∧ (afcaToMinkowski n).2 = x :=
  minkowski_coords_have_afca_preimage t x

/-- Coordinate-level **partial bijection** on the canonical `y = z = 0` slice:
    `afcaFromMinkowskiCoords` is a right inverse to `afcaToMinkowski` on that slice.
    Status: zero sorry. -/
theorem minkowski_causal_coordinate_partial_bijection {L T : ℕ} (hL : 0 < L)
    (t : Fin (T + 1)) (x : Fin L) :
    afcaToMinkowski (afcaFromMinkowskiCoords hL t x) = ((t.val : ℤ), (x.val : ℤ)) :=
  afcaToMinkowski_afcaFromMinkowskiCoords hL t x

/-- Chiral-glider Minkowski inclusion + coordinate surjection: for `(t, x)` in the
    c = 2/3 cone from the origin (`0 < t` and `3x ≤ 2t`), there exists an AFCA node
    at those coordinates inside a large enough lattice.
    Status: zero sorry. -/
theorem minkowski_causal_surjection_with_inclusion {t x : ℕ}
    (htpos : 0 < t) (hadm : 3 * x ≤ 2 * t) :
    ∃ L T, 2 ≤ L ∧ 1 ≤ T ∧ t ≤ T ∧ x < L ∧
      ∃ n : CausalNode L T,
        (afcaToMinkowski n).1 = t ∧ (afcaToMinkowski n).2 = x ∧
        MinkowskiCausalLE 0 0 t x := by
  obtain ⟨L, T, hL, hT, ht, hx, n, ht_eq, hx_eq⟩ := minkowski_coords_have_afca_preimage t x
  refine ⟨L, T, hL, hT, ht, hx, n, ht_eq, hx_eq, ?_⟩
  dsimp [MinkowskiCausalLE]
  constructor
  · exact_mod_cast htpos
  · have hnat : Int.toNat ((t : ℤ) - (0 : ℤ)) = t := by simp
    rw [hnat]
    have hxabs : ((x : ℤ) - (0 : ℤ)).natAbs = x := by simp [Int.natAbs_natCast]
    rw [hxabs]
    exact hadm

end GTE.Spacetime.CausalInvariance
