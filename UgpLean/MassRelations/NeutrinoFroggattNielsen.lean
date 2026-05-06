import Mathlib

/-!
# UgpLean.MassRelations.NeutrinoFroggattNielsen

Froggatt-Nielsen texture formalisation for the neutrino seesaw exponent 29/9.

## Setup

In the standard two-flavon U(1)_1 x U(1)_2 framework (compatible with the
existing charged-lepton lepton-sector setup in `MassRelations.FroggattNielsen`),
the right-handed neutrino with FN charges (q1, q2) acquires a Majorana mass
that scales with the Braid Atlas b-value as

    M_R(g)  ~  b_g^{q1 + q2 / N_c^2}.

The Braid Atlas seesaw power law m_nu ~ b^{29/9} requires

    q1 + q2 / N_c^2 = 29/9.                              (*)

## Solutions and selection

At N_c = 3, equation (*) admits exactly four non-negative integer solutions
in the FN-natural range (0 <= q1 <= 6, 0 <= q2 <= 30):

    (q1, q2) in {(0, 29), (1, 20), (2, 11), (3, 2)}.

Each charge has a structural reading:
- (0, 29):  q2 = 29 = 4 N_c^2 - delta  (compound: 2 atoms + delta)
- (1, 20):  q2 = 20 = 2(N_c^2 + 1)    (compound: 2 atoms)
- (2, 11):  q2 = 11 = N_c^2 + strand  (compound: 2 atoms; or = b(nu_muR) cascade)
- (3, 2):   q1 = N_c, q2 = strand     (BOTH single-atom UGP primitives)

## MDL selection criterion

UGP axiom A3 (Compression / MDL) selects the texture whose charges have the
shortest description in UGP-atomic primitives.  We define a charge as
"singleton-atomic" if it equals one of the elementary UGP-N_c primitives:
  N_c,   N_c^2,   N_c - 1,   N_c + 1,   strand_count = (N_c^2 - 1) / 4,
  delta = N_c + (N_c^2 - 1) / 2.
A pair (q1, q2) is "singleton-atomic" if BOTH charges are singleton-atomic.

Theorem (`fn_texture_3_2_is_unique_singleton_atomic`):
the unique singleton-atomic FN solution at N_c = 3 is (q1, q2) = (3, 2),
i.e.\ (q1, q2) = (N_c, strand).  This selects the structural texture from
the four arithmetic solutions on first-principles MDL grounds.

## Companion paper

P22 §4.4 of `papers/22_neutrino_masses/neutrino_masses_from_braid_atlas.tex`.
P25 §9.5 (charge derivation) supplies the upstream `Q = W_g/N_c` and
`y_ql_unifies_vv_and_winding` results that connect the same N_c-atomic
quantities to the SM hypercharge spectrum.

Zero `sorry`. 110th module.
-/

namespace UgpLean.MassRelations.NeutrinoFroggattNielsen

open Nat

/-- FN charge equation: q1 + q2 / N_c^2 = 29/9 (Braid Atlas seesaw exponent),
    rewritten with integer arithmetic as 9 q1 + q2 = 29 at N_c = 3 (since
    9 q2 / 9 = q2 and 9 (q1) = 9 q1 require multiplying both sides by 9). -/
def fnEqAtNc3 (q1 q2 : ℕ) : Prop :=
  9 * q1 + q2 = 29

/-- The four non-negative integer solutions of (*) at N_c = 3, q1 in [0,6]. -/
def fnSolutionsAtNc3 : Finset (ℕ × ℕ) :=
  ({(0, 29), (1, 20), (2, 11), (3, 2)} : Finset (ℕ × ℕ))

/-- Each pair in `fnSolutionsAtNc3` satisfies the FN charge equation. -/
theorem fn_solutions_satisfy_eq :
    ∀ p ∈ fnSolutionsAtNc3, fnEqAtNc3 p.1 p.2 := by
  intro p hp
  unfold fnSolutionsAtNc3 fnEqAtNc3 at *
  fin_cases hp <;> rfl

/-- Conversely, every (q1, q2) with q1 ≤ 6 satisfying the equation is in the list. -/
theorem fn_solutions_are_complete :
    ∀ q1 q2 : ℕ, q1 ≤ 6 → q2 ≤ 30 → fnEqAtNc3 q1 q2 →
      (q1, q2) ∈ fnSolutionsAtNc3 := by
  intros q1 q2 h1 h2 heq
  unfold fnEqAtNc3 at heq
  unfold fnSolutionsAtNc3
  -- 9 q1 + q2 = 29 with 0 ≤ q1 ≤ 6 forces q1 ∈ {0,1,2,3} and the matching q2
  interval_cases q1
  · -- q1=0: q2=29
    have : q2 = 29 := by omega
    subst this; decide
  · -- q1=1: q2=20
    have : q2 = 20 := by omega
    subst this; decide
  · -- q1=2: q2=11
    have : q2 = 11 := by omega
    subst this; decide
  · -- q1=3: q2=2
    have : q2 = 2 := by omega
    subst this; decide
  · -- q1=4: q2 = -7, impossible
    omega
  · -- q1=5: impossible
    omega
  · -- q1=6: impossible
    omega

-- ─────────────────────────────────────────────────────────────────────
-- §  MDL selection: singleton-atomicity
-- ─────────────────────────────────────────────────────────────────────

/-- A charge is "singleton-atomic" in N_c if it equals one of the elementary
    UGP-N_c primitives.  At N_c = 3 the singleton-atomic values are:

      N_c           = 3
      strand        = (N_c^2 - 1) / 4 = 2
      N_c - 1       = 2  (same value as strand at N_c=3, so collapse)
      N_c + 1       = 4
      N_c^2         = 9
      N_c^2 - 1     = 8

    Note: delta = N_c + (N_c^2-1)/2 = 7 is NOT a singleton-atomic primitive --
    delta is itself a compound (two-atom) function of N_c.  Including it would
    expand the singleton set; we exclude it because the MDL discipline counts
    delta as a derived constant. -/
def isSingletonAtomicAtNc3 (q : ℕ) : Prop :=
  q = 2 ∨ q = 3 ∨ q = 4 ∨ q = 8 ∨ q = 9

instance (q : ℕ) : Decidable (isSingletonAtomicAtNc3 q) := by
  unfold isSingletonAtomicAtNc3; exact inferInstance

/-- The pair (q1, q2) is singleton-atomic iff both components are. -/
def isSingletonAtomicPair (p : ℕ × ℕ) : Prop :=
  isSingletonAtomicAtNc3 p.1 ∧ isSingletonAtomicAtNc3 p.2

instance (p : ℕ × ℕ) : Decidable (isSingletonAtomicPair p) := by
  unfold isSingletonAtomicPair; exact inferInstance

-- ─────────────────────────────────────────────────────────────────────
-- §  Selection theorem: (3, 2) is the unique singleton-atomic solution
-- ─────────────────────────────────────────────────────────────────────

/-- (3, 2) is in the solution set. -/
theorem texture_3_2_is_solution : ((3, 2) : ℕ × ℕ) ∈ fnSolutionsAtNc3 := by
  unfold fnSolutionsAtNc3; decide

/-- (3, 2) is singleton-atomic: q1 = 3 = N_c, q2 = 2 = strand. -/
theorem texture_3_2_is_singleton_atomic :
    isSingletonAtomicPair (3, 2) := by
  unfold isSingletonAtomicPair isSingletonAtomicAtNc3
  refine ⟨?_, ?_⟩ <;> decide

/-- (0, 29) is NOT singleton-atomic (q2 = 29 is compound). -/
theorem texture_0_29_not_singleton_atomic :
    ¬ isSingletonAtomicPair (0, 29) := by
  unfold isSingletonAtomicPair isSingletonAtomicAtNc3
  decide

/-- (1, 20) is NOT singleton-atomic (q2 = 20 is compound). -/
theorem texture_1_20_not_singleton_atomic :
    ¬ isSingletonAtomicPair (1, 20) := by
  unfold isSingletonAtomicPair isSingletonAtomicAtNc3
  decide

/-- (2, 11) is NOT singleton-atomic (q2 = 11 is compound: N_c^2 + strand,
    or alternatively the cascade-derived b-value b(nu_muR)). -/
theorem texture_2_11_not_singleton_atomic :
    ¬ isSingletonAtomicPair (2, 11) := by
  unfold isSingletonAtomicPair isSingletonAtomicAtNc3
  decide

/-- **Main theorem (FN texture uniqueness under MDL).**
    Among the four FN-charge solutions of q1 + q2/N_c^2 = 29/9 at N_c = 3,
    the unique singleton-atomic texture is (q1, q2) = (N_c, strand) = (3, 2).

    Equivalently: every FN solution that gives both charges as elementary
    UGP-N_c primitives is the (N_c, strand) texture.  The alternatives
    (0, 29), (1, 20), (2, 11) all require compound (multi-atom) expressions
    for at least one charge, hence have higher MDL cost.

    Proof: each solution is enumerated; non-(3,2) cases fail
    `isSingletonAtomicPair` by `decide`; (3,2) satisfies it. -/
theorem fn_texture_3_2_is_unique_singleton_atomic :
    ∀ p ∈ fnSolutionsAtNc3, isSingletonAtomicPair p ↔ p = (3, 2) := by
  intro p hp
  unfold fnSolutionsAtNc3 at hp
  fin_cases hp
  · -- p = (0, 29)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact absurd h texture_0_29_not_singleton_atomic
    · exact absurd h (by decide : ((0, 29) : ℕ × ℕ) ≠ (3, 2))
  · -- p = (1, 20)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact absurd h texture_1_20_not_singleton_atomic
    · exact absurd h (by decide : ((1, 20) : ℕ × ℕ) ≠ (3, 2))
  · -- p = (2, 11)
    refine ⟨fun h => ?_, fun h => ?_⟩
    · exact absurd h texture_2_11_not_singleton_atomic
    · exact absurd h (by decide : ((2, 11) : ℕ × ℕ) ≠ (3, 2))
  · -- p = (3, 2)
    refine ⟨fun _ => rfl, fun _ => texture_3_2_is_singleton_atomic⟩

/-- Bundled headline: the structural FN texture for b^(29/9) is unique.

    Exists-form: there exists a singleton-atomic solution, and it equals (3, 2). -/
theorem fn_structural_texture_existence_and_uniqueness :
    ∃! p : ℕ × ℕ, p ∈ fnSolutionsAtNc3 ∧ isSingletonAtomicPair p := by
  refine ⟨(3, 2), ⟨texture_3_2_is_solution, texture_3_2_is_singleton_atomic⟩, ?_⟩
  rintro ⟨a, b⟩ ⟨hmem, hatom⟩
  have h := (fn_texture_3_2_is_unique_singleton_atomic _ hmem).mp hatom
  exact h

-- ─────────────────────────────────────────────────────────────────────
-- §  Connection to existing UGP atoms
-- ─────────────────────────────────────────────────────────────────────

/-- The structural texture charges are explicit UGP atoms:
    q1 = N_c (colour rank); q2 = strand_count = (N_c^2 - 1)/4 (Braid Atlas
    invariant, also the numerator of theta_Koide). -/
theorem texture_charges_are_Nc_atoms :
    (3 : ℕ) = 3 ∧ (2 : ℕ) = (3 * 3 - 1) / 4 := by
  refine ⟨rfl, ?_⟩; decide

/-- The texture exponent equals 29/9 = N_c + theta_Koide where
    theta_Koide = strand / N_c^2 = 2/9. -/
theorem texture_reproduces_Nc_plus_theta :
    9 * 3 + 2 = 29 := by decide

end UgpLean.MassRelations.NeutrinoFroggattNielsen
