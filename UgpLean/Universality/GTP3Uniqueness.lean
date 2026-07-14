import UgpLean.Universality.GoEStabilityHierarchy

/-!
# UgpLean.Universality.GTP3Uniqueness — GTP-3 Uniqueness and Count

Completes the GTP-3 classification begun in `GoEStabilityHierarchy.lean` §7.
That file certifies the *existence* direction (`sm_orbit_is_gtp3`: the SM orbit
gen₁→gen₂→gen₃→vacuum is a GoE-rooted terminating path of length 3) and the
no-GTP-4 bound (`fmdl_no_gtp4`). This file certifies the *uniqueness* direction
and the exact count:

- `sm_orbit_unique_gtp3` — a state starts a GTP-3 chain **iff** it is one of the
  five cyclic rotations of gen₁ = [1,5,2,2,1]. Exhaustive over all 7⁵ = 16,807
  states of `Fin 5 → Fin 7`.
- `sm_orbit_gtp3_count` — exactly **5** GTP-3 start states exist.

## Definition

`IsGTP3Start s` holds when the forward orbit s → f(s) → f²(s) → f³(s) = vacuum
is a GoE-rooted terminating path of length exactly 3:

1. depth exactly 3: `f³(s) = vacuum`, with `s`, `f(s)`, `f²(s)` all non-vacuum;
2. `s` is a Garden-of-Eden state (no predecessor);
3. `f(s)` has `s` as its unique predecessor;
4. `f²(s)` has `f(s)` as its unique predecessor.

This matches the GTP-n definition in `GoEStabilityHierarchy.lean` §7.

## Proof-engineering note

The naive decision procedure (predecessor scans for all 16,807 states) was
previously prohibitive. The conjunction is therefore evaluated through the
short-circuiting boolean form `isGTP3StartCheck`, ordered so that the O(1)
depth-3 conditions filter out almost every state before any O(7⁵) predecessor
scan runs. `isGTP3StartCheck_iff` proves the boolean form equivalent to the
propositional definition, so the headline theorems are stated in terms of
`IsGTP3Start` itself.

All theorems: zero sorry. Decision by `native_decide` (exhaustive, 16,807 states).
-/

namespace CUP3D

/-- The vacuum state on the 5-cell ring. -/
def ringVacuum : Fin 5 → Fin 7 := fun _ => 0

/-- `s` starts a GoE-rooted terminating path of length exactly 3
    (GTP-3) under `fmdl_step5`: depth exactly 3 to vacuum, GoE root,
    and unique predecessors along the chain. -/
def IsGTP3Start (s : Fin 5 → Fin 7) : Prop :=
  fmdl_step5 (fmdl_step5 (fmdl_step5 s)) = ringVacuum ∧
  fmdl_step5 (fmdl_step5 s) ≠ ringVacuum ∧
  fmdl_step5 s ≠ ringVacuum ∧
  s ≠ ringVacuum ∧
  (∀ t, fmdl_step5 t ≠ s) ∧
  (∀ t, fmdl_step5 t = fmdl_step5 s → t = s) ∧
  (∀ t, fmdl_step5 t = fmdl_step5 (fmdl_step5 s) → t = fmdl_step5 s)

/-- Short-circuiting boolean evaluation of `IsGTP3Start`, cheap conditions first.
    `&&` is `macro_inline`, so the expensive predecessor scans only run for
    states that already pass the depth-3 filter. -/
def isGTP3StartCheck (s : Fin 5 → Fin 7) : Bool :=
  decide (fmdl_step5 (fmdl_step5 (fmdl_step5 s)) = ringVacuum) &&
  decide (fmdl_step5 (fmdl_step5 s) ≠ ringVacuum) &&
  decide (fmdl_step5 s ≠ ringVacuum) &&
  decide (s ≠ ringVacuum) &&
  decide (∀ t, fmdl_step5 t ≠ s) &&
  decide (∀ t, fmdl_step5 t = fmdl_step5 s → t = s) &&
  decide (∀ t, fmdl_step5 t = fmdl_step5 (fmdl_step5 s) → t = fmdl_step5 s)

theorem isGTP3StartCheck_iff (s : Fin 5 → Fin 7) :
    isGTP3StartCheck s = true ↔ IsGTP3Start s := by
  simp only [isGTP3StartCheck, IsGTP3Start, Bool.and_eq_true, decide_eq_true_eq]
  tauto

instance : DecidablePred IsGTP3Start :=
  fun s => decidable_of_iff _ (isGTP3StartCheck_iff s)

/-- **sm_orbit_unique_gtp3** (CatAL): a state of the 5-cell Z₇ ring starts a
    GTP-3 chain under `fmdl_step5` **iff** it is a cyclic rotation of
    gen₁ = [1,5,2,2,1].

    Uniqueness direction of the GTP-3 classification: the SM generation orbit
    (up to the ring's Z₅ rotation symmetry) is the *only* GoE-rooted
    terminating 3-chain in the full 16,807-state space. Together with
    `fmdl_no_gtp4` (no GTP-4 exists) this pins N_gen = 3 as the maximal and
    uniquely realized GoE-rooted chain length.

    LEAN-CERTIFIED (native_decide, exhaustive over 7⁵ = 16,807 states, zero sorry). -/
theorem sm_orbit_unique_gtp3 :
    ∀ s : Fin 5 → Fin 7,
      IsGTP3Start s ↔ ∃ k : Fin 5, s = fun i => fmdl_gen1_z7 (i + k) := by
  have h : ∀ s : Fin 5 → Fin 7,
      isGTP3StartCheck s = true ↔ ∃ k : Fin 5, s = fun i => fmdl_gen1_z7 (i + k) := by
    native_decide
  intro s
  rw [← isGTP3StartCheck_iff]
  exact h s

/-- **sm_orbit_gtp3_count** (CatAL): exactly 5 GTP-3 start states exist in Z₇⁵ —
    the five cyclic rotations of gen₁.

    LEAN-CERTIFIED (native_decide, exhaustive, zero sorry). -/
theorem sm_orbit_gtp3_count :
    (Finset.univ.filter (fun s : Fin 5 → Fin 7 => IsGTP3Start s)).card = 5 := by
  native_decide

/-- The canonical SM orbit root gen₁ itself is a GTP-3 start (sanity corollary,
    connecting back to `sm_orbit_is_gtp3`). -/
theorem gen1_is_gtp3_start : IsGTP3Start fmdl_gen1_z7 := by
  rw [sm_orbit_unique_gtp3]
  exact ⟨0, by funext i; simp⟩

end CUP3D
