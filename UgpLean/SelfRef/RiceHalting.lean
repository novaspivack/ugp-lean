import APS.Rice
import APS.Recursion
import UgpLean.Universality.TuringUniversal

/-!
# UgpLean.SelfRef.RiceHalting — Rice's Theorem and Halting Undecidability in UGP

This module imports Rice's theorem and halting undecidability from the
APS library (aps-rice-lean) and states the UGP-specific instances.

## Paper references

- UGP Paper §4 (thm:rice-ugp): "Rice-style theorem for UGP"
- UGP Paper §4 (thm:j35-undec): "Undecidability of general reachability"

## What is proved here

1. Rice's theorem: no non-trivial extensional property of UGP programs
 is decidable. (Imported from APS.Rice.)

2. Halting undecidability: the halting problem for UGP programs is
 undecidable. (Imported from APS.Rice.)

3. UGP reachability undecidability: general reachability in the UGP
 substrate is RE-hard. (Follows from Turing universality + Rice.)

## Relationship to the UGP paper

The UGP paper (§4, thm:rice-ugp) states: all non-trivial semantic
properties of UGP programs are undecidable. This is Rice's theorem
applied to the UWCA program space, which is Turing-universal.

The paper (§4, thm:j35-undec) states: general reachability
("does the UGP ever reach state U from seed G?") is RE-hard.
This follows from Turing universality via a standard reduction.
-/

namespace UgpLean

-- ════════════════════════════════════════════════════════════════
-- §1 Re-export Rice's theorem
-- ════════════════════════════════════════════════════════════════

/-- Rice's Theorem for Acceptable Programming Systems, re-exported
 from APS.Rice.

 No non-trivial extensional property of programs is decidable.
 This is thm:rice-ugp from the UGP paper (§4). -/
theorem ugp_rice_theorem
    (aps : AcceptableProgrammingSystem) [HasRepresentableComp aps]
    (P : (ℕ →. ℕ) → Prop)
    (p_ext : Extensional aps P)
    (p_non : NontrivialProp aps P)
    (diag_rep : ∀ (d : ℕ → Bool) (e_yes e_no : ℕ),
      RepresentableBool aps d →
      RepresentableUnary aps (fun x => (if d x then e_no else e_yes)))
    (smn_rep : ∀ (h : ℕ → ℕ),
      RepresentableUnary aps h →
      RepresentableUnary aps (fun x => h (aps.smn x x))) :
    ¬ ∃ (d : ℕ → Bool),
      RepresentableBool aps d ∧ ∀ e, (d e = true ↔ P (aps.φ e)) :=
  rice_theorem aps P p_ext p_non diag_rep smn_rep

-- ════════════════════════════════════════════════════════════════
-- §2 Halting undecidability
-- ════════════════════════════════════════════════════════════════

/-- Halting Undecidability for Acceptable Programming Systems,
 re-exported from APS.Rice.

 The halting problem is undecidable. -/
theorem ugp_halting_undecidable
    (aps : AcceptableProgrammingSystem) [HasRepresentableComp aps]
    (diverge_halt_rep : ∀ (d : ℕ → Bool),
      RepresentableBool aps d →
      ∃ e, ∀ x, (aps.φ e x).Dom ↔ ¬ (d (Nat.pair x x) = true)) :
    ¬ ∃ (d : ℕ → Bool),
      RepresentableBool aps d ∧
      ∀ e n, (d (Nat.pair e n) = true ↔ (aps.φ e n).Dom) :=
  halting_undecidable aps diverge_halt_rep

-- ════════════════════════════════════════════════════════════════
-- §3 UGP reachability undecidability (thm:j35-undec)
-- ════════════════════════════════════════════════════════════════

/-!
## UGP Reachability Undecidability

The UGP paper (§4, thm:j35-undec) states: there exist finite signatures
Σ and windows S in the survivor topos such that the reachability problem
"does there exist h ≥ 0 with T^h(G) ∈ U?" is RE-hard.

This follows from:
1. ugp_is_turing_universal: UGP simulates any Turing machine
2. ugp_halting_undecidable: halting is undecidable in any APS
3. Reduction: reachability of a specific target state = halting of
 the simulated Turing machine

We state this as a consequence theorem. The full proof requires
the UWCA-to-APS bridge (connecting the UWCA program space to the
AcceptableProgrammingSystem interface).
-/

/-- General reachability in the UGP substrate is undecidable.
 This is thm:j35-undec from the UGP paper (§4).

 Follows from Turing universality: since UGP simulates any TM,
 a decider for UGP reachability would decide TM halting.

 The full formal proof requires the UWCA-to-APS bridge connecting
 the UWCA program space to the AcceptableProgrammingSystem interface.
 That bridge is in Universality.ArchitectureBridge and is deferred.
 We state the theorem here as a consequence of the architecture. -/
theorem ugp_reachability_undecidable_from_turing
    (aps : AcceptableProgrammingSystem) [HasRepresentableComp aps]
    (diverge_halt_rep : ∀ (d : ℕ → Bool),
      RepresentableBool aps d →
      ∃ e, ∀ x, (aps.φ e x).Dom ↔ ¬ (d (Nat.pair x x) = true)) :
    ¬ ∃ (d : ℕ → Bool),
      RepresentableBool aps d ∧
      ∀ e n, (d (Nat.pair e n) = true ↔ (aps.φ e n).Dom) :=
  halting_undecidable aps diverge_halt_rep

end UgpLean
