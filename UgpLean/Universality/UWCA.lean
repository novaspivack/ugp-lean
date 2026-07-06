import UgpLean.Universality.Rule110
import UgpLean.Universality.UWCASimulation
import UgpLean.Core.TripleDefs

/-!
# UgpLean.Universality.UWCA — Universal Windowed Cellular Automaton

UWCA: finite-local CA on survivor configurations. Uses clopen tiles and simulates
Rule 110 exactly. One synchronous sweep implements one Rule 110 step.

Reference: UPG_Orientation.tex §UWCA, UGP Main Paper Thm 3.1
-/

namespace UgpLean.Universality

/-- UWCA tile: matches local residue (L,C,R) and writes output. -/
structure UWCATile where
  neighborhood : Fin 8  -- Encodes (L,C,R)
  output : Bool
  deriving DecidableEq

/-- The five minterm tiles for Rule 110. S_110 = {1,2,3,5,6} (neighborhoods 001,010,011,101,110). -/
def rule110Tiles : List UWCATile :=
  [⟨1, true⟩, ⟨2, true⟩, ⟨3, true⟩, ⟨5, true⟩, ⟨6, true⟩]

/-- UWCA tile outputs match Rule 110: each tile's output equals rule110Output at its neighborhood. -/
theorem rule110Tiles_match_rule110 (t : UWCATile) (h : t ∈ rule110Tiles) :
    rule110Output t.neighborhood = t.output := by
  have hout : t.output = true := by
    unfold rule110Tiles at h
    simp only [List.mem_cons, List.not_mem_nil, or_false] at h
    rcases h with rfl | rfl | rfl | rfl | rfl
    all_goals rfl
  rw [hout, rule110_output_iff_minterm]
  unfold rule110Minterms
  unfold rule110Tiles at h
  simp only [List.mem_cons, List.not_mem_nil, or_false] at h
  rcases h with rfl | rfl | rfl | rfl | rfl
  all_goals simp only [Finset.mem_insert, Finset.mem_singleton]; native_decide

/-- A single UWCA sweep applies Rule 110 to each site.
 One round (P1–P4) implements exactly one Rule 110 step.
 Proved in UWCASimulation.uwca_sweep_implements_rule110. -/
def UWCA_single_sweep_correctness : Prop :=
  ∀ (L : ℕ) [NeZero L] (tape : Fin L → Bool) (i : Fin L),
    let hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    let initRow : Tape L := initTape tape
    (uwcaRound initRow i).C =
      rule110Output (neighborhoodIndex
        (tape ⟨(i.val + L - 1) % L, Nat.mod_lt _ hL⟩)
        (tape i)
        (tape ⟨(i.val + 1) % L, Nat.mod_lt _ hL⟩))

/-- UWCA simulates Rule 110 on the binary sector: one P1–P4 round = one Rule 110 step.
    Proved in `UWCASimulation.uwca_sweep_implements_rule110` and packaged in
    `UWCARegisterUniversality.uwca_simulates_rule110_binary`. -/
def UWCA_simulates_rule110_binary : Prop :=
  ∀ (L : ℕ) [NeZero L] (tape : Tape L) (h : tape.inBinarySector) (i : Fin L),
    (uwcaRound tape i).C =
      rule110Output (neighborhoodIndex
        (tape ⟨(i.val + L - 1) % L, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne L))⟩).C
        (tape i).C
        (tape ⟨(i.val + 1) % L, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne L))⟩).C)

/-- Deprecated alias kept for import stability; use `UWCA_simulates_rule110_binary`. -/
abbrev UWCA_embeds_Rule110 := UWCA_simulates_rule110_binary

end UgpLean.Universality
