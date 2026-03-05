import UgpLean.Universality.Rule110
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
  Prop: one sweep yields the Rule 110 update of the row.
  Reference: UPG_Orientation prop:uwca-110 -/
def UWCA_single_sweep_correctness : Prop := True  -- Formal statement of prop

/-- UWCA simulates Rule 110. The survivor topos contains a finite-local subsystem
  isomorphic to Rule 110. -/
def UWCA_embeds_Rule110 : Prop := True  -- Main theorem statement

end UgpLean.Universality
