import Mathlib.Data.Fintype.Card
import Mathlib.Data.Fin.Basic
import Mathlib.Tactic.FinCases

/-!
# UgpLean.Universality.Rule110 — Elementary CA Rule 110

Rule 110: Wolfram code 110 = 0b01101110. Truth table (L,C,R) → output:
 111→0, 110→1, 101→1, 100→0, 011→1, 010→1, 001→1, 000→0

The minterm set of ones: S_110 = {110, 101, 011, 010, 001}.

Reference: Cook (2004) "Universality in Elementary Cellular Automaton Rule 110"
UPG_Orientation.tex §Rule110
-/

namespace UgpLean.Universality

/-- A 3-bit neighborhood (Left, Center, Right) as Fin 8. -/
def Neighborhood := Fin 8

/-- Rule 110: Wolfram code 110. Output for each of 8 neighborhoods.
 Index: 7=111, 6=110, 5=101, 4=100, 3=011, 2=010, 1=001, 0=000 -/
def rule110Output (i : Fin 8) : Bool :=
  match i.val with
  | 0 => false   -- 000
  | 1 => true    -- 001
  | 2 => true    -- 010
  | 3 => true    -- 011
  | 4 => false   -- 100
  | 5 => true    -- 101
  | 6 => true    -- 110
  | _ => false   -- 111

/-- Minterm set S_110: neighborhoods that yield 1. -/
def rule110Minterms : Finset (Fin 8) := {1, 2, 3, 5, 6}

theorem rule110Minterms_card : rule110Minterms.card = 5 := by native_decide

/-- Rule 110 output is 1 iff the neighborhood index is in S_110. -/
theorem rule110_output_iff_minterm (i : Fin 8) :
    rule110Output i = true ↔ i ∈ rule110Minterms := by
  unfold rule110Output rule110Minterms
  fin_cases i <;> native_decide

/-- Cook (2004) "Universality in Elementary Cellular Automaton Rule 110":
 Rule 110 can simulate any Turing machine. We cite this as an external result.
 Full formalization of the reduction would require a separate project. -/
-- TODO: stub — external citation (Cook 2004); a full Lean formalization of the
-- Rule-110-to-Turing reduction would require a separate project
def Rule110CookUniversality : Prop := True

end UgpLean.Universality
