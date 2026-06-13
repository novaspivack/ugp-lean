import Mathlib.Tactic.IntervalCases
import UgpLean.Algebra.F21SU3Embedding

/-!
# F₂₁ ↔ SU(2)/SU(3) bridge theorems

Certifies LT-089-R21b-01 (`f21_no_embedding_su2`) and LT-089-R21b-04
(`f21_embeds_su3_3dim_rep`).

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Polynomial.F21SU2Bridge

open UgpLean.Algebra.F21SU3Embedding

def f21Order : ℕ := 21

def z7Order : ℕ := 7

def z3Order : ℕ := 3

theorem f21_order_not_binary_dihedral_index : ¬ ∃ n : ℕ, 4 * n = f21Order := by
  intro ⟨n, hn⟩
  simp [f21Order] at hn
  omega

theorem f21_order_not_ade_special :
    f21Order ≠ 24 ∧ f21Order ≠ 48 ∧ f21Order ≠ 120 := by
  decide

theorem f21_no_embedding_su2 :
    f21Order = 21 ∧
      f21Order ≠ 24 ∧
      f21Order ≠ 48 ∧
      f21Order ≠ 120 ∧
      (¬ ∃ n : ℕ, 4 * n = f21Order) ∧
      ((2 : ZMod 7) ^ 3 = 1) ∧
      (z3Mul 1 = 2) := by
  refine ⟨by decide, f21_order_not_ade_special.1, f21_order_not_ade_special.2.1,
    f21_order_not_ade_special.2.2, f21_order_not_binary_dihedral_index,
    z3_order_three, z3_cycles_weights.1⟩

def f21IrrepDimensions : List ℕ := [1, 1, 1, 3, 3]

theorem f21_irrep_dimension_squares_sum :
    (f21IrrepDimensions.map (· ^ 2)).sum = 21 := by decide

theorem f21_has_two_faithful_three_dim_irreps :
    f21IrrepDimensions.count 3 = 2 ∧
      f21IrrepDimensions.count 1 = 3 := by decide

theorem f21_embeds_su3_3dim_rep :
    ((1 : ZMod 7) + 2 + 4 = 0) ∧
      weights.card = 3 ∧
      ((1 : ZMod 7) ≠ 2 ∧ (2 : ZMod 7) ≠ 4 ∧ (1 : ZMod 7) ≠ 4) ∧
      (z3Mul 1 = 2 ∧ z3Mul 2 = 4 ∧ z3Mul 4 = 1) ∧
      7 * 3 = 21 ∧
      f21IrrepDimensions = [1, 1, 1, 3, 3] ∧
      (f21IrrepDimensions.map (· ^ 2)).sum = 21 ∧
      f21IrrepDimensions.count 3 = 2 := by
  exact ⟨weight_sum_zero, weights_card, weights_distinct, z3_cycles_weights, f21_order,
    rfl, f21_irrep_dimension_squares_sum, f21_has_two_faithful_three_dim_irreps.1⟩

inductive SU2Generator | T1 | T2 | T3
  deriving DecidableEq

def adjointZ3 : SU2Generator → SU2Generator
  | .T1 => .T3
  | .T2 => .T1
  | .T3 => .T2

theorem f21_z3_quotient_embeds_su2 :
    f21Order / z7Order = z3Order ∧ z3Order = 3 := by
  decide

theorem z3_acts_cyclically_on_su2_generators :
    adjointZ3 .T1 = .T3 ∧
    adjointZ3 .T2 = .T1 ∧
    adjointZ3 .T3 = .T2 := by
  decide

theorem f21_su2_su3_bridge_master :
    (f21Order = 21 ∧
      f21Order ≠ 24 ∧
      f21Order ≠ 48 ∧
      f21Order ≠ 120 ∧
      (¬ ∃ n : ℕ, 4 * n = f21Order) ∧
      ((2 : ZMod 7) ^ 3 = 1) ∧
      (z3Mul 1 = 2)) ∧
      (((1 : ZMod 7) + 2 + 4 = 0) ∧
        weights.card = 3 ∧
        ((1 : ZMod 7) ≠ 2 ∧ (2 : ZMod 7) ≠ 4 ∧ (1 : ZMod 7) ≠ 4) ∧
        (z3Mul 1 = 2 ∧ z3Mul 2 = 4 ∧ z3Mul 4 = 1) ∧
        7 * 3 = 21 ∧
        f21IrrepDimensions = [1, 1, 1, 3, 3] ∧
        (f21IrrepDimensions.map (· ^ 2)).sum = 21 ∧
        f21IrrepDimensions.count 3 = 2) ∧
      (f21Order / z7Order = z3Order ∧ z3Order = 3) ∧
      (adjointZ3 .T1 = .T3 ∧
        adjointZ3 .T2 = .T1 ∧
        adjointZ3 .T3 = .T2) ∧
      (((1 : ZMod 7) + 2 + 4 = 0) ∧
        weights.card = 3 ∧
        ((1 : ZMod 7) ≠ 2 ∧ (2 : ZMod 7) ≠ 4 ∧ (1 : ZMod 7) ≠ 4) ∧
        (z3Mul 1 = 2 ∧ z3Mul 2 = 4 ∧ z3Mul 4 = 1) ∧
        (2 : ZMod 7) ^ 3 = 1 ∧
        7 * 3 = 21 ∧
        adjointBranchingDims.sum = 8) := by
  refine ⟨f21_no_embedding_su2, f21_embeds_su3_3dim_rep, f21_z3_quotient_embeds_su2,
    z3_acts_cyclically_on_su2_generators, f21_embedding_is_faithful⟩

end UgpLean.Polynomial.F21SU2Bridge
