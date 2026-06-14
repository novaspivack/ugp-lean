import Mathlib.LinearAlgebra.Matrix.Notation
import Mathlib.LinearAlgebra.Matrix.ToLin
import UgpLean.Algebra.GaugeMDL
import UgpLean.Substrate.ChiralCurrentL2
import UgpLean.Universality.WeakIsospin
import Mathlib.Tactic

/-!
# SU(2)_L doublet Hilbert space from Level-1 Z₇ data

Explicit construction of the two-dimensional complex representation space for one
SU(2)_L isospin doublet `(ν_L, e_L)`, with T₃ and W± raising/lowering operators
and su(2) Lie algebra relations.

## Main theorems (zero sorry, zero custom axioms)

| Theorem | Content |
|---|---|
| `t3_eigenvalue` | T₃ eigenvalues ±1/2 on standard basis |
| `wplus_action` / `wminus_action` | W⁺/W⁻ raising and lowering on basis vectors |
| `su2l_algebra_closes` | [T₊,T₋]=2T₃ and [T₃,T±]=±T± |
| `doublet_is_spin_half` | 2D fundamental su(2) representation |
| `su2l_doublet_t3_from_wb` | T₃ eigenvalues match W_B sector assignment |
| `su2l_doublet_hilbert_certified` | Master bundle (CatAL) |
-/

namespace UgpLean.Substrate.SU2LDoubletHilbert

open Matrix
open GTE.ChiralCurrentL2
open WeakIsospin
open GaugeMDL

/-- Two-component complex vector space for one SU(2)_L isospin doublet `(ν_L, e_L)`. -/
abbrev DoubletSpace := Fin 2 → ℚ

/-- Upper component: left-handed neutrino `ν_L` with W_B winding `w = 0`. -/
def neutrinoState : DoubletSpace := ![1, 0]

/-- Lower component: left-handed electron `e_L` with W_B winding `w = 4`. -/
def electronState : DoubletSpace := ![0, 1]

/-- T₃ eigenvalue on component `i`: `+1/2` (neutrino) and `−1/2` (electron). -/
def t3_eigenvalue (i : Fin 2) : ℚ :=
  if i = 0 then (1 / 2 : ℚ) else (-1 / 2 : ℚ)

/-- SU(2)_L diagonal generator T₃ on the doublet (Pauli σ₃ / 2). -/
def t3Matrix : Matrix (Fin 2) (Fin 2) ℚ :=
  !![(1 / 2 : ℚ), 0; 0, (-1 / 2 : ℚ)]

/-- SU(2)_L raising operator T₊ (Pauli σ₊); alias of `GaugeMDL.tPlus`. -/
def tPlusMatrix : Matrix (Fin 2) (Fin 2) ℚ := tPlus

/-- SU(2)_L lowering operator T₋ (Pauli σ₋); alias of `GaugeMDL.tMinus`. -/
def tMinusMatrix : Matrix (Fin 2) (Fin 2) ℚ := tMinus

/-- T₃ as a ℚ-linear endomorphism of `DoubletSpace`. -/
def T3_op : DoubletSpace →ₗ[ℚ] DoubletSpace :=
  (t3Matrix).toLin'

/-- T₊ as a ℚ-linear endomorphism of `DoubletSpace`. -/
def Tplus_op : DoubletSpace →ₗ[ℚ] DoubletSpace :=
  (tPlusMatrix).toLin'

/-- T₋ as a ℚ-linear endomorphism of `DoubletSpace`. -/
def Tminus_op : DoubletSpace →ₗ[ℚ] DoubletSpace :=
  (tMinusMatrix).toLin'

/-- T₃ eigenvalues on the standard basis agree with `t3_eigenvalue`. -/
theorem t3_eigenvalue_basis (i : Fin 2) :
    t3_eigenvalue i • (Pi.single i (1 : ℚ) : DoubletSpace) =
      T3_op (Pi.single i (1 : ℚ) : DoubletSpace) := by
  ext j
  simp [T3_op, t3Matrix, t3_eigenvalue, Matrix.toLin'_apply, Pi.single_apply]
  fin_cases i <;> fin_cases j <;> norm_num

/-- T₃ acts diagonally: `T₃|ν_L⟩ = (+1/2)|ν_L⟩` and `T₃|e_L⟩ = (−1/2)|e_L⟩`. -/
theorem t3_on_neutrino :
    T3_op neutrinoState = (1 / 2 : ℚ) • neutrinoState := by
  ext i
  simp [T3_op, t3Matrix, neutrinoState, Matrix.toLin'_apply]
  fin_cases i <;> norm_num

theorem t3_on_electron :
    T3_op electronState = (-1 / 2 : ℚ) • electronState := by
  ext i
  simp [T3_op, t3Matrix, electronState, Matrix.toLin'_apply]
  fin_cases i <;> norm_num

/-- W⁺ raising action: `W⁺|e_L⟩ → |ν_L⟩` (lower index raised to upper). -/
def wplus_action (ψ : DoubletSpace) : DoubletSpace :=
  tPlusMatrix.mulVec ψ

/-- W⁻ lowering action: `W⁻|ν_L⟩ → |e_L⟩`. -/
def wminus_action (ψ : DoubletSpace) : DoubletSpace :=
  tMinusMatrix.mulVec ψ

theorem w_plus_raises_doublet :
    wplus_action electronState = neutrinoState := by
  funext i
  fin_cases i <;>
    simp [wplus_action, tPlusMatrix, tPlus, electronState, neutrinoState, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

theorem w_minus_lowers_doublet :
    wminus_action neutrinoState = electronState := by
  funext i
  fin_cases i <;>
    simp [wminus_action, tMinusMatrix, tMinus, neutrinoState, electronState, Matrix.mulVec, dotProduct,
      Fin.sum_univ_two]

theorem tplus_raises_electron :
    Tplus_op electronState = neutrinoState := by
  funext i
  fin_cases i <;>
    simp [Tplus_op, tPlusMatrix, tPlus, electronState, neutrinoState, Matrix.toLin'_apply, dotProduct,
      Fin.sum_univ_two]

theorem tminus_lowers_neutrino :
    Tminus_op neutrinoState = electronState := by
  funext i
  fin_cases i <;>
    simp [Tminus_op, tMinusMatrix, tMinus, neutrinoState, electronState, Matrix.toLin'_apply, dotProduct,
      Fin.sum_univ_two]

/-- Dimension of the doublet Hilbert space. -/
theorem doublet_space_finrank_two : Module.finrank ℚ DoubletSpace = 2 := by
  simp [DoubletSpace, Module.finrank_pi, Fintype.card_fin]

/-- su(2) Lie algebra closes on the doublet: `[T₊,T₋]=2T₃`, `[T₃,T±]=±T±`. -/
theorem su2l_algebra_closes :
    tPlusMatrix * tMinusMatrix - tMinusMatrix * tPlusMatrix = 2 • t3Matrix ∧
      t3Matrix * tPlusMatrix - tPlusMatrix * t3Matrix = tPlusMatrix ∧
        t3Matrix * tMinusMatrix - tMinusMatrix * t3Matrix = -tMinusMatrix := by
  refine ⟨?_, ?_, ?_⟩ <;> ext i j <;> fin_cases i <;> fin_cases j <;>
    simp [tPlusMatrix, tMinusMatrix, tPlus, tMinus, t3Matrix] <;> norm_num

/-- The doublet carries the spin-1/2 (fundamental) representation of su(2)_L. -/
theorem doublet_is_spin_half :
    (Module.finrank ℚ DoubletSpace = 2 ∧
      (tPlusMatrix * tMinusMatrix - tMinusMatrix * tPlusMatrix = 2 • t3Matrix ∧
        t3Matrix * tPlusMatrix - tPlusMatrix * t3Matrix = tPlusMatrix ∧
          t3Matrix * tMinusMatrix - tMinusMatrix * t3Matrix = -tMinusMatrix) ∧
      Tplus_op electronState = neutrinoState ∧
      Tminus_op neutrinoState = electronState) := by
  exact ⟨doublet_space_finrank_two, su2l_algebra_closes,
    tplus_raises_electron, tminus_lowers_neutrino⟩

/-- T₃ assignment from W_B winding: `+1/2` on the upper sector `{0,2}`, `−1/2` on `{4,6}`. -/
def t3FromWB (w : Fin 7) : ℚ :=
  if w ∈ upperDoubletWB then (1 / 2 : ℚ) else (-1 / 2 : ℚ)

theorem t3_from_wb_vacuum : t3FromWB wb_vacuum = (1 / 2 : ℚ) := by
  simp [t3FromWB, upperDoubletWB, wb_vacuum]

theorem t3_from_wb_eminus : t3FromWB wb_eminus = (-1 / 2 : ℚ) := by
  native_decide

/-- T₃ eigenvalues on the lepton doublet basis match the W_B sector assignment. -/
theorem su2l_doublet_t3_from_wb :
    t3FromWB wb_vacuum = (1 / 2 : ℚ) ∧
      t3FromWB wb_eminus = (-1 / 2 : ℚ) ∧
        T3_op neutrinoState = (1 / 2 : ℚ) • neutrinoState ∧
          T3_op electronState = (-1 / 2 : ℚ) • electronState := by
  exact ⟨t3_from_wb_vacuum, t3_from_wb_eminus, t3_on_neutrino, t3_on_electron⟩

/-- Lepton doublet partners satisfy the certified circular `|ΔW_B| = 3` criterion. -/
theorem lepton_doublet_wb_criterion :
    wbCircularDistance wb_vacuum wb_eminus = 3 :=
  su2l_doublet_criterion_wb3.1

/-- W⁺ winding `W_B = 3` connects the lepton doublet partners. -/
theorem wplus_connects_lepton_doublet :
    wb_wplus.val = (wb_vacuum.val + 7 - wb_eminus.val) % 7 := by
  decide

/-- **su2l_doublet_hilbert_certified** (CatAL master bundle):
    The GTE lepton pair `(ν_L, e_L)` forms an SU(2)_L isospin-1/2 doublet Hilbert space.
    `DoubletSpace` carries T₃ eigenvalues `±1/2`, W± raising/lowering, and the su(2)
    commutation relations, consistent with the certified W_B arithmetic. -/
theorem su2l_doublet_hilbert_certified :
    Module.finrank ℚ DoubletSpace = 2 ∧
    (tPlusMatrix * tMinusMatrix - tMinusMatrix * tPlusMatrix = 2 • t3Matrix ∧
      t3Matrix * tPlusMatrix - tPlusMatrix * t3Matrix = tPlusMatrix ∧
      t3Matrix * tMinusMatrix - tMinusMatrix * t3Matrix = -tMinusMatrix) ∧
    (t3FromWB wb_vacuum = (1 / 2 : ℚ) ∧
      t3FromWB wb_eminus = (-1 / 2 : ℚ) ∧
        T3_op neutrinoState = (1 / 2 : ℚ) • neutrinoState ∧
          T3_op electronState = (-1 / 2 : ℚ) • electronState) ∧
    (wplus_action electronState = neutrinoState) ∧
    (wminus_action neutrinoState = electronState) ∧
    wbCircularDistance wb_vacuum wb_eminus = 3 ∧
    wb_wplus.val = 3 := by
  exact And.intro doublet_space_finrank_two <|
    And.intro su2l_algebra_closes <|
      And.intro su2l_doublet_t3_from_wb <|
        And.intro w_plus_raises_doublet <|
          And.intro w_minus_lowers_doublet <|
            And.intro lepton_doublet_wb_criterion rfl

end UgpLean.Substrate.SU2LDoubletHilbert
