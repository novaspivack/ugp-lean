import Mathlib.Data.Finset.Basic
import Mathlib.Data.List.Basic
import UgpLean.Polynomial.EisensteinIdentities
import UgpLean.Spacetime.PhiMDLKinkQuantumNumbers

set_option maxRecDepth 10000

/-!
# KinkSigmaParityAction: Aut(F₂₁) rigidity of Φ_MDL kink labels

Machine certificate replaying `kink_sigma_parity_action.py`. All statements are finite
and close with `decide` / `native_decide`.

**Physical content:** The outer Spin(8) triality involution σ swaps the spinor triality
slots while fixing the vector slot. On the joint kink quantum numbers `(Q_φ, Q_χ)` this
induces a permutation of the four GTE orbit labels that is **not** realized by any
non-identity automorphism of `F₂₁ = ℤ₇ ⋊ ℤ₃`. Under the Eisenstein pinning
(gen₁ at the vector slot), σ acts on the spinor winding charges `Q_φ` as target-space
`ℤ₂` parity `φ ↦ −φ`, exchanging `Q_φ = 4` and `Q_φ = 3`.

Level framing: Level 1 algebraic certificate (finite group arithmetic on kink labels).
-/

namespace UgpLean.Algebra.KinkSigmaParityAction

open GTE.Spacetime
open GTE.Spacetime.KinkQuantumNumbers (vacuum gen1 gen2 gen3)
open UgpLean.Polynomial.EisensteinIdentities (standardF21Mul)

abbrev F21Elem := Fin 7 × Fin 3

def f21ElemEq (x y : F21Elem) : Bool :=
  x.1.val == y.1.val && x.2.val == y.2.val

def allF21Elems : List F21Elem :=
  (List.finRange 7).flatMap fun a =>
    (List.finRange 3).map fun b => (a, b)

/-- Semidirect product `F₂₁ = ℤ₇ ⋊ ℤ₃` with `(a,b)·(c,d) = (a + 2^b·c, b+d)`.
    Matches `standardF21Mul` in `EisensteinIdentities` and the Python mirror. -/
def f21Mul : F21Elem → F21Elem → F21Elem := standardF21Mul

/-- Analytic parametrization `φ_{k,a}` from the Python mirror: for units `k ∈ {1,…,6}`
    and shifts `a ∈ {0,…,6}`,
    `φ_{k,a}(m,0) = (mk, 0)`, `φ_{k,a}(m,1) = (mk+a, 1)`, `φ_{k,a}(m,2) = (mk+3a, 2)`. -/
def autF21Param (k : Fin 6) (a : Fin 7) (x : F21Elem) : F21Elem :=
  let kUnit := k.val + 1
  match x.2 with
  | ⟨0, _⟩ =>
    (⟨(kUnit * x.1.val) % 7, by omega⟩, ⟨0, by decide⟩)
  | ⟨1, _⟩ =>
    (⟨(kUnit * x.1.val + a.val) % 7, by omega⟩, ⟨1, by decide⟩)
  | ⟨2, _⟩ =>
    (⟨(kUnit * x.1.val + 3 * a.val) % 7, by omega⟩, ⟨2, by decide⟩)

def isAutF21 (f : F21Elem → F21Elem) : Bool :=
  allF21Elems.all fun x =>
    allF21Elems.all fun y =>
      f21ElemEq (f (f21Mul x y)) (f21Mul (f x) (f y))

def allAutF21Params : List (Fin 6 × Fin 7) :=
  (List.finRange 6).flatMap fun k => (List.finRange 7).map fun a => (k, a)

def autF21FromParam (p : Fin 6 × Fin 7) : F21Elem → F21Elem :=
  autF21Param p.1 p.2

def validAutF21Params : List (Fin 6 × Fin 7) :=
  allAutF21Params.filter fun p => isAutF21 (autF21FromParam p)

/-- The four GTE orbit kink labels as `(Q_φ, Q_χ) ∈ ℤ₇ × ℤ₃`. -/
def kinkLabel (k : KinkQuantumNumbers) : F21Elem :=
  (k.qPhi, k.qChi)

def kinkLabelList : List F21Elem :=
  [kinkLabel vacuum, kinkLabel gen1, kinkLabel gen2, kinkLabel gen3]

def mapsKinkLabelSet (f : F21Elem → F21Elem) : Bool :=
  kinkLabelList.all fun x => kinkLabelList.any fun y => f21ElemEq (f x) y

def isIdentityAut (p : Fin 6 × Fin 7) : Bool :=
  p.1.val == 0 && p.2.val == 0

def nonIdentityPreservingKinkLabels : List (Fin 6 × Fin 7) :=
  validAutF21Params.filter fun p =>
    !isIdentityAut p && mapsKinkLabelSet (autF21FromParam p)

def autF21PreservesZ3 (p : Fin 6 × Fin 7) : Bool :=
  allF21Elems.all fun x => x.2.val == (autF21FromParam p x).2.val

/-- Target-space `ℤ₂` parity on winding charge: `Q_φ ↦ −Q_φ` (mod 7). -/
def windingParity (q : Fin 7) : Fin 7 :=
  ⟨(7 - q.val) % 7, by omega⟩

def spinorWindingValues : List (Fin 7) :=
  [gen1.qPhi, gen2.qPhi, gen3.qPhi]

def spinorWindingParityImage : List (Fin 7) :=
  spinorWindingValues.map windingParity

/-- Under gen₁↔V the spinor-slot pair carries `Q_φ ∈ {4, 3}`; parity exchanges them. -/
def gen1VSpinorPairQPhi : List (Fin 7) :=
  [gen2.qPhi, gen3.qPhi]

/-! ## Certificate theorems -/

theorem aut_f21_param_count :
    allAutF21Params.length = 42 := by native_decide

theorem aut_f21_order_forty_two :
    validAutF21Params.length = 42 ∧
    validAutF21Params.length = allAutF21Params.length := by
  native_decide

theorem aut_f21_preserves_z3_component :
    validAutF21Params.all autF21PreservesZ3 := by
  native_decide

theorem kink_label_list_length : kinkLabelList.length = 4 := by native_decide

theorem kink_labels_match_quantum_numbers :
    kinkLabel vacuum = (⟨0, by decide⟩, ⟨0, by decide⟩) ∧
    kinkLabel gen3 = (⟨3, by decide⟩, ⟨1, by decide⟩) ∧
    kinkLabel gen1 = (⟨4, by decide⟩, ⟨1, by decide⟩) ∧
    kinkLabel gen2 = (⟨4, by decide⟩, ⟨2, by decide⟩) := by
  native_decide

theorem identity_aut_preserves_kink_labels :
    mapsKinkLabelSet (autF21FromParam (⟨0, by decide⟩, ⟨0, by decide⟩)) := by
  native_decide

theorem kink_labels_rigid_under_aut_f21 :
    nonIdentityPreservingKinkLabels.length = 0 := by
  native_decide

theorem winding_parity_on_kink_qphi :
    windingParity vacuum.qPhi = vacuum.qPhi ∧
    windingParity gen3.qPhi = gen1.qPhi ∧
    windingParity gen1.qPhi = gen3.qPhi ∧
    windingParity gen2.qPhi = gen3.qPhi := by
  native_decide

theorem winding_parity_exchanges_spinor_windings :
    windingParity gen1.qPhi = gen3.qPhi ∧
    windingParity gen3.qPhi = gen1.qPhi := by
  native_decide

theorem gen1V_spinor_pair_qphi_parity :
    gen1VSpinorPairQPhi.map windingParity = [gen3.qPhi, gen1.qPhi] := by
  native_decide

/-- **kink_sigma_parity_certificate** (CatAL): `|Aut(F₂₁)| = 42`; every automorphism
    preserves the `ℤ₃` layer; only the identity automorphism stabilizes the four GTE
    kink orbit labels; target-space winding parity exchanges the spinor windings
    `Q_φ = 4` and `Q_φ = 3`. The σ-induced kink permutation is therefore not an
    `F₂₁` automorphism action on labels; under the Eisenstein pinning, σ acts as
    `ℤ₂` target-space parity on `Q_φ`. -/
theorem kink_sigma_parity_certificate :
    validAutF21Params.length = 42 ∧
    nonIdentityPreservingKinkLabels.length = 0 ∧
    validAutF21Params.all autF21PreservesZ3 ∧
    windingParity gen1.qPhi = gen3.qPhi ∧
    windingParity gen3.qPhi = gen1.qPhi ∧
    kinkLabelList.length = 4 ∧
    mapsKinkLabelSet (autF21FromParam (⟨0, by decide⟩, ⟨0, by decide⟩)) ∧
    gen1VSpinorPairQPhi.map windingParity = [gen3.qPhi, gen1.qPhi] := by
  refine ⟨aut_f21_order_forty_two.1, ?_⟩
  refine ⟨kink_labels_rigid_under_aut_f21, ?_⟩
  refine ⟨aut_f21_preserves_z3_component, ?_⟩
  exact ⟨winding_parity_exchanges_spinor_windings.1,
    ⟨winding_parity_exchanges_spinor_windings.2,
      ⟨kink_label_list_length,
        ⟨identity_aut_preserves_kink_labels, gen1V_spinor_pair_qphi_parity⟩⟩⟩⟩

end UgpLean.Algebra.KinkSigmaParityAction
