import Mathlib
import UgpLean.Polynomial.DynamicalZeta

/-!
# PSL(2,7) unification certificates

Computational group-theory certificates for the golden Möbius action on `P¹(GF(7))`,
the Borel subgroup `F₂₁`, and the Fano-plane automorphism group.

All theorems: zero sorry, zero custom axioms.
-/

namespace UgpLean.Polynomial.PSL27Unification

open UgpLean.Polynomial.DynamicalZeta

private def zmodOfFin7 (x : Fin 7) : ZMod 7 := x

private def fin7OfZMod (x : ZMod 7) : Fin 7 := ⟨x.val, x.val_lt⟩

private def p1Index (p : P1GF7) : Fin 8 :=
  match p with
  | .fin x => ⟨x.val, by omega⟩
  | .inf => ⟨7, by decide⟩

private def indexToP1 (i : Fin 8) : P1GF7 :=
  if h : i.val < 7 then .fin ⟨i.val, h⟩ else .inf

private def matrixDet (M : Matrix (Fin 2) (Fin 2) (ZMod 7)) : ZMod 7 :=
  M 0 0 * M 1 1 - M 0 1 * M 1 0

private def isInvertible (M : Matrix (Fin 2) (Fin 2) (ZMod 7)) : Bool :=
  matrixDet M ≠ 0

private def isUpperTriangular (M : Matrix (Fin 2) (Fin 2) (ZMod 7)) : Bool :=
  M 1 0 = 0

private def matrixOf (a b c d : ZMod 7) : Matrix (Fin 2) (Fin 2) (ZMod 7) :=
  !![a, b; c, d]

private def mobiusAct (M : Matrix (Fin 2) (Fin 2) (ZMod 7)) : P1GF7 → P1GF7
  | .inf =>
    if M 1 0 = 0 then .inf
    else .fin (fin7OfZMod (M 0 0 / M 1 0))
  | .fin x =>
    let z := zmodOfFin7 x
    let num := M 0 0 * z + M 0 1
    let den := M 1 0 * z + M 1 1
    if h : den = 0 then .inf else .fin (fin7OfZMod (num / den))

private def permOfMatrix (M : Matrix (Fin 2) (Fin 2) (ZMod 7)) (i : Fin 8) : Fin 8 :=
  p1Index (mobiusAct M (indexToP1 i))

private def permKey (M : Matrix (Fin 2) (Fin 2) (ZMod 7)) : List Nat :=
  List.ofFn fun i : Fin 8 => (permOfMatrix M i).val

private abbrev MatEntry := ZMod 7 × ZMod 7 × ZMod 7 × ZMod 7

private def matrixOfEntry (t : MatEntry) : Matrix (Fin 2) (Fin 2) (ZMod 7) :=
  matrixOf t.1 t.2.1 t.2.2.1 t.2.2.2

private def invertibleEntries : Finset MatEntry :=
  (Finset.univ : Finset MatEntry).filter fun t => isInvertible (matrixOfEntry t)

private def pglPermKeys : Finset (List Nat) :=
  invertibleEntries.image fun t => permKey (matrixOfEntry t)

private def borelPermKeys : Finset (List Nat) :=
  invertibleEntries.filter (fun t => isUpperTriangular (matrixOfEntry t))
    |>.image fun t => permKey (matrixOfEntry t)

private def borelPslKeys : Finset (List Nat) :=
  invertibleEntries.filter (fun t =>
    isUpperTriangular (matrixOfEntry t) && matrixDet (matrixOfEntry t) = 1)
    |>.image fun t => permKey (matrixOfEntry t)

private def pslPermKeys : Finset (List Nat) :=
  invertibleEntries.filter (fun t => matrixDet (matrixOfEntry t) = 1)
    |>.image fun t => permKey (matrixOfEntry t)

private def fixesInfinity (p : List Nat) : Bool :=
  match p[7]? with
  | some 7 => true
  | _ => false

def singerMatrix : Matrix (Fin 2) (Fin 2) (ZMod 7) := !![0, 1; 1, 1]

def borelTranslationMatrix : Matrix (Fin 2) (Fin 2) (ZMod 7) := !![1, 1; 0, 1]

def borelScalingMatrix : Matrix (Fin 2) (Fin 2) (ZMod 7) := !![2, 0; 0, 1]

private def getAt (l : List Nat) (i : Nat) : Nat :=
  match l[i]? with
  | some n => n
  | none => 0

private def composePermKeys (p q : List Nat) : List Nat :=
  List.ofFn fun i : Fin 8 => getAt p (getAt q i.val)

private def permKeyId : List Nat := List.ofFn (fun i : Fin 8 => i.val)

private def generatorKeys : Finset (List Nat) :=
  {permKey singerMatrix, permKey borelTranslationMatrix, permKey borelScalingMatrix}

private def closureStep (S : Finset (List Nat)) (gens : Finset (List Nat)) : Finset (List Nat) :=
  S.biUnion fun p => gens.image fun g => composePermKeys g p

private def closureN (n : Nat) (seed gens : Finset (List Nat)) : Finset (List Nat) :=
  (List.range n).foldl (fun acc _ => closureStep acc gens) seed

private def singerBorelGeneratedKeys : Finset (List Nat) :=
  closureN 20 {permKeyId} generatorKeys

private def f2Point (i : Fin 7) : Fin 3 → Fin 2 :=
  match i.val with
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![1, 1, 0]
  | 3 => ![0, 0, 1]
  | 4 => ![1, 0, 1]
  | 5 => ![0, 1, 1]
  | _ => ![1, 1, 1]

private abbrev Mat3F2 := Matrix (Fin 3) (Fin 3) (Fin 2)

private def matrix3Det (M : Mat3F2) : Fin 2 :=
  let a := M 0 0; let b := M 0 1; let c := M 0 2
  let d := M 1 0; let e := M 1 1; let f := M 1 2
  let g := M 2 0; let h := M 2 1; let i := M 2 2
  (a * e * i + b * f * g + c * d * h + c * e * g + a * f * h + b * d * i) % 2

private def isInvertible3 (M : Mat3F2) : Bool := matrix3Det M = 1

private def mat3Of (entries : Fin 9 → Fin 2) : Mat3F2 :=
  !![entries 0, entries 1, entries 2;
      entries 3, entries 4, entries 5;
      entries 6, entries 7, entries 8]

private def applyMat3 (M : Mat3F2) (v : Fin 3 → Fin 2) : Fin 3 → Fin 2 :=
  fun i => ((M i 0 * v 0 + M i 1 * v 1 + M i 2 * v 2) : Fin 2)

private def pointIndexOf (v : Fin 3 → Fin 2) : Option (Fin 7) :=
  if v = ![0, 0, 0] then none
  else if v = ![1, 0, 0] then some 0
  else if v = ![0, 1, 0] then some 1
  else if v = ![1, 1, 0] then some 2
  else if v = ![0, 0, 1] then some 3
  else if v = ![1, 0, 1] then some 4
  else if v = ![0, 1, 1] then some 5
  else if v = ![1, 1, 1] then some 6
  else none

private def perm7OfMat3 (M : Mat3F2) (i : Fin 7) : Fin 7 :=
  match pointIndexOf (applyMat3 M (f2Point i)) with
  | some j => j
  | none => i

private def perm7KeyOfMat3 (M : Mat3F2) : List Nat :=
  List.ofFn fun i : Fin 7 => (perm7OfMat3 M i).val

private def invertibleMat3Entries : Finset (Fin 9 → Fin 2) :=
  (Finset.univ : Finset (Fin 9 → Fin 2)).filter fun e => isInvertible3 (mat3Of e)

private def psl7PermKeys : Finset (List Nat) :=
  invertibleMat3Entries.image fun e => perm7KeyOfMat3 (mat3Of e)

private def fanoLine (a b c : Fin 7) : Finset (Fin 7) := {a, b, c}

private def fanoLines : List (Finset (Fin 7)) :=
  [fanoLine 0 1 2, fanoLine 0 3 4, fanoLine 0 5 6,
   fanoLine 1 3 5, fanoLine 1 4 6, fanoLine 2 3 6, fanoLine 2 4 5]

private def preservesFanoLines (σ : Equiv.Perm (Fin 7)) : Bool :=
  fanoLines.all fun L =>
    let image := L.image σ
    fanoLines.any fun L' => decide (image = L')

private def autFanoPermKeys : Finset (List Nat) :=
  (Finset.univ : Finset (Equiv.Perm (Fin 7))).filter (fun σ => preservesFanoLines σ)
    |>.image (fun σ : Equiv.Perm (Fin 7) => List.ofFn fun i : Fin 7 => (σ i).val)

private theorem borel_psl_bundle :
    borelPslKeys.card = 21 ∧
      pslPermKeys.card = 168 ∧
        borelPermKeys.card = 42 ∧
          (∀ p ∈ borelPermKeys, fixesInfinity p) ∧
            borelPslKeys ⊆ pslPermKeys := by native_decide

private theorem pgl_generation_bundle :
    pglPermKeys.card = 336 ∧
      singerBorelGeneratedKeys.card = 336 ∧
        pglPermKeys ⊆ singerBorelGeneratedKeys ∧
          permKey singerMatrix ∈ pglPermKeys ∧
            permKey borelTranslationMatrix ∈ borelPermKeys ∧
              permKey borelScalingMatrix ∈ borelPermKeys := by native_decide

private theorem fano_aut_bundle :
    psl7PermKeys.card = 168 ∧
      autFanoPermKeys.card = 168 ∧
        psl7PermKeys = autFanoPermKeys := by native_decide

theorem mobius_singer_matches_dynamical :
    ∀ x : P1GF7, mobiusAct singerMatrix x = moebiusP1 x := by
  intro x
  fin_cases x <;> native_decide

theorem f21_is_borel_psl27 :
    borelPslKeys.card = 21 ∧
      pslPermKeys.card = 168 ∧
        borelPermKeys.card = 42 ∧
          (∀ p ∈ borelPermKeys, fixesInfinity p) ∧
            borelPslKeys ⊆ pslPermKeys := by
  exact borel_psl_bundle

theorem pgl27_generated_by_singer_and_borel :
    pglPermKeys.card = 336 ∧
      singerBorelGeneratedKeys.card = 336 ∧
        pglPermKeys ⊆ singerBorelGeneratedKeys ∧
          permKey singerMatrix ∈ pglPermKeys ∧
            permKey borelTranslationMatrix ∈ borelPermKeys ∧
              permKey borelScalingMatrix ∈ borelPermKeys ∧
                (∀ x : P1GF7, mobiusAct singerMatrix x = moebiusP1 x) := by
  rcases pgl_generation_bundle with ⟨h336, hgen, hsub, hs, ht, hb⟩
  exact ⟨h336, hgen, hsub, hs, ht, hb, mobius_singer_matches_dynamical⟩

theorem psl27_is_aut_fano :
    psl7PermKeys.card = 168 ∧
      autFanoPermKeys.card = 168 ∧
        psl7PermKeys = autFanoPermKeys ∧
          pslPermKeys.card = 168 := by
  rcases fano_aut_bundle with ⟨h168, haut, heq⟩
  exact ⟨h168, haut, heq, borel_psl_bundle.2.1⟩

end UgpLean.Polynomial.PSL27Unification
