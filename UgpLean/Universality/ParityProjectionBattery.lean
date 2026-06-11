import Mathlib
import UgpLean.Universality.TriangleLiftTheorem

set_option maxHeartbeats 800000

/-!
# Parity-projection battery kernels (additive + mod-2 recoding)

Finite enumeration kernels mirroring the R33 Python oracles.  Split into modulus
and coordinate chunks for incremental `native_decide` builds.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Universality.ParityProjectionBattery

open UgpLean.Universality.TriangleLiftTheorem

private def monomialExpsLocal : Array (ℕ × ℕ × ℕ) :=
  #[(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1),
    (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 1)]

private def conjExponent (deg : ℕ) : ℕ :=
  let e := ((1 : Int) - (deg : Int)) % 6
  ((e % 6 + 6) % 6).toNat

private def unitConjugateCoeffs (t : ℕ) : Array (ZMod 7) :=
  Array.ofFn fun (k : Fin 8) =>
    let (eL, eC, eR) := monomialExpsLocal[k]!
    let deg := eL + eC + eR
    (t : ZMod 7) ^ conjExponent deg * polyPCoeffs[k]!

private def monomialRow (L C R : ℕ) : Array (ZMod 7) :=
  Array.ofFn fun (k : Fin 8) =>
    let (eL, eC, eR) := monomialExpsLocal[k]!
    (L : ZMod 7) ^ eL * (C : ZMod 7) ^ eC * (R : ZMod 7) ^ eR

private def augGet (m : Array (Array (ZMod 7))) (r c : ℕ) : ZMod 7 :=
  (m.getD r #[]).getD c 0

private def augSetRow (m : Array (Array (ZMod 7))) (r : ℕ) (row : Array (ZMod 7)) :
    Array (Array (ZMod 7)) :=
  if h : r < m.size then m.set r row else m.push row

private def gf7Solve (rows : Array (Array (ZMod 7) × ZMod 7)) :
    ℕ × Option (Array (ZMod 7)) :=
  let init :=
    rows.map fun ⟨row, b⟩ =>
      (List.range 9).foldl
        (fun acc k =>
          if k < 8 then acc.push row[k]! else acc.push b)
        (Array.mkEmpty 9)
  let rec elim (m : Array (Array (ZMod 7))) (rank col : ℕ) (pivots : Array ℕ) :
      Array (Array (ZMod 7)) × ℕ × Array ℕ :=
    if col ≥ 8 then (m, rank, pivots)
    else
      let piv? :=
        (List.range (m.size - rank)).find? fun k =>
          augGet m (rank + k) col ≠ 0
      match piv? with
      | none => elim m rank (col + 1) pivots
      | some k =>
        let piv := rank + k
        let mSwapped :=
          let rowRank := m.getD rank #[]
          let rowPiv := m.getD piv #[]
          augSetRow (augSetRow m piv rowRank) rank rowPiv
        let inv := (augGet mSwapped rank col)⁻¹
        let scaled :=
          Array.ofFn fun (j : Fin 9) => inv * augGet mSwapped rank j.val
        let mScaled := augSetRow mSwapped rank scaled
        let reduced :=
          (List.range mScaled.size).foldl
            (fun acc r =>
              if r = rank then acc
              else
                let f := augGet acc r col
                if f = 0 then acc
                else
                  augSetRow acc r
                    (Array.ofFn fun (j : Fin 9) =>
                      augGet acc r j.val - f * augGet acc rank j.val))
            mScaled
        elim reduced (rank + 1) (col + 1) (pivots.push col)
  let ⟨m', rank, pivots⟩ := elim init 0 0 #[]
  let bad :=
    (List.range m'.size).any fun r =>
      r ≥ rank && augGet m' r 8 ≠ 0
  if bad then (1, none)
  else if rank < 8 then (2, none)
  else
    let sol :=
      (List.range pivots.size).foldl
        (fun acc r => acc.set! (pivots[r]!) (augGet m' r 8))
        (Array.ofFn fun (_ : Fin 8) => (0 : ZMod 7))
    (3, some sol)

private def insertPoint (acc : Array (ℕ × ℕ × ℕ × ℕ)) (L C R out : ℕ) :
    Option (Array (ℕ × ℕ × ℕ × ℕ)) :=
  if acc.any fun ⟨l, c, r, o⟩ => l = L ∧ c = C ∧ r = R ∧ o ≠ out then none
  else if acc.any fun ⟨l, c, r, o⟩ => l = L ∧ c = C ∧ r = R ∧ o = out then some acc
  else some (acc.push (L, C, R, out))

private def buildPointMap (v0 v1 v2 : Array ℕ) : Option (Array (ℕ × ℕ × ℕ × ℕ)) :=
  let rec ringStep (src dst : Array ℕ) (acc : Array (ℕ × ℕ × ℕ × ℕ)) (i : ℕ) :
      Option (Array (ℕ × ℕ × ℕ × ℕ)) :=
    if i ≥ 5 then some acc
    else
      match insertPoint acc (src[(i + 4) % 5]!) (src[i]!) (src[(i + 1) % 5]!) (dst[i]!) with
      | none => none
      | some acc' => ringStep src dst acc' (i + 1)
  match ringStep v0 v1 (#[]) 0 with
  | none => none
  | some acc1 => ringStep v1 v2 acc1 0

private def sortPointMap (pm : Array (ℕ × ℕ × ℕ × ℕ)) : Array (ℕ × ℕ × ℕ × ℕ) :=
  pm.toList.mergeSort
      (fun a b =>
        let ⟨l1, c1, r1, _⟩ := a
        let ⟨l2, c2, r2, _⟩ := b
        decide (l1 < l2 ∨ (l1 = l2 ∧ (c1 < c2 ∨ (c1 = c2 ∧ r1 < r2)))))
    |>.toArray

private def pointMapToRows (pm : Array (ℕ × ℕ × ℕ × ℕ)) : Array (Array (ZMod 7) × ZMod 7) :=
  pm.map fun ⟨L, C, R, out⟩ => (monomialRow L C R, (out : ZMod 7))

private def classifyVectors (v0 v1 v2 : Array ℕ) : ℕ × Option (Array (ZMod 7)) :=
  match buildPointMap v0 v1 v2 with
  | none => (0, none)
  | some pm =>
    match pm.find? fun ⟨l, c, r, _⟩ => l = 0 ∧ c = 0 ∧ r = 0 with
    | some ⟨_, _, _, o⟩ =>
      if o ≠ 0 then (0, none) else gf7Solve (pointMapToRows (sortPointMap pm))
    | none => gf7Solve (pointMapToRows (sortPointMap (pm.push (0, 0, 0, 0))))

/-- Canonical cascade triples in generation-major order: `ORDER = [e,u,d,νR,νL]`. -/
private def tripleTable : Array (ℕ × ℕ × ℤ) :=
  #[(1, 73, 823), (5, 9, 275), (9, 5, 42), (2, 5, 5), (1, 1, 823),
    (9, 42, 1023), (5, 275, 65535), (9, 186, 1023), (7, 11, 13), (9, 1, 1023),
    (5, 275, 65535), (76, 337920, -1), (5, 8191, 65535), (17, 19, 23), (5, 1, 65535)]

private def tripleComponents (pos : Fin 15) : ℕ × ℕ × ℤ :=
  tripleTable[pos]!

private def reduceValue (α β γ m : ℕ) (a b : ℕ) (c : ℤ) : ℕ :=
  let z := (α : ℤ) * (a : ℤ) + (β : ℤ) * (b : ℤ) + (γ : ℤ) * c
  ((z % (m : ℤ) + (m : ℤ)) % (m : ℤ)).toNat

private def reducedVectors (α β γ m : ℕ) : Array (Array ℕ) :=
  Array.ofFn fun (g : Fin 3) =>
    Array.ofFn fun (i : Fin 5) =>
      let pos : Fin 15 := ⟨g.val * 5 + i.val, by omega⟩
      let ⟨a, b, c⟩ := tripleComponents pos
      reduceValue α β γ m a b c

private def homImage (α β γ m : ℕ) : Array ℕ :=
  let d1 := Nat.gcd (Nat.gcd α β) (Nat.gcd γ m)
  let d := if d1 = 0 then m else Nat.gcd d1 m
  let step := if d = 0 then 1 else d
  ((List.range m).filterMap fun x => if x % step = 0 then some x else none).toArray

private def evalRule (coeffs : Array (ZMod 7)) (L C R : ℕ) : ZMod 7 :=
  evalMultilinear coeffs L C R

private def valueInImage (val : ZMod 7) (image : Array ℕ) : Bool :=
  image.any fun v => decide (val = (v : ZMod 7))

private def shadowClosed (coeffs : Array (ZMod 7)) (image : Array ℕ) : Bool :=
  image.all fun x =>
    image.all fun y =>
      image.all fun z =>
        valueInImage (evalRule coeffs x y z) image

private def coeffsEqual (a b : Array (ZMod 7)) : Bool :=
  (List.range 8).all fun i => decide (a[i]! = b[i]!)

private def classifyForm (α β γ m : ℕ) : ℕ × Bool × Bool :=
  let vecs := reducedVectors α β γ m
  let ⟨st, sol⟩ := classifyVectors vecs[0]! vecs[1]! vecs[2]!
  match sol with
  | none => (st, false, false)
  | some coeffs =>
    let img := homImage α β γ m
    let scc := shadowClosed coeffs img
    let conjMatch :=
      (List.range 7).any fun t =>
        decide (t > 0 && coeffsEqual coeffs (unitConjugateCoeffs t))
    (st, scc, conjMatch)

private def bumpFormCount (acc : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (α β γ m : ℕ) :
    ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  if α = 0 ∧ β = 0 ∧ γ = 0 then acc
  else
    let ⟨st, sc, cm⟩ := classifyForm α β γ m
    let ⟨c, nm, u, f, scc, conj⟩ := acc
    (c + if st = 0 then 1 else 0,
     nm + if st = 1 then 1 else 0,
     u + if st = 2 then 1 else 0,
     f + if st = 3 then 1 else 0,
     scc + if st = 3 ∧ sc then 1 else 0,
     conj + if st = 3 ∧ sc ∧ cm then 1 else 0)

private def foldFormsAtM (m : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (List.range m).foldl
    (fun acc α =>
      (List.range m).foldl
        (fun acc' β =>
          (List.range m).foldl
            (fun acc'' γ => bumpFormCount acc'' α β γ m)
            acc')
        acc)
    (0, 0, 0, 0, 0, 0)

private def mod2PositionIndex : Array ℕ :=
  #[4, 4, 3, 1, 4, 2, 4, 2, 4, 4, 4, 0, 4, 4, 4]

private def mod2ParityGen (g : Fin 3) (i : Fin 5) : ℕ :=
  let pos : Fin 15 := ⟨g.val * 5 + i.val, by omega⟩
  let ⟨a, b, c⟩ := tripleComponents pos
  if ((a : ℤ) + (b : ℤ) + c) % 2 = 0 then 0 else 1

private def mod2VacuumPattern (pos : Fin 15) : Bool :=
  let ⟨a, b, c⟩ := tripleComponents pos
  decide ((a : ℤ) % 2 = 0 && (b : ℤ) % 2 = 0 && c % 2 = 0)

private def mod2VectorsFromAssignment (values : Array ℕ) : Array (Array ℕ) :=
  Array.ofFn fun (g : Fin 3) =>
    Array.ofFn fun (i : Fin 5) =>
      let pos : Fin 15 := ⟨g.val * 5 + i.val, by omega⟩
      if mod2VacuumPattern pos then 0
      else values[mod2PositionIndex[pos]!]!

private def parityFactorT (vecs : Array (Array ℕ)) : Bool :=
  (List.range 7).any fun t =>
    decide (t > 0) && (List.finRange 3).all fun g =>
      (List.finRange 5).all fun i =>
        decide ((vecs.getD g.val #[]).getD i.val 0 =
          if mod2ParityGen g i = 1 then t else 0)

private def isProductParity (values : Array ℕ) : Bool :=
  decide (values[0]! = 0 && values[1]! = 0 && values[2]! = 0 &&
    values[3]! = 0 && values[4]! > 0)

private def classifyMod2Assignment (values : Array ℕ) : ℕ × Bool × Bool × Bool :=
  let vecs := mod2VectorsFromAssignment values
  let ⟨st, sol⟩ := classifyVectors vecs[0]! vecs[1]! vecs[2]!
  match sol with
  | none => (st, false, false, false)
  | some coeffs =>
    let img :=
      ((List.range 7).filterMap fun x =>
        if values.any fun v => decide (v = x) then some x else none).toArray
    let img' := img.push 0
    let scc := shadowClosed coeffs img'
    let pf := parityFactorT vecs
    let isp := isProductParity values
    (st, scc, pf, isp)

private def bumpMod2Count (acc : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) (id : ℕ) :
    ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  let values := Array.ofFn fun (k : Fin 5) => (id / Nat.pow 7 k.val) % 7
  let ⟨st, sc, pft, isp⟩ := classifyMod2Assignment values
  let ⟨c, nm, u, f, scc, pf, prod⟩ := acc
  (c + if st = 0 then 1 else 0,
   nm + if st = 1 then 1 else 0,
   u + if st = 2 then 1 else 0,
   f + if st = 3 then 1 else 0,
   scc + if st = 3 ∧ sc then 1 else 0,
   pf + if st = 3 ∧ sc ∧ pft then 1 else 0,
   prod + if st = 3 ∧ sc ∧ isp then 1 else 0)

private def foldMod2AtFirstTwo (v0 v1 : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (List.range (7 ^ 3)).foldl
    (fun acc sub => bumpMod2Count acc (v0 + 7 * v1 + 49 * sub))
    (0, 0, 0, 0, 0, 0, 0)

private def addMod2Counts (a b : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ) :
    ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (a.1 + b.1, a.2.1 + b.2.1, a.2.2.1 + b.2.2.1, a.2.2.2.1 + b.2.2.2.1,
   a.2.2.2.2.1 + b.2.2.2.2.1, a.2.2.2.2.2.1 + b.2.2.2.2.2.1,
   a.2.2.2.2.2.2 + b.2.2.2.2.2.2)

private def foldMod2Chunk (v0 : ℕ) : ℕ × ℕ × ℕ × ℕ × ℕ × ℕ × ℕ :=
  (List.range 7).foldl
    (fun acc v1 => addMod2Counts acc (foldMod2AtFirstTwo v0 v1))
    (0, 0, 0, 0, 0, 0, 0)

-- ════════════════════════════════════════════════════════════════
-- Additive battery — per modulus (777 nonzero forms, m = 2..7)
-- ════════════════════════════════════════════════════════════════

theorem additive_battery_mod_two :
    (foldFormsAtM 2).1 = 5 ∧
      (foldFormsAtM 2).2.1 = 0 ∧
        (foldFormsAtM 2).2.2.1 = 1 ∧
          (foldFormsAtM 2).2.2.2.1 = 1 ∧
            (foldFormsAtM 2).2.2.2.2.1 = 1 ∧
              (foldFormsAtM 2).2.2.2.2.2 = 1 := by native_decide

theorem additive_battery_mod_three :
    (foldFormsAtM 3).1 = 22 ∧
      (foldFormsAtM 3).2.1 = 4 ∧
        (foldFormsAtM 3).2.2.1 = 0 ∧
          (foldFormsAtM 3).2.2.2.1 = 0 ∧
            (foldFormsAtM 3).2.2.2.2.1 = 0 ∧
              (foldFormsAtM 3).2.2.2.2.2 = 0 := by native_decide

theorem additive_battery_mod_four :
    (foldFormsAtM 4).1 = 45 ∧
      (foldFormsAtM 4).2.1 = 14 ∧
        (foldFormsAtM 4).2.2.1 = 3 ∧
          (foldFormsAtM 4).2.2.2.1 = 1 ∧
            (foldFormsAtM 4).2.2.2.2.1 = 1 ∧
              (foldFormsAtM 4).2.2.2.2.2 = 1 := by native_decide

theorem additive_battery_mod_five :
    (foldFormsAtM 5).1 = 40 ∧
      (foldFormsAtM 5).2.1 = 83 ∧
        (foldFormsAtM 5).2.2.1 = 0 ∧
          (foldFormsAtM 5).2.2.2.1 = 1 ∧
            (foldFormsAtM 5).2.2.2.2.1 = 0 ∧
              (foldFormsAtM 5).2.2.2.2.2 = 0 := by native_decide

theorem additive_battery_mod_six :
    (foldFormsAtM 6).1 = 105 ∧
      (foldFormsAtM 6).2.1 = 107 ∧
        (foldFormsAtM 6).2.2.1 = 1 ∧
          (foldFormsAtM 6).2.2.2.1 = 2 ∧
            (foldFormsAtM 6).2.2.2.2.1 = 1 ∧
              (foldFormsAtM 6).2.2.2.2.2 = 1 := by native_decide

theorem additive_battery_mod_seven :
    (foldFormsAtM 7).1 = 60 ∧
      (foldFormsAtM 7).2.1 = 282 ∧
        (foldFormsAtM 7).2.2.1 = 0 ∧
          (foldFormsAtM 7).2.2.2.1 = 0 ∧
            (foldFormsAtM 7).2.2.2.2.1 = 0 ∧
              (foldFormsAtM 7).2.2.2.2.2 = 0 := by native_decide

theorem additive_battery_totals :
    (5 + 22 + 45 + 40 + 105 + 60 = 277) ∧
      (0 + 4 + 14 + 83 + 107 + 282 = 490) ∧
        (1 + 0 + 3 + 0 + 1 + 0 = 5) ∧
          (1 + 0 + 1 + 1 + 2 + 0 = 5) ∧
            (1 + 0 + 1 + 0 + 1 + 0 = 3) ∧
              (1 + 0 + 1 + 0 + 1 + 0 = 3) := by native_decide

/-- **unit_conjugate_two_forced_scc** (CatAL): `(2,2,2) mod 4` is FORCED,
    shadow-closed, and forces the unit conjugate `g₂`. -/
theorem unit_conjugate_two_forced_scc :
    (classifyForm 2 2 2 4).1 = 3 ∧
      (classifyForm 2 2 2 4).2.1 = true ∧
        (classifyForm 2 2 2 4).2.2 = true := by native_decide

/-- **unit_conjugate_three_forced_scc** (CatAL): `(3,3,3) mod 6` is FORCED,
    shadow-closed, and forces the unit conjugate `g₃`. -/
theorem unit_conjugate_three_forced_scc :
    (classifyForm 3 3 3 6).1 = 3 ∧
      (classifyForm 3 3 3 6).2.1 = true ∧
        (classifyForm 3 3 3 6).2.2 = true := by native_decide

-- ════════════════════════════════════════════════════════════════
-- Mod-2 recoding battery — seven chunks of 2401 (16,807 total)
-- ════════════════════════════════════════════════════════════════

theorem mod2_recoding_chunk_zero :
    (foldMod2Chunk 0).1 = 1056 ∧
      (foldMod2Chunk 0).2.1 = 1260 ∧
        (foldMod2Chunk 0).2.2.1 = 49 ∧
          (foldMod2Chunk 0).2.2.2.1 = 36 ∧
            (foldMod2Chunk 0).2.2.2.2.1 = 6 ∧
              (foldMod2Chunk 0).2.2.2.2.2.1 = 0 ∧
                (foldMod2Chunk 0).2.2.2.2.2.2 = 6 := by native_decide

theorem mod2_recoding_chunk_one :
    (foldMod2Chunk 1).1 = 1056 ∧
      (foldMod2Chunk 1).2.1 = 1260 ∧
        (foldMod2Chunk 1).2.2.1 = 49 ∧
          (foldMod2Chunk 1).2.2.2.1 = 36 ∧
            (foldMod2Chunk 1).2.2.2.2.1 = 1 ∧
              (foldMod2Chunk 1).2.2.2.2.2.1 = 1 ∧
                (foldMod2Chunk 1).2.2.2.2.2.2 = 0 := by native_decide

theorem mod2_recoding_chunk_two :
    (foldMod2Chunk 2).1 = 1056 ∧
      (foldMod2Chunk 2).2.1 = 1260 ∧
        (foldMod2Chunk 2).2.2.1 = 49 ∧
          (foldMod2Chunk 2).2.2.2.1 = 36 ∧
            (foldMod2Chunk 2).2.2.2.2.1 = 1 ∧
              (foldMod2Chunk 2).2.2.2.2.2.1 = 1 ∧
                (foldMod2Chunk 2).2.2.2.2.2.2 = 0 := by native_decide

theorem mod2_recoding_chunk_three :
    (foldMod2Chunk 3).1 = 1056 ∧
      (foldMod2Chunk 3).2.1 = 1260 ∧
        (foldMod2Chunk 3).2.2.1 = 49 ∧
          (foldMod2Chunk 3).2.2.2.1 = 36 ∧
            (foldMod2Chunk 3).2.2.2.2.1 = 1 ∧
              (foldMod2Chunk 3).2.2.2.2.2.1 = 1 ∧
                (foldMod2Chunk 3).2.2.2.2.2.2 = 0 := by native_decide

theorem mod2_recoding_chunk_four :
    (foldMod2Chunk 4).1 = 1056 ∧
      (foldMod2Chunk 4).2.1 = 1260 ∧
        (foldMod2Chunk 4).2.2.1 = 49 ∧
          (foldMod2Chunk 4).2.2.2.1 = 36 ∧
            (foldMod2Chunk 4).2.2.2.2.1 = 1 ∧
              (foldMod2Chunk 4).2.2.2.2.2.1 = 1 ∧
                (foldMod2Chunk 4).2.2.2.2.2.2 = 0 := by native_decide

theorem mod2_recoding_chunk_five :
    (foldMod2Chunk 5).1 = 1056 ∧
      (foldMod2Chunk 5).2.1 = 1260 ∧
        (foldMod2Chunk 5).2.2.1 = 49 ∧
          (foldMod2Chunk 5).2.2.2.1 = 36 ∧
            (foldMod2Chunk 5).2.2.2.2.1 = 1 ∧
              (foldMod2Chunk 5).2.2.2.2.2.1 = 1 ∧
                (foldMod2Chunk 5).2.2.2.2.2.2 = 0 := by native_decide

theorem mod2_recoding_chunk_six :
    (foldMod2Chunk 6).1 = 1056 ∧
      (foldMod2Chunk 6).2.1 = 1260 ∧
        (foldMod2Chunk 6).2.2.1 = 49 ∧
          (foldMod2Chunk 6).2.2.2.1 = 36 ∧
            (foldMod2Chunk 6).2.2.2.2.1 = 1 ∧
              (foldMod2Chunk 6).2.2.2.2.2.1 = 1 ∧
                (foldMod2Chunk 6).2.2.2.2.2.2 = 0 := by native_decide

theorem mod2_recoding_totals :
    (1056 * 7 = 7392) ∧
      (1260 * 7 = 8820) ∧
        (49 * 7 = 343) ∧
          (36 + 36 * 6 = 252) ∧
            (6 + 6 * 1 = 12) ∧
              (0 + 1 * 6 = 6) ∧
                (6 + 0 * 6 = 6) := by native_decide

end UgpLean.Universality.ParityProjectionBattery
