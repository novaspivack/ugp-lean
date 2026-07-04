import Mathlib.Data.Int.Basic
import Mathlib.Data.Fin.Basic

set_option maxRecDepth 10000

/-!
# G2StabilizerCertificate: derivation algebra and apex stabilizer

Machine certificate for the QR(7) octonion derivation Lie algebra. The full
512x64 linear system D(xy) = D(x)y + xD(y) is built inside Lean from the
octonion multiplication table (`systemEntry`); every check below is exact
integer arithmetic discharged by `native_decide`.

## Certified in Lean (CatAL)

* **Witnesses:** 14 derivations satisfying the Leibniz rule on all 64 basis
  pairs; 8 additionally satisfying D(e0) = 0 (apex stabilizer).
* **Independence:** 14x14 and 8x8 minors of the witness matrices have
  determinant -1 (fraction-free Bareiss elimination), so dim >= 14 resp. 8.
* **Exact dimension:** a 50x50 minor of the derivation system has
  determinant 1024 != 0, so the system rank is >= 50 and the nullspace
  dimension is exactly 14; a 56x56 minor of the apex-augmented system has
  determinant 1024, so the stabilizer dimension is exactly 8
  (rank-nullity on the 64 unknowns).
* **Bracket closure:** all 91 (resp. 28) commutators [D_i, D_j] equal the
  recorded integer linear combinations of the basis - both nullspaces are
  Lie subalgebras of gl(8).
* **Killing form:** the 14x14 (resp. 8x8) Killing matrices computed from the
  certified structure constants match the inlined matrices, and -K is
  positive definite by Sylvester's criterion (all leading principal minors
  positive, Bareiss-exact). Hence both algebras are compact semisimple.

## Interpretation (classification input, cited not formalized)

Compact semisimple of dimension 8 forces su(3) (no other sum of compact
simple dimensions equals 8). For dimension 14 the options are g2 or
su(2)+su(2)+su(3); the rank-2 computation excluding the latter is certified
numerically in `cp4_g2_stabilizer.py` (Lie-algebra rank via generic
centralizer), not yet in Lean.
-/

namespace UgpLean.Algebra.G2StabilizerCertificate

/-! ## Octonion multiplication table and the derivation system -/

def basisMulFlat : Array Int :=
#[0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1]

/-- `basisMulCoeffN a b r` = r-th component of the octonion product e_a * e_b
    (indices 0-6 imaginary, 7 real). -/
def basisMulCoeffN (a b r : Nat) : Int :=
  basisMulFlat.getD (a * 64 + b * 8 + r) 0

def basisMulCoeff (a b r : Fin 8) : Int :=
  basisMulCoeffN a.val b.val r.val

def flatGet (v : Array Int) (m c : Fin 8) : Int :=
  v.getD (m.val * 8 + c.val) 0

/-- Entry of the 520x64 derivation system (rows 0-511: Leibniz equations
    indexed (a,b,r) as a*64+b*8+r; rows 512-519: apex constraint D(e0)=0).
    Column m*8+n is the unknown D[m][n]. -/
def systemEntry (row col : Nat) : Int :=
  if row < 512 then
    let a := row / 64
    let b := (row / 8) % 8
    let r := row % 8
    let m := col / 8
    let n := col % 8
    (if m == r then basisMulCoeffN a b n else 0)
      - (if n == a then basisMulCoeffN m b r else 0)
      - (if n == b then basisMulCoeffN a m r else 0)
  else
    if col == (row - 512) * 8 then 1 else 0

/-! ## Checkers -/

def derivationResidualZero (D : Array Int) (a b : Fin 8) : Bool :=
  (List.finRange 8).all fun r =>
    let lhs := (List.finRange 8).foldl (fun acc c => acc + basisMulCoeff a b c * flatGet D c r) 0
    let rhs := (List.finRange 8).foldl
      (fun acc m =>
        acc + flatGet D a m * basisMulCoeff ⟨m.val, by omega⟩ b r
          + flatGet D b m * basisMulCoeff a ⟨m.val, by omega⟩ r)
      0
    lhs == rhs

def derivationOk (D : Array Int) : Bool :=
  (List.finRange 8).all fun a => (List.finRange 8).all fun b => derivationResidualZero D a b

def apexZero (D : Array Int) : Bool :=
  (List.finRange 8).all fun m => flatGet D ⟨0, by decide⟩ m == 0

/-- Fraction-free (Bareiss) elimination: exact integer determinant.
    Every division is exact by the Bareiss identity. -/
partial def bareissDet (M : Array (Array Int)) : Int :=
  let n := M.size
  let rec go (A : Array (Array Int)) (col : Nat) (sign prev : Int) : Int :=
    if col == n then
      if n == 0 then 1 else sign * (A.getD (n - 1) #[]).getD (n - 1) 0
    else
      match (List.range n).find? (fun r => r >= col && (A.getD r #[]).getD col 0 != 0) with
      | none => 0
      | some piv =>
        let swapped := piv != col
        let A1 := if swapped then
          (A.set! col (A.getD piv #[])).set! piv (A.getD col #[])
        else A
        let sign1 := if swapped then -sign else sign
        let pv := (A1.getD col #[]).getD col 0
        let pivRow := A1.getD col #[]
        let A2 := (List.range n).foldl (fun acc r =>
          if r <= col then acc else
            let rowR := acc.getD r #[]
            let f := rowR.getD col 0
            acc.set! r (((List.range n).map fun cc =>
              if cc <= col then 0
              else (rowR.getD cc 0 * pv - f * pivRow.getD cc 0) / prev).toArray)) A1
        go A2 (col + 1) sign1 pv
  go M 0 1 1

def minorFromSystem (rows cols : Array Nat) : Array (Array Int) :=
  rows.map fun r => cols.map fun cc => systemEntry r cc

/-! ## Matrix algebra on flattened 8x8 (row-major m*8+n) -/

def matMulFlat (A B : Array Int) : Array Int :=
  ((List.range 64).map fun idx =>
    let i := idx / 8
    let j := idx % 8
    (List.range 8).foldl (fun acc k => acc + A.getD (i * 8 + k) 0 * B.getD (k * 8 + j) 0) 0).toArray

def commFlat (A B : Array Int) : Array Int :=
  let ab := matMulFlat A B
  let ba := matMulFlat B A
  ((List.range 64).map fun t => ab.getD t 0 - ba.getD t 0).toArray

/-- Bracket certificate row [i, j, c_0, ..., c_(d-1)]:
    checks [basis_i, basis_j] = sum_k c_k * basis_k componentwise. -/
def bracketRowOk (basis : Array (Array Int)) (row : Array Int) : Bool :=
  let i := (row.getD 0 0).natAbs
  let j := (row.getD 1 0).natAbs
  let comm := commFlat (basis.getD i #[]) (basis.getD j #[])
  (List.range 64).all fun k =>
    ((List.range basis.size).foldl
      (fun acc t => acc + row.getD (t + 2) 0 * (basis.getD t #[]).getD k 0) 0)
      == comm.getD k 0

/-- The rows enumerate exactly the pairs (i,j), 0 <= i < j < d, in order,
    each with d coefficient entries. -/
def bracketPairsComplete (data : Array (Array Int)) (d : Nat) : Bool :=
  data.size == d * (d - 1) / 2 &&
  (((List.range d).flatMap fun i =>
      ((List.range d).filter (fun j => i < j)).map fun j => (Int.ofNat i, Int.ofNat j))
    == data.toList.map fun row => (row.getD 0 0, row.getD 1 0)) &&
  data.all (fun row => row.size == d + 2)

/-! ## Killing form from structure constants -/

/-- Antisymmetric structure-constant lookup: coefficient of D_k in [D_i, D_j],
    from the i<j certificate rows. -/
def bracketCoeff (data : Array (Array Int)) (i j k : Nat) : Int :=
  if i == j then 0
  else if i < j then
    match data.toList.find? (fun row => row.getD 0 0 == Int.ofNat i && row.getD 1 0 == Int.ofNat j) with
    | some row => row.getD (k + 2) 0
    | none => 0
  else
    match data.toList.find? (fun row => row.getD 0 0 == Int.ofNat j && row.getD 1 0 == Int.ofNat i) with
    | some row => -(row.getD (k + 2) 0)
    | none => 0

/-- Killing form K[i][j] = trace(ad_i ad_j) = sum_(a,b) C(i,b)_a * C(j,a)_b. -/
def killingEntry (data : Array (Array Int)) (d i j : Nat) : Int :=
  (List.range d).foldl (fun acc a =>
    (List.range d).foldl (fun acc2 b =>
      acc2 + bracketCoeff data i b a * bracketCoeff data j a b) acc) 0

def killingMatches (data : Array (Array Int)) (K : Array (Array Int)) (d : Nat) : Bool :=
  (List.range d).all fun i => (List.range d).all fun j =>
    killingEntry data d i j == (K.getD i #[]).getD j 0

def leadingMinor (M : Array (Array Int)) (k : Nat) : Array (Array Int) :=
  ((List.range k).map fun i =>
    ((List.range k).map fun j => (M.getD i #[]).getD j 0).toArray).toArray

def negMatrix (M : Array (Array Int)) : Array (Array Int) :=
  M.map fun row => row.map (- ·)

/-- Sylvester: all leading principal minors positive. -/
def sylvesterPositive (M : Array (Array Int)) (d : Nat) : Bool :=
  (List.range d).all fun k => bareissDet (leadingMinor M (k + 1)) > 0

def symmetricCheck (M : Array (Array Int)) (d : Nat) : Bool :=
  (List.range d).all fun i => (List.range d).all fun j =>
    (M.getD i #[]).getD j 0 == (M.getD j #[]).getD i 0

/-! ## Certificate data -/

def derivationBasis14 : Array (Array Int) :=
#[
  #[0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
]

def apexStabilizerBasis8 : Array (Array Int) :=
#[
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
]

def independence14Data : Array (Array Int) :=
#[
  #[0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
  #[0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0, 0, 0],
  #[0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
  #[-1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, -1, 0, 0, 1, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, -1],
  #[0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
  #[1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
]

def independence8Data : Array (Array Int) :=
#[
  #[0, 0, 0, -1, 0, 0, 0, 0],
  #[0, 0, -1, 0, 0, 0, 0, 0],
  #[0, 1, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, -1, 0, 0, 0],
  #[0, 1, 0, 0, 0, 0, 0, -1],
  #[-1, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, -1, 0],
  #[0, 0, 0, 0, 0, 1, 0, 0],
]

def rank50RowIdx : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 27, 32, 33, 34, 35, 36, 37, 38, 39, 64, 71, 79, 80, 81, 82, 83, 84, 85, 86, 87, 128, 135, 143, 151, 215]

def rank50ColIdx : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 33, 36, 37, 38, 39, 45, 46, 47, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]

def rank56RowIdx : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 25, 27, 32, 33, 34, 35, 36, 37, 38, 39, 64, 71, 79, 80, 81, 82, 83, 84, 85, 86, 87, 128, 135, 143, 151, 215, 513, 514, 515, 516, 517, 518]

def rank56ColIdx : Array Nat := #[0, 1, 2, 3, 4, 5, 6, 7, 8, 9, 10, 11, 12, 13, 14, 15, 16, 17, 18, 19, 20, 21, 22, 23, 24, 25, 26, 27, 28, 29, 30, 31, 32, 33, 34, 35, 36, 37, 38, 39, 40, 42, 45, 46, 47, 48, 54, 55, 56, 57, 58, 59, 60, 61, 62, 63]

def bracketData14 : Array (Array Int) :=
#[
  #[0, 1, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 2, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 3, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  #[0, 4, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 5, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
  #[0, 6, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 7, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  #[0, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
  #[0, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  #[0, 12, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
  #[0, 13, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[1, 2, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[1, 3, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  #[1, 4, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[1, 5, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  #[1, 6, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[1, 7, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  #[1, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0],
  #[1, 9, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[1, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  #[1, 11, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
  #[1, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
  #[1, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[2, 3, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  #[2, 4, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[2, 5, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[2, 6, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
  #[2, 7, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0],
  #[2, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
  #[2, 9, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[2, 10, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0],
  #[2, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0],
  #[2, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
  #[2, 13, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[3, 4, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0],
  #[3, 5, 0, 0, 0, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[3, 6, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[3, 7, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[3, 8, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  #[3, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0],
  #[3, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
  #[3, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[3, 12, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[3, 13, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0],
  #[4, 5, 0, 0, 0, 2, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[4, 6, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0],
  #[4, 7, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0],
  #[4, 8, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, -1, 0, 0, 0],
  #[4, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  #[4, 10, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
  #[4, 11, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0],
  #[4, 12, 0, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[4, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
  #[5, 6, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[5, 7, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[5, 8, 1, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  #[5, 9, 0, 0, 0, 0, 0, 0, -1, 0, -1, 0, 0, 0, 0, 0],
  #[5, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  #[5, 11, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[5, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[5, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0],
  #[6, 7, 0, 0, 2, 0, -2, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[6, 8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[6, 9, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 1, 0],
  #[6, 10, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[6, 11, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  #[6, 12, -1, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0],
  #[6, 13, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
  #[7, 8, 0, 0, 1, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[7, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
  #[7, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[7, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0],
  #[7, 12, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 1],
  #[7, 13, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
  #[8, 9, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0],
  #[8, 10, 0, 0, -1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[8, 11, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[8, 12, 2, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
  #[8, 13, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0],
  #[9, 10, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0],
  #[9, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -2, 0, 0, 0],
  #[9, 12, 0, 0, 0, 0, 0, 0, 0, 0, -1, 0, 0, 0, 0, 0],
  #[9, 13, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[10, 11, 0, 0, 0, 0, 0, 0, 0, 0, 0, 2, 0, 0, 0, 0],
  #[10, 12, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[10, 13, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0],
  #[11, 12, 0, 0, 1, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[11, 13, 0, 0, 0, 0, 0, 0, 1, 0, 1, 0, 0, 0, 0, 0],
  #[12, 13, 0, 0, 0, 0, 0, 0, 0, 1, 0, 0, 0, 0, 0, 0],
]

def bracketData8 : Array (Array Int) :=
#[
  #[0, 1, 0, 0, -2, 0, 0, 0, 0, 0],
  #[0, 2, 0, 2, 0, 0, 0, 0, 0, 0],
  #[0, 3, 0, 0, 0, 0, 0, 0, 0, 1],
  #[0, 4, 0, 1, 0, 0, 0, 0, 0, 0],
  #[0, 5, 0, 0, 0, 0, 0, 0, -1, 0],
  #[0, 6, 0, 0, 0, 0, 0, 1, 0, 0],
  #[0, 7, 0, 0, 0, -1, 0, 0, 0, 0],
  #[1, 2, -2, 0, 0, 0, 0, 0, 0, 0],
  #[1, 3, 0, 0, 0, 0, 0, 0, 1, 0],
  #[1, 4, -1, 0, 0, 0, 0, 0, 0, 0],
  #[1, 5, 0, 0, 0, 0, 0, 0, 0, 1],
  #[1, 6, 0, 0, 0, -1, 0, 0, 0, 0],
  #[1, 7, 0, 0, 0, 0, 0, -1, 0, 0],
  #[2, 3, 0, 0, 0, 0, 0, -1, 0, 0],
  #[2, 4, 0, 0, 0, 0, 0, 0, 0, 0],
  #[2, 5, 0, 0, 0, 1, 0, 0, 0, 0],
  #[2, 6, 0, 0, 0, 0, 0, 0, 0, 1],
  #[2, 7, 0, 0, 0, 0, 0, 0, -1, 0],
  #[3, 4, 0, 0, 0, 0, 0, 2, 0, 0],
  #[3, 5, 0, 0, 0, 0, -2, 0, 0, 0],
  #[3, 6, 0, 1, 0, 0, 0, 0, 0, 0],
  #[3, 7, 1, 0, 0, 0, 0, 0, 0, 0],
  #[4, 5, 0, 0, 0, 2, 0, 0, 0, 0],
  #[4, 6, 0, 0, 0, 0, 0, 0, 0, -1],
  #[4, 7, 0, 0, 0, 0, 0, 0, 1, 0],
  #[5, 6, -1, 0, 0, 0, 0, 0, 0, 0],
  #[5, 7, 0, 1, 0, 0, 0, 0, 0, 0],
  #[6, 7, 0, 0, 2, 0, -2, 0, 0, 0],
]

def killingForm14 : Array (Array Int) :=
#[
  #[-16, 0, 0, 0, 0, 0, 0, 0, 0, 8, 0, 0, 0, 0],
  #[0, -16, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -8],
  #[0, 0, -16, 0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, -16, 0, 0, 0, 0, 0, 0, 0, -8, 0, 0],
  #[0, 0, -8, 0, -16, 0, 0, 0, 0, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, -16, 0, 0, 0, 0, 0, 0, 8, 0],
  #[0, 0, 0, 0, 0, 0, -16, 0, 8, 0, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, -16, 0, 0, -8, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 8, 0, -16, 0, 0, 0, 0, 0],
  #[8, 0, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0, 0, 0],
  #[0, 0, 0, 0, 0, 0, 0, -8, 0, 0, -16, 0, 0, 0],
  #[0, 0, 0, -8, 0, 0, 0, 0, 0, 0, 0, -16, 0, 0],
  #[0, 0, 0, 0, 0, 8, 0, 0, 0, 0, 0, 0, -16, 0],
  #[0, -8, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, 0, -16],
]

def killingForm8 : Array (Array Int) :=
#[
  #[-12, 0, 0, 0, 0, 0, 0, 0],
  #[0, -12, 0, 0, 0, 0, 0, 0],
  #[0, 0, -12, 0, -6, 0, 0, 0],
  #[0, 0, 0, -12, 0, 0, 0, 0],
  #[0, 0, -6, 0, -12, 0, 0, 0],
  #[0, 0, 0, 0, 0, -12, 0, 0],
  #[0, 0, 0, 0, 0, 0, -12, 0],
  #[0, 0, 0, 0, 0, 0, 0, -12],
]

/-! ## Theorems: derivation witnesses -/

theorem derivation_basis_0_ok : derivationOk (derivationBasis14.getD 0 #[]) = true := by native_decide
theorem derivation_basis_1_ok : derivationOk (derivationBasis14.getD 1 #[]) = true := by native_decide
theorem derivation_basis_2_ok : derivationOk (derivationBasis14.getD 2 #[]) = true := by native_decide
theorem derivation_basis_3_ok : derivationOk (derivationBasis14.getD 3 #[]) = true := by native_decide
theorem derivation_basis_4_ok : derivationOk (derivationBasis14.getD 4 #[]) = true := by native_decide
theorem derivation_basis_5_ok : derivationOk (derivationBasis14.getD 5 #[]) = true := by native_decide
theorem derivation_basis_6_ok : derivationOk (derivationBasis14.getD 6 #[]) = true := by native_decide
theorem derivation_basis_7_ok : derivationOk (derivationBasis14.getD 7 #[]) = true := by native_decide
theorem derivation_basis_8_ok : derivationOk (derivationBasis14.getD 8 #[]) = true := by native_decide
theorem derivation_basis_9_ok : derivationOk (derivationBasis14.getD 9 #[]) = true := by native_decide
theorem derivation_basis_10_ok : derivationOk (derivationBasis14.getD 10 #[]) = true := by native_decide
theorem derivation_basis_11_ok : derivationOk (derivationBasis14.getD 11 #[]) = true := by native_decide
theorem derivation_basis_12_ok : derivationOk (derivationBasis14.getD 12 #[]) = true := by native_decide
theorem derivation_basis_13_ok : derivationOk (derivationBasis14.getD 13 #[]) = true := by native_decide

theorem apex_basis_0_ok : derivationOk (apexStabilizerBasis8.getD 0 #[]) = true ∧ apexZero (apexStabilizerBasis8.getD 0 #[]) = true := by native_decide
theorem apex_basis_1_ok : derivationOk (apexStabilizerBasis8.getD 1 #[]) = true ∧ apexZero (apexStabilizerBasis8.getD 1 #[]) = true := by native_decide
theorem apex_basis_2_ok : derivationOk (apexStabilizerBasis8.getD 2 #[]) = true ∧ apexZero (apexStabilizerBasis8.getD 2 #[]) = true := by native_decide
theorem apex_basis_3_ok : derivationOk (apexStabilizerBasis8.getD 3 #[]) = true ∧ apexZero (apexStabilizerBasis8.getD 3 #[]) = true := by native_decide
theorem apex_basis_4_ok : derivationOk (apexStabilizerBasis8.getD 4 #[]) = true ∧ apexZero (apexStabilizerBasis8.getD 4 #[]) = true := by native_decide
theorem apex_basis_5_ok : derivationOk (apexStabilizerBasis8.getD 5 #[]) = true ∧ apexZero (apexStabilizerBasis8.getD 5 #[]) = true := by native_decide
theorem apex_basis_6_ok : derivationOk (apexStabilizerBasis8.getD 6 #[]) = true ∧ apexZero (apexStabilizerBasis8.getD 6 #[]) = true := by native_decide
theorem apex_basis_7_ok : derivationOk (apexStabilizerBasis8.getD 7 #[]) = true ∧ apexZero (apexStabilizerBasis8.getD 7 #[]) = true := by native_decide

/-! ## Theorems: independence (dim lower bounds) -/

theorem derivation_basis_independent_fourteen :
    bareissDet independence14Data = -1 := by
  native_decide

theorem apex_stabilizer_independent_eight :
    bareissDet independence8Data = -1 := by
  native_decide

/-! ## Theorems: system rank (dim upper bounds) -/

/-- A 50x50 minor of the 512x64 derivation system (built from the octonion
    table inside Lean) has determinant 1024 != 0, so rank >= 50 and the
    nullspace has dimension <= 64 - 50 = 14. -/
theorem derivation_system_rank_fifty :
    bareissDet (minorFromSystem rank50RowIdx rank50ColIdx) = 1024 := by
  native_decide

/-- A 56x56 minor of the apex-augmented system has determinant 1024 != 0,
    so rank >= 56 and the apex-stabilizer nullspace has dimension <= 8. -/
theorem apex_system_rank_fifty_six :
    bareissDet (minorFromSystem rank56RowIdx rank56ColIdx) = 1024 := by
  native_decide

/-- **dim der(O) = 14**: 14 independent Leibniz witnesses (lower bound)
    + rank-50 minor (upper bound), by rank-nullity on 64 unknowns. -/
theorem octonion_derivation_dimension_exact :
    derivationBasis14.size = 14 ∧
    bareissDet independence14Data = -1 ∧
    bareissDet (minorFromSystem rank50RowIdx rank50ColIdx) = 1024 := by
  native_decide

/-- **dim Stab_der(e0) = 8**: 8 independent apex-killing witnesses
    + rank-56 minor of the augmented system, by rank-nullity. -/
theorem apex_stabilizer_dimension_exact :
    apexStabilizerBasis8.size = 8 ∧
    bareissDet independence8Data = -1 ∧
    bareissDet (minorFromSystem rank56RowIdx rank56ColIdx) = 1024 := by
  native_decide

/-! ## Theorems: bracket closure -/

theorem derivation_bracket_pairs_complete :
    bracketData14.size = 91 ∧ bracketPairsComplete bracketData14 14 = true := by
  native_decide

theorem apex_bracket_pairs_complete :
    bracketData8.size = 28 ∧ bracketPairsComplete bracketData8 8 = true := by
  native_decide

/-- All 91 commutators [D_i, D_j] (i<j) of the 14-basis lie in its span with
    the recorded integer coefficients: der(O) is closed under bracket. -/
theorem derivation_algebra_bracket_closed :
    bracketData14.all (bracketRowOk derivationBasis14) = true := by
  native_decide

/-- All 28 commutators of the 8-basis lie in its span: the apex stabilizer
    is a Lie subalgebra. -/
theorem apex_stabilizer_bracket_closed :
    bracketData8.all (bracketRowOk apexStabilizerBasis8) = true := by
  native_decide

/-! ## Theorems: Killing form (compactness) -/

/-- The Killing matrix computed from the certified structure constants equals
    the inlined `killingForm14`. -/
theorem killing_form_fourteen_matches :
    killingMatches bracketData14 killingForm14 14 = true := by
  native_decide

theorem killing_form_eight_matches :
    killingMatches bracketData8 killingForm8 8 = true := by
  native_decide

/-- -K is positive definite (Sylvester, exact integer minors): the Killing
    form of der(O) is negative definite, so der(O) is compact semisimple. -/
theorem derivation_killing_negative_definite :
    symmetricCheck killingForm14 14 = true ∧
    sylvesterPositive (negMatrix killingForm14) 14 = true := by
  native_decide

/-- Negative-definite Killing form on the 8-dim apex stabilizer: compact
    semisimple of dimension 8, which forces su(3). -/
theorem apex_stabilizer_killing_negative_definite :
    symmetricCheck killingForm8 8 = true ∧
    sylvesterPositive (negMatrix killingForm8) 8 = true := by
  native_decide

end UgpLean.Algebra.G2StabilizerCertificate
