import Mathlib
import UgpLean.Core.TripleDefs
import UgpLean.GTE.Evolution
import UgpLean.Universality.CUP4TotalParity
import UgpLean.Universality.PhiMDLUniversality
import UgpLean.Polynomial.EisensteinIdentities
import UgpLean.Polynomial.PolyExplorations
import UgpLean.Algebra.ChiralDoublet
import UgpLean.Polynomial.AGL17ChiralZ2

set_option maxHeartbeats 800000

/-!
# Direct-interpolation lift of the GTE polynomial

The SM generation orbit under total parity, together with vacuum transparency,
uniquely determines the multilinear GF(7) polynomial `p(L,C,R) = C + R − C·R − L·C·R`
among all `7⁸` multilinear rules.  Rule 110 is its binary restriction; the chiral
outer pair `{110, 124}` is the full vacuum-transparent image over all family orderings.

All theorems: zero sorry, zero custom axioms.
-/

namespace UgpLean.Universality.TriangleLiftTheorem

open UgpLean
open UgpLean.Universality
open UgpLean.Universality.PhiMDLUniversality
open UgpLean.Polynomial.EisensteinIdentities
open UgpLean.Polynomial.PolyExplorations
open ChiralDoublet

-- ════════════════════════════════════════════════════════════════
-- §1  Canonical cascade triples and total-parity provenance
-- ════════════════════════════════════════════════════════════════

/-- Total parity `(a + b + c) mod 2` for nonnegative cascade components. -/
def totalParityNat (a b c : ℕ) : Fin 2 :=
  ⟨(a + b + c) % 2, Nat.mod_lt _ (by omega)⟩

/-- Total parity for signed `c` (top-quark branch capacity `−1`). -/
def totalParitySigned (a b : ℕ) (c : ℤ) : Fin 2 :=
  if ((a : ℤ) + (b : ℤ) + c) % 2 = 0 then 0 else 1

/-- Canonical P01 cascade triples in CUP-4 family order. -/
inductive SMFamily
  | e | u | d | nuR | nuL
  deriving DecidableEq, Repr, Fintype, Inhabited

/-- Generation-indexed triple for one SM family (`g = 0,1,2`). -/
def smFamilyTriple (f : SMFamily) (g : Fin 3) : Triple × Option (ℕ × ℕ × ℤ) :=
  match f, g with
  | .e,  ⟨0, _⟩ => (LeptonSeed, none)
  | .e,  ⟨1, _⟩ => (canonicalGen2, none)
  | .e,  ⟨2, _⟩ => (canonicalGen3, none)
  | .u,  ⟨0, _⟩ => (⟨5, 9, 275⟩, none)
  | .u,  ⟨1, _⟩ => (⟨5, 275, 65535⟩, none)
  | .u,  ⟨2, _⟩ => (⟨76, 337920, 0⟩, some (76, 337920, (-1 : ℤ)))
  | .d,  ⟨0, _⟩ => (⟨9, 5, 42⟩, none)
  | .d,  ⟨1, _⟩ => (⟨9, 186, 1023⟩, none)
  | .d,  ⟨2, _⟩ => (⟨5, 8191, 65535⟩, none)
  | .nuR, ⟨0, _⟩ => (⟨2, 5, 5⟩, none)
  | .nuR, ⟨1, _⟩ => (⟨7, 11, 13⟩, none)
  | .nuR, ⟨2, _⟩ => (⟨17, 19, 23⟩, none)
  | .nuL, ⟨0, _⟩ => (⟨1, 1, 823⟩, none)
  | .nuL, ⟨1, _⟩ => (⟨9, 1, 1023⟩, none)
  | .nuL, ⟨2, _⟩ => (⟨5, 1, 65535⟩, none)

/-- Total parity of a canonical family triple at generation `g`. -/
def smFamilyParity (f : SMFamily) (g : Fin 3) : Fin 2 :=
  match smFamilyTriple f g with
  | (t, none) => totalParityNat t.a t.b t.c
  | (_, some (a, b, c)) => totalParitySigned a b c

/-- Canonical CUP-4 ordering of the five families. -/
def canonicalFamilyOrder : Fin 5 → SMFamily
  | 0 => .e | 1 => .u | 2 => .d | 3 => .nuR | 4 => .nuL

/-- Parity ring state built from a family ordering at generation `g`. -/
def parityRingOfOrder (order : Fin 5 → SMFamily) (g : Fin 3) : Fin 5 → Fin 2 :=
  fun i => smFamilyParity (order i) g

/-- Parity ring for the canonical CUP-4 ordering. -/
def canonicalParityGen (g : Fin 3) : Fin 5 → Fin 2 :=
  parityRingOfOrder canonicalFamilyOrder g

/-- **gte_orbit_parity_provenance** (CatAL): total parities of the fifteen canonical
    cascade triples reproduce the certified `smGen1` / `smGen2` / `smGen3` vectors. -/
theorem gte_orbit_parity_provenance :
    canonicalParityGen ⟨0, by decide⟩ = smGen1 ∧
    canonicalParityGen ⟨1, by decide⟩ = smGen2 ∧
    canonicalParityGen ⟨2, by decide⟩ = smGen3 := by
  refine ⟨?_, ?_, ?_⟩
  · funext i; fin_cases i <;> native_decide
  · funext i; fin_cases i <;> native_decide
  · funext i; fin_cases i <;> native_decide

-- ════════════════════════════════════════════════════════════════
-- §2  Multilinear GF(7) class and orbit interpolation
-- ════════════════════════════════════════════════════════════════

/-- Fixed monomial order: constant, `L`, `C`, `R`, `LC`, `LR`, `CR`, `LCR`. -/
private def monomialExps : Array (ℕ × ℕ × ℕ) :=
  #[(0, 0, 0), (1, 0, 0), (0, 1, 0), (0, 0, 1),
    (1, 1, 0), (1, 0, 1), (0, 1, 1), (1, 1, 1)]

/-- Decode an id in `0 … 7⁸−1` to multilinear coefficients in the fixed monomial order. -/
def decodeMultilinearCoeffs (id : ℕ) : Array (ZMod 7) :=
  Array.ofFn fun (k : Fin 8) =>
    ⟨(id / Nat.pow 7 k.val % 7), Nat.mod_lt _ (by decide)⟩

/-- Evaluate a multilinear GF(7) rule at `(L,C,R)`. -/
def evalMultilinear (coeffs : Array (ZMod 7)) (L C R : ℕ) : ZMod 7 :=
  (List.range 8).foldl (fun acc n =>
    let (eL, eC, eR) := monomialExps[n]!
    acc + coeffs[n]! * ((L : ZMod 7) ^ eL * (C : ZMod 7) ^ eC * (R : ZMod 7) ^ eR)) 0

/-- Coefficient vector of `p(L,C,R) = C + R − C·R − L·C·R` in the fixed monomial order. -/
def polyPCoeffs : Array (ZMod 7) :=
  #[0, 0, 1, 1, 0, 0, -1, -1]

/-- One orbit ring-evaluation constraint on the multilinear class. -/
private def orbitConstraintRow (src dst : Fin 5 → Fin 2) (i : Fin 5) :
    Array (ZMod 7) × ZMod 7 :=
  let L := src (i + 4)
  let C := src i
  let R := src (i + 1)
  let row := Array.ofFn fun (k : Fin 8) =>
    let (eL, eC, eR) := monomialExps[k]!
    (L.val : ZMod 7) ^ eL * (C.val : ZMod 7) ^ eC * (R.val : ZMod 7) ^ eR
  (row, (dst i : ZMod 7))

/-- All ten orbit rows from the canonical parity ring. -/
private def orbitRows : Array (Array (ZMod 7) × ZMod 7) :=
  (List.range 10).foldl
    (fun acc k =>
      let step := if k < 5 then (0 : ℕ) else 1
      let i := ⟨k % 5, by omega⟩
      let src := if step = 0 then smGen1 else smGen2
      let dst := if step = 0 then smGen2 else smGen3
      acc.push (orbitConstraintRow src dst i))
    (#[] : Array (Array (ZMod 7) × ZMod 7))

/-- Dot product of coefficient vector with one constraint row. -/
private def rowDot (coeffs : Array (ZMod 7)) (row : Array (ZMod 7)) : ZMod 7 :=
  (List.range 8).foldl (fun acc n => acc + coeffs[n]! * row[n]!) 0

/-- A multilinear rule satisfies the canonical orbit constraints. -/
def satisfiesOrbitConstraints (coeffs : Array (ZMod 7)) : Bool :=
  orbitRows.all fun ⟨row, b⟩ => decide (rowDot coeffs row = b)

/-- A multilinear rule satisfies orbit + vacuum transparency. -/
def satisfiesOrbitVTConstraints (coeffs : Array (ZMod 7)) : Bool :=
  satisfiesOrbitConstraints coeffs && decide (evalMultilinear coeffs 0 0 0 = 0)

/-- Count multilinear survivors in `0 … 7⁸−1` under a predicate. -/
private def countMultilinearSurvivors (pred : Array (ZMod 7) → Bool) : ℕ :=
  (List.range (7 ^ 8)).foldl
    (fun acc id => if pred (decodeMultilinearCoeffs id) then acc + 1 else acc) 0

private def orbitOnlySurvivorCount : ℕ :=
  countMultilinearSurvivors satisfiesOrbitConstraints

private def orbitVTSurvivorCount : ℕ :=
  countMultilinearSurvivors satisfiesOrbitVTConstraints

/-- The unique orbit+VT survivor is `polyPCoeffs`. -/
private def orbitVTUniqueIsP : Bool :=
  (List.range (7 ^ 8)).all fun id =>
    let coeffs := decodeMultilinearCoeffs id
    decide (satisfiesOrbitVTConstraints coeffs = true ↔ coeffs = polyPCoeffs)

/-- **orbit_interpolation_vandermonde_full_rank** (CatAL): exhaustive `7⁸` census —
    orbit-only leaves `7` survivors; orbit + vacuum transparency leaves `1` survivor `p`. -/
theorem orbit_interpolation_vandermonde_full_rank :
    orbitOnlySurvivorCount = 7 ∧
    orbitVTSurvivorCount = 1 ∧
    orbitVTUniqueIsP = true ∧
    satisfiesOrbitVTConstraints polyPCoeffs = true := by
  native_decide

/-- **ugp_orbit_interpolation_lift** (CatAL): among all `7⁸` multilinear GF(7) rules,
    exactly one satisfies the parity-orbit ring evaluations together with vacuum
    transparency; it is `p`.  Without vacuum transparency, exactly seven survive. -/
theorem ugp_orbit_interpolation_lift :
    orbitOnlySurvivorCount = 7 ∧
    orbitVTSurvivorCount = 1 ∧
    orbitVTUniqueIsP = true ∧
    satisfiesOrbitVTConstraints polyPCoeffs = true ∧
    evalMultilinear polyPCoeffs 0 0 0 = 0 := by
  have h := orbit_interpolation_vandermonde_full_rank
  exact ⟨h.1, h.2.1, h.2.2.1, h.2.2.2, by native_decide⟩

/-- `evalMultilinear polyPCoeffs` agrees with `poly_p` on all `GF(7)` inputs. -/
theorem evalMultilinear_eq_poly_p (L C R : ZMod 7) :
    evalMultilinear polyPCoeffs L.val C.val R.val = poly_p L C R := by
  unfold evalMultilinear polyPCoeffs poly_p monomialExps
  fin_cases L <;> fin_cases C <;> fin_cases R <;> decide

-- ════════════════════════════════════════════════════════════════
-- §3  Rule 110 as corollary of the lift
-- ════════════════════════════════════════════════════════════════

/-- **interpolation_lift_binary_corollary** (CatAL): the certified interpolant's binary
    restriction is Rule 110 — derived from the lift, not assumed. -/
theorem interpolation_lift_binary_corollary :
    ∀ L C R : Bool,
      bool_to_z7 (rule110_output L C R) =
        evalMultilinear polyPCoeffs (if L then 1 else 0) (if C then 1 else 0) (if R then 1 else 0) := by
  intro L C R; cases L <;> cases C <;> cases R <;> native_decide

/-- Alias packaging the CUP-4 uniqueness chain with the lift corollary. -/
theorem cup4_parity_uniqueness_from_lift :
    (∀ r : Fin 256,
      (elementaryCAStep r smGen1 = smGen2 ∧
       elementaryCAStep r smGen2 = smGen3 ∧
       r.val % 2 = 0) ↔ r = 110) ∧
    (∀ L C R : Bool,
      bool_to_z7 (rule110_output L C R) =
        evalMultilinear polyPCoeffs (if L then 1 else 0) (if C then 1 else 0) (if R then 1 else 0)) := by
  exact ⟨cup4_parity_uniqueness, interpolation_lift_binary_corollary⟩

-- ════════════════════════════════════════════════════════════════
-- §4  Exponent flattening and MDL sparsity floor
-- ════════════════════════════════════════════════════════════════

/-- Support class of a monomial exponent triple: each positive exponent is collapsed to `1`. -/
def flattenSupport (eL eC eR : ℕ) : ℕ × ℕ × ℕ :=
  (if 0 < eL then 1 else 0, if 0 < eC then 1 else 0, if 0 < eR then 1 else 0)

/-- Exponent flattening on a coefficient vector. -/
def flattenCoeffs (coeffs : Array (ZMod 7)) : Array (ZMod 7) :=
  Array.ofFn fun (k : Fin 8) =>
    (List.range 8).foldl (fun acc n =>
      if flattenSupport (monomialExps[n]!.1) (monomialExps[n]!.2.1) (monomialExps[n]!.2.2) =
         monomialExps[k.val]! then
        acc + coeffs[n]!
      else acc) 0

/-- Number of nonzero flattened support classes. -/
def flattenedSupportCount (coeffs : Array (ZMod 7)) : ℕ :=
  (List.range 8).foldl (fun acc n =>
    if (flattenCoeffs coeffs)[n]! ≠ 0 then acc + 1 else acc) 0

/-- `poly_p` has exactly four nonzero support classes. -/
theorem poly_p_support_class_count : flattenedSupportCount polyPCoeffs = 4 := by
  native_decide

/-- Rule-110 agreement on all eight binary neighbourhoods. -/
private def agreesWithRule110 (coeffs : Array (ZMod 7)) : Bool :=
  (List.range 8).all fun n =>
    let L : Bool := n / 4 % 2 == 1
    let C : Bool := n / 2 % 2 == 1
    let R : Bool := n % 2 == 1
    decide (bool_to_z7 (rule110_output L C R) =
      evalMultilinear coeffs (if L then 1 else 0) (if C then 1 else 0) (if R then 1 else 0))

private def rule110BinarySurvivorCount : ℕ :=
  countMultilinearSurvivors agreesWithRule110

/-- Among multilinear rules, Rule-110 agreement on `{0,1}³` has exactly one survivor. -/
private def rule110BinaryUniqueIsP : Bool :=
  (List.range (7 ^ 8)).all fun id =>
    let coeffs := decodeMultilinearCoeffs id
    decide (agreesWithRule110 coeffs = true ↔ coeffs = polyPCoeffs)

/-- **lift_interpolant_sparsity_floor** (CatAL): within the multilinear GF(7) class, Rule-110
    agreement on `{0,1}³` forces the unique interpolant `p`, whose flattened form has exactly
    four nonzero support classes — the MDL sparsity floor. -/
theorem rule110_binary_interp_unique :
    rule110BinarySurvivorCount = 1 ∧ rule110BinaryUniqueIsP = true := by
  native_decide

theorem lift_interpolant_sparsity_floor :
    rule110BinarySurvivorCount = 1 ∧
    rule110BinaryUniqueIsP = true ∧
    flattenedSupportCount polyPCoeffs = 4 ∧
    flattenCoeffs polyPCoeffs = polyPCoeffs := by
  exact ⟨rule110_binary_interp_unique.1, rule110_binary_interp_unique.2,
    poly_p_support_class_count, by native_decide⟩

/-- The MDL sparsity floor stated from the Rule-110 side: within the multilinear
    class, Rule-110 binary agreement forces the four-support-class interpolant. -/
alias rule110_lift_sparsity_floor := lift_interpolant_sparsity_floor

-- ════════════════════════════════════════════════════════════════
-- §5  Chirality census over 120 family orderings
-- ════════════════════════════════════════════════════════════════

/-- Build a `Fin 5 → SMFamily` from a five-element ordering list. -/
private def orderFromList (xs : List SMFamily) : Fin 5 → SMFamily :=
  fun i => xs[i.val]!

/-- All `5! = 120` family orderings. -/
private def allFamilyOrders : List (Fin 5 → SMFamily) :=
  (List.permutations [.e, .u, .d, .nuR, .nuL]).map orderFromList

/-- Parity ring for one ordering at generation `g`. -/
private def parityRingForOrder (order : Fin 5 → SMFamily) (g : Fin 3) : Fin 5 → Fin 2 :=
  fun i => smFamilyParity (order i) g

/-- Vacuum-transparent orbit survivors for one ordering. -/
private def vtSurvivorsForOrder (order : Fin 5 → SMFamily) : List ℕ :=
  let g1 := parityRingForOrder order ⟨0, by decide⟩
  let g2 := parityRingForOrder order ⟨1, by decide⟩
  let g3 := parityRingForOrder order ⟨2, by decide⟩
  (List.range 256).filterMap fun r =>
    if h : r < 256 then
      let rule : Fin 256 := ⟨r, h⟩
      if elementaryCAStep rule g1 = g2 ∧
         elementaryCAStep rule g2 = g3 ∧
         r % 2 = 0 then some r else none
    else none

/-- Reversed family ordering (chirality reflection on the ring). -/
private def reverseOrder (order : Fin 5 → SMFamily) : Fin 5 → SMFamily :=
  fun i => order ⟨4 - i.val, by omega⟩

/-- Distinct vacuum-transparent rules across all orderings. -/
private def censusDistinctVTRules : List ℕ :=
  allFamilyOrders.foldl
    (fun acc order =>
      (vtSurvivorsForOrder order).foldl
        (fun a r => if a.contains r then a else r :: a) acc)
    []

private def censusOrderingsWithVT : ℕ :=
  allFamilyOrders.foldl
    (fun acc order => if (vtSurvivorsForOrder order).length > 0 then acc + 1 else acc) 0

/-- Reflection bijection certificate. -/
private def reflectionBijectionCert : Bool :=
  allFamilyOrders.all fun order =>
    let fwd := vtSurvivorsForOrder order
    let rev := vtSurvivorsForOrder (reverseOrder order)
    decide ((110 ∈ fwd ↔ 124 ∈ rev) ∧ (124 ∈ fwd ↔ 110 ∈ rev))

/-- **orbit_chirality_census** (CatAL): over all `120` family orderings, exactly `20`
    admit a vacuum-transparent orbit rule; the survivor union is `{110, 124}`; reversal
    bijects the `110`-orderings onto the `124`-orderings. -/
theorem orbit_chirality_census :
    censusOrderingsWithVT = 20 ∧
    (110 ∈ censusDistinctVTRules ∧ 124 ∈ censusDistinctVTRules ∧
      ∀ r ∈ censusDistinctVTRules, r = 110 ∨ r = 124) ∧
    reflectionBijectionCert = true := by
  native_decide

/-- Chirality census connects to the certified `AGL(1,7)` reflection swap. -/
theorem orbit_chirality_census_reflection_link :
    (110 ∈ censusDistinctVTRules ∧ 124 ∈ censusDistinctVTRules) ∧
    (∀ l c r : Fin 2, rule124 l c r = rule110 r c l) := by
  rcases orbit_chirality_census with ⟨_, hdist, _⟩
  rcases hdist with ⟨h110, h124, _⟩
  refine ⟨⟨h110, h124⟩, ?_⟩
  intro l c r
  exact rule124_eq_rule110_reflected l c r

end UgpLean.Universality.TriangleLiftTheorem
