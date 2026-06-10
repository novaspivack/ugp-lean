import Mathlib.Tactic
import UgpLean.Polynomial.PolyExplorations
import UgpLean.Polynomial.DynamicalZeta
import UgpLean.Polynomial.SpinSevenGroundSpace

open UgpLean.Polynomial.PolyExplorations
open UgpLean.Polynomial.DynamicalZeta
open UgpLean.Polynomial.SpinSevenGroundSpace

/-!
# Spin-7 directed wall spectroscopy

Certifies the directed minimal-interface table of the spin-7 pair digraph
(49 nodes `(a,b) ∈ (ℤ/7ℤ)²`, edge `(a,b) → (b,c)` weighted by the local triple
energy `p(a,b,c) = C + R − C·R − L·C·R`), the composite hub identity
`E_w(5→1) = E_w(5→0) + E_w(0→1)`, the bump (closed-excursion) table
`E_loop ∈ {2,3,4}`, and the half-integer gap exponent
`(E_w(0→1) + E_w(1→0))/2 = 3/2`.

Finite shortest-path facts — bounded Bellman–Ford search with 48 rounds on the
49-node digraph (positive integer weights ≤ 6, minimal wall energies ≤ 4).

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Polynomial.SpinSevenWallSpectroscopy

/-- Pair state `(a,b)` on the spin-7 de Bruijn window. -/
abbrev SpinPair := Fin 7 × Fin 7

/-- Local triple energy `p(L,C,R)` as a natural number in `{0,…,6}`. -/
def tripleEnergy (L C R : Fin 7) : ℕ :=
  (poly_p_fin7 L C R).val

private def spinPairIndex (v : SpinPair) : Fin 49 :=
  ⟨v.1.val * 7 + v.2.val, by
    have h1 : v.1.val < 7 := v.1.isLt
    have h2 : v.2.val < 7 := v.2.isLt
    omega⟩

private def indexSpinPair (i : Fin 49) : SpinPair :=
  (⟨i.val / 7, by omega⟩, ⟨i.val % 7, by omega⟩)

private structure DistTable where
  data : Fin 49 → Option ℕ
  deriving Inhabited

private def DistTable.set (t : DistTable) (i : Fin 49) (v : Option ℕ) : DistTable :=
  ⟨fun j => if j = i then v else t.data j⟩

private def initDists (src : SpinPair) : DistTable :=
  ⟨fun i => if indexSpinPair i = src then some 0 else none⟩

private def relaxOneNode (d : DistTable) (i : Fin 49) : DistTable :=
  match d.data i with
  | none => d
  | some du =>
    let u := indexSpinPair i
    (List.finRange 7).foldl (fun acc fc =>
      let j := spinPairIndex (u.2, fc)
      let nd := du + tripleEnergy u.1 u.2 fc
      match acc.data j with
      | none => acc.set j (some nd)
      | some dv => if nd < dv then acc.set j (some nd) else acc) d

private def relaxAll (d : DistTable) : DistTable :=
  (List.finRange 49).foldl relaxOneNode d

private def bellmanFordDist (src : SpinPair) : DistTable :=
  Nat.iterate relaxAll 48 (initDists src)

/-- Shortest-path distance from `src` to `tgt` on the weighted pair digraph. -/
def minDistFromTo (src tgt : SpinPair) : ℕ :=
  match (bellmanFordDist src).data (spinPairIndex tgt) with
  | some n => n
  | none => 999

/-- Minimal directed wall energy from uniform sector `g` to distinct sector `gp`. -/
def directedWallEnergy (g gp : Fin 7) : ℕ :=
  minDistFromTo (g, g) (gp, gp)

/-- Minimal positive-weight closed excursion from the uniform self-loop `(g,g)`. -/
def loopBumpEnergy (g : Fin 7) : ℕ :=
  (List.finRange 7).foldl (fun best fc =>
    let w0 := tripleEnergy g g fc
    let back := minDistFromTo (g, fc) (g, g)
    let total := w0 + back
    if 0 < total && (best = 0 || total < best) then total else best) 0

-- ════════════════════════════════════════════════════════════════
-- §1  Directed minimal-interface table
-- ════════════════════════════════════════════════════════════════

theorem directed_wall_energy_one_to_zero :
    directedWallEnergy 1 0 = 1 := by native_decide

theorem directed_wall_energy_zero_to_one :
    directedWallEnergy 0 1 = 2 := by native_decide

theorem directed_wall_energy_five_to_zero :
    directedWallEnergy 5 0 = 2 := by native_decide

theorem directed_wall_energy_zero_to_five :
    directedWallEnergy 0 5 = 4 := by native_decide

theorem directed_wall_energy_one_to_five :
    directedWallEnergy 1 5 = 4 := by native_decide

theorem directed_wall_energy_five_to_one :
    directedWallEnergy 5 1 = 4 := by native_decide

theorem directed_wall_energy_five_to_one_composite :
    directedWallEnergy 5 1 =
      directedWallEnergy 5 0 + directedWallEnergy 0 1 := by native_decide

/-- **directed_wall_energy_table** (CatAL — native_decide):
    The six directed minimal-interface energies between ground sectors `{0,1,5}`. -/
theorem directed_wall_energy_table :
    directedWallEnergy 1 0 = 1 ∧
      directedWallEnergy 0 1 = 2 ∧
        directedWallEnergy 5 0 = 2 ∧
          directedWallEnergy 0 5 = 4 ∧
            directedWallEnergy 1 5 = 4 ∧
              directedWallEnergy 5 1 = 4 ∧
                directedWallEnergy 5 1 =
                  directedWallEnergy 5 0 + directedWallEnergy 0 1 := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- §2  Bump (closed-excursion) table
-- ════════════════════════════════════════════════════════════════

theorem loop_bump_energy_zero : loopBumpEnergy 0 = 2 := by native_decide

theorem loop_bump_energy_one : loopBumpEnergy 1 = 3 := by native_decide

theorem loop_bump_energy_five : loopBumpEnergy 5 = 4 := by native_decide

/-- **loop_bump_energy_table** (CatAL — native_decide):
    Minimal positive-weight closed excursions from each uniform self-loop. -/
theorem loop_bump_energy_table :
    loopBumpEnergy 0 = 2 ∧
      loopBumpEnergy 1 = 3 ∧
        loopBumpEnergy 5 = 4 := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- §3  Half-integer gap exponent
-- ════════════════════════════════════════════════════════════════

/-- **directed_wall_half_integer_gap** (CatAL — native_decide):
    The geometric mean of the directed 0↔1 fugacities is the half-integer `3/2`. -/
theorem directed_wall_half_integer_gap :
    (directedWallEnergy 0 1 + directedWallEnergy 1 0 : ℚ) / 2 = 3 / 2 := by
  native_decide

/-- **spin7_directed_wall_energies** (CatAL — master bundle):
    Directed wall table, composite hub identity, bump table, and half-integer gap. -/
theorem spin7_directed_wall_energies :
    directedWallEnergy 1 0 = 1 ∧
      directedWallEnergy 0 1 = 2 ∧
        directedWallEnergy 5 0 = 2 ∧
          directedWallEnergy 0 5 = 4 ∧
            directedWallEnergy 1 5 = 4 ∧
              directedWallEnergy 5 1 = 4 ∧
                directedWallEnergy 5 1 = directedWallEnergy 5 0 + directedWallEnergy 0 1 ∧
                  loopBumpEnergy 0 = 2 ∧
                    loopBumpEnergy 1 = 3 ∧
                      loopBumpEnergy 5 = 4 ∧
                        (directedWallEnergy 0 1 + directedWallEnergy 1 0 : ℚ) / 2 = 3 / 2 := by
  native_decide

end UgpLean.Polynomial.SpinSevenWallSpectroscopy
