import Mathlib.Data.Finset.Basic
import Mathlib.Tactic
import UgpLean.Universality.CUP3DUniqueness
import UgpLean.Universality.LawvereZone

namespace GTE.Universality.PSCOrbitWindows

open CUP3D UgpLean.Universality.LawvereZone

/-!
# PSC Orbit 3-Cell Windows — OQ-G1-LEAN2

The PSC-admissible 5-cell beables are exactly `{vacuum, gen₁, gen₂, gen₃}`
(`psc_admissible_iff_orbit`, CatAL).

Each non-vacuum generation beable carries exactly one **generic-sector** 3-cell window
(all three components distinct). The remaining four sliding windows are two-equal
(two components equal, third distinct). Vacuum windows are all-equal.

Two-equal F₂₁-orbit canonical representatives on Z₇³ are disjoint from the PSC
generic windows. Hence degenerate F₂₁ orbits are not PSC-selected for the
log|F₂₁| MDL weight — they receive the Z₃-reduced log|Z₇| contribution instead
(OQ-G1-MECHANISM-FORMAL, CatAD; disjointness in `Z3SubOrbitDisjointness`).
-/

/-- A 3-cell window is generic-sector: all three components distinct. -/
def IsGenericTriple (l c r : Fin 7) : Prop :=
  l ≠ c ∧ c ≠ r ∧ l ≠ r

/-- A 3-cell window is two-equal: exactly two components equal, not all three. -/
def IsTwoEqualTriple (l c r : Fin 7) : Prop :=
  (l = c ∧ c ≠ r) ∨ (l = r ∧ l ≠ c) ∨ (c = r ∧ c ≠ l)

/-- A 3-cell window is all-equal. -/
def IsAllEqualTriple (l c r : Fin 7) : Prop :=
  l = c ∧ c = r

instance decidableIsGenericTriple (l c r : Fin 7) : Decidable (IsGenericTriple l c r) := by
  unfold IsGenericTriple
  infer_instance

instance decidableIsTwoEqualTriple (l c r : Fin 7) : Decidable (IsTwoEqualTriple l c r) := by
  unfold IsTwoEqualTriple
  infer_instance

instance decidableIsAllEqualTriple (l c r : Fin 7) : Decidable (IsAllEqualTriple l c r) := by
  unfold IsAllEqualTriple
  infer_instance

private def isGenericTriple (t : Fin 7 × Fin 7 × Fin 7) : Bool :=
  t.1 ≠ t.2.1 && t.2.1 ≠ t.2.2 && t.1 ≠ t.2.2

private def isTwoEqualTriple (t : Fin 7 × Fin 7 × Fin 7) : Bool :=
  (t.1 == t.2.1 && t.2.1 != t.2.2) ||
    (t.1 == t.2.2 && t.1 != t.2.1) ||
      (t.2.1 == t.2.2 && t.2.1 != t.1)

private def isAllEqualTriple (t : Fin 7 × Fin 7 × Fin 7) : Bool :=
  t.1 == t.2.1 && t.2.1 == t.2.2

/-- Periodic 3-cell sliding window at position `i` on a 5-cell ring. -/
def window3 (b : Fin 5 → Fin 7) (i : Fin 5) : Fin 7 × Fin 7 × Fin 7 :=
  (b i, b (i + 1), b (i + 2))

private def allWindows (b : Fin 5 → Fin 7) : List (Fin 7 × Fin 7 × Fin 7) :=
  List.ofFn fun i : Fin 5 => window3 b i

private def countGenericWindows (b : Fin 5 → Fin 7) : ℕ :=
  (allWindows b).filter isGenericTriple |>.length

private def countTwoEqualWindows (b : Fin 5 → Fin 7) : ℕ :=
  (allWindows b).filter isTwoEqualTriple |>.length

private def countAllEqualWindows (b : Fin 5 → Fin 7) : ℕ :=
  (allWindows b).filter isAllEqualTriple |>.length

/-- Generic-sector windows of the three PSC generation beables. -/
def pscGenericWindows : Finset (Fin 7 × Fin 7 × Fin 7) :=
  {window3 fmdl_gen1_z7 0, window3 fmdl_gen2_z7 1, window3 fmdl_gen3_z7 1}

/-- Canonical representatives of the six two-equal F₂₁ orbits on Z₇³: `(a,a,b)` with `a < b`. -/
def twoEqualOrbitReps : Finset (Fin 7 × Fin 7 × Fin 7) :=
  {(0, 0, 1), (0, 0, 2), (0, 0, 3), (0, 0, 4), (0, 0, 5), (0, 0, 6)}

/-- gen₁ has exactly one generic-sector 3-cell window: `(1,5,2)`. -/
theorem gen1_one_generic_window : countGenericWindows fmdl_gen1_z7 = 1 := by native_decide

/-- gen₂ has exactly one generic-sector 3-cell window: `(5,2,0)`. -/
theorem gen2_one_generic_window : countGenericWindows fmdl_gen2_z7 = 1 := by native_decide

/-- gen₃ has exactly one generic-sector 3-cell window: `(6,5,3)`. -/
theorem gen3_one_generic_window : countGenericWindows fmdl_gen3_z7 = 1 := by native_decide

/-- Each generation beable has four two-equal sliding windows. -/
theorem gen_beables_four_two_equal_windows :
    countTwoEqualWindows fmdl_gen1_z7 = 4 ∧
      countTwoEqualWindows fmdl_gen2_z7 = 4 ∧
      countTwoEqualWindows fmdl_gen3_z7 = 4 := by
  native_decide

/-- Vacuum has five all-equal `(0,0,0)` windows and no generic or two-equal windows. -/
theorem vacuum_all_equal_windows :
    countAllEqualWindows fmdl_vacuum5 = 5 ∧
      countGenericWindows fmdl_vacuum5 = 0 ∧
      countTwoEqualWindows fmdl_vacuum5 = 0 := by
  native_decide

/-- The PSC generic windows are exactly `(1,5,2)`, `(5,2,0)`, `(6,5,3)`. -/
theorem psc_generic_windows_eq :
    pscGenericWindows =
      ({(1, 5, 2), (5, 2, 0), (6, 5, 3)} : Finset (Fin 7 × Fin 7 × Fin 7)) := by
  native_decide

/-- Each listed PSC generic window is generic-sector (all components distinct). -/
theorem psc_generic_window_values :
    IsGenericTriple 1 5 2 ∧ IsGenericTriple 5 2 0 ∧ IsGenericTriple 6 5 3 := by
  refine ⟨by decide, by decide, by decide⟩

/-- **OQ-G1-LEAN2:** No two-equal F₂₁-orbit canonical representative is a PSC generic window.

    Two-equal F₂₁ orbits on Z₇³ are PSC-non-selected for the full log|F₂₁| MDL weight.
    Combined with `Z3SubOrbitDisjointness.z7_suborbit_disjoint_z3_conjugate`, this
    certifies the Z₃-reduced log|Z₇| weight for degenerate orbits in the G formula. -/
theorem two_equal_orbits_not_psc_selected :
    Disjoint twoEqualOrbitReps pscGenericWindows := by
  native_decide

/-- Bundle: non-vacuum PSC generation beables each have one generic and four two-equal windows. -/
theorem psc_generation_window_structure :
    countGenericWindows fmdl_gen1_z7 = 1 ∧
      countGenericWindows fmdl_gen2_z7 = 1 ∧
      countGenericWindows fmdl_gen3_z7 = 1 ∧
      countTwoEqualWindows fmdl_gen1_z7 = 4 ∧
      countTwoEqualWindows fmdl_gen2_z7 = 4 ∧
      countTwoEqualWindows fmdl_gen3_z7 = 4 ∧
      Disjoint twoEqualOrbitReps pscGenericWindows := by
  native_decide

end GTE.Universality.PSCOrbitWindows
