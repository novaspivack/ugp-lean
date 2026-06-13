import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic

/-!
# F₂₁ regular action on Fano-plane incidence flags

The Fano plane PG(2, GF(2)) has 7 points and 7 lines (Singer difference-set
translates of `{0,1,3}` in Z₇). Its 21 incidence flags `(point, line)` are acted
on simply transitively by F₂₁ = ℤ₇ ⋊ ℤ₃: points transform by `x ↦ 2^k·x + a`,
and lines transform as the induced set map on Singer translates.

All checks are finite `native_decide` proofs: zero sorry, zero custom axioms.

Level framing: Level 1 algebraic certificate (F₂₁ gauge skeleton group theory).
-/

namespace UgpLean.Algebra.FanoRegularAction

def fanoLine (shift : ZMod 7) : Finset (ZMod 7) :=
  {shift, shift + 1, shift + 3}

def fanoLines : Finset (Finset (ZMod 7)) :=
  { {0, 1, 3}, {1, 2, 4}, {2, 3, 5}, {3, 4, 6}, {4, 5, 0}, {5, 6, 1}, {6, 0, 2} }

theorem fano_line_count : fanoLines.card = 7 := by native_decide

theorem fano_lines_size_3 : ∀ L ∈ fanoLines, L.card = 3 := by native_decide

def isFlag (p : ZMod 7) (shift : ZMod 7) : Bool :=
  p ∈ fanoLine shift

def allFlags : Finset (ZMod 7 × ZMod 7) :=
  Finset.univ.filter (fun ps : ZMod 7 × ZMod 7 => isFlag ps.1 ps.2)

theorem fano_flag_count : allFlags.card = 21 := by native_decide

def z3Mult : ZMod 3 → ZMod 7 → ZMod 7
  | 0, x => x
  | 1, x => 2 * x
  | 2, x => 4 * x
  | _, x => x

def f21ActPoint (a : ZMod 7) (k : ZMod 3) (x : ZMod 7) : ZMod 7 :=
  z3Mult k x + a

def f21ActLine (a : ZMod 7) (k : ZMod 3) (shift : ZMod 7) : Finset (ZMod 7) :=
  (fanoLine shift).image (f21ActPoint a k)

/-- Select the unique Singer-line index for a given three-point line. -/
def lineIndexOf (L : Finset (ZMod 7)) : ZMod 7 :=
  if L = fanoLine 0 then 0
  else if L = fanoLine 1 then 1
  else if L = fanoLine 2 then 2
  else if L = fanoLine 3 then 3
  else if L = fanoLine 4 then 4
  else if L = fanoLine 5 then 5
  else 6

def f21ActShift (a : ZMod 7) (k : ZMod 3) (shift : ZMod 7) : ZMod 7 :=
  lineIndexOf (f21ActLine a k shift)

def f21ActFlag (a : ZMod 7) (k : ZMod 3) (ps : ZMod 7 × ZMod 7) : ZMod 7 × ZMod 7 :=
  (f21ActPoint a k ps.1, f21ActShift a k ps.2)

theorem f21_preserves_flags :
    ∀ (a : ZMod 7) (k : ZMod 3) (ps : ZMod 7 × ZMod 7),
      ps ∈ allFlags → f21ActFlag a k ps ∈ allFlags := by
  native_decide

def referenceFlag : ZMod 7 × ZMod 7 := (0, 0)

theorem ref_flag_is_flag : referenceFlag ∈ allFlags := by native_decide

def f21OrbitMap : ZMod 7 × ZMod 3 → ZMod 7 × ZMod 7 :=
  fun ak => f21ActFlag ak.1 ak.2 referenceFlag

theorem f21_orbit_injective : Function.Injective f21OrbitMap := by native_decide

theorem f21_orbit_surjective :
    ∀ f ∈ allFlags, ∃ ak : ZMod 7 × ZMod 3, f21OrbitMap ak = f := by native_decide

/-- **f21_regular_on_fano_flags** (CatAL):
    F₂₁ acts regularly (simply transitively) on the 21 Fano incidence flags. -/
theorem f21_regular_on_fano_flags :
    Function.Injective f21OrbitMap ∧
      (∀ f ∈ allFlags, ∃ ak : ZMod 7 × ZMod 3, f21OrbitMap ak = f) ∧
        allFlags.card = 21 :=
  ⟨f21_orbit_injective, f21_orbit_surjective, fano_flag_count⟩

end UgpLean.Algebra.FanoRegularAction
