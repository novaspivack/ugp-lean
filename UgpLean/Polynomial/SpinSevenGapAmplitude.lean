import Mathlib.Tactic
import UgpLean.Polynomial.PolyExplorations
import UgpLean.Polynomial.SpinSevenWallSpectroscopy

open UgpLean.Polynomial.PolyExplorations
open UgpLean.Polynomial.SpinSevenWallSpectroscopy

/-!
# Spin-7 gap-amplitude combinatorial certificate

The transfer-matrix gap of the spin-7 chain obeys the exact asymptotic law
`Δ(β) = A·e^(−3β/2)·(1 + (b₀/2)·e^(−β/2) + O(e^(−β)))` with amplitude
`A = √(c₁₀·c₀₁)`, where the structure constants are *through-walk counts* on
the 49-node pair digraph (edge `(a,b) → (b,c)` weighted `p(a,b,c)`):

* `c₁₀` — walks from the ground loop `(1,1)` to `(0,0)` of total weight 1
  whose interior states avoid all three ground loops `{(0,0),(1,1),(5,5)}`;
* `c₀₁` — through-walks `(0,0) → (1,1)` of total weight 2;
* `b₀, b₁, b₅` — closed through-excursions (bumps) from `(0,0)`, `(1,1)`,
  `(5,5)` of weights 2, 3, 4 respectively.

Counting is carried out in the weight-truncation semiring `ℕ[t]/(t⁵)`
(coefficient arrays of length 5), with frontiers materialized as strict
arrays.  Through-walks are accumulated to length 47; the *frontier-death
certificate* (`wall_frontier_death`) shows the weight-≤4 interior frontier
vanishes after 45 steps, and `through_counts_vanish_beyond` extends the
totality to all lengths, so the certified values are the full counts:

`c₁₀ = 1`, `c₀₁ = 1` (hence `A² = 1`: amplitude exactly 1), `b₀ = 1`
(hence first correction coefficient `1/2`), `b₁ = 1`, and `b₅ = 2`
(the spectator eigenvalue `λ₂ = 1 + 2e^(−4β) + …`).

These counts are the inputs to the analytic degenerate-perturbation
derivation (Schur complement on the ground multiplet with the
nilpotent-resolvent expansion); the eigenvalue ordering and the Puiseux
expansion are analytic statements documented with the derivation.

Zero sorry.  Zero custom axioms.
-/

namespace UgpLean.Polynomial.SpinSevenGapAmplitude

/-- Weight-truncation semiring carrier `ℕ[t]/(t⁵)`: strict coefficient
    arrays of length 5 (weights 0,…,4). -/
abbrev Wt := Array ℕ

def wtZero : Wt := Array.replicate 5 0

def wtAdd (x y : Wt) : Wt :=
  Array.ofFn (n := 5) fun k => x.getD k.val 0 + y.getD k.val 0

/-- Truncated convolution product on `ℕ[t]/(t⁵)`. -/
def wtMul (x y : Wt) : Wt :=
  Array.ofFn (n := 5) fun k =>
    (List.range (k.val + 1)).foldl
      (fun acc i => acc + x.getD i 0 * y.getD (k.val - i) 0) 0

/-- Weight monomial `t^w` (zero in the quotient when `w ≥ 5`). -/
def wtMono (w : ℕ) : Wt :=
  Array.ofFn (n := 5) fun k => if k.val = w then 1 else 0

/-- Interior pair states: everything except the three ground self-loops. -/
def isInterior (v : SpinPair) : Bool :=
  decide (v ≠ ((0 : Fin 7), (0 : Fin 7)) ∧ v ≠ ((1 : Fin 7), (1 : Fin 7)) ∧
    v ≠ ((5 : Fin 7), (5 : Fin 7)))

/-- Frontier vector over the 49 pair states (index `a·7 + b`), materialized
    as a strict array of weight-graded counts. -/
abbrev Vw := Array Wt

def vwZero : Vw := Array.replicate 49 wtZero

def pairIdx (v : SpinPair) : ℕ := v.1.val * 7 + v.2.val

private def idxPair (i : Fin 49) : SpinPair :=
  (⟨i.val / 7, by omega⟩, ⟨i.val % 7, by omega⟩)

/-- One interior step: frontier mass flows along edges `(a,b) → (b,c)`
    weighted `t^{p(a,b,c)}`, between interior states only. -/
def stepRight (x : Vw) : Vw :=
  Array.ofFn (n := 49) fun vi =>
    let v := idxPair vi
    if isInterior v then
      (List.finRange 7).foldl
        (fun acc a =>
          let u : SpinPair := (a, v.1)
          if isInterior u then
            wtAdd acc (wtMul (x.getD (pairIdx u) wtZero)
              (wtMono (tripleEnergy a v.1 v.2)))
          else acc)
        wtZero
    else wtZero

/-- First edge of a through-walk: `(g,g) → (g,c)` into an interior state. -/
def startFrom (g : Fin 7) : Vw :=
  Array.ofFn (n := 49) fun vi =>
    let v := idxPair vi
    if v.1 = g ∧ isInterior v then wtMono (tripleEnergy g g v.2) else wtZero

/-- Last edge of a through-walk: `(b,g') → (g',g')` from an interior state. -/
def endAt (gp : Fin 7) (x : Vw) : Wt :=
  (List.finRange 7).foldl
    (fun acc b =>
      let u : SpinPair := (b, gp)
      if isInterior u then
        wtAdd acc (wtMul (x.getD (pairIdx u) wtZero)
          (wtMono (tripleEnergy b gp gp)))
      else acc)
    wtZero

/-- Interior frontier after `k` interior steps. -/
def frontier (g : Fin 7) (k : ℕ) : Vw :=
  Nat.iterate stepRight k (startFrom g)

/-- Count (weight-graded) of through-walks of length `k + 2`. -/
def throughCount (g gp : Fin 7) (k : ℕ) : Wt :=
  endAt gp (frontier g k)

/-- Accumulated (count, frontier) state: linear-time cumulative counting. -/
def throughState (g gp : Fin 7) : ℕ → Wt × Vw
  | 0 => (endAt gp (startFrom g), startFrom g)
  | k + 1 =>
    let s := throughState g gp k
    let fr' := stepRight s.2
    (wtAdd s.1 (endAt gp fr'), fr')

/-- Total weight-graded through-walk count up to length `K + 2`. -/
def cumThrough (g gp : Fin 7) (K : ℕ) : Wt :=
  (throughState g gp K).1

-- ════════════════════════════════════════════════════════════════
-- §1  Frontier death: the weight-≤4 interior frontier dies at 45 steps
-- ════════════════════════════════════════════════════════════════

/-- **wall_frontier_death** (CatAL — native_decide): from each ground loop,
    the weight-≤4 interior frontier is empty after 45 steps. -/
theorem wall_frontier_death :
    frontier 0 45 = vwZero ∧ frontier 1 45 = vwZero ∧
      frontier 5 45 = vwZero := by native_decide

/-- The zero frontier is a fixed point of the interior step (concrete
    array computation). -/
theorem stepRight_vwZero : stepRight vwZero = vwZero := by native_decide

/-- The zero frontier produces zero terminal counts at every sector. -/
theorem endAt_vwZero : ∀ gp : Fin 7, endAt gp vwZero = wtZero := by
  native_decide

theorem frontier_death_persists (g : Fin 7) (h : frontier g 45 = vwZero) :
    ∀ k, 45 ≤ k → frontier g k = vwZero := by
  intro k hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction m with
  | zero => simpa using h
  | succ m ih =>
    have hstep : (45 : ℕ) + (m + 1) = (45 + m) + 1 := by omega
    rw [hstep]
    simp only [frontier, Function.iterate_succ_apply']
    have hm := ih (by omega)
    simp only [frontier] at hm
    rw [hm]
    exact stepRight_vwZero

/-- **through_counts_vanish_beyond** (zero sorry): no through-walk of length
    `> 47` contributes at weights ≤ 4 — the accumulated counts are total. -/
theorem through_counts_vanish_beyond (g gp : Fin 7)
    (hg : frontier g 45 = vwZero) :
    ∀ k, 45 ≤ k → throughCount g gp k = wtZero := by
  intro k hk
  unfold throughCount
  rw [frontier_death_persists g hg k hk]
  exact endAt_vwZero gp

-- ════════════════════════════════════════════════════════════════
-- §2  The certified structure constants
-- ════════════════════════════════════════════════════════════════

/-- **minimal_wall_count_one_to_zero** (CatAL — native_decide):
    `c₁₀ = 1` — the weight-1 through-wall `1 → 0` is unique. -/
theorem minimal_wall_count_one_to_zero :
    (cumThrough 1 0 45).getD 1 0 = 1 := by native_decide

/-- **minimal_wall_count_zero_to_one** (CatAL — native_decide):
    `c₀₁ = 1` — the weight-2 through-wall `0 → 1` is unique. -/
theorem minimal_wall_count_zero_to_one :
    (cumThrough 0 1 45).getD 2 0 = 1 := by native_decide

/-- **bump_count_sector_zero** (CatAL — native_decide): `b₀ = 1` — the
    weight-2 closed through-excursion from the vacuum loop is unique; the
    leading gap-law correction coefficient is `b₀/2 = 1/2`. -/
theorem bump_count_sector_zero :
    (cumThrough 0 0 45).getD 2 0 = 1 := by native_decide

/-- **bump_count_sector_one** (CatAL — native_decide): `b₁ = 1`. -/
theorem bump_count_sector_one :
    (cumThrough 1 1 45).getD 3 0 = 1 := by native_decide

/-- **bump_count_sector_five** (CatAL — native_decide): `b₅ = 2` — the
    spectator eigenvalue tail `λ₂ = 1 + 2e^(−4β) + …`. -/
theorem bump_count_sector_five :
    (cumThrough 5 5 45).getD 4 0 = 2 := by native_decide

-- ════════════════════════════════════════════════════════════════
-- §3  The amplitude identity
-- ════════════════════════════════════════════════════════════════

/-- **gap_amplitude_sq_unit** (CatAL): `A² = c₁₀·c₀₁ = 1` — the gap-law
    amplitude is exactly 1.  (Analytic content: the Perron multiplet splits
    as `λ± = 1 ± √(c₁₀c₀₁)·e^(−3β/2) + …` while the spectator sector 5 sits
    between them at `λ₂ = 1 + b₅·e^(−4β)`, so
    `Δ = ln(λ₁/λ₂) = √(c₁₀c₀₁)·e^(−3β/2)(1 + (b₀/2)e^(−β/2) + O(e^(−β)))`.) -/
theorem gap_amplitude_sq_unit :
    (cumThrough 1 0 45).getD 1 0 * (cumThrough 0 1 45).getD 2 0 = 1 := by
  rw [minimal_wall_count_one_to_zero, minimal_wall_count_zero_to_one]

/-- **gap_amplitude_correction_half** (CatAL): the leading correction
    coefficient of the gap law is `b₀/2 = 1/2` exactly (as a rational). -/
theorem gap_amplitude_correction_half :
    ((cumThrough 0 0 45).getD 2 0 : ℚ) / 2 = 1 / 2 := by
  rw [bump_count_sector_zero]
  norm_num

/-- **spin7_gap_amplitude_certificate** (CatAL — master bundle):
    the complete combinatorial core of the gap-amplitude theorem:
    unique minimal through-walls (`c₁₀ = c₀₁ = 1`, hence `A = 1`),
    bump constants (`b₀ = b₁ = 1`, `b₅ = 2`), and frontier death
    (totality of the counts). -/
theorem spin7_gap_amplitude_certificate :
    (cumThrough 1 0 45).getD 1 0 = 1 ∧
      (cumThrough 0 1 45).getD 2 0 = 1 ∧
        (cumThrough 0 0 45).getD 2 0 = 1 ∧
          (cumThrough 1 1 45).getD 3 0 = 1 ∧
            (cumThrough 5 5 45).getD 4 0 = 2 ∧
              (frontier 0 45 = vwZero ∧ frontier 1 45 = vwZero ∧
                frontier 5 45 = vwZero) :=
  ⟨minimal_wall_count_one_to_zero, minimal_wall_count_zero_to_one,
    bump_count_sector_zero, bump_count_sector_one, bump_count_sector_five,
    wall_frontier_death⟩

end UgpLean.Polynomial.SpinSevenGapAmplitude
