import Mathlib

/-!
# UgpLean.Gravity.EtherProperTimeRate — proper-time rate τ = 3/7 from Rule 110

The CMCA proper-time rate `τ = τ_proper/τ_lab = 3/7` (P45 §clock) is derived here
**directly from the Rule 110 vacuum-background (ether) dynamics**, not asserted as
`N_spatial/|Z₇|`.

The canonical Rule 110 ether is the period-14 spatial background pattern
`[1,1,1,1,1,0,0,0,1,0,0,1,1,0]`. Under one Rule 110 update it left-translates by
exactly 4 cells (`ether_is_rule110_orbit`); since `4·t ≡ 0 (mod 14)` first at
`t = 14/gcd(4,14) = 7`, the temporal period at any fixed cell is exactly 7
(`ether_period_seven`). Over one period, a fixed cell visits the seven ether
positions of its own parity class; the gate (proper-time tick) fires iff the
ether cell is in state 1. Counting the 1-cells of the ether by parity gives

  odd-parity cell: fires 3 of 7 steps  →  τ = 3/7   (`tau_proper_rate`)
  even-parity cell: fires 5 of 7 steps →      5/7
  global ether average:                        4/7.

All statements are `decide`-checked over the explicit pattern: zero axioms,
zero sorry. The denominator 7 is forced (drift 4, spatial period 14) and equals
the ether's intrinsic period — which is exactly why the Z₇ winding is
`w = τ_c mod 7`. The numerator 3 is the odd-parity 1-count, forced by the ether
pattern. The only physical input is the odd-parity identification of the
proper-time-carrying cell (P45).
-/

namespace UgpLean.Gravity.EtherProperTimeRate

/-- Elementary cellular-automaton Rule 110 as a Boolean function of the
    `(left, center, right)` neighbourhood (Wolfram code `0b01101110`). -/
def r110 (l c r : Bool) : Bool :=
  match l, c, r with
  | true,  true,  true  => false
  | true,  true,  false => true
  | true,  false, true  => true
  | true,  false, false => false
  | false, true,  true  => true
  | false, true,  false => true
  | false, false, true  => true
  | false, false, false => false

/-- The canonical Rule 110 vacuum-background (ether) tile, period-14 spatial:
    `1 1 1 1 1 0 0 0 1 0 0 1 1 0`. -/
def ether : Fin 14 → Bool :=
  ![true, true, true, true, true, false, false, false,
    true, false, false, true, true, false]

/-- One Rule 110 update on a cyclic length-14 lattice (`Fin 14` arithmetic wraps
    mod 14, realising periodic boundary conditions). -/
def step (s : Fin 14 → Bool) : Fin 14 → Bool :=
  fun i => r110 (s (i - 1)) (s i) (s (i + 1))

/-- **The ether is a genuine Rule 110 orbit.** One update equals a left-shift by
    exactly 4 cells: `step ether i = ether (i + 4)` for all `i`. -/
theorem ether_is_rule110_orbit : step ether = fun i => ether (i + 4) := by decide

/-- **Temporal period 7.** Iterating the Rule 110 update seven times returns the
    ether to itself (it has drifted `4·7 = 28 ≡ 0 (mod 14)`). -/
theorem ether_period_seven : step^[7] ether = ether := by decide

/-- The period is the *smallest* positive return time: `step^[k] ether ≠ ether`
    for `0 < k < 7`. Hence the intrinsic period is exactly 7. -/
theorem ether_period_minimal :
    step^[1] ether ≠ ether ∧ step^[2] ether ≠ ether ∧ step^[3] ether ≠ ether ∧
    step^[4] ether ≠ ether ∧ step^[5] ether ≠ ether ∧ step^[6] ether ≠ ether := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩ <;> decide

/-- The period `7` is `14 / gcd(4,14)`: forced by drift 4 and spatial period 14,
    and equal to the order of the Z₇ winding group (`w = τ_c mod 7`). -/
theorem ether_period_formula : 14 / Nat.gcd 4 14 = 7 := by decide

/-- **Odd-parity gate-fire count = 3.** Of the seven odd-index ether cells,
    exactly three are in state 1. -/
theorem ether_odd_fire_count :
    (Finset.univ.filter (fun i : Fin 14 => i.val % 2 = 1 ∧ ether i = true)).card = 3 := by
  decide

/-- **Even-parity gate-fire count = 5.** Of the seven even-index ether cells,
    exactly five are in state 1. -/
theorem ether_even_fire_count :
    (Finset.univ.filter (fun i : Fin 14 => i.val % 2 = 0 ∧ ether i = true)).card = 5 := by
  decide

/-- **Global ether 1-count = 8 = 3 + 5** (average fire rate 8/14 = 4/7). -/
theorem ether_total_fire_count :
    (Finset.univ.filter (fun i : Fin 14 => ether i = true)).card = 8 := by decide

/-- **Proper-time rate over one period for a fixed odd cell.** Because one Rule 110
    step is a 4-shift (`ether_is_rule110_orbit`), after `t` steps a fixed cell `i`
    reads `ether (i + 4t)`; over the period `t = 0,…,6` an odd cell visits exactly
    the seven odd ether positions. Hence its gate-fire count over one period equals
    the odd-parity 1-count of the ether, which is 3 (`ether_odd_fire_count`). -/
def oddFireCount : ℕ :=
  (Finset.univ.filter (fun i : Fin 14 => i.val % 2 = 1 ∧ ether i = true)).card

theorem oddFireCount_eq_three : oddFireCount = 3 := by decide

/-- The proper-time rate of an odd-parity cell, defined as (gate-fire count over
    one period) / (temporal period 7). -/
def tauProper : ℚ := (oddFireCount : ℚ) / 7

/-- **τ = 3/7.** The proper-time rate of an odd-parity ether cell equals the
    gate-fire count (3, certified by `oddFireCount_eq_three`) divided by the
    temporal period (7). This is the exact CMCA-dynamical origin of the P45
    special-relativistic time-dilation ratio. -/
theorem tau_proper_rate : tauProper = 3 / 7 := by
  unfold tauProper
  rw [oddFireCount_eq_three]
  norm_num

/-- The proper-time rate is strictly less than 1 (proper time runs slower than
    coordinate time — the CMCA realisation of Lorentz time dilation). -/
theorem tau_lt_one : (3 : ℚ) / 7 < 1 := by norm_num

/-- The three gate-fire rates partition the unit interval as the ether 1-count
    splits by parity: odd `3/7`, even `5/7`, average `4/7`. -/
theorem fire_rates_consistent :
    (3 : ℚ) / 7 + 5 / 7 = 8 / 7 ∧ (8 : ℚ) / 7 / 2 = 4 / 7 := by
  constructor <;> norm_num

/-- **Master bundle (zero axioms, zero sorry).** The proper-time rate `τ = 3/7`
    follows from the Rule 110 ether dynamics: a genuine orbit (4-shift), period 7,
    odd-parity fire-count 3. -/
theorem tau_three_sevenths_from_ether :
    step ether = (fun i => ether (i + 4)) ∧
    step^[7] ether = ether ∧
    (Finset.univ.filter (fun i : Fin 14 => i.val % 2 = 1 ∧ ether i = true)).card = 3 ∧
    (3 : ℚ) / 7 < 1 := by
  exact ⟨ether_is_rule110_orbit, ether_period_seven, ether_odd_fire_count, tau_lt_one⟩

end UgpLean.Gravity.EtherProperTimeRate
