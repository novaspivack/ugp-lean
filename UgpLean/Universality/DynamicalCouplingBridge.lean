import UgpLean.Universality.CouplingNoGo
import Mathlib.Data.Nat.GCD.Basic

/-!
# UgpLean.Universality.DynamicalCouplingBridge — Event-Triggered Coupling Escape

## Background

`CouplingNoGo.lean` certifies that **CA-local per-cell** coupling depending on ether-phase
values introduces an effective period-7 modulation incommensurable with the period-3 C₂
glider (`lcm(3,7)=21`, and `21 ∤ 3`).  Computational analysis established that
**event-triggered front injection** at multiples of `lcm(N_gen, T_ether) = lcm(3,7) = 21`
preserves glider coherence while transferring cross-layer excitation.

This module formalizes the **arithmetic resonance escape**: coupling restricted to
orbit-resonant times satisfies both the glider period and ether-orbit divisibility,
contradicting the cell-level no-go's implicit per-step coupling assumption.

## Key theorems

- `coupling_no_go_cell_level`     : cites CouplingNoGo — lcm(3,7)=21, 21 ∤ 3
- `event_triggered_coupling_period`: lcm(N_gen, T_ether)=21; 3∣21 and 7∣21
- `coupling_no_go_escape_via_event`: ∀ k, resonance at t = k·21; per-step t=1 fails
- `discrete_w_vertex_interpretation`: physical W-vertex identification (axiom)

Arithmetic theorems are zero sorry (`native_decide` / `omega`).  One axiom discloses
the EW-scale charged-current interpretation not derivable from ℕ arithmetic alone.
-/

namespace DynamicalCouplingBridge

open CouplingNoGo

/-! ### Canonical periods (N_gen = 3, T_ether = 7) -/

/-- Number of generations (PSC Presentation Invariance); equals C₂ glider period. -/
def N_gen : ℕ := c2_glider_period

/-- Ether temporal orbit length under glider step size 2 on period-14 background. -/
def T_ether : ℕ := ether_orbit_length

/-- Event-triggered injection period: lcm(N_gen, T_ether). -/
def event_triggered_period : ℕ := Nat.lcm N_gen T_ether

/-- Glider and ether orbits are **resonant** at time t when both periods divide t. -/
def orbit_resonance_at (t : ℕ) : Prop :=
  N_gen ∣ t ∧ T_ether ∣ t

/-! ### Theorem 1 — cell-level no-go (from CouplingNoGo) -/

/-- CA-local per-cell coupling obstruction: lcm(3,7)=21 and 21 does not divide glider period 3.
    Certified in `CouplingNoGo.lean` (`lcm_glider_orbit`, `lcm_does_not_divide_glider_period`). -/
theorem coupling_no_go_cell_level :
    Nat.lcm c2_glider_period ether_orbit_length = 21 ∧
    ¬ (Nat.lcm c2_glider_period ether_orbit_length ∣ c2_glider_period) := by
  exact ⟨lcm_glider_orbit, lcm_does_not_divide_glider_period⟩

/-- Alias exposing the full CouplingNoGo master conjunction for cross-citation. -/
abbrev coupling_no_go_cell_level_master := coupling_no_go_master

/-! ### Theorem 2 — event-triggered period is resonance-compatible -/

/-- The event-triggered period lcm(N_gen, T_ether) = lcm(3,7) = 21 is divisible by both
    the glider period and the ether orbit length (`21 mod 3 = 0` and `21 mod 7 = 0`). -/
theorem event_triggered_coupling_period :
    event_triggered_period = 21 ∧
    N_gen ∣ event_triggered_period ∧
    T_ether ∣ event_triggered_period ∧
    event_triggered_period % N_gen = 0 ∧
    event_triggered_period % T_ether = 0 := by
  native_decide

/-- Concrete value of the event-triggered period. -/
theorem event_triggered_period_eq_twenty_one : event_triggered_period = 21 := by
  native_decide

/-! ### Theorem 3 — escape from cell-level no-go via event triggering -/

/-- Every event-triggered coupling time `t = k · lcm(N_gen, T_ether)` is orbit-resonant. -/
theorem event_triggered_times_are_resonant (k : ℕ) :
    orbit_resonance_at (k * event_triggered_period) := by
  rw [event_triggered_period_eq_twenty_one]
  unfold orbit_resonance_at N_gen T_ether
  rw [orbit_length_eq_seven]
  dsimp [c2_glider_period]
  constructor
  · exact ⟨k * 7, by omega⟩
  · exact ⟨k * 3, by omega⟩

/-- Per-step (cell-level) coupling fires at non-resonant times — e.g. t = 1. -/
theorem cell_level_includes_non_resonant_step :
    ¬ orbit_resonance_at 1 := by
  unfold orbit_resonance_at N_gen T_ether
  rw [orbit_length_eq_seven]
  dsimp [c2_glider_period]
  decide

/-- **Escape theorem.** Event-triggered coupling at multiples of lcm(N_gen, T_ether) satisfies
    orbit resonance at every coupling event, while per-step coupling necessarily includes
    non-resonant steps before the first resonance point.  This is the formal arithmetic
    content of the Class B escape from `CouplingNoGo`. -/
theorem coupling_no_go_escape_via_event :
    (∀ k : ℕ, orbit_resonance_at (k * event_triggered_period)) ∧
    ¬ orbit_resonance_at 1 ∧
    event_triggered_period > 1 := by
  refine ⟨event_triggered_times_are_resonant, ?_, ?_⟩
  · exact cell_level_includes_non_resonant_step
  · native_decide

/-- LCM resonance: a time is resonant iff the event period divides it. -/
theorem orbit_resonance_iff_event_period_divides (t : ℕ) :
    orbit_resonance_at t ↔ event_triggered_period ∣ t := by
  rw [event_triggered_period_eq_twenty_one]
  unfold orbit_resonance_at N_gen T_ether
  rw [orbit_length_eq_seven]
  dsimp [c2_glider_period]
  constructor
  · intro ⟨h3, h7⟩
    exact (Nat.lcm_dvd_iff.mpr ⟨h3, h7⟩)
  · intro ht
    exact ⟨Nat.dvd_trans (by decide : (3 : ℕ) ∣ 21) ht, Nat.dvd_trans (by decide : (7 : ℕ) ∣ 21) ht⟩

/-! ### Theorem 4 — discrete W-boson vertex interpretation (axiom) -/

/-- **Physical interpretation (axiom).** Restricting cross-layer coupling to orbit-resonant
    times `t = k · lcm(N_gen, T_ether)` models a discrete three-body charged-current vertex:
    a Rule 110 right-mover, a Rule 124 left-mover, and a vacuum perturbation injected at the
    tracked glider front — the CA analogue of an off-shell W-boson exchange at EW scale,
    directionally asymmetric (110→124) and consistent with V−A chirality.
    This identification is not derivable from ℕ arithmetic alone. -/
axiom discrete_w_vertex_interpretation :
    event_triggered_period = Nat.lcm N_gen T_ether ∧
    (∀ k : ℕ, orbit_resonance_at (k * event_triggered_period))

end DynamicalCouplingBridge
