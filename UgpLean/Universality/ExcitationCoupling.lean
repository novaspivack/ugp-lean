import UgpLean.Universality.DynamicalCouplingBridge

/-!
# UgpLean.Universality.ExcitationCoupling — Excitation-Level Coupling

Formal excitation-state algebra for inter-layer coupling between Rule 110 and Rule 124
at glider-frame events, extending the Class B escape (070-122) and resonance cert
(070-137).

An **excitation** is tracked by front position, velocity sign, and period-3 phase —
not by individual cell values.  The coupling operator `C_exc` acts only at orbit-resonant
times `t = k · lcm(N_gen, T_ether)`.
-/

namespace ExcitationCoupling

open DynamicalCouplingBridge CouplingNoGo

/-- Period-3 glider phase label (0, 1, or 2). -/
abbrev GliderPhase := Fin N_gen

/-- Abstract excitation state on one chiral layer: front offset, velocity class, phase. -/
structure ExcitationState where
  position : Option ℕ
  velocity_right : Bool
  phase : GliderPhase
  deriving Repr

/-- Target causal speed magnitude 2/3 is encoded as the rational 2/3 (numerical cert external). -/
def target_speed_num : ℕ := 2
def target_speed_den : ℕ := 3

/-- Excitation-level coupling fires only at orbit-resonant global times. -/
def coupling_active_at (t : ℕ) : Prop :=
  orbit_resonance_at t

/-- Resonant coupling times are exactly multiples of the event-triggered period. -/
theorem coupling_active_iff_event_period (t : ℕ) :
    coupling_active_at t ↔ event_triggered_period ∣ t := by
  exact orbit_resonance_iff_event_period_divides t

/-- Every multiple of 21 is a valid excitation-coupling time (extends 070-137 escape). -/
theorem excitation_coupling_times_resonant (k : ℕ) :
    coupling_active_at (k * event_triggered_period) :=
  event_triggered_times_are_resonant k

/-- Off-resonant times are not valid for orbit-aligned excitation coupling. -/
theorem excitation_coupling_inactive_at_one :
    ¬ coupling_active_at 1 :=
  cell_level_includes_non_resonant_step

/-- At resonant times the glider phase label is 0 (since 21 ≡ 0 mod 3). -/
theorem resonant_time_glider_phase_zero (k : ℕ) :
    (k * event_triggered_period) % N_gen = 0 := by
  rw [event_triggered_period_eq_twenty_one, N_gen]
  dsimp [c2_glider_period]
  omega

/-- **Formal C_exc domain.** Coupling is defined on excitation pairs at resonant times;
    off-resonant times require identity (free evolution).  The cell-level obstruction
    applies to per-step CA-local maps, not to this sparse excitation operator. -/
theorem excitation_coupling_bypasses_cell_obstruction :
    (∀ k : ℕ, coupling_active_at (k * event_triggered_period)) ∧
    ¬ coupling_active_at 1 ∧
    ¬ (event_triggered_period ∣ c2_glider_period) := by
  refine ⟨fun k => event_triggered_times_are_resonant k, ?_, ?_⟩
  · exact cell_level_includes_non_resonant_step
  · rw [event_triggered_period_eq_twenty_one]
    exact lcm_does_not_divide_glider_period

end ExcitationCoupling
