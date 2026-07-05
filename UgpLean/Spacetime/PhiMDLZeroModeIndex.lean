import Mathlib.Data.Real.Basic
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import UgpLean.Physics.ZSevenVacuumSelection

/-!
# PhiMDLZeroModeIndex: Callias index vanishes for cos(7φ) Yukawa coupling (Case A)

Certifies the algebraic core of the Session 8 Dirac index theorem on GTE kink backgrounds.
The Python mirror is `yukawa_dirac_index_kink.py`.

**Physical content (Case A):** For the Z₇-invariant Yukawa profile `f(φ) = cos(7φ)`, the
Dirac mass term `M(x) = g · cos(7φ_K(x))` equals `g` at every Z₇ vacuum
`φ_k = 2πk/7` because `cos(7φ_k) = cos(2πk) = 1`. Hence at both asymptotic ends of a
kink connecting vacuum `0` to vacuum `n`, `M(±∞) = g` with the same sign, and the
Callias spectral-flow index `½[sign M(+∞) − sign M(−∞)]` vanishes.

**Case B** (`f = sin(7φ)`, `f = sin²(7φ/2)`, or `∂_xφ`): boundary mass vanishes;
asymptotically massless Dirac analysis shows no normalizable zero mode. That analytic
route is CatAD and is not formalized here (Mathlib lacks half-line Dirac spectral theory).

Level framing: Level 3 obstruction certificate — the JR/Yukawa zero-mode route is
blocked for Z₇-periodic GTE kinks; fermionic statistics follow triple exchange (P48).
This module certifies only the finite Callias boundary-value core (Case A, CatAL).
-/

namespace GTE.Spacetime.PhiMDLZeroModeIndex

open Real
open UgpLean.Physics.ZSevenVacuumSelection (vacuumAngle)

noncomputable section

/-- Z₇-invariant Yukawa profile `f(φ) = cos(7φ)` evaluated at vacuum `φ_k = 2πk/7`. -/
def cosineYukawaAtVacuum (k : Fin 7) : ℝ :=
  cos (7 * vacuumAngle k)

/-- Dirac mass `M = g · f(φ)` at a Z₇ vacuum. -/
def diracMassAtVacuum (g : ℝ) (k : Fin 7) : ℝ :=
  g * cosineYukawaAtVacuum k

/-- Callias index from asymptotic Dirac mass values (1+1D Jackiw–Rebbi convention). -/
def calliasIndex (M_minus M_plus : ℝ) : ℝ :=
  (1 / 2) * (sign M_plus - sign M_minus)

theorem seven_times_vacuum_angle (k : Fin 7) :
    (7 : ℝ) * vacuumAngle k = (k.val : ℤ) * (2 * π) := by
  unfold vacuumAngle
  push_cast
  ring

/-- At every Z₇ vacuum, `cos(7φ_k) = 1`. -/
theorem cosine_yukawa_at_vacuum (k : Fin 7) : cosineYukawaAtVacuum k = 1 := by
  unfold cosineYukawaAtVacuum
  rw [seven_times_vacuum_angle, Real.cos_int_mul_two_pi]

theorem dirac_mass_at_vacuum_eq_g (g : ℝ) (k : Fin 7) :
    diracMassAtVacuum g k = g := by
  unfold diracMassAtVacuum
  rw [cosine_yukawa_at_vacuum, mul_one]

theorem yukawa_cos7_boundary_values_equal (g : ℝ) (n : Fin 7) :
    diracMassAtVacuum g ⟨0, by decide⟩ = diracMassAtVacuum g n := by
  rw [dirac_mass_at_vacuum_eq_g, dirac_mass_at_vacuum_eq_g]

theorem callias_index_zero_equal_masses (M : ℝ) :
    calliasIndex M M = 0 := by
  unfold calliasIndex
  ring

theorem callias_index_zero_same_sign (M : ℝ) :
    (1 / 2) * (sign M - sign M) = 0 := by
  ring

/-- **zero_mode_index_vanishes_for_cosine_coupling** (CatAL, Case A): for
    `M(x) = g · cos(7φ_K(x))` on a kink connecting vacuum `0` to vacuum `n`, the
    Callias index vanishes because `M(−∞) = M(+∞) = g`. Requires `g ≠ 0` only for
    the physical mass term; the index vanishes identically as a sign-difference. -/
theorem zero_mode_index_vanishes_for_cosine_coupling (g : ℝ) (n : Fin 7) :
    calliasIndex (diracMassAtVacuum g ⟨0, by decide⟩) (diracMassAtVacuum g n) = 0 := by
  rw [yukawa_cos7_boundary_values_equal]
  exact callias_index_zero_equal_masses (diracMassAtVacuum g n)

theorem zero_mode_index_vanishes_for_cosine_coupling_alt (g : ℝ) (n : Fin 7) :
    (1 / 2) * (sign (diracMassAtVacuum g n) - sign (diracMassAtVacuum g ⟨0, by decide⟩)) = 0 := by
  have h := zero_mode_index_vanishes_for_cosine_coupling g n
  unfold calliasIndex at h
  exact h

/-- Bundle: Z₇ vacuum boundary values for `cos(7φ)` and Callias index zero. -/
theorem phimdl_zero_mode_index_cosine_certificate (g : ℝ) (n : Fin 7) :
    (∀ k : Fin 7, cosineYukawaAtVacuum k = 1) ∧
    diracMassAtVacuum g ⟨0, by decide⟩ = g ∧
    diracMassAtVacuum g n = g ∧
    calliasIndex (diracMassAtVacuum g ⟨0, by decide⟩) (diracMassAtVacuum g n) = 0 := by
  refine ⟨fun k => cosine_yukawa_at_vacuum k, ?_⟩
  refine ⟨dirac_mass_at_vacuum_eq_g g ⟨0, by decide⟩, ?_⟩
  exact ⟨dirac_mass_at_vacuum_eq_g g n, zero_mode_index_vanishes_for_cosine_coupling g n⟩

end

end GTE.Spacetime.PhiMDLZeroModeIndex
