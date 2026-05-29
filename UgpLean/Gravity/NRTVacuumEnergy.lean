import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Data.Real.Basic

/-!
# PSC Non-Renormalization Theorem — Level 1 (Topological Mass-Independence)

The Z₇ vacuum potential vanishes at every vacuum state Φ_k = 2πk/7,
and this vanishing is mass-independent: dV/dm² = 0 at all Z₇ vacua.

**Physical content:** mass renormalization in the Turing-decidable sector
cannot shift V(Φ_k) from zero. This is the algebraic foundation of the NRT:
the Z₇ superselection structure is stable against mass renormalization.

**Certification:** CatAL, zero sorry.
-/

namespace GTE.NRTVacuumEnergy

open Real

/-- V_{Z₇}(Φ_k) = (m²/49)(1 − cos(7Φ_k)) = 0 for all Z₇ vacuum states
    Φ_k = 2πk/7.  The vanishing is independent of m: dV/dm² = 0 at all vacua. -/
theorem z7_vacuum_energy_mass_independent (m : ℝ) (_hm : 0 < m) (k : Fin 7) :
    (m ^ 2 / 49) * (1 - Real.cos (7 * (2 * Real.pi * (k.val : ℝ) / 7))) = 0 := by
  have hcos : Real.cos (7 * (2 * Real.pi * (k.val : ℝ) / 7)) = 1 := by
    have hrw : 7 * (2 * Real.pi * (k.val : ℝ) / 7) = (k.val : ℝ) * (2 * Real.pi) := by
      ring
    rw [hrw]
    exact Real.cos_nat_mul_two_pi k.val
  rw [hcos]
  ring

/-- Corollary: the Z₇ potential vanishes at every vacuum regardless of m. -/
theorem z7_vacuum_zero_for_all_masses (k : Fin 7) :
    ∀ (m : ℝ), 0 < m →
    (m ^ 2 / 49) * (1 - Real.cos (7 * (2 * Real.pi * (k.val : ℝ) / 7))) = 0 :=
  fun m hm => z7_vacuum_energy_mass_independent m hm k

/-- The argument 7 · Φ_k is an integer multiple of 2π. -/
theorem z7_vacuum_phase_is_integer_multiple_of_two_pi (k : Fin 7) :
    ∃ (n : ℕ), 7 * (2 * Real.pi * (k.val : ℝ) / 7) = (n : ℝ) * (2 * Real.pi) := by
  exact ⟨k.val, by ring⟩

end GTE.NRTVacuumEnergy
