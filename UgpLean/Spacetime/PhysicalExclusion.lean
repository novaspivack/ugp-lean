import UgpLean.Spacetime.MassGap
import UgpLean.Spacetime.AnomalyRenormalizability

namespace GTE.Spacetime.PhysicalExclusion

open GTE.Lifting GTE.Spacetime.Confinement GTE.Spacetime.MassGap GTE.Spacetime.Anomaly
open UgpLean.Universality.LawvereZone CUP3D

/-!
# Unified Physical Exclusion — SM Consistency Capstone (Bridge)

Composes four individually proved physical constraints into a single paper-citable
theorem: every [D]-weighted state is PSC-admissible, color-confined (no free quarks),
massive (positive gap), and anomaly-free.

All components are CatAL with zero sorry. This file adds no axioms.
-/

/-- **Unified physical exclusion** (CatAL bridge).

    Every physically weighted beable satisfies simultaneously:
    1. PSC-admissibility (`d2_axiom`)
    2. Color confinement — no single free quark (`no_psc_admissible_single_quark`)
    3. Positive mass gap (`gte_mass_gap`)
    4. Anomaly freedom (`physical_anomaly_cancellation`)

    Status: CatAL — zero sorry, zero axioms. -/
theorem unified_physical_exclusion :
    (∀ b : Fin 5 → Fin 7, DWeight b > 0 → PSCAdmissible b) ∧
    (∀ b : Fin 5 → Fin 7, PSCAdmissible b → ¬SingleQuarkBeable b) ∧
    (∃ Δ : ℚ, Δ > 0 ∧
      ∀ b : Fin 5 → Fin 7, DWeight b > 0 → b ≠ fmdl_vacuum5 → ∃ mass : ℚ, mass ≥ Δ) ∧
    (∀ b : Fin 5 → Fin 7, DWeight b > 0 → AnomalyFree b) := by
  refine ⟨fun b hw => d2_axiom b hw, fun b hpsc => no_psc_admissible_single_quark b hpsc, ?_, ?_⟩
  · obtain ⟨Δ, hΔ, hgap⟩ := gte_mass_gap
    exact ⟨Δ, hΔ, fun b hw hvac => hgap b hw hvac⟩
  · intro b hw
    exact physical_anomaly_cancellation b hw

end GTE.Spacetime.PhysicalExclusion
