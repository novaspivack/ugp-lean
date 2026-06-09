import UgpLean.Universality.MDLDerivabilityCriterion
import UgpLean.Algebra.SRRGCABridge
import UgpLean.Universality.CUP3DUniqueness
import UgpLean.Polynomial.PolyExplorations
import Transputation.Theorems.ForcedAdjudication

/-!
# MDL Three-Level Unification

The formula P^⊤(X) = argmin K(x | PSC constraints) operates at three nested physical levels,
with the GTE polynomial `p` as the connecting object (P51).

| Level | Transition | Certification |
|-------|------------|---------------|
| 0→1 | Theory selection (Z_N×Z_M CA rule space) | `mdl_ca_rule_coding_closed` |
| 1→2 | Field dynamics (SRRG adjudication fixed point) | `gte_poly_srrg_bridge` |
| 2→3 | Measurement (PSC-projection orbit + adjudication) | `psc_projection_gives_fmdl`, `fmdl_orbit_is_unique_psc_trajectory` |

Level 2→3 adjudication forcing (transputation under PSC + record-divergent choice) is certified
by `closed_choice_forces_transputation` from transputation-lean (hypothesis-bearing).
-/

namespace UgpLean.Polynomial.MDLThreeLevelUnification

open UgpLean.Universality.MDLDerivability
open SRRGCABridge
open CUP3D
open UgpLean.Polynomial.PolyExplorations

/-- **mdl_level23_closed_choice_forces_transputation** (CatAL — transputation-lean wrapper):
    Under PSC closure and record-divergent choice, an internal adjudicator (transputation)
    is forced. Direct alias of `Transputation.Theorems.closed_choice_forces_transputation`. -/
theorem mdl_level23_closed_choice_forces_transputation
    {F : NemS.Framework} {IsInternal : F.Selector → Prop}
    (psc : NemS.MFRR.PSCBundle F IsInternal)
    (cd : NemS.MFRR.ChoiceData F)
    (hChoice : NemS.MFRR.HasRecordDivergentChoice F cd) :
    ∃ _pt : NemS.MFRR.PT F IsInternal, True :=
  Transputation.Theorems.closed_choice_forces_transputation psc cd hChoice

/-- **mdl_three_level_unification** (CatAL — cross-module bundle, zero sorry):

The Three-Level MDL Unification bundle for P51:

(a) **Level 0→1 (theory selection):** MDL selects the Z₇×Z₃ CA substrate over Z₅×Z₃
    — `mdl_ca_rule_coding_closed` (MDLDerivabilityCriterion).

(b) **Level 1→2 (field dynamics):** the diagonal self-referential fixed point satisfies
    x² + x = 1 at x = (√5−1)/2 — `gte_poly_srrg_bridge` (SRRGCABridge).

(c) **Cross-link (p → f_MDL):** the PSC-projection of `p` defines `fmdl` on free and
    binary neighborhoods — `psc_projection_gives_fmdl` (PolyExplorations).

(d) **Level 2→3 (measurement orbit):** the PSC-projection orbit gen₁→gen₂→gen₃→vacuum
    is unique under `fmdl_step5` — `fmdl_orbit_is_unique_psc_trajectory` (CUP3DUniqueness).

Adjudication forcing at Level 2→3 is certified separately by
`mdl_level23_closed_choice_forces_transputation` (transputation-lean dependency). -/
theorem mdl_three_level_unification :
    (∃ (K_data : ℕ → ℕ → ℕ),
      K_data 7 3 = z7GenerationDataPenalty ∧
        K_data 5 3 = z5GenerationDataPenalty ∧
          structureSpecCost 7 3 + K_data 7 3 <
            structureSpecCost 5 3 + K_data 5 3) ∧
      (let x := (Real.sqrt 5 - 1) / 2; x ^ 2 + x = 1) ∧
      (∀ L C R : Fin 7, ¬CUP3D.isFixedNeighborhood L C R → CUP3D.fmdl L C R = 0) ∧
      (∀ L C R : Fin 7,
        L ∈ GTE.Z7InvariantSubsets.binarySublayer →
          C ∈ GTE.Z7InvariantSubsets.binarySublayer →
            R ∈ GTE.Z7InvariantSubsets.binarySublayer →
              GTE.Z7InvariantSubsets.p_poly L C R = CUP3D.fmdl L C R) ∧
      (fmdl_step5 fmdl_gen1_z7 = fmdl_gen2_z7 ∧
        fmdl_step5 fmdl_gen2_z7 = fmdl_gen3_z7 ∧
        fmdl_step5 fmdl_gen3_z7 = (fun _ => 0) ∧
        (∀ s : Fin 5 → Fin 7, fmdl_step5 fmdl_gen1_z7 = s → s = fmdl_gen2_z7)) := by
  refine ⟨mdl_ca_rule_coding_closed, ?_, ?_, ?_, ?_⟩
  · exact gte_poly_srrg_bridge
  · exact psc_projection_gives_fmdl.1
  · exact psc_projection_gives_fmdl.2
  · exact ⟨fmdl_orbit_is_unique_psc_trajectory.1,
      fmdl_orbit_is_unique_psc_trajectory.2.1,
      fmdl_orbit_is_unique_psc_trajectory.2.2.1,
      fmdl_orbit_is_unique_psc_trajectory.2.2.2.1⟩

end UgpLean.Polynomial.MDLThreeLevelUnification
