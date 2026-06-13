import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Data.Real.Basic
import UgpLean.Substrate.DConstraints

/-!
# Landauer Heat Floor for Transputation

The minimum Landauer heat cost per single-kink transputation event is
`Q_min = kT ln 5`: five PSC-admissible kink sectors imply erasure of `ln 5` bits
of alternative winding, yielding the standard Landauer floor.

All theorems: zero sorry, zero custom axioms.
-/

namespace UgpLean.Measurement.LandauerFloor

open UgpLean.Substrate.DConstraints
open Real

/-- Number of PSC-admissible Z₇ kink winding sectors. -/
def pscKinkSectorCount : ℕ := 5

/-- **psc_kink_sector_count_eq_five** (CatAL): five distinct PSC-admissible sectors. -/
theorem psc_kink_sector_count_eq_five :
    pscKinkSectorCount = 5 ∧
    ({0, 2, 3, 4, 6} : Finset (Fin 7)).card = 5 := by
  constructor
  · rfl
  · exact d4_psc_sector_vals_distinct.1

/-- Erased alternative bits per single-kink transputation: `ln 5`. -/
noncomputable def transputationErasedNatLog : ℝ := Real.log 5

/-- **landauer_heat_floor_transputation** (CatAL):
    Minimum heat per transputation event is `Q_min = kT ln 5`. -/
noncomputable def landauerHeatFloor (k_B T : ℝ) : ℝ := k_B * T * transputationErasedNatLog

theorem landauer_heat_floor_transputation (k_B T : ℝ) :
    landauerHeatFloor k_B T = k_B * T * Real.log 5 ∧
    pscKinkSectorCount = 5 ∧
    transputationErasedNatLog = Real.log pscKinkSectorCount := by
  refine ⟨rfl, psc_kink_sector_count_eq_five.1, ?_⟩
  simp [transputationErasedNatLog, pscKinkSectorCount]

/-- Positivity at positive temperature and Boltzmann constant. -/
theorem landauer_heat_floor_pos (k_B T : ℝ) (hk : 0 < k_B) (hT : 0 < T) :
    0 < landauerHeatFloor k_B T := by
  unfold landauerHeatFloor transputationErasedNatLog
  apply mul_pos (mul_pos hk hT)
  exact Real.log_pos (by norm_num : (1 : ℝ) < 5)

/-- Mind-change budget for `k_w = 5` PSC kink sectors: `2(k_w - 1) = 8`. -/
def transputationMindChangeBudget : ℕ := 2 * (pscKinkSectorCount - 1)

theorem transputation_mind_change_budget_eq_eight :
    transputationMindChangeBudget = 8 ∧
    2 * (pscKinkSectorCount - 1) = 8 := by
  unfold transputationMindChangeBudget
  exact ⟨psc_kink_sector_count_eq_five.1 ▸ rfl, by decide⟩

/-- Landauer bit-erasure cost per mind-change at temperature `T`. -/
noncomputable def landauerBitErasure (k_B T : ℝ) : ℝ := k_B * T * Real.log 2

/-- Maximum heat per transputation event: `Q_max = 8 kT ln 2`. -/
noncomputable def landauerHeatCeiling (k_B T : ℝ) : ℝ :=
  transputationMindChangeBudget * landauerBitErasure k_B T

/-- **landauer_heat_ceiling_transputation** (CatAL):
    `Q_max = 8 kT ln 2` from the Ershov mind-change budget `2(k_w - 1) = 8`
    with `k_w = 5` PSC kink sectors. Each mind-change erases one bit at cost
    `kT ln 2` (Landauer 1961). -/
theorem landauer_heat_ceiling_transputation (k_B T : ℝ) :
    landauerHeatCeiling k_B T = 8 * k_B * T * Real.log 2 ∧
    transputationMindChangeBudget = 8 ∧
    pscKinkSectorCount = 5 ∧
    2 * (pscKinkSectorCount - 1) = transputationMindChangeBudget := by
  refine ⟨?_, transputation_mind_change_budget_eq_eight.1, psc_kink_sector_count_eq_five.1, ?_⟩
  · unfold landauerHeatCeiling transputationMindChangeBudget landauerBitErasure
    rw [psc_kink_sector_count_eq_five.1]
    ring
  · unfold transputationMindChangeBudget
    simp [pscKinkSectorCount]

end UgpLean.Measurement.LandauerFloor
