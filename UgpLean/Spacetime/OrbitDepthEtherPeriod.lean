import UgpLean.Universality.CUP3DUniqueness
import UgpLean.Spacetime.CausalInvariance
import UgpLean.Substrate.LExtended
import Rule110

/-!
# Orbit Depth = Ether Temporal Period via Z₇ Structure (Rank 070-110, CatAL)

Two independent routes to the integer **7**, both grounded in the GTE mod-7 ring:

1. **f_MDL orbit depth bound:** every state in Z₇⁵ decays to vacuum under `fmdl_step5`
   in at most 7 steps (`fmdl_max_depth_is_7`, CUP3DUniqueness).
2. **Rule 110 ether temporal period:** the Cook ether has spatial period 14 and drifts
   4 cells per outer CA step; the return period is `14 / gcd(4, 14) = 7`.

Both equal `z7SubstratePeriod = 7 = |ℤ₇|`.

Computational confirmation (Rank 95 CatA, EPIC_073 2026-05-25):
`research-sandbox/epic073_rank070_110_orbit_depth_ether_period.py`.

## Main theorems (zero sorry)

- `ether_temporal_period_eq_seven` — drift/spatial gcd arithmetic
- `orbit_depth_ether_period_z7_identity` — bundles max depth, temporal period, and |Z₇|
-/

namespace GTE.Spacetime.OrbitDepthEtherPeriod

open CUP3D
open UgpLean.Substrate.LExtended
open GTE.Spacetime.CausalInvariance

/-- Order of the GTE mod-7 arithmetic ring. -/
def z7Order : ℕ := 7

/-- Rule 110 ether spatial period in cells (Cook/Martinez catalog). -/
def etherSpatialPeriodCells : ℕ := etherSpatialPeriod

/-- Ether coordinate drift per outer CA step: three Rule 110 steps advance 42 → 54. -/
def etherDriftPerStep : ℕ := 4

/-- Temporal ether period: time steps until the drifting background returns to phase. -/
def etherTemporalPeriod : ℕ := etherSpatialPeriodCells / Nat.gcd etherDriftPerStep etherSpatialPeriodCells

theorem z7_order_eq_seven : z7Order = 7 := rfl

theorem ether_spatial_period_eq_fourteen : etherSpatialPeriodCells = 14 := rfl

/-- Three Cook ether steps advance the coordinate by 12 cells (42 → 54). -/
theorem ether_drift_three_steps_certified :
    Rule110.infRule110Steps 3 Rule110.cookEther 42 = Rule110.cookEther 54 := by
  native_decide

theorem ether_drift_per_step_eq_four : etherDriftPerStep = 4 := rfl

theorem gcd_ether_drift_spatial : Nat.gcd etherDriftPerStep etherSpatialPeriodCells = 2 := by
  native_decide

theorem ether_temporal_period_eq_seven : etherTemporalPeriod = 7 := by
  unfold etherTemporalPeriod etherSpatialPeriodCells etherDriftPerStep
  native_decide

theorem ether_outer_half_period_matches :
    etherOuterHalfPeriod = etherTemporalPeriod := by
  unfold etherOuterHalfPeriod etherTemporalPeriod etherSpatialPeriodCells etherDriftPerStep
  native_decide

theorem z7_substrate_period_matches_order :
    z7SubstratePeriod = z7Order := by
  unfold z7SubstratePeriod z7Order
  rfl

/-- **Rank 070-110 — structural Z₇ identity** (CatAL).

    The f_MDL maximum decay depth on Z₇⁵, the Rule 110 ether temporal period, and the
    GTE substrate period all equal 7 — the order of the fundamental mod-7 ring.

    Orbit route: coordinate-wise mod-7 dynamics ⇒ depth ≤ |Z₇| (certified max = 7).
    Ether route: spatial period 14 = 2 × 7 with drift gcd halving ⇒ temporal period 7. -/
theorem orbit_depth_ether_period_z7_identity :
    z7Order = 7 ∧
    z7SubstratePeriod = z7Order ∧
    etherSpatialPeriodCells = 14 ∧
    etherDriftPerStep = 4 ∧
    Nat.gcd etherDriftPerStep etherSpatialPeriodCells = 2 ∧
    etherTemporalPeriod = 7 ∧
    etherOuterHalfPeriod = etherTemporalPeriod ∧
    (∃ v : Fin 5 → Fin 7,
      fmdl_step5 (fmdl_step5 (fmdl_step5 (fmdl_step5
        (fmdl_step5 (fmdl_step5 v))))) ≠ (fun _ => (0 : Fin 7))) ∧
    (∀ v : Fin 5 → Fin 7,
      fmdl_step5 (fmdl_step5 (fmdl_step5 (fmdl_step5
        (fmdl_step5 (fmdl_step5 (fmdl_step5 v)))))) = (fun _ => (0 : Fin 7))) := by
  refine ⟨z7_order_eq_seven, z7_substrate_period_matches_order,
    ether_spatial_period_eq_fourteen, ether_drift_per_step_eq_four,
    gcd_ether_drift_spatial, ether_temporal_period_eq_seven,
    ether_outer_half_period_matches, ?_⟩
  exact fmdl_max_depth_is_7

end GTE.Spacetime.OrbitDepthEtherPeriod
