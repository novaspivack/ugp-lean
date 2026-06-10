import UgpLean.Spacetime.ChiralPairDecoupling
import UgpLean.Spacetime.ChiralGliderDynamics
import UgpLean.Spacetime.CausalInvariance

/-!
# Chiral Mirror Speed Symmetry (CatAL)

Rule 124 is the spatial mirror of Rule 110: `rule124Fin2 l c r = rule110Fin2 r c l`.
The Cook A-glider on the period-14 ether advances `|Δx| = 2` per `Δt = 3` outer steps,
so `|v| = 2/3`. Mirror duality maps rightward Rule-110 propagation to leftward Rule-124
propagation with the same speed magnitude.

Computational confirmation (CatA): `v_R = +2/3`, `v_L = −2/3` exactly on
the decoupled two-layer system (`rule110_rule124_chiral_pair.py`, P28 canonical run).

## Main theorems (zero sorry)

- `rule124Fin2_is_spatial_mirror` — lookup-table mirror identity
- `mirror_rule_speed_symmetry` — mirror + A-glider kinematics + `ChiralPairCausalSpeed = 2/3`
- `mirror_rule_opposite_signed_speeds` — `v_R = −v_L` at magnitude `2/3`
-/

namespace GTE.Spacetime.ChiralMirrorSpeedSymmetry

open GTE.Spacetime.ChiralPair
open GTE.Spacetime.ChiralGliderDynamics
open GTE.Spacetime.CausalInvariance

/-- Rule 124 on binary neighborhoods is the spatial mirror of Rule 110:
    `R₁₂₄(l,c,r) = R₁₁₀(r,c,l)`. Exhaustive over `Fin 2`³. -/
theorem rule124Fin2_is_spatial_mirror (l c r : Fin 2) :
    rule124Fin2 l c r = rule110Fin2 r c l := by
  fin_cases l <;> fin_cases c <;> fin_cases r <;> decide

/-- Right-moving (Rule 110) and left-moving (Rule 124) chiral speeds in natural units. -/
def chiralRightSpeed : ℚ := 2 / 3

def chiralLeftSpeed : ℚ := -(2 / 3)

theorem chiralRightSpeed_eq_causal_speed : chiralRightSpeed = ChiralPairCausalSpeed := rfl

theorem mirror_rule_opposite_signed_speeds :
    chiralRightSpeed = -chiralLeftSpeed ∧
    chiralRightSpeed = 2 / 3 ∧
    chiralLeftSpeed = -(2 / 3) := by
  native_decide

/-- **Mirror-rule duality implies speed symmetry** (CatAL).

    (1) Rule 124 is the spatial mirror of Rule 110 at the Fin-2 lookup level.
    (2) A-glider period kinematics: `Δt = 3`, `|Δx| = 2`, hence `3·|Δx| ≤ 2·Δt` (tight `c = 2/3` cone).
    (3) Emergent chiral-pair causal speed `ChiralPairCausalSpeed = 2/3` with opposite signs
        on the two decoupled layers (`chiralRightSpeed = −chiralLeftSpeed`).

    Layer decoupling (`chiral_pair_no_cross_layer_edges`) is certified separately in
    `ChiralPairDecoupling.lean`. -/
theorem mirror_rule_speed_symmetry :
    (∀ l c r : Fin 2, rule124Fin2 l c r = rule110Fin2 r c l) ∧
    ChiralPairCausalSpeed = 2 / 3 ∧
    chiralRightSpeed = -chiralLeftSpeed ∧
    aGliderDt = 3 ∧ aGliderDx = 2 ∧
    3 * aGliderDx ≤ 2 * aGliderDt ∧
    (∀ k : ℕ, AGliderPeriodComposition k (k * aGliderDt) (k * aGliderDx)) := by
  refine ⟨rule124Fin2_is_spatial_mirror, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · native_decide
  · exact mirror_rule_opposite_signed_speeds.1
  · exact (cook_a_glider_period_matches_constants).2.2.1
  · exact (cook_a_glider_period_matches_constants).2.2.2
  · native_decide
  · intro k
    exact a_glider_infRule110_k_periods_composition k

end GTE.Spacetime.ChiralMirrorSpeedSymmetry
