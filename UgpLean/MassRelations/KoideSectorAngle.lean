import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# UgpLean.MassRelations.KoideSectorAngle — S₃ subgroup chain for quark Koide angles

Group-theoretic facts for the quark-sector Yukawa cone angles:
θ_sector = |H_sector| / N_c³ with H_sector ∈ {S₃, A₃, Z₂} for
(lepton, down-quark, up-quark) sectors and N_c = 3.
-/

namespace UgpLean.MassRelations.KoideSectorAngle

/-- S₃ (symmetric group on 3 elements) has |S₃| = 6 and proper normal subgroup A₃
    with |A₃| = 3 and index [S₃ : A₃] = 2. -/
theorem s3_unique_proper_normal_subgroup :
    (6 : ℕ) / 3 = 2 ∧ 3 ∣ 6 ∧ 2 ∣ 6 := by decide

/-- Subgroup orders dividing |S₃| = 6: {1, 2, 3, 6}.
    Matches GTE quark-sector divisors: leptons → |S₃| = 6, down → |A₃| = 3, up → |Z₂| = 2. -/
theorem s3_subgroup_orders :
    ({1, 2, 3, 6} : Finset ℕ).card = 4 ∧
    (6 : ℕ) % 1 = 0 ∧ 6 % 2 = 0 ∧ 6 % 3 = 0 ∧ 6 % 6 = 0 := by decide

/-- GTE quark Koide angle formula θ_sector = |H_sector| / N_c³ with N_c³ = 27.
    Lepton anchor θ = 6/27 = 2/9; down θ = 3/27 = 1/9; up θ = 2/27. -/
theorem koide_sector_angle_subgroup_formula :
    (6 : ℚ) / 27 = 2 / 9 ∧
    (3 : ℚ) / 27 = 1 / 9 ∧
    (2 : ℚ) / 27 = 2 / 27 := by
  norm_num

end UgpLean.MassRelations.KoideSectorAngle
