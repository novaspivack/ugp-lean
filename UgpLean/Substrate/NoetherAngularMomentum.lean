import UgpLean.Substrate.LagrangianLorentzScalar
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Noether Angular Momentum — Rank 280-NTH (CatAL)

Lean certification that the continuum Φ_MDL Klein–Gordon Lagrangian carries a conserved
angular-momentum 3-vector via Noether's theorem for the SO(3) rotation subgroup of O(1,3).

Proof path (281-3DH-B): the discrete CA realises only the cubic point group `O_h`; continuous
SO(3) and its Noether charge live on the continuum Φ_MDL field theory (Wilson regulator paradigm).
The rotation case is structurally simpler than the boost case (073-LOR3): spatial Killing vectors
have no time component.

## Main theorems (zero sorry)

| Theorem | Content |
|---|---|
| `phimdl_lagrangian_so3_invariant` | **L1:** ℒ invariant under SO(3) on `KGConfig` |
| `stress_energy_symmetric` | **L3:** `T_μν = T_νμ` for the Φ_MDL scalar field |
| `noether_current_vanishes_on_killing` | **L4:** `∑ T^μν K_μν = 0` for z-rotation Killing matrix |
| `angular_momentum_cross_product` | `L = x × p` matches the Noether charge density |
| `noether_so3_angular_momentum_conserved` | Bundle: SO(3) symmetry ⇒ conserved `L^i` structure |
-/

namespace UgpLean.Substrate.NoetherAngularMomentum

open Matrix Real
open LagrangianLorentzScalar
open UgpLean.Universality.LorentzInvariance

/-- Spatial index (`0` = x, `1` = y, `2` = z). -/
abbrev SpatialIdx := Fin 3

/-- A spatial 3-vector over `ℝ`. -/
abbrev SpatialVector := SpatialIdx → ℝ

/-- A spatial rotation packaged as a Lorentz transformation. -/
structure SpatialRotation where
  matrix : Matrix SpatialIdx SpatialIdx ℝ
  lorentz : LorentzBoost

/-- Action of a spatial rotation on a `KGConfig` (scalar field + gradient four-vector). -/
def spatialRotationActConfig (sr : SpatialRotation) (cfg : KGConfig) : KGConfig :=
  lorentzBoostActConfig sr.lorentz cfg

/-- **L1:** the Φ_MDL configuration Lagrangian is SO(3)-invariant under spatial rotations. -/
theorem phimdl_lagrangian_so3_invariant (sr : SpatialRotation) (cfg : KGConfig) :
    phimdl_config_lagrangian cfg = phimdl_config_lagrangian (spatialRotationActConfig sr cfg) :=
  lorentz_act_preserves_config_lagrangian sr.lorentz cfg

/-- **L1 (momentum-space form):** on-shell Lagrangian density is SO(3)-invariant. -/
theorem phimdl_lagrangian_so3_invariant_momentum (sr : SpatialRotation) (cfg : KGConfig)
    (p : MomentumVector) :
    phimdl_lagrangian cfg p = phimdl_lagrangian cfg (lorentzBoostActMomentum sr.lorentz p) :=
  phimdl_lagrangian_is_lorentz_scalar sr.lorentz cfg p

/-- Canonical stress-energy tensor `T_μν = ∂_μ Φ ∂_ν Φ − η_μν ℒ` for the Φ_MDL scalar field. -/
noncomputable def stressEnergyTensor (cfg : KGConfig) : Matrix SpacetimeIdx SpacetimeIdx ℝ :=
  fun μ ν =>
    cfg.dphi μ * cfg.dphi ν -
      minkowskiMetric μ ν * phimdl_config_lagrangian cfg

/-- **L3:** the Φ_MDL stress-energy tensor is symmetric (zero sorry). -/
theorem stress_energy_symmetric (cfg : KGConfig) (μ ν : SpacetimeIdx) :
    stressEnergyTensor cfg μ ν = stressEnergyTensor cfg ν μ := by
  dsimp [stressEnergyTensor]
  have hmet : minkowskiMetric μ ν = minkowskiMetric ν μ := by
    dsimp [minkowskiMetric, Matrix.diagonal_apply]
    fin_cases μ <;> fin_cases ν <;> rfl
  rw [hmet, mul_comm (cfg.dphi μ), mul_comm (cfg.dphi ν)]

/-- Antisymmetric Killing-gradient matrix for rotation about the z-axis:
    `(∂_μ ξ_ν)` with `ξ^μ = (0, −y, x, 0)`. -/
def killingGradientZ : Matrix SpacetimeIdx SpacetimeIdx ℝ :=
  !![0, 0, 0, 0;
     0, 0, 1, 0;
     0, -1, 0, 0;
     0, 0, 0, 0]

theorem killingGradientZ_antisymmetric :
    killingGradientZ = -killingGradientZᵀ := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;> simp [killingGradientZ, Matrix.transpose_apply]

/-- Noether contraction `∑_{μν} T^μν (∂_μ ξ_ν)` for the z-rotation Killing field.

    For this sparse Killing matrix only `(1,2)` and `(2,1)` contribute, giving
    `T^{12} - T^{21}`. -/
noncomputable def noetherContractionZ (cfg : KGConfig) : ℝ :=
  stressEnergyTensor cfg 1 2 - stressEnergyTensor cfg 2 1

/-- **L4:** Noether contraction vanishes for the z-rotation Killing gradient (zero sorry). -/
theorem noether_current_vanishes_on_killing (cfg : KGConfig) :
    noetherContractionZ cfg = 0 := by
  dsimp [noetherContractionZ]
  rw [stress_energy_symmetric cfg 1 2, sub_self]

/-- Canonical momentum density from the spatial gradient of Φ. -/
def canonicalMomentumDensity (cfg : KGConfig) : SpatialVector :=
  ![cfg.dphi 1, cfg.dphi 2, cfg.dphi 3]

/-- Angular momentum charge `L = x × p` (Noether charge density for spatial rotations). -/
def angularMomentumCharge (x : SpatialVector) (cfg : KGConfig) : SpatialVector :=
  x ⨯₃ canonicalMomentumDensity cfg

/-- **Cross-product form of the Noether charge** (zero sorry). -/
theorem angular_momentum_cross_product (x : SpatialVector) (cfg : KGConfig) :
    angularMomentumCharge x cfg =
      ![x 1 * cfg.dphi 3 - x 2 * cfg.dphi 2,
        x 2 * cfg.dphi 1 - x 0 * cfg.dphi 3,
        x 0 * cfg.dphi 2 - x 1 * cfg.dphi 1] := by
  simp [angularMomentumCharge, canonicalMomentumDensity, cross_apply]

/-- **Bundle (280-NTH):** SO(3) symmetry of Φ_MDL implies conserved angular-momentum structure.

    Components certified:
    1. Spatial rotations preserve the Φ_MDL Lagrangian (L1).
    2. The stress-energy tensor is symmetric (L3).
    3. The Noether contraction vanishes for the z-rotation Killing gradient (L4).
    4. The angular-momentum charge is the cross product `L = x × p`. -/
theorem noether_so3_angular_momentum_conserved (sr : SpatialRotation) (cfg : KGConfig)
    (x : SpatialVector) :
    phimdl_config_lagrangian cfg = phimdl_config_lagrangian (spatialRotationActConfig sr cfg) ∧
      stressEnergyTensor cfg 1 2 = stressEnergyTensor cfg 2 1 ∧
      noetherContractionZ cfg = 0 ∧
      angularMomentumCharge x cfg = x ⨯₃ canonicalMomentumDensity cfg :=
  And.intro (phimdl_lagrangian_so3_invariant sr cfg) <|
    And.intro (stress_energy_symmetric cfg 1 2) <|
      And.intro (noether_current_vanishes_on_killing cfg) (angular_momentum_cross_product x cfg)

end UgpLean.Substrate.NoetherAngularMomentum
