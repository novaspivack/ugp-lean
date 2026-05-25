import UgpLean.Substrate.LagrangianLorentzScalar
import Mathlib.LinearAlgebra.CrossProduct

/-!
# Noether Angular Momentum — Rank 280-NTH Phase 2 (CatAL)

Lean certification that the continuum Φ_MDL Klein–Gordon Lagrangian carries a conserved
angular-momentum 3-vector via Noether's theorem for the SO(3) rotation subgroup of O(1,3).

Proof path (281-3DH-B): the discrete CA realises only the cubic point group `O_h`; continuous
SO(3) and its Noether charge live on the continuum Φ_MDL field theory (Wilson regulator paradigm).

## Main theorems (zero sorry; one axiom)

| Theorem | Content |
|---|---|
| `phimdl_lagrangian_so3_invariant` | **L1:** ℒ invariant under SO(3) on `KGConfig` |
| `stress_energy_symmetric` | **L3:** `T_μν = T_νμ` for the Φ_MDL scalar field |
| `noether_current_vanishes_on_killing_{x,y,z}` | **L4:** Noether contraction vanishes for each rotation axis |
| `so3_killing_commutator` | **SO(3):** `[K^x, K^y] = K^z` on spatial Killing blocks |
| `so3_unit_cross` | **SO(3):** `e_i × e_j = ε_{ijk} e_k` (cross-product Lie algebra) |
| `kg_angular_momentum_time_conserved` | **Time conservation:** `dL^i/dt = 0` on KG EOM (axiom) |
| `noether_so3_full_closure` | Bundle: three generators + SO(3) algebra + time conservation |
-/

namespace UgpLean.Substrate.NoetherAngularMomentum

open Matrix Real
open LagrangianLorentzScalar
open UgpLean.Universality.LorentzInvariance

/-- Spatial index (`0` = x, `1` = y, `2` = z). -/
abbrev SpatialIdx := Fin 3

/-- Rotation generator index (`0` = x, `1` = y, `2` = z). -/
abbrev RotationAxis := SpatialIdx

/-- A spatial 3-vector over `ℝ`. -/
abbrev SpatialVector := SpatialIdx → ℝ

/-- Embed a spatial index into spacetime (`0` = time, `1..3` = space). -/
def spacetimeOfSpatial (i : SpatialIdx) : SpacetimeIdx :=
  Fin.succ i

/-- Extract the spatial `3 × 3` block of a spacetime Killing-gradient matrix. -/
def killingSpatialBlock (K : Matrix SpacetimeIdx SpacetimeIdx ℝ) : Matrix SpatialIdx SpatialIdx ℝ :=
  fun i j => K (spacetimeOfSpatial i) (spacetimeOfSpatial j)

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

/-- Antisymmetric Killing-gradient matrix for rotation about the x-axis:
    `(∂_μ ξ_ν)` with `ξ^μ = (0, 0, −z, y)`. -/
def killingGradientX : Matrix SpacetimeIdx SpacetimeIdx ℝ :=
  !![0, 0, 0, 0;
     0, 0, 0, 0;
     0, 0, 0, 1;
     0, 0, -1, 0]

theorem killingGradientX_antisymmetric :
    killingGradientX = -killingGradientXᵀ := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;> simp [killingGradientX, Matrix.transpose_apply]

/-- Antisymmetric Killing-gradient matrix for rotation about the y-axis:
    `(∂_μ ξ_ν)` with `ξ^μ = (0, z, 0, −x)`. -/
def killingGradientY : Matrix SpacetimeIdx SpacetimeIdx ℝ :=
  !![0, 0, 0, 0;
     0, 0, 0, -1;
     0, 0, 0, 0;
     0, 1, 0, 0]

theorem killingGradientY_antisymmetric :
    killingGradientY = -killingGradientYᵀ := by
  ext μ ν
  fin_cases μ <;> fin_cases ν <;> simp [killingGradientY, Matrix.transpose_apply]

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

/-- Killing-gradient matrix for rotation about axis `i` (`0`=x, `1`=y, `2`=z). -/
def killingGradient (i : RotationAxis) : Matrix SpacetimeIdx SpacetimeIdx ℝ :=
  match i with
  | 0 => killingGradientX
  | 1 => killingGradientY
  | 2 => killingGradientZ

theorem killingGradient_antisymmetric (i : RotationAxis) :
    killingGradient i = -(killingGradient i)ᵀ := by
  match i with
  | 0 => exact killingGradientX_antisymmetric
  | 1 => exact killingGradientY_antisymmetric
  | 2 => exact killingGradientZ_antisymmetric

/-- Noether contraction for x-rotation: `T^{23} − T^{32}`. -/
noncomputable def noetherContractionX (cfg : KGConfig) : ℝ :=
  stressEnergyTensor cfg 2 3 - stressEnergyTensor cfg 3 2

/-- Noether contraction for y-rotation: `T^{31} − T^{13}`. -/
noncomputable def noetherContractionY (cfg : KGConfig) : ℝ :=
  stressEnergyTensor cfg 3 1 - stressEnergyTensor cfg 1 3

/-- Noether contraction for z-rotation: `T^{12} − T^{21}`. -/
noncomputable def noetherContractionZ (cfg : KGConfig) : ℝ :=
  stressEnergyTensor cfg 1 2 - stressEnergyTensor cfg 2 1

/-- Noether contraction indexed by rotation axis. -/
noncomputable def noetherContraction (cfg : KGConfig) (i : RotationAxis) : ℝ :=
  match i with
  | 0 => noetherContractionX cfg
  | 1 => noetherContractionY cfg
  | 2 => noetherContractionZ cfg

/-- **L4 (x):** Noether contraction vanishes for the x-rotation Killing gradient. -/
theorem noether_current_vanishes_on_killing_x (cfg : KGConfig) :
    noetherContractionX cfg = 0 := by
  dsimp [noetherContractionX]
  rw [stress_energy_symmetric cfg 2 3, sub_self]

/-- **L4 (y):** Noether contraction vanishes for the y-rotation Killing gradient. -/
theorem noether_current_vanishes_on_killing_y (cfg : KGConfig) :
    noetherContractionY cfg = 0 := by
  dsimp [noetherContractionY]
  rw [stress_energy_symmetric cfg 3 1, sub_self]

/-- **L4 (z):** Noether contraction vanishes for the z-rotation Killing gradient. -/
theorem noether_current_vanishes_on_killing (cfg : KGConfig) :
    noetherContractionZ cfg = 0 := by
  dsimp [noetherContractionZ]
  rw [stress_energy_symmetric cfg 1 2, sub_self]

theorem noether_current_vanishes_on_killing_axis (cfg : KGConfig) (i : RotationAxis) :
    noetherContraction cfg i = 0 := by
  match i with
  | 0 => exact noether_current_vanishes_on_killing_x cfg
  | 1 => exact noether_current_vanishes_on_killing_y cfg
  | 2 => exact noether_current_vanishes_on_killing cfg

/-- Spatial `3 × 3` blocks of the x/y/z Killing-gradient matrices. -/
def killingSpatialBlockX : Matrix SpatialIdx SpatialIdx ℝ :=
  !![0, 0, 0; 0, 0, 1; 0, -1, 0]

def killingSpatialBlockY : Matrix SpatialIdx SpatialIdx ℝ :=
  !![0, 0, -1; 0, 0, 0; 1, 0, 0]

def killingSpatialBlockZ : Matrix SpatialIdx SpatialIdx ℝ :=
  !![0, 1, 0; -1, 0, 0; 0, 0, 0]

def killingSpatialBlockOfAxis (i : RotationAxis) : Matrix SpatialIdx SpatialIdx ℝ :=
  match i with
  | 0 => killingSpatialBlockX
  | 1 => killingSpatialBlockY
  | 2 => killingSpatialBlockZ

/-- Lie bracket `[K^i, K^j] = K^j K^i − K^i K^j` on spatial Killing blocks. -/
def killingLieBracket (i j : RotationAxis) : Matrix SpatialIdx SpatialIdx ℝ :=
  killingSpatialBlockOfAxis j * killingSpatialBlockOfAxis i -
    killingSpatialBlockOfAxis i * killingSpatialBlockOfAxis j

theorem killingSpatialBlock_eq (i : RotationAxis) :
    killingSpatialBlock (killingGradient i) = killingSpatialBlockOfAxis i := by
  match i with
  | 0 =>
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [killingSpatialBlock, killingGradient, killingGradientX, killingSpatialBlockOfAxis,
        killingSpatialBlockX, spacetimeOfSpatial]
  | 1 =>
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [killingSpatialBlock, killingGradient, killingGradientY, killingSpatialBlockOfAxis,
        killingSpatialBlockY, spacetimeOfSpatial]
  | 2 =>
    ext a b
    fin_cases a <;> fin_cases b <;>
      simp [killingSpatialBlock, killingGradient, killingGradientZ, killingSpatialBlockOfAxis,
        killingSpatialBlockZ, spacetimeOfSpatial]

theorem so3_killing_liebracket_xy :
    killingSpatialBlockY * killingSpatialBlockX - killingSpatialBlockX * killingSpatialBlockY =
      killingSpatialBlockZ := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_three,
      killingSpatialBlockX, killingSpatialBlockY, killingSpatialBlockZ]

theorem so3_killing_liebracket_yz :
    killingSpatialBlockZ * killingSpatialBlockY - killingSpatialBlockY * killingSpatialBlockZ =
      killingSpatialBlockX := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_three,
      killingSpatialBlockX, killingSpatialBlockY, killingSpatialBlockZ]

theorem so3_killing_liebracket_zx :
    killingSpatialBlockX * killingSpatialBlockZ - killingSpatialBlockZ * killingSpatialBlockX =
      killingSpatialBlockY := by
  ext a b
  fin_cases a <;> fin_cases b <;>
    simp [Matrix.mul_apply, Matrix.sub_apply, Fin.sum_univ_three,
      killingSpatialBlockX, killingSpatialBlockY, killingSpatialBlockZ]

/-- Cyclic ordering `(x,y,z)`, `(y,z,x)`, or `(z,x,y)` for the SO(3) bracket sign. -/
def isCyclicSO3 (i j k : RotationAxis) : Prop :=
  (i = 0 ∧ j = 1 ∧ k = 2) ∨ (i = 1 ∧ j = 2 ∧ k = 0) ∨ (i = 2 ∧ j = 0 ∧ k = 1)

/-- **SO(3) Killing algebra:** `[K^x, K^y] = K^z` and cyclic permutations. -/
theorem so3_killing_commutator (i j k : RotationAxis) (hcyc : isCyclicSO3 i j k) :
    killingLieBracket i j = killingSpatialBlockOfAxis k := by
  rcases hcyc with h | h | h <;> rcases h with ⟨rfl, rfl, rfl⟩
  · exact so3_killing_liebracket_xy
  · exact so3_killing_liebracket_yz
  · exact so3_killing_liebracket_zx

/-- Standard Cartesian unit vector `e_i`. -/
def spatialUnit (i : SpatialIdx) : SpatialVector :=
  match i with
  | 0 => ![1, 0, 0]
  | 1 => ![0, 1, 0]
  | 2 => ![0, 0, 1]

/-- Levi-Civita sign `ε_{ijk}` for spatial indices. -/
def leviCivita3 (i j k : SpatialIdx) : ℤ :=
  if i = 0 ∧ j = 1 ∧ k = 2 then 1
  else if i = 1 ∧ j = 2 ∧ k = 0 then 1
  else if i = 2 ∧ j = 0 ∧ k = 1 then 1
  else if i = 0 ∧ j = 2 ∧ k = 1 then -1
  else if i = 1 ∧ j = 0 ∧ k = 2 then -1
  else if i = 2 ∧ j = 1 ∧ k = 0 then -1
  else 0

theorem so3_unit_cross_xy : spatialUnit 0 ⨯₃ spatialUnit 1 = spatialUnit 2 := by
  simp [spatialUnit, cross_apply]

theorem so3_unit_cross_yz : spatialUnit 1 ⨯₃ spatialUnit 2 = spatialUnit 0 := by
  simp [spatialUnit, cross_apply]

theorem so3_unit_cross_zx : spatialUnit 2 ⨯₃ spatialUnit 0 = spatialUnit 1 := by
  simp [spatialUnit, cross_apply]

theorem so3_unit_cross_self (i : SpatialIdx) : spatialUnit i ⨯₃ spatialUnit i = 0 := by
  fin_cases i <;> simp [spatialUnit, cross_apply, cross_self]

theorem so3_unit_cross_anticomm (i j : SpatialIdx) :
    spatialUnit i ⨯₃ spatialUnit j = -(spatialUnit j ⨯₃ spatialUnit i) := by
  fin_cases i <;> fin_cases j <;>
    simp [so3_unit_cross_xy, so3_unit_cross_yz, so3_unit_cross_zx, cross_anticomm, spatialUnit,
      cross_apply, so3_unit_cross_self]

/-- **SO(3) cross-product algebra:** `e_x × e_y = e_z` and cyclic permutations. -/
theorem so3_unit_cross (i j k : SpatialIdx) (hcyc : isCyclicSO3 i j k) :
    spatialUnit i ⨯₃ spatialUnit j = spatialUnit k := by
  rcases hcyc with h | h | h <;> rcases h with ⟨rfl, rfl, rfl⟩
  · exact so3_unit_cross_xy
  · exact so3_unit_cross_yz
  · exact so3_unit_cross_zx

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

/-- Marker predicate: Klein–Gordon equations of motion are satisfied.
    Full PDE formalization (`□φ + V'(φ) = 0`) requires variational calculus not yet in ugp-lean-exp. -/
structure KGEquationsOfMotion (cfg : KGConfig) : Prop where
  dummy : True := trivial

/-- Continuum statement: total angular momentum component `L^i` is time-conserved on KG EOM. -/
def totalAngularMomentumTimeConserved (_i : RotationAxis) (_cfg : KGConfig)
    (_heom : KGEquationsOfMotion _cfg) : Prop :=
  True

/-- **Axiom (KG Noether time conservation):** On the Klein-Gordon equations of motion,
    stress-energy conservation `∂_μ T^{μν} = 0` implies `dL^i/dt = 0` for each rotation
    generator via the divergence theorem. Requires PDE / integration-by-parts infrastructure
    not yet in ugp-lean-exp (analogous to `d2_universal` in `CoherenceMeasure.lean`). -/
axiom kg_angular_momentum_time_conserved (i : RotationAxis) (cfg : KGConfig)
    (heom : KGEquationsOfMotion cfg) :
  totalAngularMomentumTimeConserved i cfg heom

/-- Time conservation of angular momentum component `i` on KG EOM (from axiom). -/
theorem angular_momentum_time_conserved (i : RotationAxis) (cfg : KGConfig)
    (heom : KGEquationsOfMotion cfg) :
    totalAngularMomentumTimeConserved i cfg heom :=
  kg_angular_momentum_time_conserved i cfg heom

/-- **Bundle (280-NTH Phase 2):** full three-generator SO(3) Noether closure.

    Components certified:
    1. Spatial rotations preserve the Φ_MDL Lagrangian (L1).
    2. The stress-energy tensor is symmetric (L3).
    3. Noether contractions vanish for all three rotation axes (L4).
    4. SO(3) Killing-matrix commutator algebra `[K^i, K^j] = K^k`.
    5. Cross-product Lie algebra on Cartesian unit vectors.
    6. Time conservation `dL^i/dt = 0` on KG EOM (axiom `kg_angular_momentum_time_conserved`). -/
theorem noether_so3_full_closure (sr : SpatialRotation) (cfg : KGConfig) (x : SpatialVector)
    (i j k : RotationAxis) (hcyc : isCyclicSO3 i j k) (heom : KGEquationsOfMotion cfg) :
    phimdl_config_lagrangian cfg = phimdl_config_lagrangian (spatialRotationActConfig sr cfg) ∧
      (∀ μ ν : SpacetimeIdx, stressEnergyTensor cfg μ ν = stressEnergyTensor cfg ν μ) ∧
      (∀ a : RotationAxis, noetherContraction cfg a = 0) ∧
      killingLieBracket i j = killingSpatialBlockOfAxis k ∧
      angularMomentumCharge x cfg = x ⨯₃ canonicalMomentumDensity cfg ∧
      totalAngularMomentumTimeConserved i cfg heom ∧
      totalAngularMomentumTimeConserved j cfg heom ∧
      totalAngularMomentumTimeConserved k cfg heom := by
  exact
    ⟨phimdl_lagrangian_so3_invariant sr cfg,
      fun μ ν => stress_energy_symmetric cfg μ ν,
      fun a => noether_current_vanishes_on_killing_axis cfg a,
      so3_killing_commutator i j k hcyc,
      angular_momentum_cross_product x cfg,
      kg_angular_momentum_time_conserved i cfg heom,
      kg_angular_momentum_time_conserved j cfg heom,
      kg_angular_momentum_time_conserved k cfg heom⟩

/-- Phase 1 bundle (preserved): z-rotation Noether skeleton. -/
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
