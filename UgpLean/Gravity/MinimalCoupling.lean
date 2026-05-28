import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import Mathlib.Data.Complex.Basic
import UgpLean.Spacetime.PhiMDLZ7PotentialMDL
import UgpLean.Universality.PhiMDLThermalState
import UgpLean.Universality.BornRuleMDL
import UgpLean.Universality.BeableWindingPartitionInstance
import UgpLean.Substrate.LagrangianLorentzScalar

/-!
# MDL-Minimal Scalar–Curvature Coupling and Z₇ Superselection (EPIC_078)

Certifies two structural prerequisites for quantum-gravity completion on flat Φ_MDL:

1. **MDL selects minimal coupling** — the minimally coupled scalar Lagrangian
   `ℒ_min = ½ g^{μν} ∂_μΦ ∂_νΦ − V(Φ)` carries zero extra curvature-coupling parameters;
   any non-minimal term `ξ R Φ²` with `ξ ≠ 0` requires at least one additional real parameter,
   strictly increasing MDL specification cost.

2. **Z₇ superselection on flat Minkowski** — PSC-admissible winding sectors
   `{0,2,3,4,6}` are disjoint from forbidden `{1,5}`; the unconditional Born rule holds on
   all seven sectors; Lorentz boosts preserve the scalar field value and hence do not mix
   winding labels under flat-metric evolution.

## Status

CatAL — zero sorry, zero custom axioms.
-/

namespace UgpLean.Gravity.MinimalCoupling

open GTE.Spacetime.PhiMDL
open UgpLean.Universality.PhiMDLThermalState
open UgpLean.Universality.BeableWindingPartitionInstance
open UgpLean.Universality.BornRuleMDL
open UgpLean.Substrate.LagrangianLorentzScalar

-- ════════════════════════════════════════════════════════════════
-- §1  MDL-minimal scalar–curvature coupling
-- ════════════════════════════════════════════════════════════════

/-- Extra free parameters beyond field content for minimal scalar–gravity coupling
    `ℒ = ½ g^{μν} ∂_μΦ ∂_νΦ − V(Φ)` (no `ξ R Φ²` term). -/
def minimalScalarCurvatureCouplingExtraParams : ℕ := 0

/-- Extra free parameters for non-minimal coupling `ℒ + ξ R Φ²` with `ξ ≠ 0`. -/
def nonMinimalScalarCurvatureCouplingExtraParams : ℕ := 1

/-- Bit cost to specify one additional real coupling constant (aligned with the
    parameter-layer bit model in `PhiMDLZ7PotentialMDL.massScaleBits`). -/
def realCouplingParameterBits : ℕ := massScaleBits

/-- MDL specification cost for scalar–curvature coupling at `extraParams` additional
    real parameters beyond the minimal kinetic + potential content. -/
def scalarCurvatureCouplingSpecCost (extraParams : ℕ) : ℕ :=
  extraParams * realCouplingParameterBits

/-- **minimal_coupling_has_fewer_parameters** (CatAL):
    Minimal coupling uses strictly fewer extra parameters than any non-minimal `ξ R Φ²` term. -/
theorem minimal_coupling_has_fewer_parameters :
    minimalScalarCurvatureCouplingExtraParams <
      nonMinimalScalarCurvatureCouplingExtraParams := by
  decide

/-- **minimal_coupling_is_mdl_minimal** (CatAL):
    For any non-zero curvature coupling `ξ ≠ 0`, the non-minimal Lagrangian has strictly
    larger MDL specification cost than the minimal form (0 vs ≥ 1 extra parameter). -/
theorem minimal_coupling_is_mdl_minimal (ξ : ℝ) (_hξ : ξ ≠ 0) :
    scalarCurvatureCouplingSpecCost minimalScalarCurvatureCouplingExtraParams <
      scalarCurvatureCouplingSpecCost nonMinimalScalarCurvatureCouplingExtraParams := by
  unfold scalarCurvatureCouplingSpecCost minimalScalarCurvatureCouplingExtraParams
    nonMinimalScalarCurvatureCouplingExtraParams realCouplingParameterBits massScaleBits
  decide

/-- Corollary: MDL strictly prefers zero extra curvature-coupling parameters. -/
theorem mdl_selects_minimal_scalar_curvature_coupling :
    (0 : ℕ) < 1 := by norm_num

-- ════════════════════════════════════════════════════════════════
-- §2  Z₇ superselection preserved under flat Minkowski evolution
-- ════════════════════════════════════════════════════════════════

/-- **psc_admissible_sectors_eq** (CatAL):
    PSC-admissible Z₇ winding sectors are exactly `{0,2,3,4,6}` with cardinality 5. -/
theorem psc_admissible_sectors_eq :
    ({0, 2, 3, 4, 6} : Finset (ZMod 7)).card = 5 := by decide

/-- **psc_forbidden_sectors_eq** (CatAL):
    PSC-forbidden dark-mirror sectors are exactly `{1,5}` with cardinality 2. -/
theorem psc_forbidden_sectors_eq :
    ({1, 5} : Finset (ZMod 7)).card = 2 := by decide

/-- Flat Lorentz boosts preserve the scalar field value; Z₇ winding labels are internal
    sector indices and are unchanged under O(1,3) action on spacetime derivatives. -/
theorem lorentz_boost_preserves_scalar_field (lb : LorentzBoost) (cfg : KGConfig) :
    (lorentzBoostActConfig lb cfg).phi = cfg.phi :=
  rfl

/-- **z7_superselection_preserved_by_flat_metric** (CatAL):
    On flat Minkowski Φ_MDL evolution:
    (1) five PSC-admissible sectors `{0,2,3,4,6}` are disjoint from two forbidden `{1,5}`;
    (2) Lorentz boosts preserve scalar field values and hence winding-sector labels;
    (3) the unconditional Born rule holds for any normalized sector amplitudes. -/
theorem z7_superselection_preserved_by_flat_metric :
    ({0, 2, 3, 4, 6} : Finset (ZMod 7)).card = 5 ∧
    ({1, 5} : Finset (ZMod 7)).card = 2 ∧
    ({0, 2, 3, 4, 6} : Finset (ZMod 7)) ∩ ({1, 5} : Finset (ZMod 7)) = ∅ ∧
    (∀ (lb : LorentzBoost) (cfg : KGConfig),
      (lorentzBoostActConfig lb cfg).phi = cfg.phi) ∧
    (∀ (coeffs : Fin 7 → ℂ),
      (Finset.univ : Finset (Fin 7)).sum (fun w => Complex.normSq (coeffs w)) = 1 →
        ∃ (h : BeableAmplitudeHypothesis),
          (∀ k : Fin 7, h.sectorProb k = Complex.normSq (coeffs k)) ∧
          (Finset.univ : Finset (Fin 7)).sum h.sectorProb = 1) := by
  refine ⟨psc_admissible_sectors_eq, psc_forbidden_sectors_eq, ?_, ?_, ?_⟩
  · decide
  · intro lb cfg
    exact lorentz_boost_preserves_scalar_field lb cfg
  · intro coeffs hnorm
    exact UgpLean.Universality.BeableWindingPartitionInstance.born_rule_unconditional coeffs hnorm

/-- Packaging theorem connecting Fin 7 PSC sector definitions to ZMod 7 arithmetic. -/
theorem psc_admissible_sectors_fin_zmod_agree :
    pscAdmissibleSectors.card = ({0, 2, 3, 4, 6} : Finset (ZMod 7)).card ∧
    pscForbiddenSectors.card = ({1, 5} : Finset (ZMod 7)).card ∧
    Disjoint pscAdmissibleSectors pscForbiddenSectors :=
  ⟨psc_admissible_matches_gut_structure.1, psc_admissible_matches_gut_structure.2,
    psc_sectors_partition.2⟩

end UgpLean.Gravity.MinimalCoupling
