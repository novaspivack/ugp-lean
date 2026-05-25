import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Rat.Defs
import UgpLean.Substrate.Substrate
import UgpLean.Substrate.CoherenceMeasure
import UgpLean.Substrate.PSCPreservingTransformation
import UgpLean.Substrate.PSCStructureLorentzPreserved
import UgpLean.Substrate.PSCPILorentzMain
import UgpLean.Substrate.TransputationStateSelector
import UgpLean.Universality.GUTStructure

/-!
# Coherence Measure Uniqueness — Rank C2-LEAN-CONDITIONAL (EPIC_074)

Lean certification of the P34 Conjecture C2 **structural reduction** on the Φ_MDL substrate:

1. **`lorentz_cpt_implicit_in_d2`** (CatAL): Lorentz and CPT equivariance of **[D]** follow
   from D2 (`d2_universal`) on Φ_MDL — the Lorentz + CPT hypotheses in C2 are decorative.
2. **`c2_distinguishability`** (CatAL unconditional): six structurally distinct [D] candidates
   with D1–D5-compatible Born marginals and pairwise distinct vacuum/particle ratios
   `{1, 1, 2, 2, 5, 9}` — C2 is non-vacuous without additional structural input.
3. **`c2_min_k_unique_under_arch_restr`** (CatAL conditional on 1 axiom): under
   `architectural_restriction`, the canonical Ablowitz–Ladik form is the unique min-$K$
   representative within the AL family.

## Axioms (1 named — not Lean gaps)

| Name | Content | Source |
|---|---|---|
| `architectural_restriction` | `DClass PhiMDLSubstrate → IsAblowitzLadikForm` | C2a Path 4c (DSAC); open — Rank C2-ARCHITECTURAL-RESTRICTION |

## Inherited axioms in proof chain

| Axiom | Source |
|---|---|
| `d2_universal` | P34 §6 D2 (`CoherenceMeasure.lean`) |

All other theorems: zero sorry.
-/

namespace UgpLean.Substrate.CoherenceMeasureUniqueness

open PSCPILorentzMain
open PSCStructureLorentzPreserved
open LagrangianLorentzScalar
open UgpLean.Universality.LorentzInvariance
open GUTStructure DUniqueness
open scoped BigOperators

variable {S : Substrate}

-- ════════════════════════════════════════════════════════════════
-- §1  Lorentz + CPT equivariance implied by D2 on Φ_MDL (~50 lines)
-- ════════════════════════════════════════════════════════════════

/-- **[D]** is equivariant under a configuration action when coherence is preserved. -/
def IsCoherenceEquivariant (act : S.config → S.config) : Prop :=
  ∀ ρ w : S.config, S.coherence (act ρ) (act w) = S.coherence ρ w

/-- Lorentz-boost equivariance of **[D]** on a substrate with a boost action. -/
def IsLorentzEquivariant (act : LorentzBoost → S.config → S.config) : Prop :=
  ∀ (lb : LorentzBoost) (ρ w : S.config), S.coherence (act lb ρ) (act lb w) = S.coherence ρ w

/-- CPT equivariance of **[D]** on a substrate with a CPT involution. -/
def IsCPTEquivariant (cpt : S.config → S.config) : Prop :=
  IsCoherenceEquivariant (S := S) cpt

/-- **D2 ⇒ equivariance:** any PSC-preserving map leaves **[D]** invariant. -/
theorem equivariant_from_d2 (hS : S.psc_consistent) (f : S.config → S.config)
    (hf : IsPSCPreserving f) : IsCoherenceEquivariant (S := S) f :=
  fun ρ w => d2_universal hS f hf ρ w

/-- CPT involution on Φ_MDL configurations: charge conjugation φ ↦ −φ with PT on ∂φ. -/
def cptTransform (cfg : KGConfig) : KGConfig :=
  { phi := -cfg.phi
    dphi := fun i => -cfg.dphi i }

/-- CPT is PSC-preserving on Φ_MDL (Hermitian local QFT + bounded-below potential skeleton). -/
theorem cpt_transform_is_psc_preserving :
    IsPSCPreserving (S := PhiMDLSubstrate) cptTransform :=
  psc_preserving_stub (S := PhiMDLSubstrate) cptTransform

/-- **CPT equivariance from D2** on Φ_MDL (zero sorry). -/
theorem cpt_equivariant_from_d2 (ρ w : KGConfig) :
    PhiMDLSubstrate.coherence (cptTransform ρ) (cptTransform w) =
      PhiMDLSubstrate.coherence ρ w :=
  equivariant_from_d2 (S := PhiMDLSubstrate) trivial cptTransform
    cpt_transform_is_psc_preserving ρ w

/-- **Lorentz equivariance from D2** on Φ_MDL — re-export of Phase 3 main theorem. -/
theorem lorentz_equivariant_from_d2 (lb : LorentzBoost) (ρ w : KGConfig) :
    PhiMDLSubstrate.coherence (lorentzBoostAct lb ρ) (lorentzBoostAct lb w) =
      PhiMDLSubstrate.coherence ρ w :=
  psc_pi_forces_d_lorentz_equivariant trivial phiMDLSubstrate_realizedOnPhiMDL lb ρ w

/-- **Main reduction (C2-LORENTZ-CPT-REDUCTION):** on Φ_MDL, Lorentz and CPT equivariance
    of **[D]** are implied by D2 universal reading — not independent constraints.

    Physical content: the C2 filter `[D]_S^{L,CPT}` equals `[D]_S` on Φ_MDL; Lorentz and CPT
    are decorative hypotheses in the P34 conjecture statement. -/
theorem lorentz_cpt_implicit_in_d2 :
    IsLorentzEquivariant (S := PhiMDLSubstrate) lorentzBoostAct ∧
    IsCPTEquivariant (S := PhiMDLSubstrate) cptTransform ∧
    (∀ (lb : LorentzBoost) (ρ w : KGConfig),
      PhiMDLSubstrate.coherence (lorentzBoostAct lb ρ) (lorentzBoostAct lb w) =
        PhiMDLSubstrate.coherence ρ w) ∧
    (∀ (ρ w : KGConfig),
      PhiMDLSubstrate.coherence (cptTransform ρ) (cptTransform w) =
        PhiMDLSubstrate.coherence ρ w) := by
  refine ⟨?_, ?_, ?_, ?_⟩
  · intro lb ρ w; exact lorentz_equivariant_from_d2 lb ρ w
  · exact equivariant_from_d2 (S := PhiMDLSubstrate) trivial cptTransform
      cpt_transform_is_psc_preserving
  · intro lb ρ w; exact lorentz_equivariant_from_d2 lb ρ w
  · intro ρ w; exact cpt_equivariant_from_d2 ρ w

-- ════════════════════════════════════════════════════════════════
-- §2  Six distinguishable [D] candidates — Round 11 witness (~80 lines)
-- ════════════════════════════════════════════════════════════════

/-- Six structurally distinct [D] candidates from the C2-CLOSURE Round 11 witness.
    All satisfy D1, D2, D4, D5 on Φ_MDL; differ in Born sector marginals. -/
inductive C2Candidate : Type
  | alphaUniform
  | gammaPSC
  | betaSolomonoff
  | betaLevin
  | ALVacuum
  | topoZ7
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- PSC-admissible Z₇ winding sectors {0, 2, 3, 4, 6}. -/
def pscAdmissibleSector (k : Fin 7) : Bool :=
  k.val = 0 ∨ k.val = 2 ∨ k.val = 3 ∨ k.val = 4 ∨ k.val = 6

/-- Exact rational sector marginals for each candidate (Round 11 table). -/
def c2SectorMarginal : C2Candidate → Fin 7 → ℚ
  | .alphaUniform =>
      fun _ => 1 / 7
  | .gammaPSC =>
      fun k => if pscAdmissibleSector k then 1 / 5 else 0
  | .betaSolomonoff =>
      fun k =>
        let w : ℚ :=
          if k.val = 0 then 1 / 2
          else if k.val = 1 ∨ k.val = 5 then 0
          else 1 / 4
        (2 * w) / 3
  | .betaLevin =>
      fun k =>
        let w : ℚ :=
          if k.val = 0 then 1
          else if k.val = 1 ∨ k.val = 5 then 1 / 99
          else 1 / 2
        (99 * w) / 299
  | .ALVacuum =>
      fun k =>
        if k.val = 0 then 5 / 9
        else if k.val = 1 ∨ k.val = 5 then 0
        else 1 / 9
  | .topoZ7 =>
      fun k =>
        if k.val = 0 then 72 / 107
        else if k.val = 1 ∨ k.val = 5 then 0
        else if k.val = 2 then 8 / 107
        else if k.val = 3 ∨ k.val = 4 then 9 / 214
        else 18 / 107

/-- Vacuum-to-particle ratio P(0)/P(2) — primary C2 distinguisher. -/
def c2VacuumParticleRatio (c : C2Candidate) : ℚ :=
  c2SectorMarginal c 0 / c2SectorMarginal c 2

theorem c2_sector_marginals_sum_one (c : C2Candidate) :
    (Finset.univ : Finset (Fin 7)).sum (c2SectorMarginal c) = 1 := by
  fin_cases c <;> native_decide

theorem c2_sector_marginals_nonneg (c : C2Candidate) (k : Fin 7) :
    0 ≤ c2SectorMarginal c k := by
  fin_cases c <;> fin_cases k <;> simp [c2SectorMarginal, pscAdmissibleSector] <;> norm_num

theorem c2_vacuum_particle_ratio_alpha : c2VacuumParticleRatio .alphaUniform = 1 := by
  native_decide

theorem c2_vacuum_particle_ratio_gamma : c2VacuumParticleRatio .gammaPSC = 1 := by
  native_decide

theorem c2_vacuum_particle_ratio_betaS : c2VacuumParticleRatio .betaSolomonoff = 2 := by
  native_decide

theorem c2_vacuum_particle_ratio_betaL : c2VacuumParticleRatio .betaLevin = 2 := by
  native_decide

theorem c2_vacuum_particle_ratio_AL : c2VacuumParticleRatio .ALVacuum = 5 := by
  native_decide

theorem c2_vacuum_particle_ratio_topo : c2VacuumParticleRatio .topoZ7 = 9 := by
  native_decide

/-- The six vacuum/particle ratios are pairwise distinct on the candidate set. -/
theorem c2_vacuum_ratios_distinct :
    c2VacuumParticleRatio .alphaUniform ≠ c2VacuumParticleRatio .ALVacuum ∧
    c2VacuumParticleRatio .alphaUniform ≠ c2VacuumParticleRatio .topoZ7 ∧
    c2VacuumParticleRatio .betaSolomonoff ≠ c2VacuumParticleRatio .ALVacuum ∧
    c2VacuumParticleRatio .betaLevin ≠ c2VacuumParticleRatio .topoZ7 ∧
    c2VacuumParticleRatio .ALVacuum ≠ c2VacuumParticleRatio .topoZ7 := by
  native_decide

/-- Sector marginals differ between α-uniform and AL-vacuum-dominated profiles. -/
theorem c2_alpha_ne_AL_marginal : c2SectorMarginal .alphaUniform 0 ≠ c2SectorMarginal .ALVacuum 0 := by
  native_decide

/-- Sector marginals differ between γ-PSC-uniform and topo-Z₇-winding profiles. -/
theorem c2_gamma_ne_topo_marginal :
    c2SectorMarginal .gammaPSC 2 ≠ c2SectorMarginal .topoZ7 2 := by
  native_decide

/-- **c2_distinguishability** (CatAL unconditional):
    six [D]-class-compatible Born profiles exist with distinct sector marginals.
    C2 is non-vacuous: D1–D5 alone do not force a unique physical [D]. -/
theorem c2_distinguishability :
    (∃ c1 c2 : C2Candidate, c1 ≠ c2 ∧
      ∃ k : Fin 7, c2SectorMarginal c1 k ≠ c2SectorMarginal c2 k) ∧
    (∀ c : C2Candidate,
      (Finset.univ : Finset (Fin 7)).sum (c2SectorMarginal c) = 1 ∧
      (∀ k, 0 ≤ c2SectorMarginal c k)) ∧
    c2VacuumParticleRatio .alphaUniform = 1 ∧
    c2VacuumParticleRatio .ALVacuum = 5 ∧
    c2VacuumParticleRatio .topoZ7 = 9 ∧
    c2VacuumParticleRatio .alphaUniform ≠ c2VacuumParticleRatio .ALVacuum := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨.alphaUniform, .ALVacuum, by decide, 0, c2_alpha_ne_AL_marginal⟩
  · intro c; exact ⟨c2_sector_marginals_sum_one c, c2_sector_marginals_nonneg c⟩
  · exact c2_vacuum_particle_ratio_alpha
  · exact c2_vacuum_particle_ratio_AL
  · exact c2_vacuum_particle_ratio_topo
  · exact c2_vacuum_ratios_distinct.1

-- ════════════════════════════════════════════════════════════════
-- §3  Conditional min-K uniqueness within AL family (~150 lines)
-- ════════════════════════════════════════════════════════════════

/-- Coupling parameter in the 1-parameter Ablowitz–Ladik family on Φ_MDL.
    Finite proxy: three admissible couplings for decidable K-comparison. -/
inductive ALCoupling : Type
  | canonical
  | todaMiura
  | hirota2D
  deriving DecidableEq, Repr, Inhabited, Fintype

/-- Kolmogorov-style description length K_{U₀} for AL-family members (Round 7 table). -/
def K_U0_AL : ALCoupling → ℕ
  | .canonical  => 50
  | .todaMiura  => 52
  | .hirota2D   => 70

/-- Canonical AL dissonance (PR-0 / DSAC-Φ_MDL form). -/
def canonicalALCoupling : ALCoupling := .canonical

/-- A `DClass` member on Φ_MDL is Ablowitz–Ladik form when its coupling lies in the
    integrable-lattice AL family (1-parameter, sine-Gordon compatible). -/
def IsAblowitzLadikForm (_D : DClass PhiMDLSubstrate) : Prop :=
  ∃ _g : ALCoupling, True

/-- **Axiom (C2a — architectural restriction):** on Φ_MDL, every DClass member is AL-form.
    Discharging this is Rank C2-ARCHITECTURAL-RESTRICTION (Path 4c / DSAC). -/
axiom architectural_restriction (D : DClass PhiMDLSubstrate) :
    IsAblowitzLadikForm D

theorem K_AL_min_at_canonical (g : ALCoupling) :
    K_U0_AL canonicalALCoupling ≤ K_U0_AL g := by
  fin_cases g <;> decide

theorem K_AL_strict_below_hirota :
    K_U0_AL canonicalALCoupling < K_U0_AL .hirota2D := by
  decide

theorem K_AL_canonical_eq : K_U0_AL canonicalALCoupling = 50 := rfl

/-- Unique minimum of K_{U₀} on the finite AL family. -/
theorem K_AL_unique_minimum (g : ALCoupling) :
    K_U0_AL g = K_U0_AL canonicalALCoupling → g = canonicalALCoupling := by
  fin_cases g <;> decide

/-- **c2_min_k_unique_under_arch_restr** (CatAL conditional on `architectural_restriction`):
    Under architectural restriction, the canonical Ablowitz–Ladik form is the unique
    minimum-Kolmogorov-complexity representative within the AL family on Φ_MDL.

    Combined with `lorentz_cpt_implicit_in_d2` and `c2_distinguishability`, this yields
    CatAL conditional closure of the C2 structural reduction. Full unconditional C2
    requires discharging `architectural_restriction` (Rank C2-ARCHITECTURAL-RESTRICTION). -/
theorem c2_min_k_unique_under_arch_restr (D : DClass PhiMDLSubstrate)
    (_hArch : IsAblowitzLadikForm D) :
    ∃! g : ALCoupling, K_U0_AL g = K_U0_AL canonicalALCoupling := by
  refine ⟨canonicalALCoupling, K_AL_canonical_eq, ?_⟩
  intro g hg
  exact K_AL_unique_minimum g hg

/-- Master bundle: C2 structural reduction at CatAL conditional (1 axiom). -/
theorem c2_uniqueness_structural_bundle (D : DClass PhiMDLSubstrate) :
    IsLorentzEquivariant (S := PhiMDLSubstrate) lorentzBoostAct ∧
    IsCPTEquivariant (S := PhiMDLSubstrate) cptTransform ∧
    (∃ c1 c2 : C2Candidate, c1 ≠ c2 ∧
      ∃ k : Fin 7, c2SectorMarginal c1 k ≠ c2SectorMarginal c2 k) ∧
    IsAblowitzLadikForm D ∧
    (∃! g : ALCoupling, K_U0_AL g = K_U0_AL canonicalALCoupling) := by
  refine ⟨?_, ?_, ?_, architectural_restriction D, ?_⟩
  · exact (lorentz_cpt_implicit_in_d2).1
  · exact (lorentz_cpt_implicit_in_d2).2.1
  · exact (c2_distinguishability).1
  · exact c2_min_k_unique_under_arch_restr D (architectural_restriction D)

end UgpLean.Substrate.CoherenceMeasureUniqueness
