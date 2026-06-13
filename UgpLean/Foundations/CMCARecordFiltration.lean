import RecordEntropy.Core.EntropyFinite
import RecordEntropy.Theorems.Monotonicity
import ArrowOfTime.Core.RecordFiltration
import ArrowOfTime.Core.Refinement
import Mathlib.Data.Fintype.Basic

/-!
# CMCA Record Filtration — Level-1 Second Law

Instantiates the nems-lean `RecordFiltration` for a finite CMCA witness.
Applying `recordEntropy_monotone` yields `H(t+1) ≥ H(t)`.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Foundations.CMCARecordFiltration

open ArrowOfTime
open ArrowOfTime.RecordFiltration
open RecordEntropy

/-- CMCA witness world: Z₇ winding at step `0` and step `1`. -/
structure CMCAWorld where
  w0 : Fin 7
  w1 : Fin 7
  deriving DecidableEq, Repr, Fintype

/-- CMCA observation: step tag together with measured Z₇ winding. -/
structure CMCAObs where
  step : Fin 2
  winding : Fin 7
  deriving DecidableEq, Repr, Fintype

namespace CMCA

def holds (w : CMCAWorld) (o : CMCAObs) : Prop :=
  match o.step with
  | 0 => w.w0 = o.winding
  | 1 => w.w1 = o.winding

def visible (t : Time) (o : CMCAObs) : Prop :=
  o.step.val ≤ t

theorem visible_mono (t t' : Time) (o : CMCAObs) (hle : t ≤ t') (hv : visible t o) :
    visible t' o := by
  unfold visible at hv ⊢
  exact Nat.le_trans hv hle

def cmcaFiltration : RecordFiltration CMCAWorld CMCAObs where
  Holds := holds
  Visible := visible
  mono := visible_mono

attribute [local instance] Classical.propDecidable

noncomputable instance (t : Time) :
    Fintype (cmcaFiltration.WorldTypeAt t) :=
  Quotient.fintype (cmcaFiltration.obsEqAtSetoid t)

/-- **cmca_record_filtration_entropy_monotone** (CatAL):
    Record entropy is non-decreasing: `H(t+1) ≥ H(t)`. -/
theorem cmca_record_filtration_entropy_monotone (t : Time) :
    recordEntropy cmcaFiltration (t + 1) ≥ recordEntropy cmcaFiltration t :=
  recordEntropy_monotone cmcaFiltration t

/-- Strict record growth at `t = 0`: step-1 winding becomes visible. -/
theorem cmca_strict_growth_at_zero : cmcaFiltration.StrictGrowthAt 0 := by
  refine ⟨⟨1, 0⟩, ?_, ?_, ⟨0, 0⟩, ⟨0, 1⟩, ?_, ?_⟩
  · simp [cmcaFiltration, visible]
  · simp [cmcaFiltration, visible]
  · intro o vo
    rcases o with ⟨s, w⟩
    match s with
    | 0 =>
      simp [cmcaFiltration, holds, visible] at vo ⊢
    | 1 => exact absurd vo (by simp [cmcaFiltration, visible])
  · simp [cmcaFiltration, holds]

/-- Strict refinement at the first step: `H(1) > H(0)`. -/
theorem cmca_record_entropy_strict_step :
    recordEntropy cmcaFiltration 1 > recordEntropy cmcaFiltration 0 :=
  recordEntropy_strict cmcaFiltration 0 cmca_strict_growth_at_zero

end CMCA

end UgpLean.Foundations.CMCARecordFiltration
