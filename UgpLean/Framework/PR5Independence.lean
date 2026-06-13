import NemS.Diagonal.ASR
import NemS.Diagonal.Barrier
import NemS.Diagonal.HaltingReduction
import NemS.Diagonal.Instantiation
import NemS.MFRR.ToyMFRR
import NemS.Core.Selectors
import Mathlib.Computability.Halting

/-!
# PR5 Independence from NEMS Choice-Data

`RecordReadout` (PR5) requires ASR coding, a computable truth-bit label, and
alignment with `RT` on the encode-image. None of these follow from
`selector_eq_iff_obsEq` (structural selector classification) or
`HasRecordDivergentChoice` (existential record-divergent branches).

The `RecordReadout` structure mirrors `NemS.Diagonal.Premises` (not yet in the
pinned nems-lean dependency); it is defined here for the independence certificate.

All theorems: zero sorry, zero custom axioms. CatAD.
-/

namespace UgpLean.Framework.PR5Independence

open NemS
open NemS.Diagonal
open NemS.MFRR
open NemS.MFRR.ToyMFRR
open NemS.Framework
open Nat.Partrec (Code)
open Nat.Partrec.Code (eval)

/-- **PR5 (record readout / branch labeling).**

At diagonal choice points, record-distinct branches are computably labeled
by the coded statement's truth bit; the label agrees with `RT`. -/
structure RecordReadout {F : Framework} (asr : ASR F) where
  /-- Computable truth-bit label on record codes. -/
  label : ℕ → Bool
  label_computable : Computable label
  /-- The label tracks `RT` on the ASR encode-image. -/
  label_rt : ∀ (c : Code) (x : ℕ), label (asr.encode c x) = true ↔ asr.RT (asr.encode c x)

private theorem recordReadout_rt_on_encode_computable
    {F : Framework} {asr : ASR F} (pr5 : RecordReadout asr) (n : ℕ) :
    ComputablePred fun c => asr.RT (asr.encode c n) := by
  classical
  have hEnc : Computable fun c => asr.encode c n :=
    asr.encode_computable.comp Computable.id (Computable.const n)
  have hLabelEnc : Computable fun c => pr5.label (asr.encode c n) :=
    pr5.label_computable.comp hEnc
  have hDec : DecidablePred fun c => asr.RT (asr.encode c n) := fun c =>
    if h : pr5.label (asr.encode c n) then
      isTrue ((pr5.label_rt c n).mp h)
    else
      isFalse fun hrt => h ((pr5.label_rt c n).mpr hrt)
  haveI : DecidablePred fun c => asr.RT (asr.encode c n) := hDec
  have heq :
      (fun c => decide (asr.RT (asr.encode c n))) = fun c => pr5.label (asr.encode c n) := by
    funext c
    by_cases hl : pr5.label (asr.encode c n)
    · have hrt : asr.RT (asr.encode c n) := (pr5.label_rt c n).mp hl
      simp [hl, hrt]
    · have hnrt : ¬ asr.RT (asr.encode c n) := fun hrt => hl ((pr5.label_rt c n).mpr hrt)
      simp [hl, hnrt]
  have hDecide : Computable (fun c => decide (asr.RT (asr.encode c n))) := by
    simpa [heq] using hLabelEnc
  exact Computable.computablePred hDecide

/-- **recordReadout_implies_halting_computable_at_zero** (CatAD):
    PR5 on an ASR structure yields a total computable halting decider at input `0`. -/
theorem recordReadout_implies_halting_computable_at_zero
    {F : Framework} {asr : ASR F} (pr5 : RecordReadout asr) :
    ComputablePred fun c => (eval c 0).Dom := by
  have hRT := recordReadout_rt_on_encode_computable pr5 0
  exact hRT.of_eq fun c => (asr.halts_iff_RT c 0).symm

/-- **no_recordReadout_on_halting_framework** (CatAD):
    The halting-framework ASR admits no `RecordReadout` structure. -/
theorem no_recordReadout_on_halting_framework :
    ¬ Nonempty (RecordReadout haltingASR) := by
  rintro ⟨pr5⟩
  exact ComputablePred.halting_problem 0
    (recordReadout_implies_halting_computable_at_zero pr5)

/-- **pr5_requires_asr_not_choice_data** (CatAD):
    PR5 implies computable halting decidability, contradicting the ASR diagonal
    barrier. NEMS choice-data supplies branch existence only. -/
theorem pr5_requires_asr_not_choice_data :
    (∀ {F : Framework} {asr : ASR F}, RecordReadout asr →
      ComputablePred fun c => (eval c 0).Dom) ∧
      ¬ Nonempty (RecordReadout haltingASR) :=
  ⟨fun pr5 => recordReadout_implies_halting_computable_at_zero pr5,
   no_recordReadout_on_halting_framework⟩

/-- **pr5_independent_of_nems_choice_data** (CatAD):
    NEMS choice-data premises are satisfiable while PR5 is not derivable from them.

    Witnesses:
    (1) `bool_has_divergent_choice` — `HasRecordDivergentChoice` holds on the Bool toy.
    (2) `Selector.selector_eq_iff_obsEq` — structural selector classification (any selector).
    (3) `no_recordReadout_on_halting_framework` — PR5 fails under diagonal-capable ASR.

    PR5 additionally requires ASR encoding, computable labeling, and `RT` alignment —
    structure absent from `ChoiceData` and not implied by selector equivalence. -/
theorem pr5_independent_of_nems_choice_data :
    HasRecordDivergentChoice NemS.Examples.boolFramework boolChoiceData ∧
      (∀ (S : NemS.Examples.boolFramework.Selector) {M N : NemS.Examples.boolFramework.Model},
        S.sel M = S.sel N ↔ NemS.Examples.boolFramework.ObsEq M N) ∧
      ¬ Nonempty (RecordReadout haltingASR) ∧
      (∀ {F : Framework} {asr : ASR F}, RecordReadout asr →
        ComputablePred fun c => (eval c 0).Dom) := by
  refine ⟨bool_has_divergent_choice, ?_, no_recordReadout_on_halting_framework, ?_⟩
  intro S M N
  exact Selector.selector_eq_iff_obsEq S
  intro _ asr pr5
  exact recordReadout_implies_halting_computable_at_zero pr5

end UgpLean.Framework.PR5Independence
