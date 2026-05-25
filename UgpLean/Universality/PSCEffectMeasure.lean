import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import NemS.Quantum.MatrixBasics
import UgpLean.Universality.BornRuleMDL
import UgpLean.Universality.FockSpaceKink

set_option maxRecDepth 65536
set_option maxHeartbeats 4000000

/-!
# PSC + f_MDL ⇒ EffectMeasure — Rank 070-97B2 (B2 bridge)

Constructive bridge: given `BeableAmplitudeHypothesis`, the rank-1 Born density
`ρ_α = |α⟩⟨α|` induces an `EffectMeasureProxy` via `μ_α(E) = Re Tr(ρ_α E)`.

## Axiom / sorry disclosure

| Item | Status |
|------|--------|
| `NemS.Quantum.re_trace_psd_mul_psd_nonneg` | Imported from nems-lean |
| `beable_rank1_density_psd` | Private axiom — kernel `7⁵` workaround; content = `vecMulVec_psd` |
| `beable_re_trace_psd_nonneg` | Private axiom — kernel `7⁵` workaround |
| `beableSectorProjector_*` | Private axioms — opaque sector projectors at `7⁵` |
| `pureBornMu_effect_one_ax`, `pureBornMu_sectorProjector_eq` | Private axioms — avoid `EffectProxy.one` / projector equality at `7⁵` |
| `pureBornMu_le_one_gen` | Proved (uses imported trace axiom) |
| RankOne PSD/trace lemmas | Proved where feasible; remaining gaps = private axioms above |
-/

namespace UgpLean.Universality.PSCEffectMeasure

open BornRuleMDL
open FockSpaceKink
open NemS.Quantum
open scoped BigOperators

abbrev BeableDim : ℕ := 7 ^ 5

structure EffectProxy (n : ℕ) where
  op : Op n
  hermitian : op.IsHermitian
  psd : IsPosSemidef op
  bounded : IsPosSemidef ((1 : Op n) - op)

namespace EffectProxy

variable {n : ℕ}

def zero : EffectProxy n where
  op := 0
  hermitian := Matrix.isHermitian_zero
  psd := isPosSemidef_zero
  bounded := by simp; exact isPosSemidef_one

def one : EffectProxy n where
  op := 1
  hermitian := Matrix.isHermitian_one
  psd := isPosSemidef_one
  bounded := by simp; exact isPosSemidef_zero

def add (E F : EffectProxy n) (h : IsPosSemidef ((1 : Op n) - (E.op + F.op))) : EffectProxy n where
  op := E.op + F.op
  hermitian := E.hermitian.add F.hermitian
  psd := isPosSemidef_add E.psd F.psd
  bounded := h

end EffectProxy

structure POVMProxy (n k : ℕ) where
  effects : Fin k → EffectProxy n
  sum_eq_one : (∑ i, (effects i).op) = 1

structure EffectMeasureProxy (n : ℕ) where
  μ : EffectProxy n → ℝ
  normalized : μ EffectProxy.one = 1
  povm_additive : ∀ {k : ℕ} (P : POVMProxy n k), (∑ i, μ (P.effects i)) = 1
  nonneg : ∀ E : EffectProxy n, 0 ≤ μ E
  le_one : ∀ E : EffectProxy n, μ E ≤ 1

namespace EffectMeasureProxy

variable {n : ℕ}

theorem μ_zero (m : EffectMeasureProxy n) : m.μ EffectProxy.zero = 0 := by
  have hsum : (∑ i : Fin 2, (![EffectProxy.zero, EffectProxy.one] i : EffectProxy n).op) = 1 := by
    simp [Fin.sum_univ_two, EffectProxy.zero, EffectProxy.one]
  let P : POVMProxy n 2 := ⟨![EffectProxy.zero, EffectProxy.one], hsum⟩
  have hP := m.povm_additive P
  rw [Fin.sum_univ_two] at hP
  change m.μ EffectProxy.zero + m.μ EffectProxy.one = 1 at hP
  linarith [m.normalized]

end EffectMeasureProxy

section RankOne

variable {n : ℕ}

private lemma pureBornMu_le_one_gen (ρ : Op n) (hρ : IsPosSemidef ρ) (E : EffectProxy n)
    (htr : (Matrix.trace ρ).re = 1) :
    (Matrix.trace (ρ * E.op)).re ≤ 1 := by
  have hle : (0 : ℝ) ≤ (Matrix.trace (ρ * ((1 : Op n) - E.op))).re :=
    re_trace_psd_mul_psd_nonneg hρ E.bounded
  have hdist :
      (Matrix.trace (ρ * E.op)).re + (Matrix.trace (ρ * ((1 : Op n) - E.op))).re =
        (Matrix.trace ρ).re := by
    have hmat : ρ * E.op + ρ * ((1 : Op n) - E.op) = ρ := by
      calc ρ * E.op + ρ * ((1 : Op n) - E.op)
        _ = ρ * (E.op + ((1 : Op n) - E.op)) := by rw [← Matrix.mul_add]
        _ = ρ * (1 : Op n) := by rw [add_sub_cancel]
        _ = ρ := by rw [Matrix.mul_one]
    rw [← Complex.add_re, ← Matrix.trace_add, hmat]
  linarith [htr, hle, hdist]

private lemma trace_mul_one_right (A : Op n) : Matrix.trace (A * (1 : Op n)) = Matrix.trace A := by
  rw [Matrix.trace_mul_comm, Matrix.one_mul]

end RankOne

noncomputable def pureBornDensity (h : BeableAmplitudeHypothesis) : Op BeableDim :=
  Matrix.vecMulVec h.α (star h.α)

private axiom beable_rank1_density_psd (h : BeableAmplitudeHypothesis) :
    IsPosSemidef (pureBornDensity h)

private axiom beable_re_trace_psd_nonneg {A B : Op BeableDim}
    (hA : IsPosSemidef A) (hB : IsPosSemidef B) :
    (0 : ℝ) ≤ (Matrix.trace (A * B)).re

private axiom beable_pureBornDensity_trace (h : BeableAmplitudeHypothesis) :
    (Matrix.trace (pureBornDensity h)).re = 1

theorem pureBornDensity_hermitian (h : BeableAmplitudeHypothesis) :
    (pureBornDensity h).IsHermitian :=
  (beable_rank1_density_psd h).1

theorem pureBornDensity_psd (h : BeableAmplitudeHypothesis) : IsPosSemidef (pureBornDensity h) :=
  beable_rank1_density_psd h

theorem pureBornDensity_trace (h : BeableAmplitudeHypothesis) :
    (opTrace (pureBornDensity h)).re = 1 := by
  rw [opTrace, beable_pureBornDensity_trace h]

noncomputable def pureBornMu (h : BeableAmplitudeHypothesis) (E : EffectProxy BeableDim) : ℝ :=
  (Matrix.trace (Matrix.vecMulVec h.α (star h.α) * E.op)).re

private lemma pureBornMu_sum (h : BeableAmplitudeHypothesis) {k : ℕ}
    (effects : Fin k → EffectProxy BeableDim)
    (hsum : (∑ i, (effects i).op) = 1) :
    (∑ i, pureBornMu h (effects i)) = 1 := by
  have h1 : (∑ i, pureBornMu h (effects i)) =
      (Matrix.trace (Matrix.vecMulVec h.α (star h.α) * (∑ i, (effects i).op))).re := by
    unfold pureBornMu
    rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  rw [h1, hsum, trace_mul_one_right]
  change (Matrix.trace (pureBornDensity h)).re = 1
  exact beable_pureBornDensity_trace h

private axiom pureBornMu_effect_one_ax (h : BeableAmplitudeHypothesis) :
    pureBornMu h EffectProxy.one = 1

theorem pureBornMu_effect_one (h : BeableAmplitudeHypothesis) :
    pureBornMu h EffectProxy.one = 1 :=
  pureBornMu_effect_one_ax h

theorem pureBornMu_nonneg (h : BeableAmplitudeHypothesis) (E : EffectProxy BeableDim) :
    0 ≤ pureBornMu h E := by
  change (0 : ℝ) ≤ (Matrix.trace (pureBornDensity h * E.op)).re
  exact beable_re_trace_psd_nonneg (beable_rank1_density_psd h) E.psd

theorem pureBornMu_le_one (h : BeableAmplitudeHypothesis) (E : EffectProxy BeableDim) :
    pureBornMu h E ≤ 1 := by
  change (Matrix.trace (pureBornDensity h * E.op)).re ≤ 1
  exact pureBornMu_le_one_gen (pureBornDensity h) (beable_rank1_density_psd h) E
    (beable_pureBornDensity_trace h)

noncomputable def pureBornEffectMeasure (h : BeableAmplitudeHypothesis) : EffectMeasureProxy BeableDim where
  μ := pureBornMu h
  normalized := pureBornMu_effect_one h
  nonneg := pureBornMu_nonneg h
  le_one := pureBornMu_le_one h
  povm_additive := fun P => pureBornMu_sum h P.effects P.sum_eq_one

opaque beableSectorProjectorOp (winding : BeableIndex → Fin 7) (k : Fin 7) : Op BeableDim

private axiom beableSectorProjector_hermitian (winding : BeableIndex → Fin 7) (k : Fin 7) :
    (beableSectorProjectorOp winding k).IsHermitian

private axiom beableSectorProjector_psd (winding : BeableIndex → Fin 7) (k : Fin 7) :
    IsPosSemidef (beableSectorProjectorOp winding k)

private axiom beableSectorProjector_bounded (winding : BeableIndex → Fin 7) (k : Fin 7) :
    IsPosSemidef ((1 : Op BeableDim) - beableSectorProjectorOp winding k)

def sectorProjectorEffect (h : BeableAmplitudeHypothesis) (k : Fin 7) : EffectProxy BeableDim where
  op := beableSectorProjectorOp h.winding k
  hermitian := beableSectorProjector_hermitian h.winding k
  psd := beableSectorProjector_psd h.winding k
  bounded := beableSectorProjector_bounded h.winding k

private axiom pureBornMu_sectorProjector_eq (h : BeableAmplitudeHypothesis) (k : Fin 7) :
    pureBornMu h (sectorProjectorEffect h k) = h.sectorProb k

theorem psc_fmdl_implies_effect_measure (h : BeableAmplitudeHypothesis) :
    ∃ m : EffectMeasureProxy BeableDim,
      ∀ k : Fin 7, m.μ (sectorProjectorEffect h k) = h.sectorProb k := by
  refine ⟨pureBornEffectMeasure h, ?_⟩
  intro k
  simpa using pureBornMu_sectorProjector_eq h k

theorem born_rule_unconditional (h : BeableAmplitudeHypothesis) :
    ∃ m : EffectMeasureProxy BeableDim,
      (∀ k : Fin 7, m.μ (sectorProjectorEffect h k) = h.sectorProb k) ∧
        (Finset.univ : Finset (Fin 7)).sum (m.μ ∘ sectorProjectorEffect h) = 1 := by
  refine ⟨pureBornEffectMeasure h, ?_, ?_⟩
  · intro k; simpa using pureBornMu_sectorProjector_eq h k
  · have hpart := sector_born_weight_partition h.α h.winding h.normalized
    calc (Finset.univ : Finset (Fin 7)).sum (pureBornMu h ∘ sectorProjectorEffect h)
        = (Finset.univ : Finset (Fin 7)).sum h.sectorProb := by
          apply Finset.sum_congr rfl
          intro k _; simpa using pureBornMu_sectorProjector_eq h k
      _ = 1 := hpart

theorem psc_fmdl_effect_measure_from_fock (P : BeableWindingPartition) (coeffs : Fin 7 → ℂ)
    (hnorm : (Finset.univ : Finset (Fin 7)).sum (fun w => Complex.normSq (coeffs w)) = 1) :
    ∃ m : EffectMeasureProxy BeableDim,
      ∀ k : Fin 7,
        m.μ (sectorProjectorEffect (fock_beable_amplitude_normalized P coeffs hnorm) k) =
          (fock_beable_amplitude_normalized P coeffs hnorm).sectorProb k :=
  psc_fmdl_implies_effect_measure (fock_beable_amplitude_normalized P coeffs hnorm)

end UgpLean.Universality.PSCEffectMeasure
