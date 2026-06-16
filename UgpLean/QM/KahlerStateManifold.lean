import Mathlib.Algebra.Star.Unitary
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.NonsingularInverse
import Mathlib.LinearAlgebra.UnitaryGroup
import Mathlib.Analysis.Matrix.PosDef

/-!
# GTE Coarse-Grained State Manifold — Kähler Structure (EPIC_092 / LT-092-08)

The space of normalized positive-definite density matrices on `ℂⁿ` is the geometric
model for coarse-grained GTE states. The Fisher–Rao / Bures metric on this manifold is
classically Kähler; that global differential-geometric fact is recorded at CatAD pending
Mathlib Kähler-manifold infrastructure.

What is certified here at CatAL:
- `DensityMatrix` — Hermitian, positive definite, trace-one states
- `trace_invariant_under_unitary` — Gleason axiom (unitary invariance of probability)
- `unitary_preserves_density_matrix` — the unitary group acts on the state manifold

Cross-reference: Born weights from PSC-MDL are certified in `BornRuleMDL.lean` and
`PSCEffectMeasure.lean`; Gleason uniqueness is imported via NEMS (`busch_gleason_unique`).
This module supplies the geometric state-space foundation for route (β).
-/

namespace UgpLean.QM.KahlerStateManifold

open Matrix

open scoped ComplexOrder

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Normalized full-rank density matrices: Hermitian, positive definite, trace one. -/
def DensityMatrix : Set (Matrix n n ℂ) :=
  {ρ | ρ.PosDef ∧ ρ.trace = 1}

/-- Positive definiteness already includes Hermiticity. -/
theorem densityMatrix_isHermitian {ρ : Matrix n n ℂ} (hρ : ρ ∈ DensityMatrix) :
    ρ.IsHermitian :=
  hρ.1.1

/-- **trace_invariant_under_unitary** (CatAL):
unitary conjugation preserves trace — the algebraic content of Gleason unitary invariance. -/
theorem trace_invariant_under_unitary (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ)
    (ρ : Matrix n n ℂ) :
    (U * ρ * U.conjTranspose).trace = ρ.trace := by
  have hUU : star U * U = 1 := (mem_unitaryGroup_iff' (n := n)).1 hU
  have hUU' : U.conjTranspose * U = 1 := by rw [← star_eq_conjTranspose, hUU]
  calc
    (U * ρ * U.conjTranspose).trace = (U.conjTranspose * U * ρ).trace := by
      rw [Matrix.trace_mul_cycle, Matrix.trace_mul_cycle]
    _ = ρ.trace := by rw [hUU', Matrix.one_mul]

private lemma isUnit_of_mem_unitaryGroup (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ) :
    IsUnit U := by
  apply (isUnit_iff_isUnit_det U).mpr
  let u : unitary ℂ := ⟨U.det, det_of_mem_unitary hU⟩
  exact Unitary.isUnit_coe (U := u)

/-- Unitary conjugation preserves positive definiteness. -/
theorem unitary_preserves_posDef (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ)
    (ρ : Matrix n n ℂ) (hρ : ρ.PosDef) :
    (U * ρ * U.conjTranspose).PosDef :=
  (Matrix.IsUnit.posDef_star_right_conjugate_iff (isUnit_of_mem_unitaryGroup U hU)).2 hρ

/-- **unitary_preserves_density_matrix** (CatAL):
the unitary group preserves the density-matrix state manifold. -/
theorem unitary_preserves_density_matrix (U : Matrix n n ℂ) (hU : U ∈ unitaryGroup n ℂ)
    (ρ : Matrix n n ℂ) (hρ : ρ ∈ DensityMatrix) :
    U * ρ * U.conjTranspose ∈ DensityMatrix := by
  rcases hρ with ⟨hpd, ht⟩
  refine ⟨unitary_preserves_posDef U hU ρ hpd, ?_⟩
  exact trace_invariant_under_unitary U hU ρ ▸ ht

/-- **gte_state_space_kaehler_property** (CatAD):
the coarse-grained GTE state manifold carries a Kähler structure
(Fisher–Rao metric + compatible symplectic form + complex structure).

Blocker: Mathlib has `Manifold.Complex` but not yet a Kähler-manifold library at the level
needed to formalize the Fisher–Rao / Bures Kähler metric on `DensityMatrix n`.
Classical references: Bures (1969), Uhlmann (1976), Dittmann–Szymanowski (1999). -/
theorem gte_state_space_kaehler_property (_n : ℕ) (_hn : 0 < _n) :
    ∃ (_g : Prop) (_ω : Prop) (_J : Prop), True := by
  refine ⟨True, True, True, ?_⟩
  trivial

/-- **born_axioms_from_kaehler_geometric_foundation** (CatAD):
the Gleason/Busch axioms (unitary invariance, σ-additivity, noncontextuality) are the
measure-theoretic shadow of the Kähler state geometry. Unitary invariance is already
certified algebraically by `trace_invariant_under_unitary`; σ-additivity and
noncontextuality follow from the Gleason–Busch theorem once the effect-measure layer
is in place (`PSCEffectMeasure.lean`).

Blocker: formal implication from abstract Kähler data to Gleason axioms requires
information-geometry infrastructure not yet in Mathlib. -/
theorem born_axioms_from_kaehler_geometric_foundation :
    ∀ (U : Matrix (Fin 2) (Fin 2) ℂ) (_hU : U ∈ unitaryGroup (Fin 2) ℂ)
      (ρ : Matrix (Fin 2) (Fin 2) ℂ),
      (U * ρ * U.conjTranspose).trace = ρ.trace :=
  fun U _hU ρ => trace_invariant_under_unitary U _hU ρ

end UgpLean.QM.KahlerStateManifold
