import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.Trace
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.LinearAlgebra.Matrix.ConjTranspose
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.Data.Matrix.Mul
import Mathlib.Analysis.Matrix.PosDef
import NemS.Quantum.MatrixBasics
import UgpLean.Universality.BornRuleMDL

set_option maxHeartbeats 4000000

/-!
Parametric matrix lemmas for `PSCEffectMeasure` (Rank 070-97B2-AXIOM-CLOSURE).

All proofs are over abstract `Fin n`, avoiding concrete `7⁵` kernel elaboration.
-/

namespace UgpLean.Universality.PSCEffectMeasureGeneric

open BornRuleMDL
open NemS.Quantum
open Matrix
open scoped ComplexOrder BigOperators

variable {n : ℕ}

private lemma sesqForm_re_eq_re_dotProduct (A : Op n) (v : Fin n → ℂ) :
    (sesqForm A v).re = RCLike.re (dotProduct (star v) (A *ᵥ v)) := by
  simp [sesqForm, dotProduct, mulVec, Finset.mul_sum, mul_assoc]

private lemma isPosSemidef_of_matrixPosSemidef {A : Op n} (hA : A.PosSemidef) : IsPosSemidef A := by
  constructor
  · exact hA.isHermitian
  · intro v
    rw [sesqForm_re_eq_re_dotProduct]
    exact hA.re_dotProduct_nonneg v

private lemma conj_mul_re_nonneg (v : Fin n → ℂ) (k : Fin n) :
    (0 : ℝ) ≤ (starRingEnd ℂ (v k) * v k).re := by
  have hmul :
      (starRingEnd ℂ (v k) * v k).re =
        (v k).re * (v k).re + (v k).im * (v k).im := by
    simp only [Complex.mul_re, Complex.conj_re, Complex.conj_im]
    ring
  rw [hmul]
  nlinarith [sq_nonneg (v k).re, sq_nonneg (v k).im]

private lemma normSq_eq_star_mul_re (z : ℂ) : Complex.normSq z = (starRingEnd ℂ z * z).re := by
  simp [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]

private lemma mul_star_re_eq_normSq (z : ℂ) : (z * star z).re = Complex.normSq z := by
  rcases z with ⟨re, im⟩
  simp [Complex.normSq_apply, Complex.mul_re, Complex.conj_re, Complex.conj_im]

noncomputable def rank1Density (α : Fin n → ℂ) : Op n :=
  Matrix.vecMulVec α (star α)

theorem rank1Density_psd (α : Fin n → ℂ) : IsPosSemidef (rank1Density α) :=
  isPosSemidef_of_matrixPosSemidef (Matrix.posSemidef_vecMulVec_self_star α)

theorem rank1Density_hermitian (α : Fin n → ℂ) : (rank1Density α).IsHermitian :=
  (rank1Density_psd α).1

theorem rank1Density_trace_re (α : Fin n → ℂ) :
    (Matrix.trace (rank1Density α)).re =
      (Finset.univ : Finset (Fin n)).sum (fun i => Complex.normSq (α i)) := by
  unfold rank1Density
  rw [Matrix.trace_vecMulVec]
  simp only [dotProduct, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  simpa using mul_star_re_eq_normSq (α i)

def diagProjector (i : Fin n) : Op n :=
  Matrix.single i i (1 : ℂ)

private lemma diagProjector_psd (i : Fin n) : IsPosSemidef (diagProjector i) := by
  constructor
  · ext a b
    simp [diagProjector, Matrix.conjTranspose_apply, Matrix.single_apply, and_comm (a := i = b)]
  · intro v
    simp only [sesqForm, diagProjector, Matrix.single_apply]
    have hsum :
        (∑ a : Fin n, ∑ b : Fin n,
            starRingEnd ℂ (v a) * (if i = a ∧ i = b then (1 : ℂ) else 0) * v b) =
          starRingEnd ℂ (v i) * v i := by
      have inner : ∀ a : Fin n,
          (∑ b : Fin n, starRingEnd ℂ (v a) * (if i = a ∧ i = b then (1 : ℂ) else 0) * v b) =
            if i = a then starRingEnd ℂ (v i) * v i else 0 := by
        intro a
        by_cases ha : i = a
        · subst ha; simp
        · simp [ha]
      calc
        _ = ∑ a : Fin n, if i = a then starRingEnd ℂ (v i) * v i else 0 := by
          apply Finset.sum_congr rfl; intro a _; exact inner a
        _ = starRingEnd ℂ (v i) * v i := by simp
    rw [hsum]
    exact conj_mul_re_nonneg v i

private lemma diagProjector_hermitian (i : Fin n) : (diagProjector i).IsHermitian :=
  (diagProjector_psd i).1

private lemma isPosSemidef_sum_diag {s : Finset (Fin n)} :
    IsPosSemidef (s.sum (fun i => diagProjector i)) := by
  refine Finset.induction_on s ?base ?step
  · simpa using isPosSemidef_zero
  · intro a s ha ih
    simpa [Finset.sum_insert ha] using isPosSemidef_add (diagProjector_psd a) ih

private lemma diagProjectors_sum_one :
    (∑ i : Fin n, diagProjector i) = (1 : Op n) := by
  ext a b
  by_cases hab : a = b
  · subst hab
    have hsum : (∑ i : Fin n, (diagProjector i) a a) = 1 := by
      have hsingle :
          (∑ i : Fin n, (diagProjector i) a a) = (diagProjector a) a a := by
        refine Finset.sum_eq_single a ?_ ?_
        · intro j _ hja
          simp [diagProjector, hja]
        · simp [diagProjector]
      calc
        (∑ i : Fin n, (diagProjector i) a a) = (diagProjector a) a a := hsingle
        _ = 1 := by simp [diagProjector]
    simpa [Matrix.sum_apply, Matrix.one_apply] using hsum
  · have hsum0 : (∑ i : Fin n, (diagProjector i) a b) = 0 := by
      apply Finset.sum_eq_zero
      intro j _
      by_cases hja : j = a
      · subst hja
        simp [diagProjector, hab]
      · simp [diagProjector, hja]
    simpa [Matrix.sum_apply, Matrix.one_apply, hab] using hsum0

noncomputable def sectorProjectorOp (winding : Fin n → Fin 7) (k : Fin 7) : Op n :=
  (Finset.univ.filter (fun i : Fin n => winding i = k)).sum (fun i => diagProjector i)

theorem sectorProjectorOp_psd (winding : Fin n → Fin 7) (k : Fin 7) :
    IsPosSemidef (sectorProjectorOp winding k) := by
  unfold sectorProjectorOp
  exact isPosSemidef_sum_diag

theorem sectorProjectorOp_hermitian (winding : Fin n → Fin 7) (k : Fin 7) :
    (sectorProjectorOp winding k).IsHermitian :=
  (sectorProjectorOp_psd winding k).1

private lemma sectorProjectorOp_complement (winding : Fin n → Fin 7) (k : Fin 7) :
    (1 : Op n) - sectorProjectorOp winding k =
      (Finset.univ.filter (fun i : Fin n => winding i ≠ k)).sum (fun i => diagProjector i) := by
  set Q := (Finset.univ.filter (fun i : Fin n => winding i ≠ k)).sum (fun i => diagProjector i)
  have hpartition :
      (Finset.univ.filter (fun i : Fin n => winding i = k)).sum (fun i => diagProjector i) +
        (Finset.univ.filter (fun i : Fin n => winding i ≠ k)).sum (fun i => diagProjector i) =
        (∑ i : Fin n, diagProjector i) := by
    simpa using
      (Finset.sum_filter_add_sum_filter_not (s := (Finset.univ : Finset (Fin n)))
        (p := fun i : Fin n => winding i = k) (f := fun i => diagProjector i))
  have hsum : sectorProjectorOp winding k + Q = ∑ i : Fin n, diagProjector i := by
    simpa [sectorProjectorOp, Q] using hpartition
  calc (1 : Op n) - sectorProjectorOp winding k
      = (1 : Op n) - (sectorProjectorOp winding k + Q) + Q := by abel
    _ = (1 : Op n) - (∑ i : Fin n, diagProjector i) + Q := by rw [hsum]
    _ = Q := by rw [diagProjectors_sum_one, sub_self, zero_add]

theorem sectorProjectorOp_bounded (winding : Fin n → Fin 7) (k : Fin 7) :
    IsPosSemidef ((1 : Op n) - sectorProjectorOp winding k) := by
  rw [sectorProjectorOp_complement]
  exact isPosSemidef_sum_diag

private lemma rank1_trace_diagProjector (α : Fin n → ℂ) (i : Fin n) :
    Matrix.trace (rank1Density α * diagProjector i) = α i * star (α i) := by
  unfold rank1Density diagProjector
  rw [Matrix.trace_mul_single, Matrix.vecMulVec_apply]
  simp [one_smul, MulOpposite.op_one]

theorem rank1_trace_sectorProjector (α : Fin n → ℂ) (winding : Fin n → Fin 7) (k : Fin 7) :
    (Matrix.trace (rank1Density α * sectorProjectorOp winding k)).re =
      sectorBornWeight α winding k := by
  unfold sectorProjectorOp sectorBornWeight
  rw [Matrix.mul_sum, Matrix.trace_sum, Complex.re_sum]
  refine Finset.sum_congr rfl ?_
  intro i _
  rw [rank1_trace_diagProjector]
  simpa using mul_star_re_eq_normSq (α i)

end UgpLean.Universality.PSCEffectMeasureGeneric
