import Mathlib.Tactic
import Mathlib.Data.Complex.Basic
import Mathlib.LinearAlgebra.Matrix.PosDef
import Mathlib.LinearAlgebra.Matrix.Hermitian
import Mathlib.Data.Matrix.Mul

/-!
# Dual-Frame Born Rule — Rank 074-PHIBORN2b-LEAN (EPIC_074)

Pure linear-algebra certification of the canonical dual frame for a positive-definite
Gram matrix.

For a non-orthogonal frame with Gram matrix `G` (entries `G j k = ⟨ψⱼ|ψₖ⟩`), define
primal overlap amplitudes `a = G *ᵥ c₀` from expansion coefficients `c₀`. The dual-frame
amplitudes `c̃ = G⁻¹ *ᵥ a` recover the expansion coefficients exactly:
`c̃ = c₀`.

The Born rule follows: when `∑ₖ |c₀ₖ|² = 1`, the dual-frame weights satisfy
`∑ₖ |c̃ₖ|² = 1`, hence `P(k) = |c̃ₖ|² = |c₀ₖ|²`.

## Proved (zero sorry, zero axioms — CatAL)

- `dual_gram_identity`: `G⁻¹ * G = 1` for positive-definite `G`
- `dual_frame_orthonormal`: `(G⁻¹ * G) j k = δⱼₖ`
- `dual_frame_recovers_coefficients`: `G⁻¹ *ᵥ (G *ᵥ c) = c`
- `born_rule_from_dual_frame`: normalized coefficients stay normalized under dual frame
- `born_rule_from_dual_frame_master`: bundled dual-frame Born rule statement
-/

namespace UgpLean.Universality.DualFrameBornRule

open Matrix
open scoped BigOperators ComplexOrder

variable {n : ℕ} [Fintype (Fin n)] [DecidableEq (Fin n)]

/-- Primal frame overlap amplitudes `aⱼ = ∑ₖ Gⱼₖ cₖ`. -/
noncomputable def frameOverlapAmps (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ) : Fin n → ℂ :=
  G.mulVec c

/-- Dual-frame amplitudes `c̃ = G⁻¹ *ᵥ a` from overlap amplitudes `a`. -/
noncomputable def dualFrameAmps (G : Matrix (Fin n) (Fin n) ℂ) (a : Fin n → ℂ) : Fin n → ℂ :=
  G⁻¹.mulVec a

/-- Dual-frame Born amplitudes from expansion coefficients via the Gram matrix. -/
noncomputable def dualFrameBornAmps (G : Matrix (Fin n) (Fin n) ℂ) (c : Fin n → ℂ) : Fin n → ℂ :=
  dualFrameAmps G (frameOverlapAmps G c)

/-- Coefficient vector is normalized in the Born sense: `∑ₖ |cₖ|² = 1`. -/
def coeffsNormalized (c : Fin n → ℂ) : Prop :=
  (Finset.univ : Finset (Fin n)).sum (fun k => Complex.normSq (c k)) = 1

private lemma posDef_isUnit_det (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) :
    IsUnit G.det := by
  haveI := hG.isUnit.invertible
  exact isUnit_det_of_invertible (A := G)

/-- **dual_gram_identity**: for positive-definite `G`, left inverse is `G⁻¹`. -/
theorem dual_gram_identity (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) :
    G⁻¹ * G = (1 : Matrix (Fin n) (Fin n) ℂ) :=
  nonsing_inv_mul G (posDef_isUnit_det G hG)

/-- **dual_frame_orthonormal**: dual frame is orthonormal in the Gram inner product. -/
theorem dual_frame_orthonormal (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) (j k : Fin n) :
    (G⁻¹ * G) j k = if j = k then (1 : ℂ) else 0 := by
  rw [dual_gram_identity G hG, Matrix.one_apply]

/-- **dual_frame_recovers_coefficients**: `G⁻¹ *ᵥ (G *ᵥ c) = c`. -/
theorem dual_frame_recovers_coefficients (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef)
    (c : Fin n → ℂ) : dualFrameBornAmps G c = c := by
  haveI := hG.isUnit.invertible
  exact inv_mulVec_eq_vec (u := frameOverlapAmps G c) (v := c) rfl

/-- Per-mode dual-frame amplitude equals the expansion coefficient. -/
theorem dual_frame_amplitude_eq_coeff (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef)
    (c : Fin n → ℂ) (k : Fin n) : dualFrameBornAmps G c k = c k :=
  congrArg (fun v => v k) (dual_frame_recovers_coefficients G hG c)

/-- **born_rule_from_dual_frame**: normalization is preserved by the dual frame. -/
theorem born_rule_from_dual_frame (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) (c : Fin n → ℂ)
    (hnorm : coeffsNormalized c) :
    (Finset.univ : Finset (Fin n)).sum (fun k => Complex.normSq (dualFrameBornAmps G c k)) = 1 := by
  rw [dual_frame_recovers_coefficients G hG c]
  exact hnorm

/-- **born_rule_from_dual_frame_master**: bundled dual-frame Born rule (CatAL). -/
theorem born_rule_from_dual_frame_master (G : Matrix (Fin n) (Fin n) ℂ) (hG : G.PosDef) :
    ∀ (c : Fin n → ℂ),
      coeffsNormalized c →
        (∀ k : Fin n, dualFrameBornAmps G c k = c k) ∧
          (Finset.univ : Finset (Fin n)).sum (fun k => Complex.normSq (dualFrameBornAmps G c k)) =
            1 := by
  intro c hnorm
  refine ⟨?_, born_rule_from_dual_frame G hG c hnorm⟩
  intro k
  exact dual_frame_amplitude_eq_coeff G hG c k

end UgpLean.Universality.DualFrameBornRule
