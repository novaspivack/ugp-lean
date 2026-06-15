import Mathlib.Data.Complex.Basic
import Mathlib.Data.Complex.BigOperators
import Mathlib.LinearAlgebra.UnitaryGroup

/-!
# Bilinear-D Unitarity Obstruction (BDUO) (EPIC_092 / 092-B1b)

For any unitary mixing matrix U, row sums of off-diagonal bilinear interference coefficients
vanish by unitarity (U†U = I). This obstructs simultaneous near-cancellation systems built
from PMNS-derived bilinear-D neutrino mass mechanisms.
-/

namespace UgpLean.QM.BilinearNeutrinoNoGo

open Matrix

variable {n : Type*} [Fintype n] [DecidableEq n]

/-- Off-diagonal column inner products vanish: ∑ⱼ U*ⱼα Uⱼβ = (U†U)αβ = 0 for α ≠ β. -/
theorem unitary_row_inner_product {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (α β : n) (h : α ≠ β) :
    ∑ j, star (U j α) * U j β = 0 := by
  have hUU : star U * U = 1 := (mem_unitaryGroup_iff' (n := n)).1 hU
  simpa [Matrix.mul_apply, Matrix.one_apply, h] using congrArg (fun M => M α β) hUU

/-- BDUO corollary: doubled real parts of off-diagonal bilinear interference sums vanish. -/
theorem bduo_interference_sum_zero {U : Matrix n n ℂ} (hU : U ∈ unitaryGroup n ℂ)
    (α β : n) (h : α ≠ β) :
    ∑ j, 2 * (star (U j α) * U j β).re = 0 := by
  have h0 := unitary_row_inner_product (U := U) hU α β h
  have hre : ∑ j, (star (U j α) * U j β).re = 0 := by
    rw [← Complex.re_sum, h0, Complex.zero_re]
  rw [← Finset.mul_sum, hre, mul_zero]

/-- PMNS-sized specialization (3×3 unitary). -/
theorem bduo_row_sum_zero {U : Matrix (Fin 3) (Fin 3) ℂ} (hU : U ∈ unitaryGroup (Fin 3) ℂ)
    (α β : Fin 3) (hαβ : α ≠ β) :
    ∑ j, (star (U j α) * U j β).re = 0 := by
  have h0 := unitary_row_inner_product (U := U) hU α β hαβ
  exact congrArg Complex.re h0

end UgpLean.QM.BilinearNeutrinoNoGo
