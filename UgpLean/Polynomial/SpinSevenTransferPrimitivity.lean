import Mathlib.Tactic
import Mathlib.LinearAlgebra.Matrix.Irreducible.Defs
import Mathlib.Analysis.SpecialFunctions.Exp
import UgpLean.Polynomial.PolyExplorations
import UgpLean.Polynomial.SpinSevenWallSpectroscopy

open UgpLean.Polynomial.PolyExplorations
open UgpLean.Polynomial.SpinSevenWallSpectroscopy

/-!
# Spin-7 thermal transfer matrix: Perron–Frobenius hypotheses

The exact pair-state transfer matrix of the spin-7 chain,
`M(β)[(a,b),(b,c)] = e^(−β·p(a,b,c))` (zero off the de Bruijn overlap),
is entrywise nonnegative for every real `β`, and its **square is entrywise
strictly positive**: from `(a,b)` the two de Bruijn steps
`(a,b) → (b,c) → (c,d)` reach every `(c,d)`, each with weight
`e^(−β·p(a,b,c))·e^(−β·p(b,c,d)) > 0`.

Hence `M(β)` is **primitive** (`Matrix.IsPrimitive`, with explicit power
`k = 2`) and therefore **irreducible** (`Matrix.IsIrreducible`) for *all*
`β : ℝ` — the full Perron–Frobenius hypothesis package (irreducibility and
aperiodicity, the latter subsumed by primitivity) for the entropy-rate
statement `S = ln λ₁`.  The conclusions of the Perron–Frobenius theorem
(positivity and simplicity of the spectral radius eigenvalue) are not yet
available in Mathlib; this module certifies the hypotheses under which they
apply.

Zero sorry.  Zero custom axioms.
-/

namespace UgpLean.Polynomial.SpinSevenTransferPrimitivity

/-- The thermal pair transfer matrix `M(β)` on the 49 de Bruijn pair states. -/
noncomputable def thermalTransfer (β : ℝ) : Matrix SpinPair SpinPair ℝ :=
  fun u v =>
    if u.2 = v.1 then Real.exp (-(β * (tripleEnergy u.1 u.2 v.2 : ℝ))) else 0

theorem thermalTransfer_nonneg (β : ℝ) (u v : SpinPair) :
    0 ≤ thermalTransfer β u v := by
  unfold thermalTransfer
  split
  · exact (Real.exp_pos _).le
  · exact le_rfl

theorem thermalTransfer_overlap_pos (β : ℝ) (a b c : Fin 7) :
    0 < thermalTransfer β (a, b) (b, c) := by
  have h : thermalTransfer β (a, b) (b, c)
      = Real.exp (-(β * (tripleEnergy a b c : ℝ))) := by
    simp [thermalTransfer]
  rw [h]
  exact Real.exp_pos _

/-- **thermal_transfer_sq_pos** (zero sorry): every entry of `M(β)²` is
    strictly positive — two de Bruijn steps connect every pair of pair
    states. -/
theorem thermal_transfer_sq_pos (β : ℝ) (u v : SpinPair) :
    0 < (thermalTransfer β ^ 2) u v := by
  rw [sq, Matrix.mul_apply]
  refine Finset.sum_pos' (fun w _ => mul_nonneg (thermalTransfer_nonneg β u w)
    (thermalTransfer_nonneg β w v)) ⟨(u.2, v.1), Finset.mem_univ _, ?_⟩
  have h1 : 0 < thermalTransfer β u (u.2, v.1) := by
    have := thermalTransfer_overlap_pos β u.1 u.2 v.1
    simpa using this
  have h2 : 0 < thermalTransfer β (u.2, v.1) v := by
    have := thermalTransfer_overlap_pos β u.2 v.1 v.2
    simpa using this
  exact mul_pos h1 h2

/-- **spin7_thermal_transfer_primitive** (CatAL — zero sorry): the spin-7
    pair transfer matrix is primitive for every real `β`, with explicit
    positivity power `k = 2`. -/
theorem spin7_thermal_transfer_primitive (β : ℝ) :
    (thermalTransfer β).IsPrimitive :=
  ⟨thermalTransfer_nonneg β,
    ⟨2, two_pos, fun u v => thermal_transfer_sq_pos β u v⟩⟩

/-- **spin7_thermal_transfer_irreducible** (CatAL — zero sorry): the spin-7
    pair transfer matrix is irreducible for every real `β`. -/
theorem spin7_thermal_transfer_irreducible (β : ℝ) :
    (thermalTransfer β).IsIrreducible :=
  (spin7_thermal_transfer_primitive β).isIrreducible

/-- Positive diagonal at the seven uniform pairs (`p(x,x,x)` finite):
    self-loops make aperiodicity manifest independently of primitivity. -/
theorem thermal_transfer_uniform_diag_pos (β : ℝ) (x : Fin 7) :
    0 < thermalTransfer β (x, x) (x, x) := by
  have := thermalTransfer_overlap_pos β x x x
  simpa using this

/-- **spin7_transfer_pf_hypotheses** (CatAL — master bundle): the complete
    Perron–Frobenius hypothesis package for the spin-7 thermal transfer
    matrix, uniform in `β : ℝ`: nonnegativity, primitivity at power 2,
    irreducibility, and positive uniform self-loops. -/
theorem spin7_transfer_pf_hypotheses (β : ℝ) :
    (∀ u v : SpinPair, 0 ≤ thermalTransfer β u v) ∧
      (thermalTransfer β).IsPrimitive ∧
        (thermalTransfer β).IsIrreducible ∧
          ∀ x : Fin 7, 0 < thermalTransfer β (x, x) (x, x) :=
  ⟨thermalTransfer_nonneg β, spin7_thermal_transfer_primitive β,
    spin7_thermal_transfer_irreducible β,
    thermal_transfer_uniform_diag_pos β⟩

end UgpLean.Polynomial.SpinSevenTransferPrimitivity
