import Mathlib.Data.Matrix.Basic
import Mathlib.Data.Matrix.Diagonal
import Mathlib.Data.Matrix.Mul
import Mathlib.Data.Fin.VecNotation
import Mathlib.Data.Real.Basic
import Mathlib.Data.Real.Sqrt
import Mathlib.LinearAlgebra.BilinearForm.Hom
import Mathlib.LinearAlgebra.Matrix.BilinearForm
import Mathlib.LinearAlgebra.Matrix.ToLin

/-!
# UgpLean.Universality.LorentzInvariance (CatAL)

Lean certification that the Klein–Gordon mass-shell condition
`η(p,p) = −m²` (equivalently `ω² = |k|² + m²` in natural units) is preserved
under the Lorentz group O(1,3), establishing Poincaré invariance of the
continuum Φ_MDL dispersion relation.

## Main theorems (zero sorry)

| Theorem | Content |
|---|---|
| `minkowski_metric_def` | η = diag(−1, 1, 1, 1) |
| `lorentz_transform_preserves_inner` | Λᵀ η Λ = η ⇒ η(Λp, Λq) = η(p,q) |
| `lorentz_boost_preserves_metric` | Standard x-boost with \|β\| < 1 is Lorentz |
| `kg_dispersion_iff_mass_shell` | ω² = \|k\|² + m² ↔ η(p,p) = −m² |
| `kg_dispersion_lorentz_invariant` | On-shell ⇒ Λp on-shell for Lorentz Λ |
| `poincare_invariance_of_kg` | Lorentz + momentum-space translation invariance |
-/

namespace UgpLean.Universality.LorentzInvariance

open Matrix LinearMap Real

open LinearMap (BilinForm)

/-- Spacetime component index (`0` = time, `1..3` = space). -/
abbrev SpacetimeIdx := Fin 4

/-- A four-vector over `ℝ`. -/
abbrev FourVector := SpacetimeIdx → ℝ

/-- Minkowski metric η with signature `(−,+,+,+)`. -/
def minkowskiMetric : Matrix SpacetimeIdx SpacetimeIdx ℝ :=
  diagonal ![(-1 : ℝ), 1, 1, 1]

/-- **Definition:** η = diag(−1, 1, 1, 1). -/
theorem minkowski_metric_def :
    minkowskiMetric = diagonal ![(-1 : ℝ), 1, 1, 1] := rfl

/-- Minkowski inner product `η(v,w) = −v⁰w⁰ + v¹w¹ + v²w² + v³w³`. -/
def minkowskiInner (v w : FourVector) : ℝ :=
  -(v 0 * w 0) + v 1 * w 1 + v 2 * w 2 + v 3 * w 3

theorem minkowskiInner_eq_matrix (v w : FourVector) :
    minkowskiInner v w = v ⬝ᵥ minkowskiMetric *ᵥ w := by
  simp [minkowskiInner, Matrix.mulVec, dotProduct, minkowskiMetric, Matrix.diagonal_apply,
    Fin.sum_univ_four]

/-- A Lorentz transformation: `Λᵀ η Λ = η`. -/
def IsLorentz (Λ : Matrix SpacetimeIdx SpacetimeIdx ℝ) : Prop :=
  Λᵀ * minkowskiMetric * Λ = minkowskiMetric

/-- Four-momentum vector `(ω, k_x, k_y, k_z)`. -/
def fourMomentum (ω kx ky kz : ℝ) : FourVector :=
  ![ω, kx, ky, kz]

/-- KG mass-shell condition `η(p,p) = −m²`. -/
def onKgMassShell (m : ℝ) (p : FourVector) : Prop :=
  minkowskiInner p p = -(m ^ 2)

/-- Algebraic KG dispersion `ω² = |k|² + m²` (natural units `c = 1`). -/
def kgDispersionIdentity (m ω kx ky kz : ℝ) : Prop :=
  ω ^ 2 = kx ^ 2 + ky ^ 2 + kz ^ 2 + m ^ 2

/-- **Lorentz transformations preserve the Minkowski inner product** (zero sorry). -/
theorem lorentz_transform_preserves_inner {Λ : Matrix SpacetimeIdx SpacetimeIdx ℝ}
    (hΛ : IsLorentz Λ) (v w : FourVector) :
    minkowskiInner (Λ *ᵥ v) (Λ *ᵥ w) = minkowskiInner v w := by
  rw [minkowskiInner_eq_matrix, minkowskiInner_eq_matrix]
  have hcomp :
      minkowskiMetric.toBilin'.comp Λ.toLin' Λ.toLin' = minkowskiMetric.toBilin' := by
    rw [Matrix.toBilin'_comp, hΛ]
  have h := congrArg (fun B : BilinForm ℝ FourVector => B v w) hcomp
  simpa [BilinForm.comp_apply, Matrix.toLin'_apply, Matrix.toBilin'_apply'] using h

/-- **O(1,3) membership implies inner-product preservation** (zero sorry). -/
theorem lorentz_preserves_inner (Λ : Matrix SpacetimeIdx SpacetimeIdx ℝ) (hΛ : IsLorentz Λ) :
    ∀ v w : FourVector, minkowskiInner (Λ *ᵥ v) (Λ *ᵥ w) = minkowskiInner v w :=
  fun v w => lorentz_transform_preserves_inner hΛ v w

/-- Lorentz factor `γ = 1/√(1 − β²)` for subluminal boost parameter `β`. -/
noncomputable def lorentzGamma (β : ℝ) : ℝ :=
  1 / Real.sqrt (1 - β ^ 2)

/-- Standard Lorentz boost along the x-axis with velocity parameter `β` (`|β| < 1`). -/
noncomputable def lorentzBoostX (β : ℝ) : Matrix SpacetimeIdx SpacetimeIdx ℝ :=
  let γ := lorentzGamma β
  !![γ, -β * γ, 0, 0;
     -β * γ, γ, 0, 0;
     0, 0, 1, 0;
     0, 0, 0, 1]

private theorem lorentzGamma_sq (β : ℝ) (hβ : |β| < 1) :
    lorentzGamma β ^ 2 * (1 - β ^ 2) = 1 := by
  dsimp [lorentzGamma]
  have hpos : 0 < 1 - β ^ 2 := by
    nlinarith [abs_lt.mp hβ, sq_nonneg β]
  have hsqrt := Real.sq_sqrt (le_of_lt hpos)
  field_simp [Real.sqrt_ne_zero'.mpr hpos]
  nlinarith [hsqrt]

/-- **Standard x-boost preserves the Minkowski metric** (zero sorry). -/
theorem lorentz_boost_preserves_metric {β : ℝ} (hβ : |β| < 1) :
    IsLorentz (lorentzBoostX β) := by
  have hpos : 0 < 1 - β ^ 2 := by nlinarith [abs_lt.mp hβ, sq_nonneg β]
  have hsqrt_ne : Real.sqrt (1 - β ^ 2) ≠ 0 := Real.sqrt_ne_zero'.mpr hpos
  dsimp [IsLorentz, lorentzBoostX, minkowskiMetric]
  ext i j
  fin_cases i <;> fin_cases j <;>
    simp [Matrix.mul_apply, Matrix.transpose_apply, Matrix.diagonal_apply, Fin.sum_univ_four,
      lorentzGamma]
  all_goals
    field_simp [hsqrt_ne]
    try rw [Real.sq_sqrt (le_of_lt hpos)]
    try ring
    try nlinarith [Real.sq_sqrt (le_of_lt hpos)]

/-- **KG dispersion identity ↔ mass-shell condition** (zero sorry). -/
theorem kg_dispersion_iff_mass_shell (m ω kx ky kz : ℝ) :
    kgDispersionIdentity m ω kx ky kz ↔
      onKgMassShell m (fourMomentum ω kx ky kz) := by
  dsimp [kgDispersionIdentity, onKgMassShell, fourMomentum, minkowskiInner]
  constructor <;> intro h <;> linarith

/-- **KG mass shell is Lorentz-invariant** (zero sorry). -/
theorem kg_dispersion_lorentz_invariant {m : ℝ} {Λ : Matrix SpacetimeIdx SpacetimeIdx ℝ}
    (hΛ : IsLorentz Λ) {p : FourVector} (hp : onKgMassShell m p) :
    onKgMassShell m (Λ *ᵥ p) := by
  dsimp [onKgMassShell] at hp ⊢
  rw [lorentz_transform_preserves_inner hΛ p p, hp]

/-- A Poincaré transformation acting on momentum space (Lorentz part only). -/
structure PoincareAction where
  lorentz : Matrix SpacetimeIdx SpacetimeIdx ℝ
  shift : FourVector

/-- Momentum-space action: translations do not shift four-momentum. -/
def poincareActMomentum (g : PoincareAction) (p : FourVector) : FourVector :=
  g.lorentz *ᵥ p

/-- A Poincaré transformation is Lorentz when its linear part preserves η. -/
def PoincareAction.isLorentz (g : PoincareAction) : Prop :=
  IsLorentz g.lorentz

/-- Poincaré action preserves the KG mass shell when the Lorentz part is in O(1,3). -/
theorem poincare_action_preserves_mass_shell {m : ℝ} (g : PoincareAction)
    (hg : g.isLorentz) (p : FourVector) :
    onKgMassShell m p → onKgMassShell m (poincareActMomentum g p) :=
  kg_dispersion_lorentz_invariant hg

/-- **Poincaré invariance of the KG dispersion relation** (zero sorry). -/
theorem poincare_invariance_of_kg (m : ℝ) :
    (∀ (Λ : Matrix SpacetimeIdx SpacetimeIdx ℝ) (p : FourVector),
      IsLorentz Λ → onKgMassShell m p → onKgMassShell m (Λ *ᵥ p)) ∧
    (∀ ω kx ky kz : ℝ,
      kgDispersionIdentity m ω kx ky kz ↔
        onKgMassShell m (fourMomentum ω kx ky kz)) ∧
    (∀ (g : PoincareAction) (p : FourVector),
      g.isLorentz → onKgMassShell m p → onKgMassShell m (poincareActMomentum g p)) := by
  refine ⟨?_, ?_, ?_⟩
  · intro Λ p hΛ hp
    exact kg_dispersion_lorentz_invariant hΛ hp
  · intro ω kx ky kz
    exact kg_dispersion_iff_mass_shell m ω kx ky kz
  · intro g p hg hp
    exact poincare_action_preserves_mass_shell g hg p hp

end UgpLean.Universality.LorentzInvariance
