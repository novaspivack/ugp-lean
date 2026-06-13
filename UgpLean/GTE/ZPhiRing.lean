import Mathlib

/-!
# ℤ[φ] — the golden-ratio integer ring

The ring ℤ[φ] = ℤ[x]/(x²+x−1) is modelled as pairs `(a,b)` representing
`a + b·φ` with `φ² = φ + 1`. The inverse golden ratio satisfies
`1/φ = φ − 1`, hence coordinates `(−1, 1)` in the `{1, φ}` basis.

All theorems: zero sorry, zero custom axioms.

Level framing: Level 0 (pure ring arithmetic).
-/

namespace UgpLean.GTE.ZPhiRing

/-- Element of ℤ[φ] as coordinates `(a,b)` for `a + b·φ`. -/
structure GoldenRingElem where
  a : ℤ
  b : ℤ
  deriving DecidableEq

/-- Multiplication in ℤ[φ]: `(a₁ + b₁φ)(a₂ + b₂φ)` with `φ² = φ + 1`. -/
def goldenMul (u v : GoldenRingElem) : GoldenRingElem :=
  { a := u.a * v.a + u.b * v.b
    b := u.a * v.b + u.b * v.a + u.b * v.b }

def oneGolden : GoldenRingElem := { a := 1, b := 0 }

def phiGolden : GoldenRingElem := { a := 0, b := 1 }

/-- Coordinates of `1/φ = φ − 1` in the `{1,φ}` basis. -/
def invPhiGolden : GoldenRingElem := { a := -1, b := 1 }

/-- **inv_phi_zphi_coordinates** (CatAL):
    In ℤ[φ], `φ · (φ − 1) = 1`, so `1/φ = (−1) + 1·φ`. -/
theorem inv_phi_zphi_coordinates : goldenMul phiGolden invPhiGolden = oneGolden := by
  decide

/-- Norm `N(a + bφ) = a² + ab − b²` in ℤ[φ]. -/
def goldenNorm (z : GoldenRingElem) : ℤ :=
  z.a ^ 2 + z.a * z.b - z.b ^ 2

theorem inv_phi_zphi_norm : goldenNorm invPhiGolden = -1 := by
  decide

/-- **inv_phi_zphi_unit** (CatAL): `φ − 1` is a unit because its norm has absolute value 1. -/
theorem inv_phi_zphi_unit : goldenNorm invPhiGolden = -1 ∨ goldenNorm invPhiGolden = 1 := by
  exact Or.inl inv_phi_zphi_norm

end UgpLean.GTE.ZPhiRing
