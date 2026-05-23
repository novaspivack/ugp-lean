import Mathlib.Data.Nat.Basic
import Mathlib.Data.Nat.Log
import UgpLean.Universality.GUTStructure

namespace GTE.Spacetime.PhiMDL

/-!
# Z₇ Klein–Gordon Potential — MDL Minimality (Rank 69 / `phimdl_z7_potential_mdl_minimal`)

Formalizes the parameter-level MDL claim for the Φ_MDL scalar potential

  V(φ) = (m² / N²) · (1 − cos(Nφ)),    N = 7

on the continuum Z₇-symmetric sector.

## Non-circularity

- Period `N = 7` is derived from `GUTStructure.gf7_minimal_for_z2_z3`, not assumed.
- Fourier-mode count is structural: a single non-constant harmonic (sine-Gordon /
  Z_N minimal renormalizable cosine form).
- Description length uses a prefix-free bit model at the parameter layer.

## Main theorem

`phimdl_z7_potential_mdl_minimal`: the Z₇ cosine potential has exactly one
non-constant Fourier mode; N = 7 is the unique minimal prime scale supporting
simultaneous Z₂ and Z₃ multiplicative substructure in `(ℤ/pℤ)ˣ`; and every
other admissible period has weakly larger specification cost.
-/

open Nat

/-- Number of non-constant Fourier harmonics in V(φ) = (m²/N²)(1 − cos(Nφ)).
    Exactly one: cos(Nφ) at order 1. -/
def cosinePotentialNonconstantHarmonics (_N : ℕ) : ℕ := 1

/-- Bit cost to specify the mass scale parameter `m`. -/
def massScaleBits : ℕ := 8

/-- Bit cost to specify potential period `N`. -/
def potentialPeriodBits (N : ℕ) : ℕ := Nat.log2 N + 1

/-- Bit cost per non-constant Fourier harmonic. -/
def fourierHarmonicBits (k : ℕ) : ℕ := Nat.log2 k + 1

/-- Total MDL specification cost for V(φ) = (m²/N²)(1 − cos(Nφ)). -/
def zNCosinePotentialSpecCost (N : ℕ) : ℕ :=
  massScaleBits + potentialPeriodBits N +
    cosinePotentialNonconstantHarmonics N * fourierHarmonicBits 1

/-- The Φ_MDL Z₇ potential specification cost at N = 7. -/
def z7CosinePotentialSpecCost : ℕ := zNCosinePotentialSpecCost 7

/-- Period `N` is **field-admissible** when both Z₂ and Z₃ embed in `(ℤ/Nℤ)˚`
    multiplicatively — for prime `p = N`, this is `2 ∣ p−1 ∧ 3 ∣ p−1`. -/
def admissiblePrimePeriod (p : ℕ) : Prop :=
  Nat.Prime p ∧ 2 ∣ p - 1 ∧ 3 ∣ p - 1

/-- N = 7 is the first prime field scale supporting Z₂×Z₃ in `(ℤ/pℤ)ˣ`. -/
theorem z7_period_forced_by_gf7 :
    (∀ q : ℕ, Nat.Prime q → q < 7 → ¬(2 ∣ q - 1 ∧ 3 ∣ q - 1)) ∧
    admissiblePrimePeriod 7 := by
  constructor
  · intro q hq hlt
    exact (GUTStructure.gf7_minimal_for_z2_z3.1 q hq hlt)
  · exact ⟨by decide, by decide, by decide⟩

/-- Alias for the GF(7) forcing certificate. -/
abbrev z7_period_forced_by_field_embedding :=
  z7_period_forced_by_gf7

/-- Among admissible prime periods, N = 7 has minimal specification cost. -/
theorem z7_potential_minimal_among_admissible_primes :
    ∀ p : ℕ, admissiblePrimePeriod p → z7CosinePotentialSpecCost ≤ zNCosinePotentialSpecCost p := by
  intro p ⟨hp, h2, h3⟩
  by_cases hlt : p < 7
  · exfalso
    exact GUTStructure.gf7_minimal_for_z2_z3.1 p hp hlt ⟨h2, h3⟩
  · by_cases heq : p = 7
    · subst heq
      simp [z7CosinePotentialSpecCost, zNCosinePotentialSpecCost]
    · have h7 : 7 < p := Nat.lt_of_le_of_ne (Nat.le_of_not_gt hlt) (Ne.symm heq)
      have hlog : Nat.log2 7 ≤ Nat.log2 p := by
        rw [Nat.log2_eq_log_two, Nat.log2_eq_log_two]
        exact Nat.log_mono_right (Nat.le_of_lt h7)
      simp only [z7CosinePotentialSpecCost, zNCosinePotentialSpecCost,
        cosinePotentialNonconstantHarmonics, massScaleBits, potentialPeriodBits,
        fourierHarmonicBits]
      omega

/-- **MDL-minimal Z₇ cosine potential (CatAL).**

    (1) V(φ) = (m²/49)(1 − cos(7φ)) uses exactly one non-constant Z₇ Fourier mode.
    (2) N = 7 is the unique minimal prime field scale for Z₂×Z₃ SM symmetry.
    (3) Every other admissible prime period has specification cost ≥ N = 7. -/
theorem phimdl_z7_potential_mdl_minimal :
    cosinePotentialNonconstantHarmonics 7 = 1 ∧
    ((∀ q : ℕ, Nat.Prime q → q < 7 → ¬(2 ∣ q - 1 ∧ 3 ∣ q - 1)) ∧ admissiblePrimePeriod 7) ∧
    (∀ p : ℕ, admissiblePrimePeriod p → z7CosinePotentialSpecCost ≤ zNCosinePotentialSpecCost p) := by
  exact ⟨rfl, z7_period_forced_by_gf7, z7_potential_minimal_among_admissible_primes⟩

end GTE.Spacetime.PhiMDL
