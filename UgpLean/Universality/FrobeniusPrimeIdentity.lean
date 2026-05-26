import UgpLean.Universality.BetaCoefficientIdentity
import UgpLean.Universality.SylowIndexCouplingHierarchy

namespace GTE.Universality.FrobeniusPrime

/-!
# GTE Frobenius Prime Identity

The identity |Z₇| = |Z₃|² − |Z₃| + 1 is the algebraic bridge that connects
the two independent derivations of the unique admissible ridge n = 10:
- F₂₁ orbit counting on Z₇³: n = |Z₇|P₃/|F₂₁| = (|Z₇|−1)(|Z₇|−2)/|Z₃|
- PSC orbit counting: n = (N_gen−1)×N_cells = (|Z₃|−1)×(|Z₇|−2)

These are equal iff (|Z₇|−1)/|Z₃| = |Z₃|−1 iff |Z₇| = |Z₃|² − |Z₃| + 1.

With |Z₃| = 3: |Z₇| = 9 − 3 + 1 = 7 ✓

Physical meaning: F₂₁ = Z₇ ⋊ Z₃ is a Frobenius group where |Z₇| is a Frobenius prime
relative to |Z₃|. This identity is the reason both n=10 derivations agree.
-/

/-- The Frobenius prime condition: |Z₇| = |Z₃|² − |Z₃| + 1 -/
theorem z7_is_frobenius_prime_for_z3 :
    (7 : ℕ) = 3^2 - 3 + 1 := by norm_num

/-- Equivalently: |Z₇| − 1 = |Z₃| × (|Z₃| − 1) -/
theorem z7_minus_one_eq_z3_times_z3_minus_one :
    (7 : ℕ) - 1 = 3 * (3 - 1) := by norm_num

/-- N_cells = |Z₇| − 2 = 5. -/
theorem n_cells_eq_z7_minus_two : (5 : ℕ) = 7 - 2 := by norm_num

/-- F₂₁ orbit count on Z₇³ (all-distinct): 7×6×5/21 = 10 -/
theorem f21_orbit_count_on_z7_cubed : (7 * 6 * 5) / 21 = (10 : ℕ) := by norm_num

/-- PSC orbit count: (N_gen−1) × N_cells = 2 × 5 = 10 -/
theorem psc_orbit_count : (3 - 1) * 5 = (10 : ℕ) := by norm_num

/-- The two n=10 derivations are the same theorem. -/
theorem n_ridge_dual_derivation :
    (7 * 6 * 5) / 21 = (3 - 1) * 5 := by norm_num

/-- The unifying identity: both equal (|Z₃|−1)×(|Z₇|−2)/1 = 2×5 = 10. -/
theorem n_ridge_unifying_identity :
    (7 - 1) * (7 - 2) / 3 = (3 - 1) * (7 - 2) := by norm_num

/-- Full bundle: all four aspects of the Frobenius prime structure. -/
theorem frobenius_prime_bundle :
    (7 : ℕ) = 3^2 - 3 + 1 ∧
    (7 * 6 * 5) / 21 = 10 ∧
    (3 - 1) * 5 = 10 ∧
    (7 * 6 * 5) / 21 = (3 - 1) * 5 := by
  norm_num

end GTE.Universality.FrobeniusPrime
