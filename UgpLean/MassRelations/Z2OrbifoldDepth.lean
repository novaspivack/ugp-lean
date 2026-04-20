import UgpLean.MassRelations.FroggattNielsen

/-!
# UgpLean.MassRelations.Z2OrbifoldDepth — Round 23 Claim C sub-(i)

**Round 23 (Track D Claim C residual sub-question (i)):** structural origin
of the doubled FN charges (1, 2, 4) for lepton FN_1 in Round 21's UV completion.

## Hypothesis

The doubled lepton FN_1 charge assignment `q_lep^(1)_g = 2^(g-1)` for
generations `g = 1, 2, 3` arises naturally from a **Z_2 orbifold depth
interpretation**: generation g lives at depth `(g-1)` in a binary tree
of Z_2 orbifold fixed-point classes, with `2^(g-1)` classes at depth `(g-1)`.

**Physical realisation candidate:** heterotic-string compactification on
a Z_2^n orbifold where each generation is a fixed-point class at increasing
depth.  Detailed model construction is open (string-theoretic) and out of
scope for this Lean module.

## What this module formalises

- The `binaryTreeDepth g := 2^(g-1)` function (depth-g class count of a Z_2
  orbifold).
- The exact equality `binaryTreeDepth g = -Δq^(1)_g` (Round 21 FN charge
  difference, in absolute value), establishing that the Z_2-orbifold-depth
  interpretation is a CONSISTENT structural reading of the FN charge
  assignment.

## Suggestive (but not proved) connection to Round-13 Mersenne cascade

Round 13 Session 3 observed that canonical lepton c-values follow Mersenne
numbers `2^n_g - 1` with `n_g = 4 + 6·2^(g-2)` for g ≥ 2.  This is also a
2^g cascade structure, but with a different exponential-base scaling than
the FN charges.  The two structures (FN charges and Mersenne ridge levels)
are likely DUAL aspects of the same underlying binary-doubling mechanism,
but the exact map remains an open structural question (Lab Notes 25 §3).
-/

namespace UgpLean.MassRelations.Z2OrbifoldDepth

/-- The number of Z_2-orbifold fixed-point classes at depth `(g-1)`.
    For a Z_2 action on a binary tree, depth d has 2^d classes.
    Generation g sits at depth (g-1), giving 2^(g-1) classes. -/
def binaryTreeDepth (g : ℕ) : ℕ := 2 ^ (g - 1)

/-- Standard FN-charge-magnitude function: lepton FN_1 charge is
    `q_lep^(1)_g = 2^(g-1)`, giving (1, 2, 4) for g = 1, 2, 3. -/
def leptonFN1Charge : ℕ → ℕ := binaryTreeDepth

/-- Concrete FN-charge sequence for the first three generations. -/
theorem leptonFN1_g123 :
    leptonFN1Charge 1 = 1 ∧ leptonFN1Charge 2 = 2 ∧ leptonFN1Charge 3 = 4 := by
  refine ⟨?_, ?_, ?_⟩ <;> rfl

/-- **Claim C sub-(i) connection:** the Z_2-orbifold-depth function exactly
    reproduces (the magnitude of) the Round-21 FN charge difference Δq^(1)_g.

    Concretely: `|Δq^(1)_g| = 2^(g-1) = binaryTreeDepth g` for g ≥ 1. -/
theorem binaryTreeDepth_matches_FN_charge_magnitude (g : ℕ) (hg : g ≥ 1) :
    -UgpLean.MassRelations.FroggattNielsen.Δq1 g = (binaryTreeDepth g : ℝ) := by
  unfold UgpLean.MassRelations.FroggattNielsen.Δq1 binaryTreeDepth
  -- Δq1 g = -(2 : ℝ)^(g-1), so -Δq1 g = (2 : ℝ)^(g-1) = (2^(g-1) : ℕ) : ℝ
  push_cast
  ring

/-- **Round-21 FN model is consistent with a Z_2 orbifold interpretation:**
    the FN-1 charge difference at generation g equals (with sign)
    the Z_2-orbifold-depth function for g ≥ 1. -/
theorem FN_charge_consistent_with_Z2_orbifold (g : ℕ) (hg : g ≥ 1) :
    UgpLean.MassRelations.FroggattNielsen.Δq1 g = -(binaryTreeDepth g : ℝ) :=
  by linarith [binaryTreeDepth_matches_FN_charge_magnitude g hg]

end UgpLean.MassRelations.Z2OrbifoldDepth
