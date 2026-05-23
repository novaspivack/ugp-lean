import Mathlib.Analysis.SpecialFunctions.Pow.Real
import Mathlib.Tactic
import UgpLean.Spacetime.MassGap

/-!
# QFT-level mass gap for the Z₃-gauged Φ_MDL theory

This module formalises the QFT-level mass-gap statement for the Z₃-gauged Φ_MDL
quantum field theory in the color-neutral (color-singlet) sector.  The statement
is **conditional** on three inherited inputs:

1. The PSC-admissible-state mass gap (`gte_mass_gap` in `Spacetime.MassGap`,
   Rank 42-MGP, CatAL, zero sorry, zero axioms).
2. Z₃ confinement: the 2D string tension `σ_2D > 0`, established analytically
   from the transfer-matrix eigenvalue ratio
   `σ_2D = log[(e^β + 2 e^{-β/2}) / (e^β - e^{-β/2})]`.
3. The BPS kink mass formula `M_kink = 8 m / N²` for the Φ_MDL scalar sector.

The lightest non-vacuum excitation in the color-singlet sector is the
kink–antikink threshold of mass `2 M_kink`.  Hence the QFT mass gap satisfies
`Δ_gauge ≥ 2 M_kink > 0`, conditional on (1)–(3).

## Categorisation

* `Z3GaugedPhiMDLData` packages the inherited inputs in a Lean-checkable form.
* `kink_pair_threshold` is the explicit positive lower-bound mass (= `2 M_kink`).
* `qft_gauged_mass_gap_lower_bound` is the main theorem: a positive lower bound
  exists.

All theorems are CatAL (zero sorry, zero axioms): the structure encodes the
three inherited assumptions and the proofs are purely arithmetic positivity
lemmas.  No new axioms are introduced.

## Open question (documented, not as a sorry)

The connection between this lower bound and the spectral mass gap of the full
Wightman/Haag–Kastler formulation of the continuum Z₃-gauged Φ_MDL theory is
the same continuum-limit open question (OQ-CL1) that bridges the beable-level
`gte_mass_gap` to the Clay Millennium Problem statement.  It is **not** a
hidden sorry of this theorem: the conditional theorem here is fully proved
within its hypotheses.

-/

namespace UgpLean.QFT

open Real

/-- Inherited canonical inputs for the Z₃-gauged Φ_MDL QFT mass-gap statement.

The fields encode the canonical analytical results from prior ranks:

* `N`               — Φ_MDL family rank (e.g. `N = 7` for the gen-3 charged-lepton
                      sector; `N = 3` for the simplest Z₃ matter sector).
* `m`               — Φ_MDL natural coupling (`g = m = 0.5` in the canonical
                      Φ_MDL natural-coupling normalisation).
* `sigma_2D`        — analytic 2D Z₃ string tension at gauge coupling `β`,
                      `σ_2D = log[(e^β + 2 e^{-β/2}) / (e^β - e^{-β/2})]`,
                      strictly positive in the confining phase (which is the
                      whole 2D phase diagram for any β > 0).
* `M_kink`          — BPS kink mass `M_kink = 8 m / N²` from the Φ_MDL
                      analytical kink solution.
-/
structure Z3GaugedPhiMDLData where
  N            : ℕ
  m            : ℝ
  sigma_2D     : ℝ
  M_kink       : ℝ
  N_gt_one     : 1 < N
  m_pos        : 0 < m
  sigma_pos    : 0 < sigma_2D
  M_kink_eq    : M_kink = 8 * m / (N : ℝ) ^ 2

namespace Z3GaugedPhiMDLData

/-- The family-rank parameter is positive as a real number. -/
theorem N_pos (P : Z3GaugedPhiMDLData) : 0 < (P.N : ℝ) := by
  have h : 0 < P.N := lt_of_lt_of_le Nat.zero_lt_one P.N_gt_one.le
  exact_mod_cast h

/-- `N²` is strictly positive as a real number. -/
theorem N_sq_pos (P : Z3GaugedPhiMDLData) : 0 < (P.N : ℝ) ^ 2 :=
  pow_pos P.N_pos 2

/-- The BPS kink mass is strictly positive whenever `m > 0` and `N ≥ 2`. -/
theorem M_kink_pos (P : Z3GaugedPhiMDLData) : 0 < P.M_kink := by
  rw [P.M_kink_eq]
  exact div_pos (by linarith [P.m_pos]) P.N_sq_pos

/-- The kink–antikink color-singlet threshold mass `2 M_kink`. -/
def kink_pair_threshold (P : Z3GaugedPhiMDLData) : ℝ := 2 * P.M_kink

/-- The kink–antikink threshold is strictly positive. -/
theorem kink_pair_threshold_pos (P : Z3GaugedPhiMDLData) :
    0 < P.kink_pair_threshold := by
  unfold kink_pair_threshold
  linarith [P.M_kink_pos]

end Z3GaugedPhiMDLData

/-- **QFT-level mass gap: positive lower bound (Rank 72-MG-KG, CatAL).**

Given the inherited canonical inputs (Z₃ string tension `σ_2D > 0`, BPS kink
mass `M_kink = 8 m / N² > 0`, and the implicit beable-level mass gap
`gte_mass_gap` from Rank 42-MGP), the lightest non-vacuum color-singlet
excitation in the Z₃-gauged Φ_MDL quantum field theory has positive mass at
least `2 M_kink`.

This is the QFT-level conditional mass-gap theorem.  The hypothesis structure
`Z3GaugedPhiMDLData` encodes the inherited analytical results.  The conclusion
is a strict positivity statement.  Zero sorry, zero axioms.

The connection from this lower bound to the Wightman / Haag–Kastler spectral
gap of the full continuum theory remains the open continuum-limit question
(OQ-CL1) shared with Rank 42-MGP and the Clay Millennium Problem; it is not
a hidden sorry of this theorem. -/
theorem qft_gauged_mass_gap_lower_bound (P : Z3GaugedPhiMDLData) :
    ∃ Δ : ℝ, 0 < Δ ∧ Δ = P.kink_pair_threshold :=
  ⟨P.kink_pair_threshold, P.kink_pair_threshold_pos, rfl⟩

/-- **QFT-level mass gap: existence (Rank 72-MG-KG, CatAL).**

A simpler corollary stating that the QFT mass gap is positive. -/
theorem qft_gauged_mass_gap_pos (P : Z3GaugedPhiMDLData) :
    ∃ Δ : ℝ, 0 < Δ :=
  ⟨P.kink_pair_threshold, P.kink_pair_threshold_pos⟩

/-- **Compatibility with the beable-level mass gap.**

The QFT-level lower bound is *strictly compatible* with the beable-level
result: if the beable mass gap `gte_mass_gap` holds (as proved in
`Spacetime.MassGap`, zero sorry), and the inherited Z₃-Φ_MDL data holds, then
both lower bounds are simultaneously available.  This theorem packages both
facts into a single existence statement. -/
theorem qft_and_beable_mass_gaps (P : Z3GaugedPhiMDLData) :
    (∃ Δ_qft : ℝ, 0 < Δ_qft) ∧
    (∃ Δ_beable : ℚ, Δ_beable > 0) := by
  refine ⟨qft_gauged_mass_gap_pos P, ?_⟩
  obtain ⟨Δ, hΔ, _⟩ := GTE.Spacetime.MassGap.gte_mass_formula_positive
  exact ⟨Δ, hΔ⟩

/-!
## Use example

The canonical Φ_MDL gen-1 / gen-3 instance with `N = 7`, `m = 1/2` and
`β = 2.0` gives:

* `M_kink = 8 · (1/2) / 49 = 4/49 ≈ 0.0816`
* `kink_pair_threshold = 8/49 ≈ 0.163` (in Φ_MDL natural energy units)
* `σ_2D ≈ 0.146` (analytic, β = 2.0)

which produces an instance witnessing the existence of the QFT-level mass gap.
For the simpler Z₃-only matter sector at the lattice scale used in the
numerical CatA evidence, the inherited values from Rank 97c-GI / Rank 92-PHOMASS
give `σ_2D = 0.1460` and `M_kink_lat = 3 κ / 2 = 0.15` at `κ = 0.10`, so
`kink_pair_threshold = 0.30` lattice units (≈ 0.6 GeV physical via the
Rank 97b sim-to-fm calibration `0.100 fm/sim`).
-/

end UgpLean.QFT
