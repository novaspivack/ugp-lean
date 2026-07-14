import UgpLean.Universality.BeableWindingPartitionInstance

/-!
# UgpLean.Universality.WindingSectorSuperselection — Topological Kink Stability

Certifies the winding-sector superselection statement used by the black-hole
information argument: **no winding-preserving injective evolution can map a
non-trivial Z₇ winding sector into the vacuum sector**. Information encoded in
the winding number cannot be erased by any dynamics that respects the certified
Z₇ winding conservation law.

## Setup

The beable index space `BeableIndex = Fin (7⁵)` carries the certified winding
labeling `beableIndexWinding` (see `BeableWindingPartitionInstance.lean`, which
proves each of the 7 sectors has exactly 7⁴ = 2401 beables). A wavefunction
`ψ : BeableIndex → ℂ` is *supported in sector w* when it vanishes off the
winding-w fibre.

An evolution map `U` is *winding-preserving* when it carries sector-w-supported
states to sector-w-supported states, for every w. This is the formalization of
PSC-consistency at the sector level: the Z₇ winding charge is conserved at
every SM interaction vertex (`gte_winding_sm_vertex_conserved`,
`GUTStructure.lean` §50b) and at each of the seven GTE vertex types
(`gte_seven_vertices_z7_winding`, `GaugeInvariance.lean`), so PSC-admissible
dynamics acts within winding superselection sectors. Injectivity is the
kinematic residue of unitarity used here (a unitary is injective); no inner
product structure is needed for the conclusion.

## Main results (zero sorry, zero axioms)

- `distinct_sector_support_forces_zero`: a wavefunction supported in two
  distinct sectors is identically zero.
- `winding_sector_superselection`: a winding-preserving injective evolution
  never maps a nonzero sector-w state into sector w' ≠ w.
- `topological_kink_stability`: specialization to w' = 0 — a nonzero state of
  non-trivial winding cannot evolve into the vacuum sector.
-/

namespace UgpLean.Universality.WindingSectorSuperselection

open UgpLean.Universality.BeableWindingPartitionInstance
open BornRuleMDL

/-- `ψ` is supported in the winding-`w` sector: it vanishes on every beable
    index whose certified winding label differs from `w`. -/
def SectorSupported (ψ : BeableIndex → ℂ) (w : Fin 7) : Prop :=
  ∀ i : BeableIndex, beableIndexWinding i ≠ w → ψ i = 0

/-- An evolution map on beable wavefunctions is *winding-preserving* when it
    maps each winding sector into itself. This is the sector-level content of
    the certified Z₇ winding conservation law. -/
def WindingPreserving (U : (BeableIndex → ℂ) → (BeableIndex → ℂ)) : Prop :=
  ∀ (w : Fin 7) (ψ : BeableIndex → ℂ), SectorSupported ψ w → SectorSupported (U ψ) w

/-- A wavefunction supported in two *distinct* winding sectors is identically
    zero: every beable index has exactly one winding label, so it lies outside
    at least one of the two sectors. -/
theorem distinct_sector_support_forces_zero {ψ : BeableIndex → ℂ} {w w' : Fin 7}
    (hww' : w ≠ w') (hw : SectorSupported ψ w) (hw' : SectorSupported ψ w') :
    ψ = 0 := by
  funext i
  by_cases hi : beableIndexWinding i = w
  · exact hw' i (hi ▸ hww')
  · exact hw i hi

/-- **winding_sector_superselection** (CatAL): a winding-preserving injective
    evolution never carries a nonzero sector-`w` state into a different sector
    `w'`. Winding superselection sectors are dynamically isolated. -/
theorem winding_sector_superselection
    (U : (BeableIndex → ℂ) → (BeableIndex → ℂ))
    (hU : WindingPreserving U) (hinj : Function.Injective U) (hU0 : U 0 = 0)
    {w w' : Fin 7} (hww' : w ≠ w')
    {ψ : BeableIndex → ℂ} (hψ : SectorSupported ψ w) (hnz : ψ ≠ 0) :
    ¬ SectorSupported (U ψ) w' := by
  intro hcontra
  have hUw : SectorSupported (U ψ) w := hU w ψ hψ
  have hUzero : U ψ = 0 := distinct_sector_support_forces_zero hww' hUw hcontra
  exact hnz (hinj (hUzero.trans hU0.symm))

/-- **topological_kink_stability** (CatAL): no winding-preserving injective
    evolution maps a nonzero state of non-trivial Z₇ winding `w ≠ 0` into the
    vacuum sector. Information encoded in the winding number is preserved by
    every PSC-consistent (winding-conserving, injective) evolution — in
    particular through Hawking emission, which is such an evolution.

    Hypotheses are stated explicitly: `WindingPreserving` is the sector-level
    form of the certified Z₇ conservation law (`gte_winding_sm_vertex_conserved`,
    `gte_seven_vertices_z7_winding`); injectivity and `U 0 = 0` hold for any
    unitary (or, more generally, any invertible linear) evolution. -/
theorem topological_kink_stability
    (U : (BeableIndex → ℂ) → (BeableIndex → ℂ))
    (hU : WindingPreserving U) (hinj : Function.Injective U) (hU0 : U 0 = 0)
    {w : Fin 7} (hw : w ≠ 0)
    {ψ : BeableIndex → ℂ} (hψ : SectorSupported ψ w) (hnz : ψ ≠ 0) :
    ¬ SectorSupported (U ψ) 0 :=
  winding_sector_superselection U hU hinj hU0 hw hψ hnz

end UgpLean.Universality.WindingSectorSuperselection
