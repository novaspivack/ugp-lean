import UgpLean.Spacetime.LiftingTheorem
import UgpLean.Spacetime.CausalGraph

namespace GTE.Spacetime.Centroid

/-!
# D-Measure Centroid (P34 [D] — Rank 17-GEO)

Formalizes the `[D]`-weighted spatial centroid `⟨x⟩_D` for physical beables.

## Model: point localization

The current `DWeight` definition (`LiftingTheorem.lean`) assigns a scalar
weight to each beable configuration (`1` if PSC-admissible, `0` otherwise).
It does not yet distribute weight across causal nodes — that requires the full
P34 coherence measure over orbit realizations.

This module uses the **point-localization model**: a physical beable `b` with
`DWeight b > 0` is assigned to a specific causal node `loc`.  The node-level
weight is

  `DWeightAt b loc n = DWeight b`  if `n = loc`, else `0`.

The centroid over a finite support set `S` is the `[D]`-weighted average of
spatial coordinates.  For point localization with `loc ∈ S`, the centroid
equals the spatial coordinates of `loc`.

## Upgrade path (P34 full measure)

When the P34 `[D]` coherence measure is formalized with orbit support over
multiple nodes, replace `DWeightAt` by the physical density
`DWeight(b, n) = Σ_{realizations} [D](b, realization at n)` and retain the
same centroid API.  The theorems in this file are the base case (delta
distribution); curvature-corrected deviation requires Ollivier–Ricci
computation (P36 / EPIC_073 Cluster J).

## Certification

| Component | Status |
|-----------|--------|
| `spatialCoords`, `DWeightAt` | CatAL — definitional |
| `totalDWeight`, `beableCentroid` | CatAL — definitional |
| `CentroidWellDefined` | CatAL — definitional |
| `centroid_well_defined` | CatAL — zero sorry |
| `beableCentroid_point` | CatAL — zero sorry |
| `centroid_denominator_pos` | CatAL — zero sorry |
-/

open GTE.Lifting GTE.Spacetime

variable (L T : ℕ)

-- ─────────────────────────────────────────────────────────────────────────────
-- §1  Spatial coordinates and node-level D-weight
-- ─────────────────────────────────────────────────────────────────────────────

/-- Spatial coordinates `(x, y, z)` of a causal node as natural numbers. -/
def spatialCoords (n : CausalNode L T) : ℕ × ℕ × ℕ :=
  (n.2.1.val, n.2.2.1.val, n.2.2.2.val)

/-- Node-level `[D]`-weight under point localization.

    All weight of beable `b` is concentrated at node `loc`.  Compatible with
    the scalar `DWeight b` from `LiftingTheorem.lean`: when `n = loc`, the
    node carries the full beable weight; all other nodes carry zero. -/
noncomputable def DWeightAt (b : Fin 5 → Fin 7) (loc n : CausalNode L T) : ℝ :=
  if n = loc then DWeight b else 0

/-- Total `[D]`-weight of beable `b` (localized at `loc`) over finite node set `S`. -/
noncomputable def totalDWeight (b : Fin 5 → Fin 7) (loc : CausalNode L T)
    (S : Finset (CausalNode L T)) : ℝ :=
  ∑ n ∈ S, DWeightAt L T b loc n

/-- Spatial `[D]`-weighted centroid `⟨x⟩_D` over support set `S`.

    Returns `(x̄, ȳ, z̄)` as real coordinates.  Well-defined when
    `totalDWeight b loc S > 0` (see `centroid_well_defined`). -/
noncomputable def beableCentroid (b : Fin 5 → Fin 7) (loc : CausalNode L T)
    (S : Finset (CausalNode L T)) : ℝ × ℝ × ℝ :=
  let w := totalDWeight L T b loc S
  let wx := ∑ n ∈ S, (n.2.1.val : ℝ) * DWeightAt L T b loc n
  let wy := ∑ n ∈ S, (n.2.2.1.val : ℝ) * DWeightAt L T b loc n
  let wz := ∑ n ∈ S, (n.2.2.2.val : ℝ) * DWeightAt L T b loc n
  (wx / w, wy / w, wz / w)

/-- The centroid denominator is nonzero — the centroid is well-defined. -/
def CentroidWellDefined (b : Fin 5 → Fin 7) (loc : CausalNode L T)
    (S : Finset (CausalNode L T)) : Prop :=
  totalDWeight L T b loc S > 0

-- ─────────────────────────────────────────────────────────────────────────────
-- §2  Well-definedness and point-localization identities
-- ─────────────────────────────────────────────────────────────────────────────

private lemma dweight_at_self (b : Fin 5 → Fin 7) (loc : CausalNode L T) :
    DWeightAt L T b loc loc = DWeight b := by
  simp [DWeightAt]

private lemma dweight_at_ne (b : Fin 5 → Fin 7) (loc n : CausalNode L T)
    (h : n ≠ loc) : DWeightAt L T b loc n = 0 := by
  simp [DWeightAt, h]

/-- **Centroid denominator positivity** (CatAL).

    If `DWeight b > 0` and the localization node `loc` is in the support set `S`,
    then `totalDWeight b loc S > 0`.  The centroid is therefore well-defined. -/
theorem centroid_denominator_pos (b : Fin 5 → Fin 7) (loc : CausalNode L T)
    (S : Finset (CausalNode L T)) (h_w : DWeight b > 0) (h_mem : loc ∈ S) :
    totalDWeight L T b loc S > 0 := by
  have h_nonneg : ∀ n ∈ S, 0 ≤ DWeightAt L T b loc n := by
    intro n _
    unfold DWeightAt
    split_ifs with h
    · have : DWeight b = 0 ∨ DWeight b = 1 := by
        simp only [DWeight]
        split_ifs <;> norm_num
      rcases this with h0 | h1
      · simp [h0]
      · norm_num [h1]
    · simp
  have h_le : DWeightAt L T b loc loc ≤ totalDWeight L T b loc S :=
    Finset.single_le_sum h_nonneg h_mem
  rw [dweight_at_self] at h_le
  exact lt_of_lt_of_le h_w h_le

/-- **Centroid well-defined** (CatAL).

    For any physical beable (`DWeight b > 0`) localized at `loc` with
    `loc ∈ S`, the `[D]`-weighted centroid `beableCentroid b loc S` is
    well-defined: the normalization denominator is strictly positive. -/
theorem centroid_well_defined (b : Fin 5 → Fin 7) (loc : CausalNode L T)
    (S : Finset (CausalNode L T)) (h_w : DWeight b > 0) (h_mem : loc ∈ S) :
    CentroidWellDefined L T b loc S :=
  centroid_denominator_pos L T b loc S h_w h_mem

private lemma totalDWeight_singleton (b : Fin 5 → Fin 7) (loc : CausalNode L T) :
    totalDWeight L T b loc {loc} = DWeight b := by
  simp [totalDWeight, Finset.sum_singleton, DWeightAt, dweight_at_self L T b loc]

/-- **Point-localization centroid** (CatAL).

    When all `[D]`-weight is at a single node `loc`, the centroid equals the
    spatial coordinates of `loc` (cast to `ℝ`).  This is the base case of the
    P34 `[D]` measure before orbit-superposition is formalized. -/
theorem beableCentroid_point (b : Fin 5 → Fin 7) (loc : CausalNode L T)
    (h_w : DWeight b > 0) :
    beableCentroid L T b loc {loc} =
      ((loc.2.1.val : ℝ), (loc.2.2.1.val : ℝ), (loc.2.2.2.val : ℝ)) := by
  unfold beableCentroid
  have hw : totalDWeight L T b loc {loc} = DWeight b :=
    totalDWeight_singleton L T b loc
  have hpos : DWeight b ≠ 0 := ne_of_gt h_w
  simp only [hw]
  have hsum_x : (∑ n ∈ ({loc} : Finset (CausalNode L T)),
      (n.2.1.val : ℝ) * DWeightAt L T b loc n) =
      (loc.2.1.val : ℝ) * DWeight b := by
    simp [Finset.sum_singleton, DWeightAt, dweight_at_self L T b loc]
  have hsum_y : (∑ n ∈ ({loc} : Finset (CausalNode L T)),
      (n.2.2.1.val : ℝ) * DWeightAt L T b loc n) =
      (loc.2.2.1.val : ℝ) * DWeight b := by
    simp [Finset.sum_singleton, DWeightAt, dweight_at_self L T b loc]
  have hsum_z : (∑ n ∈ ({loc} : Finset (CausalNode L T)),
      (n.2.2.2.val : ℝ) * DWeightAt L T b loc n) =
      (loc.2.2.2.val : ℝ) * DWeight b := by
    simp [Finset.sum_singleton, DWeightAt, dweight_at_self L T b loc]
  simp only [hsum_x, hsum_y, hsum_z]
  field_simp [hpos]

/-- Spatial centroid coordinates match `spatialCoords` at point localization. -/
theorem beableCentroid_spatialCoords (b : Fin 5 → Fin 7) (loc : CausalNode L T)
    (h_w : DWeight b > 0) :
    let c := beableCentroid L T b loc {loc}
    (c.1 = (spatialCoords L T loc).1 ∧
     c.2.1 = (spatialCoords L T loc).2.1 ∧
     c.2.2 = (spatialCoords L T loc).2.2) := by
  dsimp [spatialCoords]
  rcases beableCentroid_point L T b loc h_w with h
  simp [h]

end GTE.Spacetime.Centroid
