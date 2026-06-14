import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Topology.MetricSpace.GromovHausdorffRealized
import Mathlib.Topology.MetricSpace.HausdorffDistance
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Analysis.Normed.Lp.PiLp
import Mathlib.Analysis.Normed.Lp.WithLp
import Mathlib.Analysis.Normed.Module.FiniteDimension
import Mathlib.Algebra.Order.Floor.Ring
import Mathlib.Algebra.Order.Floor.Semiring
import Mathlib.Order.ConditionallyCompleteLattice.Finset
import UgpLean.Spacetime.CausalGraph
import UgpLean.Spacetime.OrbitDepthEtherPeriod
import UgpLean.Gravity.GorardRicciFlatVacuum

/-!
# Vacuum CMCA Spatial Gromov-Hausdorff Convergence to Flat Space

The scaled L∞ metric on the finite spatial grid `Fin L × Fin L × Fin L` converges in
Gromov-Hausdorff distance to the flat unit cube `[0,1]³` as `L → ∞`.
-/

namespace UgpLean.Spacetime.VacuumGHConvergence

open GTE.Spacetime
open GTE.Spacetime.OrbitDepthEtherPeriod
open UgpLean.Gravity.GorardRicciFlatVacuum
open GromovHausdorff
open Filter Topology
open WithLp
open scoped ENNReal

instance one_le_infty : Fact (1 ≤ (∞ : ENNReal)) := ⟨le_top⟩

/-! ## Section 1: Finite spatial grid with scaled L∞ metric -/

abbrev FinGrid (L : ℕ) := Fin L × Fin L × Fin L

noncomputable def finAxisDiff (x y : Fin L) : ℝ :=
  |((x.val : ℤ) - (y.val : ℤ) : ℝ)|

noncomputable def finGridDist (L : ℕ) (_hL : 0 < L) (x y : FinGrid L) : ℝ :=
  max (max (finAxisDiff x.1 y.1) (finAxisDiff x.2.1 y.2.1)) (finAxisDiff x.2.2 y.2.2) / (L : ℝ)

lemma finAxisDiff_nonneg (x y : Fin L) : 0 ≤ finAxisDiff x y := abs_nonneg _

lemma finGridDist_nonneg (L : ℕ) (hL : 0 < L) (x y : FinGrid L) :
    0 ≤ finGridDist L hL x y := by
  unfold finGridDist
  apply div_nonneg
  · unfold finAxisDiff
    positivity
  · exact Nat.cast_nonneg L

lemma real_ciSup_fin_three_max (f : Fin 3 → ℝ) :
    ⨆ i : Fin 3, f i = max (max (f 0) (f 1)) (f 2) := by
  apply le_antisymm
  · refine ciSup_le fun i => ?_
    fin_cases i <;> simp [Fin.isValue, le_max_iff]
  · have hBdd : BddAbove (Set.range f) :=
      ⟨max (max (f 0) (f 1)) (f 2), by
        rintro _ ⟨i, rfl⟩
        fin_cases i <;> simp [Fin.isValue, le_max_iff]⟩
    refine max_le (max_le (le_ciSup hBdd 0) (le_ciSup hBdd 1)) (le_ciSup hBdd 2)

lemma ciSup_fin_three_div (L : ℕ) (hL : 0 < L) (f : Fin 3 → ℝ) :
    ⨆ i, f i / (L : ℝ) = (⨆ i, f i) / (L : ℝ) := by
  have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hmax :
      max (max (f 0 / (L : ℝ)) (f 1 / (L : ℝ))) (f 2 / (L : ℝ)) =
        max (max (f 0) (f 1)) (f 2) / (L : ℝ) := by
    -- SORRY: max commutes with division on ℝ (finite case)
    sorry
  rw [real_ciSup_fin_three_max (fun i => f i / (L : ℝ)), hmax, ← real_ciSup_fin_three_max]

/-! ## Section 2: Unit cube target (compact metric space) -/

noncomputable abbrev AmbientCube := PiLp (∞ : ENNReal) (fun _ : Fin 3 => ℝ)

noncomputable def cubeCoord (p : AmbientCube) (i : Fin 3) : ℝ := p i

lemma cubeCoord_eq_ofLp (p : AmbientCube) (i : Fin 3) : cubeCoord p i = p.ofLp i := rfl

def unitCubeSet : Set AmbientCube :=
  {p | ∀ i, 0 ≤ p.ofLp i ∧ p.ofLp i ≤ 1}

abbrev UnitCube := {p : AmbientCube // p ∈ unitCubeSet}

noncomputable instance unitCubeMetricSpaceInst : MetricSpace UnitCube :=
  inferInstanceAs (MetricSpace (Subtype (· ∈ unitCubeSet)))

lemma mem_unitCubeSet_iff {p : AmbientCube} :
    p ∈ unitCubeSet ↔ ∀ i, 0 ≤ p.ofLp i ∧ p.ofLp i ≤ 1 := by
  simp [unitCubeSet]

lemma piLp_continuous_apply (i : Fin 3) :
    Continuous (fun p : AmbientCube => cubeCoord p i) := by
  simpa [cubeCoord] using PiLp.continuous_apply (∞ : ENNReal) (fun _ : Fin 3 => ℝ) i

lemma unitCube_closed : IsClosed unitCubeSet := by
  have h : unitCubeSet = ⋂ i : Fin 3, {p : AmbientCube | 0 ≤ p.ofLp i ∧ p.ofLp i ≤ 1} := by
    ext p
    simp [unitCubeSet, Set.mem_iInter]
  rw [h]
  refine isClosed_iInter fun i => ?_
  simpa [Set.setOf_and] using
    (isClosed_le continuous_const (piLp_continuous_apply i)).inter
      (isClosed_le (piLp_continuous_apply i) continuous_const)

lemma unitCube_subset_closedBall :
    unitCubeSet ⊆ Metric.closedBall (0 : AmbientCube) 2 := by
  intro p hp
  simp only [Metric.mem_closedBall, dist_zero_right, PiLp.norm_eq_ciSup, Real.norm_eq_abs]
  refine ciSup_le fun i => ?_
  simp only [unitCubeSet] at hp
  have hi := hp i
  exact le_trans (abs_le.mpr ⟨by linarith [hi.1], hi.2⟩) (by norm_num : (1 : ℝ) ≤ 2)

lemma unitCube_compact : IsCompact unitCubeSet := by
  haveI : ProperSpace AmbientCube := inferInstance
  exact IsCompact.of_isClosed_subset (isCompact_closedBall 0 2) unitCube_closed unitCube_subset_closedBall

lemma unitCube_compact_univ : IsCompact (Set.univ : Set UnitCube) := by
  rw [Subtype.isCompact_iff]
  simp only [Set.image_univ, Subtype.range_coe_subtype]
  exact unitCube_compact

noncomputable instance unitCubeCompactSpace : CompactSpace UnitCube :=
  (isCompact_univ_iff.mp unitCube_compact_univ)

noncomputable instance unitCubeNonempty : Nonempty UnitCube :=
  ⟨⟨toLp (∞ : ENNReal) (fun (_ : Fin 3) => (0 : ℝ)),
    mem_unitCubeSet_iff.mpr fun (_ : Fin 3) => ⟨le_rfl, (zero_le_one : (0 : ℝ) ≤ 1)⟩⟩⟩

/-! ## Section 3: Grid embedding and induced metric -/

noncomputable def finGridToAmbient (L : ℕ) (_hL : 0 < L) (g : FinGrid L) : AmbientCube :=
  toLp (∞ : ENNReal) fun i =>
    match i with
    | 0 => (g.1.val : ℝ) / L
    | 1 => (g.2.1.val : ℝ) / L
    | 2 => (g.2.2.val : ℝ) / L

lemma finGridToAmbient_cubeCoord (L : ℕ) (hL : 0 < L) (g : FinGrid L) (i : Fin 3) :
    cubeCoord (finGridToAmbient L hL g) i =
      match i with
      | 0 => (g.1.val : ℝ) / L
      | 1 => (g.2.1.val : ℝ) / L
      | 2 => (g.2.2.val : ℝ) / L := by
  fin_cases i <;> simp [cubeCoord, finGridToAmbient]

lemma finGrid_coord_le_L (L : ℕ) (hL : 0 < L) (x : Fin L) :
    (x.val : ℝ) ≤ L := by
  exact_mod_cast Nat.le_of_lt x.isLt

lemma finGridToAmbient_mem (L : ℕ) (hL : 0 < L) (g : FinGrid L) :
    finGridToAmbient L hL g ∈ unitCubeSet := by
  rw [mem_unitCubeSet_iff]
  intro i
  fin_cases i <;>
    refine ⟨div_nonneg (Nat.cast_nonneg _) (Nat.cast_nonneg L), ?_⟩
  · exact (div_le_one (Nat.cast_pos.mpr hL)).mpr (finGrid_coord_le_L L hL g.1)
  · exact (div_le_one (Nat.cast_pos.mpr hL)).mpr (finGrid_coord_le_L L hL g.2.1)
  · exact (div_le_one (Nat.cast_pos.mpr hL)).mpr (finGrid_coord_le_L L hL g.2.2)

noncomputable def finGridToCube (L : ℕ) (hL : 0 < L) (g : FinGrid L) : UnitCube :=
  ⟨finGridToAmbient L hL g, finGridToAmbient_mem L hL g⟩

lemma finGridToAmbient_injective (L : ℕ) (hL : 0 < L) :
    Function.Injective (finGridToAmbient L hL) := by
  intro x y h
  have hfun := congr_arg ofLp h
  rcases x with ⟨x₁, x₂, x₃⟩
  rcases y with ⟨y₁, y₂, y₃⟩
  simp only [finGridToAmbient, Fin.forall_fin_succ] at hfun
  have hLne : (L : ℝ) ≠ 0 := Nat.cast_ne_zero.mpr (ne_of_gt hL)
  have hx0 := congr_arg (fun f => f 0) hfun
  have hx1 := congr_arg (fun f => f 1) hfun
  have hx2 := congr_arg (fun f => f 2) hfun
  simp at hx0 hx1 hx2
  field_simp [hLne] at hx0 hx1 hx2
  have hx₁ : x₁ = y₁ := Fin.ext (by exact_mod_cast hx0)
  have hx₂ : x₂ = y₂ := Fin.ext (by exact_mod_cast hx1)
  have hx₃ : x₃ = y₃ := Fin.ext (by exact_mod_cast hx2)
  exact Prod.ext hx₁ (Prod.ext hx₂ hx₃)

lemma finGridToAmbient_dist_eq (L : ℕ) (hL : 0 < L) (x y : FinGrid L) :
    dist (finGridToAmbient L hL x) (finGridToAmbient L hL y) = finGridDist L hL x y := by
  -- SORRY: PiLp iSup / scaled L∞ max alignment (finGridToAmbient_cubeCoord + ciSup_fin_three_div)
  sorry

@[reducible]
noncomputable def finGridMetricSpace (L : ℕ) (hL : 0 < L) : MetricSpace (FinGrid L) :=
  MetricSpace.induced (finGridToAmbient L hL) (finGridToAmbient_injective L hL) inferInstance

noncomputable instance finGridNonemptyInst (L : ℕ) (hL : 0 < L) : Nonempty (FinGrid L) :=
  ⟨⟨⟨0, hL⟩, ⟨0, hL⟩, ⟨0, hL⟩⟩⟩

lemma finGridToCube_dist_eq (L : ℕ) (hL : 0 < L) (x y : FinGrid L) :
    dist (finGridToCube L hL x) (finGridToCube L hL y) = finGridDist L hL x y := by
  simpa using finGridToAmbient_dist_eq L hL x y

lemma floorCoord_lt (L : ℕ) (hL : 0 < L) (p : AmbientCube) (_hp : p ∈ unitCubeSet) (i : Fin 3) :
    min (⌊p i * (L : ℝ)⌋₊) (L - 1) < L :=
  (min_le_right _ _).trans_lt (Nat.pred_lt (ne_of_gt hL))

lemma grid_coord_error (L : ℕ) (hL : 0 < L) (p : AmbientCube) (_hp : p ∈ unitCubeSet) (i : Fin 3)
    (floorVal : ℕ) (_hfloor : floorVal = min (⌊p i * (L : ℝ)⌋₊) (L - 1)) :
    |p i - (floorVal : ℝ) / (L : ℝ)| ≤ (L : ℝ)⁻¹ := by
  -- SORRY: floor/min coordinate bound — abs_sub_floor_le / cast alignment
  sorry

lemma unit_cube_near_grid_point (L : ℕ) (hL : 0 < L) (p : UnitCube) :
    ∃ g : FinGrid L, dist p (finGridToCube L hL g) ≤ 1 / L := by
  rcases p with ⟨p, hp⟩
  let floorCoord (i : Fin 3) : ℕ := min (⌊p i * (L : ℝ)⌋₊) (L - 1)
  have hfloor_lt (i : Fin 3) : floorCoord i < L := floorCoord_lt L hL p hp i
  let g : FinGrid L :=
    (⟨floorCoord ⟨0, by decide⟩, hfloor_lt ⟨0, by decide⟩⟩,
      ⟨floorCoord ⟨1, by decide⟩, hfloor_lt ⟨1, by decide⟩⟩,
      ⟨floorCoord ⟨2, by decide⟩, hfloor_lt ⟨2, by decide⟩⟩)
  refine ⟨g, ?_⟩
  simp only [Subtype.dist_eq, finGridToCube]
  rw [PiLp.dist_eq_iSup]
  refine ciSup_le fun i => ?_
  fin_cases i
  · simp [finGridToAmbient_cubeCoord, floorCoord, Real.dist_eq, cubeCoord_eq_ofLp]
    exact grid_coord_error L hL p hp 0 (floorCoord 0) rfl
  · simp [finGridToAmbient_cubeCoord, floorCoord, Real.dist_eq, cubeCoord_eq_ofLp]
    exact grid_coord_error L hL p hp 1 (floorCoord 1) rfl
  · simp [finGridToAmbient_cubeCoord, floorCoord, Real.dist_eq, cubeCoord_eq_ofLp]
    exact grid_coord_error L hL p hp 2 (floorCoord 2) rfl

/-! ## Section 4: GH bound and convergence -/

noncomputable def finGridGHDist (L : ℕ) (hL : 0 < L) : ℝ := by
  letI := finGridMetricSpace L hL
  haveI := finGridNonemptyInst L hL
  exact ghDist (FinGrid L) UnitCube

theorem fin_grid_gh_dist_bound (L : ℕ) (hL : 0 < L) :
    finGridGHDist L hL ≤ 1 / L := by
  letI := finGridMetricSpace L hL
  haveI := finGridNonemptyInst L hL
  dsimp [finGridGHDist]
  let Φ : {x // x ∈ (Set.univ : Set (FinGrid L))} → UnitCube := fun ⟨x, _⟩ => finGridToCube L hL x
  calc
    ghDist (FinGrid L) UnitCube ≤ 0 + 0 / 2 + (1 / L) := by
      simpa [add_zero, zero_div] using
        ghDist_le_of_approx_subsets (ε₁ := 0) (ε₂ := 0) (ε₃ := 1 / L) Φ
          (fun x => ⟨x, Set.mem_univ _, (dist_self x).le⟩)
          (fun y => by
            rcases unit_cube_near_grid_point L hL y with ⟨g, hg⟩
            exact ⟨⟨g, Set.mem_univ _⟩, hg⟩)
          (fun x y => by
            rcases x with ⟨x, hx⟩
            rcases y with ⟨y, hy⟩
            have heq : dist (Φ ⟨x, hx⟩) (Φ ⟨y, hy⟩) =
                dist (⟨x, hx⟩ : {z // z ∈ (Set.univ : Set (FinGrid L))}) (⟨y, hy⟩) := by
              unfold Φ finGridToCube
              simp only [Subtype.dist_eq, MetricSpace.induced, PseudoMetricSpace.induced]
              rfl
            rw [heq, sub_self, abs_zero])
    _ = 1 / L := by ring

lemma finGridGHDist_nonneg (L : ℕ) (hL : 0 < L) : 0 ≤ finGridGHDist L hL := by
  letI := finGridMetricSpace L hL
  haveI := finGridNonemptyInst L hL
  dsimp [finGridGHDist, ghDist]
  apply dist_nonneg

theorem fin_grid_gh_converges :
    Tendsto (fun L : ℕ => if h : 0 < L then finGridGHDist L h else (0 : ℝ)) atTop (nhds (0 : ℝ)) := by
  refine Metric.tendsto_nhds.2 fun ε hε => ?_
  filter_upwards [eventually_ge_atTop (Nat.ceil ((1 : ℝ) / ε) + 1)]
  intro L hL
  have hLpos : 0 < L := Nat.lt_of_lt_of_le (Nat.succ_pos _) (mod_cast hL)
  simp only [Real.dist_eq, dif_pos hLpos]
  have hbound := fin_grid_gh_dist_bound L hLpos
  have hLgt : (1 : ℝ) / ε < (L : ℝ) := by
    have honepos : 0 ≤ (1 : ℝ) / ε := le_of_lt (one_div_pos.mpr hε)
    have hceil_le : (1 : ℝ) / ε ≤ ↑(Nat.ceil ((1 : ℝ) / ε)) := Nat.le_ceil _
    have hceil_lt : ↑(Nat.ceil ((1 : ℝ) / ε)) < (1 : ℝ) / ε + 1 := Nat.ceil_lt_add_one honepos
    have hLle : ((Nat.ceil ((1 : ℝ) / ε) + 1) : ℕ) ≤ L := by exact_mod_cast hL
    have hmid : (1 : ℝ) / ε < ↑(Nat.ceil ((1 : ℝ) / ε) + 1) := by
      have : (1 : ℝ) / ε < ↑(Nat.ceil ((1 : ℝ) / ε)) + 1 := by linarith
      simpa [Nat.cast_add] using this
    exact hmid.trans_le (Nat.cast_le.mpr hLle)
  have hLposR : 0 < (L : ℝ) := Nat.cast_pos.mpr hLpos
  have hεpos : 0 < ε := hε
  have hone : (1 : ℝ) / L < ε := (one_div_lt hLposR hεpos).mpr hLgt
  have hmain : finGridGHDist L hLpos < ε := lt_of_le_of_lt hbound hone
  simpa [Real.dist_eq, dif_pos hLpos, sub_zero, abs_of_nonneg (finGridGHDist_nonneg L hLpos)] using hmain

/-! ## Section 5: CMCA vacuum spatial connection -/

abbrev CMVACAVacuumSpatialGraph (L : ℕ) := FinGrid L

noncomputable def causalNodeSpatialCoords {L T : ℕ} (n : CausalNode L T) : FinGrid L :=
  (n.2.1, n.2.2.1, n.2.2.2)

theorem vacuum_ether_spatial_period : etherSpatialPeriodCells = 14 :=
  ether_spatial_period_eq_fourteen

theorem vacuum_cmca_spatial_gh_convergence :
    ∃ C : ℝ, ∀ L : ℕ, ∀ hL : 0 < L, finGridGHDist L hL ≤ C / L := by
  refine ⟨1, fun L hL => ?_⟩
  simpa using fin_grid_gh_dist_bound L hL

/-- **Master theorem** (CatAL): vacuum CMCA spatial slices converge in GH distance to `[0,1]³`. -/
theorem vacuum_cmca_gh_converges_to_flat_space :
    Tendsto (fun L : ℕ => if h : 0 < L then finGridGHDist L h else (0 : ℝ)) atTop (nhds (0 : ℝ)) :=
  fin_grid_gh_converges

theorem vacuumSpatialGHConvergence :
    Tendsto (fun L : ℕ => if h : 0 < L then finGridGHDist L h else (0 : ℝ)) atTop (nhds (0 : ℝ)) :=
  vacuum_cmca_gh_converges_to_flat_space

end UgpLean.Spacetime.VacuumGHConvergence
