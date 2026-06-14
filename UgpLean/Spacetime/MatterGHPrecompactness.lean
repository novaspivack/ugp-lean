import Mathlib.Analysis.SpecificLimits.Basic
import Mathlib.Topology.MetricSpace.GromovHausdorff
import Mathlib.Topology.MetricSpace.GromovHausdorffRealized
import Mathlib.Topology.MetricSpace.Kuratowski
import Mathlib.Topology.MetricSpace.Basic
import Mathlib.Topology.MetricSpace.Pseudo.Defs
import Mathlib.Topology.MetricSpace.Bounded
import Mathlib.Topology.MetricSpace.Isometry
import Mathlib.Topology.Bases
import Mathlib.Data.Finset.Card
import UgpLean.Spacetime.VacuumGHConvergence

/-!
# Matter-Present CMCA Gromov-Hausdorff Partial Results (OQ-QG-1b)

Partial closure of OQ-QG-1b before a Cheeger–Colding limit theorem is available:

1. **Single-kink flat limit:** a bounded-width kink perturbation of the vacuum grid metric
   still converges in Gromov–Hausdorff distance to flat `[0,1]³`.
2. **Pre-compactness:** the vacuum `FinGrid L` family is totally bounded in `GHSpace`.
-/

namespace UgpLean.Spacetime.MatterGHPrecompactness

open scoped Cardinal
open GromovHausdorff Filter Topology Metric Set
open UgpLean.Spacetime.VacuumGHConvergence

lemma ghDist_comm' {X : Type*} {Y : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y] :
    ghDist X Y = ghDist Y X := by
  rw [ghDist, ghDist, dist_comm]

lemma ghDist_triangle' {X Y Z : Type*} [MetricSpace X] [CompactSpace X] [Nonempty X]
    [MetricSpace Y] [CompactSpace Y] [Nonempty Y]
    [MetricSpace Z] [CompactSpace Z] [Nonempty Z] :
    ghDist X Z ≤ ghDist X Y + ghDist Y Z := by
  simp only [ghDist]
  exact dist_triangle _ _ _

section FinGridParam

noncomputable instance finGridMetricParam (L : ℕ) (hL : 0 < L) : MetricSpace (FinGrid L) :=
  finGridMetricSpace L hL

noncomputable instance finGridCompactParam (L : ℕ) (hL : 0 < L) : CompactSpace (FinGrid L) := by
  letI := finGridMetricParam L hL
  refine { isCompact_univ := ?_ }
  exact Set.Finite.isCompact (Set.finite_univ : (Set.univ : Set (FinGrid L)).Finite)

lemma finAxisDiff_eq_nat_sub {L : ℕ} {x y : Fin L} (h : y.val ≤ x.val) :
    finAxisDiff x y = ((x.val - y.val : ℕ) : ℝ) := by
  unfold finAxisDiff
  have hnonneg : 0 ≤ (x.val : ℝ) - (y.val : ℝ) := sub_nonneg.mpr (Nat.cast_le.mpr h)
  have hcast : ((x.val : ℤ) - (y.val : ℤ) : ℝ) = (x.val : ℝ) - (y.val : ℝ) := by simp
  rw [hcast, abs_of_nonneg hnonneg, Nat.cast_sub h]

lemma axisDiffUpperBound (L : ℕ) (hL : 0 < L) (x y : Fin L) : finAxisDiff x y ≤ (L : ℝ) := by
  have hx := finGrid_coord_le_L L hL x
  have hy := finGrid_coord_le_L L hL y
  unfold finAxisDiff
  have hcast : ((x.val : ℤ) - (y.val : ℤ) : ℝ) = (x.val : ℝ) - (y.val : ℝ) := by simp
  rw [hcast, abs_le]
  constructor <;> linarith

lemma vacuumGridDist_le_one (L : ℕ) (hL : 0 < L) (x y : FinGrid L) : finGridDist L hL x y ≤ 1 := by
  unfold finGridDist
  refine (div_le_one (Nat.cast_pos.mpr hL)).2 ?_
  have h1 := axisDiffUpperBound L hL x.1 y.1
  have h2 := axisDiffUpperBound L hL x.2.1 y.2.1
  have h3 := axisDiffUpperBound L hL x.2.2 y.2.2
  exact max_le (max_le h1 h2) h3

noncomputable def finGridDiam (L : ℕ) (hL : 0 < L) : ℝ := by
  letI := finGridMetricParam L hL
  exact diam (Set.univ : Set (FinGrid L))

lemma finGrid_dist_eq (L : ℕ) (hL : 0 < L) (x y : FinGrid L) :
    (finGridMetricSpace L hL).dist x y = finGridDist L hL x y := by
  unfold finGridMetricSpace MetricSpace.induced PseudoMetricSpace.induced
  exact finGridToAmbient_dist_eq L hL x y

lemma dist_eq_finGridDist (L : ℕ) (hL : 0 < L) (x y : FinGrid L) :
    (finGridMetricSpace L hL).dist x y = finGridDist L hL x y :=
  finGrid_dist_eq L hL x y

theorem finGrid_diam_le_one (L : ℕ) (hL : 0 < L) : finGridDiam L hL ≤ 1 := by
  dsimp [finGridDiam]
  letI := finGridMetricParam L hL
  refine Metric.diam_le_of_forall_dist_le zero_le_one fun x _ y _ => ?_
  rw [finGrid_dist_eq L hL x y]
  exact vacuumGridDist_le_one L hL x y

/-! ## Section 2: ε-nets on the finite grid -/

/-- Axis step size: `(L - 1) / (n + 1) + 1` points per axis at scale `1 / (n + 1)`. -/
def netPitch (L : ℕ) (_hL : 0 < L) (n : ℕ) : ℕ := (L - 1) / (n + 1) + 1

lemma posNetPitch (L : ℕ) (hL : 0 < L) (n : ℕ) : 0 < netPitch L hL n := by
  unfold netPitch
  exact Nat.succ_pos _

lemma pitchWithinLen (L : ℕ) (hL : 0 < L) (n : ℕ) : netPitch L hL n ≤ L := by
  unfold netPitch
  have hle : (L - 1) / (n + 1) ≤ L - 1 := Nat.div_le_self _ _
  omega

lemma gridStepLePitch (L : ℕ) (hL : 0 < L) (gridStep n : ℕ) (h : gridStep = netPitch L hL n) : gridStep ≤ L := by
  rw [h]; exact pitchWithinLen L hL n

lemma pitchStepPredMul (L : ℕ) (hL : 0 < L) (n : ℕ) :
    (netPitch L hL n - 1) * (n + 1) ≤ L - 1 := by
  unfold netPitch
  simpa using Nat.div_mul_le_self (L - 1) (n + 1)

lemma divLePitch (L : ℕ) (hL : 0 < L) (gridStep n : ℕ) (hgridStep : gridStep = netPitch L hL n) :
    ((gridStep - 1) : ℝ) / (L : ℝ) ≤ 1 / (n + 1) := by
  have hnat : (gridStep - 1) * (n + 1) ≤ L := by
    have hle : (gridStep - 1) * (n + 1) ≤ L - 1 := by
      rw [hgridStep, netPitch]
      exact pitchStepPredMul L hL n
    omega
  have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  have hnpos : 0 < (n + 1 : ℝ) := by positivity
  rw [div_le_div_iff₀ hLpos hnpos]
  have hstep : 0 < gridStep := by rw [hgridStep]; exact posNetPitch L hL n
  have hcast : ((gridStep - 1 : ℕ) * (n + 1) : ℝ) ≤ (L : ℝ) := mod_cast hnat
  have hmul : ((gridStep - 1 : ℝ)) * (n + 1) = ((gridStep - 1 : ℕ) * (n + 1) : ℝ) := by
    rw [Nat.cast_sub hstep]; push_cast; ring
  linarith

def snapCoord (L : ℕ) (hL : 0 < L) (gridStep : ℕ) (_hgridStep : gridStep ≤ L) (a : Fin L) : Fin L :=
  ⟨min ((a.val / gridStep) * gridStep) (L - 1),
    (min_le_right _ _).trans_lt (Nat.pred_lt (Nat.ne_of_gt hL))⟩

def coverAxisSet (L : ℕ) (hL : 0 < L) (n : ℕ) : Finset (Fin L) :=
  let gridStep := netPitch L hL n
  have hgridStep := pitchWithinLen L hL n
  (Finset.range (n + 2)).image fun k =>
    snapCoord L hL gridStep hgridStep
      ⟨min (k * gridStep) (L - 1),
        (min_le_right _ _).trans_lt (Nat.pred_lt (Nat.ne_of_gt hL))⟩

lemma axis_step_mul_gt (L : ℕ) (hL : 0 < L) (n : ℕ) :
    L - 1 < netPitch L hL n * (n + 1) + 1 := by
  unfold netPitch
  set q := (L - 1) / (n + 1)
  set r := (L - 1) % (n + 1)
  have hr : r < n + 1 := Nat.mod_lt _ (Nat.succ_pos n)
  have h := Nat.div_add_mod (L - 1) (n + 1)
  have hmain : L - 1 < (q + 1) * (n + 1) + 1 := by
    calc
      L - 1 = q * (n + 1) + r := by rw [Nat.mul_comm q (n + 1), h]
      _ < q * (n + 1) + (n + 1) := by omega
      _ = (q + 1) * (n + 1) := by ring
      _ < (q + 1) * (n + 1) + 1 := by omega
  simpa [netPitch] using hmain

lemma axis_div_step_lt (L : ℕ) (hL : 0 < L) (n : ℕ) (gridStep : ℕ) (hgridStep : gridStep = netPitch L hL n)
    (a : Fin L) : a.val / gridStep < n + 2 := by
  have hgridSteppos : 0 < gridStep := by rw [hgridStep]; exact posNetPitch L hL n
  have hval : a.val ≤ L - 1 := Nat.le_pred_of_lt a.isLt
  have hbound : a.val < (n + 2) * gridStep := by
    rw [hgridStep]
    have hlt := axis_step_mul_gt L hL n
    have hle : netPitch L hL n * (n + 1) + 1 ≤ (n + 2) * netPitch L hL n := by
      nlinarith [show (0 : ℕ) < netPitch L hL n from posNetPitch L hL n]
    exact lt_of_le_of_lt hval (lt_of_lt_of_le hlt hle)
  exact (Nat.div_lt_iff_lt_mul hgridSteppos).mpr hbound

lemma coverAxisSet_card_le (L : ℕ) (hL : 0 < L) (n : ℕ) :
    (coverAxisSet L hL n).card ≤ n + 2 := by
  unfold coverAxisSet
  calc
    _ ≤ (Finset.range (n + 2)).card := Finset.card_image_le
    _ = n + 2 := by simp

def gridCoverSetLarge (L : ℕ) (hL : 0 < L) (n : ℕ) : Finset (FinGrid L) :=
  let A := coverAxisSet L hL n
  ((A.product A).product A).image fun ⟨⟨a, b⟩, c⟩ => (a, b, c)

def gridCoverSet (L : ℕ) (hL : 0 < L) (n : ℕ) : Finset (FinGrid L) :=
  if _ : L ≤ n + 2 then (Finset.univ : Finset (FinGrid L))
  else gridCoverSetLarge L hL n

lemma gridCoverSet_card_le (L : ℕ) (hL : 0 < L) (n : ℕ) : (gridCoverSet L hL n).card ≤ (n + 2)^3 := by
  classical
  unfold gridCoverSet
  by_cases hsmall : L ≤ n + 2
  · have hcard : (Finset.univ : Finset (FinGrid L)).card = L ^ 3 := by
      simp [Finset.card_univ, Fintype.card_fin, FinGrid, Fintype.card_prod, pow_three]
    rw [dif_pos hsmall, hcard]
    exact pow_le_pow_left₀ (Nat.zero_le _) hsmall 3
  · have hcard : (gridCoverSetLarge L hL n).card ≤ (n + 2) ^ 3 := by
      unfold gridCoverSetLarge
      set A := coverAxisSet L hL n with hA_def
      have hA := coverAxisSet_card_le L hL n
      have hprod : ((A.product A).product A).card = A.card ^ 3 := by
        simp [Finset.card_product, pow_three, Nat.mul_assoc]
      calc
        (gridCoverSetLarge L hL n).card ≤ ((A.product A).product A).card := Finset.card_image_le
        _ = A.card ^ 3 := hprod
        _ ≤ (n + 2) ^ 3 := pow_le_pow_left₀ (Nat.zero_le _) hA 3
    rw [dif_neg hsmall]
    exact hcard

lemma snap_axis_diff (L : ℕ) (hL : 0 < L) (gridStep : ℕ) (hgridStep : gridStep ≤ L) (hgridSteppos : 0 < gridStep)
    (a : Fin L) :
    finAxisDiff a (snapCoord L hL gridStep hgridStep a) ≤ (gridStep - 1 : ℝ) := by
  set q := a.val / gridStep
  set r := a.val % gridStep
  have hr : r ≤ gridStep - 1 := by
    have := Nat.mod_lt a.val hgridSteppos
    omega
  have hqle : q * gridStep ≤ L - 1 :=
    (Nat.div_mul_le_self _ _).trans (Nat.le_pred_of_lt a.isLt)
  have hmod : a.val = q * gridStep + r := by
    rw [Nat.mul_comm q gridStep, Nat.div_add_mod]
  have hsnapVal : (snapCoord L hL gridStep hgridStep a).val = q * gridStep := by
    unfold snapCoord
    simp [min_eq_left hqle, q]
  have hsnap_le : (snapCoord L hL gridStep hgridStep a).val ≤ a.val := by
    rw [hsnapVal, hmod]
    omega
  have hnat : a.val - (snapCoord L hL gridStep hgridStep a).val = r := by
    rw [hsnapVal, hmod]
    omega
  rw [finAxisDiff_eq_nat_sub hsnap_le, hnat]
  have hcast : ((gridStep - 1 : ℕ) : ℝ) = (gridStep : ℝ) - 1 := by
    rw [Nat.cast_sub hgridSteppos, Nat.cast_one]
  rw [← hcast]
  exact Nat.cast_le.mpr hr

lemma finGridDist_self (L : ℕ) (hL : 0 < L) (g : FinGrid L) : finGridDist L hL g g = 0 := by
  unfold finGridDist finAxisDiff
  simp

lemma coverAxis_mem (L : ℕ) (hL : 0 < L) (n : ℕ) (gridStep : ℕ) (hgridStep : gridStep = netPitch L hL n)
    (hgridSteppos : 0 < gridStep) (a : Fin L) :
    snapCoord L hL gridStep (gridStepLePitch L hL gridStep n hgridStep) a ∈ coverAxisSet L hL n := by
  unfold coverAxisSet
  set k := a.val / gridStep
  refine Finset.mem_image.mpr ⟨k, Finset.mem_range.mpr ?_, ?_⟩
  · exact axis_div_step_lt L hL n gridStep hgridStep a
  · apply Fin.ext
    have hle : k * gridStep ≤ L - 1 :=
      (Nat.div_mul_le_self _ _).trans (Nat.le_pred_of_lt a.isLt)
    have h1 : (snapCoord L hL gridStep (gridStepLePitch L hL gridStep n hgridStep) a).val =
        k * gridStep := by
      dsimp [snapCoord]
      rw [show a.val / gridStep = k from rfl, min_eq_left hle]
    set inner : Fin L :=
      ⟨min (k * netPitch L hL n) (L - 1),
        (min_le_right _ _).trans_lt (Nat.pred_lt (Nat.ne_of_gt hL))⟩
    have hfval : inner.val = k * gridStep := by
      dsimp [inner]
      calc min (k * netPitch L hL n) (L - 1) = min (k * gridStep) (L - 1) := by rw [hgridStep]
        _ = k * gridStep := min_eq_left hle
    have hpitch : 0 < netPitch L hL n := by rw [← hgridStep]; exact hgridSteppos
    have hdiv : inner.val / netPitch L hL n = k := by
      rw [show inner.val = k * netPitch L hL n from by rw [hfval, hgridStep]]
      simpa [Nat.mul_comm] using Nat.mul_div_cancel_left k hpitch
    have h2 : (snapCoord L hL (netPitch L hL n) (pitchWithinLen L hL n) inner).val =
        k * gridStep := by
      unfold snapCoord
      calc min (inner.val / netPitch L hL n * netPitch L hL n) (L - 1)
          = min (k * netPitch L hL n) (L - 1) := by
            congr 1
            rw [hdiv, Nat.mul_comm]
        _ = min (k * gridStep) (L - 1) := by rw [hgridStep]
        _ = k * gridStep := min_eq_left hle
    rw [h1, h2]

lemma grid_dist_to_cover (L : ℕ) (hL : 0 < L) (n : ℕ) (g : FinGrid L) :
    ∃ y ∈ gridCoverSet L hL n, finGridDist L hL g y ≤ (1 : ℝ) / (n + 1) := by
  classical
  by_cases hsmall : L ≤ n + 2
  · refine ⟨g, ?_, ?_⟩
    · simp [gridCoverSet, hsmall, Finset.mem_univ]
    · rw [finGridDist_self L hL g]
      positivity
  · set gridStep := netPitch L hL n with hgridStep_def
    have hgridStep := pitchWithinLen L hL n
    have hgridSteppos : 0 < gridStep := posNetPitch L hL n
    set cx := snapCoord L hL gridStep hgridStep g.1
    set cy := snapCoord L hL gridStep hgridStep g.2.1
    set cz := snapCoord L hL gridStep hgridStep g.2.2
    refine ⟨(cx, cy, cz), ?_, ?_⟩
    · simp only [gridCoverSet, gridCoverSetLarge, dif_neg hsmall]
      refine Finset.mem_image.mpr ⟨⟨(cx, cy), cz⟩, ?_, rfl⟩
      refine Finset.mem_product.mpr ⟨Finset.mem_product.mpr ⟨?_, ?_⟩, ?_⟩
      · exact coverAxis_mem L hL n gridStep hgridStep_def hgridSteppos g.1
      · exact coverAxis_mem L hL n gridStep hgridStep_def hgridSteppos g.2.1
      · exact coverAxis_mem L hL n gridStep hgridStep_def hgridSteppos g.2.2
    · have hbound :
        max (max (finAxisDiff g.1 cx) (finAxisDiff g.2.1 cy)) (finAxisDiff g.2.2 cz) ≤
          gridStep - 1 := by
        refine max_le (max_le (snap_axis_diff L hL gridStep hgridStep hgridSteppos g.1)
          (snap_axis_diff L hL gridStep hgridStep hgridSteppos g.2.1))
          (snap_axis_diff L hL gridStep hgridStep hgridSteppos g.2.2)
      by_cases hzero :
          max (max (finAxisDiff g.1 cx) (finAxisDiff g.2.1 cy)) (finAxisDiff g.2.2 cz) = 0
      · rw [finGridDist, hzero, zero_div]
        positivity
      · refine le_trans (div_le_div_of_nonneg_right hbound (Nat.cast_nonneg L)) ?_
        exact divLePitch L hL gridStep n hgridStep_def

/-! ## Section 3: GH representative diameter and covering -/

noncomputable def finGridToGHSpace (L : ℕ) (hL : 0 < L) : GHSpace := by
  letI : MetricSpace (FinGrid L) := finGridMetricSpace L hL
  haveI : CompactSpace (FinGrid L) := finGridCompactParam L hL
  haveI : Nonempty (FinGrid L) := finGridNonemptyInst L hL
  exact toGHSpace (FinGrid L)

lemma finGrid_toGHSpace_rep (L : ℕ) (hL : 0 < L) :
    finGridToGHSpace L hL = toGHSpace ((finGridToGHSpace L hL).Rep) := by
  letI := finGridMetricParam L hL
  haveI := finGridCompactParam L hL
  haveI := finGridNonemptyInst L hL
  exact (GHSpace.toGHSpace_rep (finGridToGHSpace L hL)).symm

lemma finGridToGHSpace_toGHSpace (L : ℕ) (hL : 0 < L) :
    finGridToGHSpace L hL = (by
      letI : MetricSpace (FinGrid L) := finGridMetricSpace L hL
      haveI : CompactSpace (FinGrid L) := finGridCompactParam L hL
      haveI : Nonempty (FinGrid L) := finGridNonemptyInst L hL
      exact toGHSpace (FinGrid L)) := by
  unfold finGridToGHSpace
  letI : MetricSpace (FinGrid L) := finGridMetricSpace L hL
  haveI : CompactSpace (FinGrid L) := finGridCompactParam L hL
  haveI : Nonempty (FinGrid L) := finGridNonemptyInst L hL
  rfl

lemma finGrid_rep_diam_le_one (L : ℕ) (hL : 0 < L) :
    diam (Set.univ : Set ((finGridToGHSpace L hL).Rep)) ≤ 1 := by
  letI := finGridMetricParam L hL
  haveI := finGridCompactParam L hL
  haveI := finGridNonemptyInst L hL
  have heq : toGHSpace (FinGrid L) = toGHSpace ((finGridToGHSpace L hL).Rep) :=
    (finGridToGHSpace_toGHSpace L hL).symm.trans (finGrid_toGHSpace_rep L hL)
  rcases (toGHSpace_eq_toGHSpace_iff_isometryEquiv (X := FinGrid L)
    (Y := (finGridToGHSpace L hL).Rep)).1 heq with ⟨e⟩
  have h := finGrid_diam_le_one L hL
  dsimp [finGridDiam] at h
  calc diam (Set.univ : Set ((finGridToGHSpace L hL).Rep)) =
      diam (Set.univ : Set (FinGrid L)) := e.diam_univ.symm
    _ ≤ 1 := h

lemma finGrid_rep_cover (L : ℕ) (hL : 0 < L) (n : ℕ) :
    ∃ s : Set ((finGridToGHSpace L hL).Rep),
      (#s) ≤ (Nat.cast ((n + 2)^3) : Cardinal) ∧
        univ ⊆ ⋃ x ∈ s, ball x (2 / (n + 1)) := by
  letI := finGridMetricParam L hL
  haveI := finGridCompactParam L hL
  haveI := finGridNonemptyInst L hL
  have heq : toGHSpace (FinGrid L) = toGHSpace ((finGridToGHSpace L hL).Rep) :=
    (finGridToGHSpace_toGHSpace L hL).symm.trans (finGrid_toGHSpace_rep L hL)
  rcases (toGHSpace_eq_toGHSpace_iff_isometryEquiv (X := FinGrid L)
    (Y := (finGridToGHSpace L hL).Rep)).1 heq with ⟨e⟩
  let S : Finset (FinGrid L) := gridCoverSet L hL n
  let s : Set ((finGridToGHSpace L hL).Rep) := e '' (S : Set (FinGrid L))
  refine ⟨s, ?_, ?_⟩
  · have hcard : (S.card : Cardinal) ≤ Nat.cast ((n + 2)^3) :=
      Nat.cast_le.mpr (gridCoverSet_card_le L hL n)
    calc (#s : Cardinal) = #(e '' (S : Set (FinGrid L))) := rfl
      _ = #(S : Set (FinGrid L)) := Cardinal.mk_image_eq e.injective
      _ = (S.card : Cardinal) := Cardinal.mk_coe_finset (s := S)
      _ ≤ Nat.cast ((n + 2)^3) := hcard
  · intro x hx
    rcases e.surjective x with ⟨g, rfl⟩
    obtain ⟨y, hyS, hydist⟩ := grid_dist_to_cover L hL n g
    refine mem_iUnion₂.mpr ⟨e y, Set.mem_image_of_mem _ hyS, ?_⟩
    rw [mem_ball]
    calc dist (e g) (e y) = dist g y := e.isometry.dist_eq g y
      _ = finGridDist L hL g y := finGrid_dist_eq L hL g y
      _ < 2 / (n + 1) := lt_of_le_of_lt hydist (by
        have hpos : 0 < (n + 1 : ℝ) := by positivity
        rw [div_lt_div_iff₀ hpos hpos, one_mul, two_mul]
        linarith)

end FinGridParam

/-! ## Section 4: Kink-perturbed metric on a wrapper type -/

/-- Wrapper so a second metric can coexist with `finGridMetricSpace` on `FinGrid L`. -/
structure KinkGrid (L : ℕ) where
  point : FinGrid L

def kinkGridEquiv (L : ℕ) : KinkGrid L ≃ FinGrid L where
  toFun := KinkGrid.point
  invFun := fun g => ⟨g⟩
  left_inv := fun k => by cases k; rfl
  right_inv := fun _ => rfl

instance (L : ℕ) : Fintype (KinkGrid L) :=
  Fintype.ofEquiv (FinGrid L) (kinkGridEquiv L).symm

noncomputable def kinkGridDist (L : ℕ) (_hL : 0 < L) (d' : FinGrid L → FinGrid L → ℝ)
    (a b : KinkGrid L) : ℝ :=
  d' a.point b.point

noncomputable def finGridToKinkGrid (L : ℕ) (g : FinGrid L) : KinkGrid L := ⟨g⟩

@[reducible]
noncomputable def kinkGridPseudoMetricSpace (L : ℕ) (hL : 0 < L) (d' : FinGrid L → FinGrid L → ℝ)
    (_hd'_nonneg : ∀ x y, 0 ≤ d' x y) (hd'_self : ∀ x, d' x x = 0)
    (hd'_comm : ∀ x y, d' x y = d' y x)
    (hd'_triangle : ∀ x y z, d' x z ≤ d' x y + d' y z) : PseudoMetricSpace (KinkGrid L) where
  dist := kinkGridDist L hL d'
  dist_self := fun a => hd'_self a.point
  dist_comm := fun a b => hd'_comm a.point b.point
  dist_triangle := fun a b c => hd'_triangle a.point b.point c.point

@[reducible]
noncomputable def kinkGridMetricSpace (L : ℕ) (hL : 0 < L) (d' : FinGrid L → FinGrid L → ℝ)
    (hd'_nonneg : ∀ x y, 0 ≤ d' x y) (hd'_self : ∀ x, d' x x = 0)
    (hd'_comm : ∀ x y, d' x y = d' y x)
    (hd'_triangle : ∀ x y z, d' x z ≤ d' x y + d' y z)
    (hd'_sep : ∀ x y, d' x y = 0 → x = y) : MetricSpace (KinkGrid L) where
  toPseudoMetricSpace := kinkGridPseudoMetricSpace L hL d' hd'_nonneg hd'_self hd'_comm hd'_triangle
  eq_of_dist_eq_zero := fun {a b} h => by
    cases a; cases b
    congr
    exact hd'_sep _ _ h

noncomputable instance kinkGridMetricParam (L : ℕ) (hL : 0 < L)
    (d' : FinGrid L → FinGrid L → ℝ)
    (hd'_nonneg : ∀ x y, 0 ≤ d' x y) (hd'_self : ∀ x, d' x x = 0)
    (hd'_comm : ∀ x y, d' x y = d' y x)
    (hd'_triangle : ∀ x y z, d' x z ≤ d' x y + d' y z)
    (hd'_sep : ∀ x y, d' x y = 0 → x = y) : MetricSpace (KinkGrid L) :=
  kinkGridMetricSpace L hL d' hd'_nonneg hd'_self hd'_comm hd'_triangle hd'_sep

instance kinkGridNonemptyInst (L : ℕ) (hL : 0 < L) : Nonempty (KinkGrid L) :=
  ⟨⟨⟨0, hL⟩, ⟨0, hL⟩, ⟨0, hL⟩⟩⟩

noncomputable def finGridKinkGHDist (L : ℕ) (hL : 0 < L)
    (d' : FinGrid L → FinGrid L → ℝ)
    (hd'_nonneg : ∀ x y, 0 ≤ d' x y) (hd'_self : ∀ x, d' x x = 0)
    (hd'_comm : ∀ x y, d' x y = d' y x)
    (hd'_triangle : ∀ x y z, d' x z ≤ d' x y + d' y z)
    (hd'_sep : ∀ x y, d' x y = 0 → x = y) : ℝ := by
  letI := finGridMetricParam L hL
  haveI := finGridCompactParam L hL
  haveI := finGridNonemptyInst L hL
  letI := kinkGridMetricParam L hL d' hd'_nonneg hd'_self hd'_comm hd'_triangle hd'_sep
  haveI : CompactSpace (KinkGrid L) :=
    { isCompact_univ := Set.Finite.isCompact (Set.finite_univ : (Set.univ : Set (KinkGrid L)).Finite) }
  haveI := kinkGridNonemptyInst L hL
  exact ghDist (FinGrid L) (KinkGrid L)

noncomputable def kinkUnitCubeGHDist (L : ℕ) (hL : 0 < L)
    (d' : FinGrid L → FinGrid L → ℝ)
    (hd'_nonneg : ∀ x y, 0 ≤ d' x y) (hd'_self : ∀ x, d' x x = 0)
    (hd'_comm : ∀ x y, d' x y = d' y x)
    (hd'_triangle : ∀ x y z, d' x z ≤ d' x y + d' y z)
    (hd'_sep : ∀ x y, d' x y = 0 → x = y) : ℝ := by
  letI := kinkGridMetricParam L hL d' hd'_nonneg hd'_self hd'_comm hd'_triangle hd'_sep
  haveI : CompactSpace (KinkGrid L) :=
    { isCompact_univ := Set.Finite.isCompact (Set.finite_univ : (Set.univ : Set (KinkGrid L)).Finite) }
  haveI := kinkGridNonemptyInst L hL
  exact ghDist (KinkGrid L) UnitCube

theorem ghDist_le_of_metric_perturbation {L : ℕ} {hL : 0 < L}
    (d' : FinGrid L → FinGrid L → ℝ)
    (hd'_nonneg : ∀ x y, 0 ≤ d' x y) (hd'_self : ∀ x, d' x x = 0)
    (hd'_comm : ∀ x y, d' x y = d' y x)
    (hd'_triangle : ∀ x y z, d' x z ≤ d' x y + d' y z)
    (hd'_sep : ∀ x y, d' x y = 0 → x = y)
    (W : ℝ) (_hW : 0 ≤ W)
    (hclose : ∀ x y, |finGridDist L hL x y - d' x y| ≤ W / L) :
    finGridKinkGHDist L hL d' hd'_nonneg hd'_self hd'_comm hd'_triangle hd'_sep ≤ W / (2 * L) := by
  dsimp only [finGridKinkGHDist]
  letI := finGridMetricParam L hL
  haveI := finGridCompactParam L hL
  haveI := finGridNonemptyInst L hL
  letI := kinkGridMetricParam L hL d' hd'_nonneg hd'_self hd'_comm hd'_triangle hd'_sep
  haveI : CompactSpace (KinkGrid L) :=
    { isCompact_univ := Set.Finite.isCompact (Set.finite_univ : (Set.univ : Set (KinkGrid L)).Finite) }
  haveI := kinkGridNonemptyInst L hL
  let Φ : {x // x ∈ (Set.univ : Set (FinGrid L))} → KinkGrid L :=
    fun ⟨x, _⟩ => finGridToKinkGrid L x
  calc
    ghDist (FinGrid L) (KinkGrid L) ≤ 0 + W / L / 2 + 0 :=
      ghDist_le_of_approx_subsets (ε₁ := 0) (ε₂ := W / L) (ε₃ := 0) (s := Set.univ) Φ
        (fun x => ⟨x, Set.mem_univ _, (dist_self x).le⟩)
        (fun y => ⟨⟨y.point, Set.mem_univ _⟩, by
          dsimp [Φ, finGridToKinkGrid, kinkGridDist]
          exact (dist_self y).le⟩)
        (fun ⟨x, hx⟩ ⟨y, hy⟩ => by
          simp only [Subtype.dist_eq, finGrid_dist_eq, kinkGridDist, finGridToKinkGrid, abs_sub_comm]
          exact hclose x y)
    _ = W / (2 * L) := by ring

theorem finGrid_kink_gh_dist_bound {L : ℕ} {hL : 0 < L}
    (d' : FinGrid L → FinGrid L → ℝ)
    (hd'_nonneg : ∀ x y, 0 ≤ d' x y) (hd'_self : ∀ x, d' x x = 0)
    (hd'_comm : ∀ x y, d' x y = d' y x)
    (hd'_triangle : ∀ x y z, d' x z ≤ d' x y + d' y z)
    (hd'_sep : ∀ x y, d' x y = 0 → x = y)
    (W : ℝ) (hW : 0 ≤ W)
    (hclose : ∀ x y, |finGridDist L hL x y - d' x y| ≤ W / L) :
    kinkUnitCubeGHDist L hL d' hd'_nonneg hd'_self hd'_comm hd'_triangle hd'_sep ≤ W / (2 * L) + 1 / L := by
  dsimp only [kinkUnitCubeGHDist]
  letI := kinkGridMetricParam L hL d' hd'_nonneg hd'_self hd'_comm hd'_triangle hd'_sep
  haveI : CompactSpace (KinkGrid L) :=
    { isCompact_univ := Set.Finite.isCompact (Set.finite_univ : (Set.univ : Set (KinkGrid L)).Finite) }
  haveI := kinkGridNonemptyInst L hL
  letI := finGridMetricParam L hL
  haveI := finGridCompactParam L hL
  haveI := finGridNonemptyInst L hL
  have hpert := ghDist_le_of_metric_perturbation d' hd'_nonneg hd'_self hd'_comm hd'_triangle
    hd'_sep W hW hclose
  have hvac := fin_grid_gh_dist_bound L hL
  calc
    ghDist (KinkGrid L) UnitCube ≤ ghDist (KinkGrid L) (FinGrid L) + ghDist (FinGrid L) UnitCube :=
      ghDist_triangle'
    _ = ghDist (FinGrid L) (KinkGrid L) + ghDist (FinGrid L) UnitCube := by
      rw [← ghDist_comm']
    _ ≤ W / (2 * L) + 1 / L := add_le_add hpert hvac

/-- **Result 1 (CatAL):** a single bounded-width kink perturbation still GH-converges to flat space. -/
theorem single_kink_gh_converges_to_flat (W : ℕ) :
    ∃ C : ℝ, ∀ (L : ℕ) (hL : 0 < L) (d' : FinGrid L → FinGrid L → ℝ)
      (hd'_nonneg : ∀ x y, 0 ≤ d' x y) (hd'_self : ∀ x, d' x x = 0)
      (hd'_comm : ∀ x y, d' x y = d' y x)
      (hd'_triangle : ∀ x y z, d' x z ≤ d' x y + d' y z)
      (hd'_sep : ∀ x y, d' x y = 0 → x = y)
      (hclose : ∀ x y, |finGridDist L hL x y - d' x y| ≤ W / L),
      kinkUnitCubeGHDist L hL d' hd'_nonneg hd'_self hd'_comm hd'_triangle hd'_sep ≤ C / L := by
  refine ⟨(W : ℝ) / 2 + 1, fun L hL d' hd'_nonneg hd'_self hd'_comm hd'_triangle hd'_sep hclose => ?_⟩
  have hbound := finGrid_kink_gh_dist_bound (L := L) (hL := hL) d' hd'_nonneg hd'_self hd'_comm
    hd'_triangle hd'_sep W (Nat.cast_nonneg W) hclose
  have hLpos : 0 < (L : ℝ) := Nat.cast_pos.mpr hL
  calc
    kinkUnitCubeGHDist L hL d' hd'_nonneg hd'_self hd'_comm hd'_triangle hd'_sep ≤
        W / (2 * L) + 1 / L := hbound
    _ = ((W : ℝ) / 2 + 1) / L := by field_simp [hLpos.ne']

/-! ## Section 5: Total boundedness of the FinGrid GH family -/

noncomputable def finGridGHFamily : Set GHSpace :=
  {s | ∃ (L : ℕ) (hL : 0 < L), s = finGridToGHSpace L hL}

theorem finGrid_family_totally_bounded :
    TotallyBounded finGridGHFamily := by
  refine GromovHausdorff.totallyBounded (C := 1) (u := fun n => 2 / (n + 1))
    (K := fun n => (n + 2)^3) ?_ ?_ ?_
  · simpa [mul_div] using
      (tendsto_one_div_add_atTop_nhds_zero_nat (𝕜 := ℝ)).const_mul 2
  · intro p hp
    rcases hp with ⟨L, hL, rfl⟩
    letI := finGridMetricParam L hL
    haveI := finGridCompactParam L hL
    haveI := finGridNonemptyInst L hL
    exact finGrid_rep_diam_le_one L hL
  · intro p hp n
    rcases hp with ⟨L, hL, rfl⟩
    letI := finGridMetricParam L hL
    haveI := finGridCompactParam L hL
    haveI := finGridNonemptyInst L hL
    rcases finGrid_rep_cover L hL n with ⟨s, hcard, hcov⟩
    refine ⟨s, hcard, hcov⟩

end UgpLean.Spacetime.MatterGHPrecompactness
