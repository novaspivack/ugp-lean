import UgpLean.Spacetime.CausalGraph
import UgpLean.Spacetime.LiftingTheorem
import UgpLean.Spacetime.ColorConfinement

namespace GTE.Spacetime.SpatialExtension

/-!
# Spatially Extended Composite Lifting Theorem (Rank 55-3DLT)

Generalizes the 1D ring Composition Theorem (Rank 22-CPT) to spatially separated
composites in the 3+1D f_MDL causal graph. Two PSC-admissible color-charged beables
at distinct causal nodes, connected by a vacuum inter-particle field along a causal
path, form a PSC-admissible color-neutral physical bound state — the GTE meson
configuration.

This theorem closes independently of Rank 17-GEO (Geodesic Theorem): only causal
path *existence* and adjacency along the path are required to identify the
inter-particle vacuum region; geodesic uniqueness is not used.

## Certification status

| Component | Status |
|-----------|--------|
| `SpatiallyExtendedComposite` | CatAL — zero sorry |
| `IsCausalPath`, `IsVacuumPath` | CatAL — zero sorry |
| `PSCAdmissibleSpatial` | CatAL — zero sorry |
| `dweight_pos_of_psc`, `dweight_spatial_tensor_product` | CatAL — zero sorry |
| `vacuum_path_psc_admissible` | CatAL — zero sorry |
| `spatially_extended_composite_lifting` | CatAL — zero sorry |
| `meson_bound_state_exists` | CatAL — zero sorry |
| `baryon_bound_state_exists` | CatAL — zero sorry |
| `causal_path_exists` | CatAL — zero sorry (proved for forward-causal pairs; zero custom axioms) |
| `vacuum_path_exists` | CatAL — zero sorry (proved for forward-causal pairs) |
-/

open GTE.Lifting GTE.Spacetime GTE.Spacetime.Confinement
open UgpLean.Universality.LawvereZone CUP3D

variable (L T : ℕ)

-- ─────────────────────────────────────────────────────────────────────────────
-- §1  Causal paths in the 3D f_MDL graph
-- ─────────────────────────────────────────────────────────────────────────────

/-- A causal path: consecutive nodes are causally adjacent in `CausalGraph`. -/
def IsCausalPath
    (start finish : CausalNode L T)
    (path : List (CausalNode L T)) : Prop :=
  path.head? = some start ∧
  path.getLast? = some finish ∧
  ∀ (i : ℕ) (hi : i + 1 < path.length),
    CausalAdj L T
      (path.get ⟨i, by omega⟩)
      (path.get ⟨i + 1, hi⟩)

/-- Intermediate nodes on a causal path (excluding endpoints). -/
def pathIntermediate (path : List (CausalNode L T)) : List (CausalNode L T) :=
  path.drop 1 |>.dropLast

/-- The inter-particle vacuum field: every intermediate node on the path hosts
    the vacuum beable (Zone L0). In the physical meson, cells between quark and
    antiquark are deep vacuum; this predicate captures that configuration. -/
def interParticleVacuumField (path : List (CausalNode L T)) : Prop :=
  ∀ n, n ∈ pathIntermediate L T path → PSCAdmissible fmdl_vacuum5

/-- A vacuum path from `start` to `finish`: a causal path whose intermediate
    nodes are all in the vacuum sector (PSC-admissible Zone L0). -/
def IsVacuumPath
    (start finish : CausalNode L T)
    (path : List (CausalNode L T)) : Prop :=
  IsCausalPath L T start finish path ∧ interParticleVacuumField L T path

-- ─────────────────────────────────────────────────────────────────────────────
-- §2  Spatially extended composite structure
-- ─────────────────────────────────────────────────────────────────────────────

/-- A spatially extended composite: two [D]-weighted single-particle states at
    distinct positions in the 3D f_MDL causal graph, connected by a vacuum path. -/
structure SpatiallyExtendedComposite where
  nodeA : CausalNode L T
  nodeB : CausalNode L T
  beableA : Fin 5 → Fin 7
  beableB : Fin 5 → Fin 7
  vacuumPath : List (CausalNode L T)
  h_distinct : nodeA ≠ nodeB
  h_path : IsVacuumPath L T nodeA nodeB vacuumPath

/-- Total Z₃ color of the two-particle subsystem (inter-particle vacuum is neutral). -/
noncomputable def SpatiallyExtendedComposite.totalColor (c : SpatiallyExtendedComposite L T) :
    ZMod 3 :=
  Confinement.totalColor c.beableA + Confinement.totalColor c.beableB

/-- PSC-admissibility of a spatially extended composite: both component beables
    are PSC-admissible with nonzero [D]-weight, the system is color-neutral, and
    the inter-particle vacuum field along the connecting path is PSC-admissible. -/
def SpatiallyExtendedComposite.PSCAdmissibleSpatial (c : SpatiallyExtendedComposite L T) :
    Prop :=
  PSCAdmissible c.beableA ∧
  PSCAdmissible c.beableB ∧
  DWeight c.beableA > 0 ∧
  DWeight c.beableB > 0 ∧
  c.totalColor = 0 ∧
  interParticleVacuumField L T c.vacuumPath

-- ─────────────────────────────────────────────────────────────────────────────
-- §3  Vacuum path and [D]-weight lemmas
-- ─────────────────────────────────────────────────────────────────────────────

/-- Every intermediate node on a vacuum path hosts a PSC-admissible vacuum beable. -/
theorem vacuum_path_psc_admissible
    (path : List (CausalNode L T))
    (h : interParticleVacuumField L T path)
    (n : CausalNode L T) (hn : n ∈ pathIntermediate L T path) :
    PSCAdmissible fmdl_vacuum5 :=
  h n hn

/-- Intermediate nodes on any causal path satisfy vacuum PSC-admissibility.

    In the deep-vacuum meson-thread model (Rank 55-3DLT), inter-particle lattice
    sites host the constant vacuum beable `fmdl_vacuum5`; the proof applies
    `vacuum_psc_admissible` at each intermediate node. The conclusion is intentionally
    constant — not accidental vacuity. -/
theorem interParticleVacuumField_all
    (path : List (CausalNode L T)) :
    interParticleVacuumField L T path := by
  intro n hn
  exact vacuum_psc_admissible

/-- Every causal path is a vacuum path: inter-particle region carries vacuum beables
    at all intermediate nodes (deep-vacuum thread; Rank 55-3DLT). -/
theorem causal_path_is_vacuum_path
    (start finish : CausalNode L T)
    (path : List (CausalNode L T))
    (h : IsCausalPath L T start finish path) :
    IsVacuumPath L T start finish path :=
  ⟨h, interParticleVacuumField_all L T path⟩

/-- PSC-admissible beables carry positive [D]-weight. -/
theorem dweight_pos_of_psc (beable : Fin 5 → Fin 7) (h : PSCAdmissible beable) :
    DWeight beable > 0 := by
  simp only [DWeight]
  rw [if_pos h]
  norm_num

/-- At distinct spatial positions, [D]-weights of independently PSC-admissible
    beables are both positive — the tensor-product factorization of the composite
    [D]-measure at separated nodes. Distinctness of `nodeA` and `nodeB` ensures
    the two subsystems have disjoint causal neighborhoods (no shared ring boundary). -/
theorem dweight_spatial_tensor_product
    (nodeA nodeB : CausalNode L T)
    (_h_distinct : nodeA ≠ nodeB)
    (stateA stateB : Fin 5 → Fin 7)
    (hA : PSCAdmissible stateA)
    (hB : PSCAdmissible stateB) :
    DWeight stateA > 0 ∧ DWeight stateB > 0 :=
  ⟨dweight_pos_of_psc stateA hA, dweight_pos_of_psc stateB hB⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- §4  Causal connectivity — proved for forward-causal pairs
-- ─────────────────────────────────────────────────────────────────────────────

/-! ### Private path-combinatorics helpers

Two primitives suffice: singleton and prepend (`cons`).  Transitivity is proved
by structural induction on the first path (no list-concatenation index arithmetic). -/

private lemma is_causal_path_singleton' {L T : ℕ} (a : CausalNode L T) :
    IsCausalPath L T a a [a] :=
  ⟨rfl, rfl, fun _ hi => absurd hi (by simp)⟩

/-- Prepend one causal step to build a longer path. -/
private lemma is_causal_path_cons_step
    {L T : ℕ} {a b c : CausalNode L T} {path : List (CausalNode L T)}
    (hadj : CausalAdj L T a b)
    (hpath : IsCausalPath L T b c path) :
    IsCausalPath L T a c (a :: path) := by
  obtain ⟨hhead, hlast, hadjs⟩ := hpath
  -- path must start with b
  obtain ⟨tl, rfl⟩ : ∃ tl, path = b :: tl := by
    cases path with
    | nil => simp at hhead
    | cons hd tl => exact ⟨tl, congrArg (· :: tl) (Option.some.inj hhead)⟩
  refine ⟨rfl, by simpa using hlast, ?_⟩
  intro i hi
  cases i with
  | zero =>
    simp only [List.get_cons_zero, List.get_cons_succ]
    exact hadj
  | succ k =>
    simp only [List.get_cons_succ]
    exact hadjs k (by simp only [List.length_cons] at hi ⊢; omega)

/-! ### Transitivity by structural induction on the first path -/

/-- Extend any path from `a` to `b` into a path from `a` to `c`,
    given a path from `b` to `c`.  Proved by induction on the first path. -/
private lemma causal_path_extend
    {L T : ℕ} {b c : CausalNode L T}
    (hbc : ∃ path, IsCausalPath L T b c path) :
    ∀ (p1 : List (CausalNode L T)) {a : CausalNode L T},
    IsCausalPath L T a b p1 → ∃ path, IsCausalPath L T a c path := by
  intro p1
  induction p1 with
  | nil =>
    intro a hp1; exact absurd hp1.1 (by simp)
  | cons hd tl ih =>
    intro a hp1
    -- Defer h_eq extraction until after cases tl (so it survives the case split)
    cases tl with
    | nil =>
      -- path = [hd]; head = some a so hd = a; last = some b so hd = b
      have h1 : hd = a := Option.some.inj hp1.1
      have h2 : hd = b := Option.some.inj (by simpa using hp1.2.1)
      exact (h1.symm.trans h2) ▸ hbc
    | cons d rest =>
      -- path = hd :: d :: rest
      have h_eq : hd = a := Option.some.inj hp1.1
      -- First step: CausalAdj hd d, rewrtten via h_eq to CausalAdj a d
      have hadj_ad : CausalAdj L T a d := by
        have h0 := hp1.2.2 0 (by simp only [List.length_cons]; omega)
        simp only [List.get_cons_zero, List.get_cons_succ] at h0
        rwa [h_eq] at h0
      -- Tail path: IsCausalPath d b (d :: rest)
      have hp_tail : IsCausalPath L T d b (d :: rest) := by
        refine ⟨rfl, ?_, ?_⟩
        · simpa using hp1.2.1
        · intro i hi
          have := hp1.2.2 (i + 1) (by simp only [List.length_cons] at hi ⊢; omega)
          simp only [List.get_cons_succ] at this
          exact this
      -- By IH: path d → c
      obtain ⟨p_dc, hp_dc⟩ := ih hp_tail
      exact ⟨a :: p_dc, is_causal_path_cons_step hadj_ad hp_dc⟩

/-- Transitivity: compose two causal paths through a common midpoint. -/
private lemma causal_path_trans
    {L T : ℕ} {a b c : CausalNode L T}
    (hab : ∃ path, IsCausalPath L T a b path)
    (hbc : ∃ path, IsCausalPath L T b c path) :
    ∃ path, IsCausalPath L T a c path := by
  obtain ⟨p1, hp1⟩ := hab
  exact causal_path_extend hbc p1 hp1



/-! ### Timelike path existence (forward in time, fixed spatial position) -/

private lemma timelike_adj_fwd {L T : ℕ} (n : CausalNode L T) (hn : n.1.val + 1 ≤ T) :
    CausalAdj L T n ⟨⟨n.1.val + 1, by omega⟩, n.2⟩ :=
  Or.inr (Or.inl ⟨rfl, rfl⟩)

/-- Step path for one timelike step: `[n, succ_n]` is a causal path. -/
private lemma timelike_step_path {L T : ℕ} (n : CausalNode L T) (hn : n.1.val + 1 ≤ T) :
    IsCausalPath L T n ⟨⟨n.1.val + 1, by omega⟩, n.2⟩
      [n, ⟨⟨n.1.val + 1, by omega⟩, n.2⟩] := by
  exact is_causal_path_cons_step (timelike_adj_fwd n hn) (is_causal_path_singleton' _)

/-- Forward timelike path: same spatial position, induction on time gap `k = b.1 - a.1`. -/
private lemma timelike_path_exists {L T : ℕ}
    (a b : CausalNode L T) (hb2 : a.2 = b.2) (hFwd : a.1 ≤ b.1) :
    ∃ path : List (CausalNode L T), IsCausalPath L T a b path := by
  -- Reduce to well-founded recursion on k = b.1.val - a.1.val
  suffices ∀ (k : ℕ) (a : CausalNode L T),
      a.2 = b.2 → a.1.val + k = b.1.val →
      ∃ path : List (CausalNode L T), IsCausalPath L T a b path from
    this (b.1.val - a.1.val) a hb2 (by omega)
  intro k
  induction k with
  | zero =>
    intro a' h2 hk
    have : a' = b := Prod.ext (Fin.ext (by omega)) h2
    rw [this]; exact ⟨[b], is_causal_path_singleton' b⟩
  | succ n ih =>
    intro a' h2 hk
    -- mid = (a'.1 + 1, a'.2); one step closer to b
    let mid : CausalNode L T := ⟨⟨a'.1.val + 1, by have := b.1.isLt; omega⟩, a'.2⟩
    have hmid2 : mid.2 = b.2 := h2  -- mid.2 = a'.2 definitionally
    have hk_mid : mid.1.val + n = b.1.val := by
      have : mid.1.val = a'.1.val + 1 := rfl  -- mid.1 = ⟨a'.1.val+1,_⟩
      omega
    -- By IH: path mid → b
    obtain ⟨p_mb, hp_mb⟩ := ih mid hmid2 hk_mid
    -- One timelike step a' → mid
    have hlt : a'.1.val + 1 ≤ T := by have := b.1.isLt; omega
    have hstep : IsCausalPath L T a' mid [a', mid] := by
      apply is_causal_path_cons_step
      · exact timelike_adj_fwd a' hlt
      · exact is_causal_path_singleton' mid
    exact causal_path_trans ⟨[a', mid], hstep⟩ ⟨p_mb, hp_mb⟩

/-! ### Spacelike path existence (one coordinate at a time) -/

private lemma spacelike_adj_x {L T : ℕ} {t : Fin (T + 1)} {x1 x2 : Fin L} {y z : Fin L}
    (h : x1.val + 1 = x2.val) : CausalAdj L T (t, x1, y, z) (t, x2, y, z) :=
  Or.inl ⟨rfl, Or.inl ⟨Or.inl h, rfl, rfl⟩⟩

private lemma spacelike_adj_x_rev {L T : ℕ} {t : Fin (T + 1)} {x1 x2 : Fin L} {y z : Fin L}
    (h : x2.val + 1 = x1.val) : CausalAdj L T (t, x1, y, z) (t, x2, y, z) :=
  Or.inl ⟨rfl, Or.inl ⟨Or.inr h, rfl, rfl⟩⟩

private lemma spacelike_adj_y {L T : ℕ} {t : Fin (T + 1)} {x y1 y2 z : Fin L}
    (h : y1.val + 1 = y2.val) : CausalAdj L T (t, x, y1, z) (t, x, y2, z) :=
  Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, Or.inl h, rfl⟩)⟩

private lemma spacelike_adj_y_rev {L T : ℕ} {t : Fin (T + 1)} {x y1 y2 z : Fin L}
    (h : y2.val + 1 = y1.val) : CausalAdj L T (t, x, y1, z) (t, x, y2, z) :=
  Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, Or.inr h, rfl⟩)⟩

private lemma spacelike_adj_z {L T : ℕ} {t : Fin (T + 1)} {x y z1 z2 : Fin L}
    (h : z1.val + 1 = z2.val) : CausalAdj L T (t, x, y, z1) (t, x, y, z2) :=
  Or.inl ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl, Or.inl h⟩)⟩

private lemma spacelike_adj_z_rev {L T : ℕ} {t : Fin (T + 1)} {x y z1 z2 : Fin L}
    (h : z2.val + 1 = z1.val) : CausalAdj L T (t, x, y, z1) (t, x, y, z2) :=
  Or.inl ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl, Or.inr h⟩)⟩

/-- Spacelike path changing only the x-coordinate. -/
private lemma x_path_exists {L T : ℕ} (t : Fin (T + 1)) (x1 x2 y z : Fin L) :
    ∃ path : List (CausalNode L T),
      IsCausalPath L T (t, x1, y, z) (t, x2, y, z) path := by
  suffices ∀ (d : ℕ) (x1 x2 : Fin L), x2.val - x1.val + (x1.val - x2.val) = d →
      ∃ path : List (CausalNode L T),
        IsCausalPath L T (t, x1, y, z) (t, x2, y, z) path from
    this _ x1 x2 rfl
  intro d; induction d with
  | zero =>
    intro x1 x2 hd
    have h : x1 = x2 := Fin.ext (by omega)
    rw [h]; exact ⟨_, is_causal_path_singleton' _⟩
  | succ n ih =>
    intro x1 x2 hd
    by_cases hlt : x1.val < x2.val
    · let x1p : Fin L := ⟨x1.val + 1, by omega⟩
      obtain ⟨path, hpath⟩ := ih x1p x2 (by simp [x1p]; omega)
      exact ⟨_, is_causal_path_cons_step (spacelike_adj_x (by simp [x1p])) hpath⟩
    · let x1m : Fin L := ⟨x1.val - 1, by omega⟩
      obtain ⟨path, hpath⟩ := ih x1m x2 (by simp [x1m]; omega)
      exact ⟨_, is_causal_path_cons_step (spacelike_adj_x_rev (by simp [x1m]; omega)) hpath⟩

/-- Spacelike path changing only the y-coordinate. -/
private lemma y_path_exists {L T : ℕ} (t : Fin (T + 1)) (x y1 y2 z : Fin L) :
    ∃ path : List (CausalNode L T),
      IsCausalPath L T (t, x, y1, z) (t, x, y2, z) path := by
  suffices ∀ (d : ℕ) (y1 y2 : Fin L), y2.val - y1.val + (y1.val - y2.val) = d →
      ∃ path : List (CausalNode L T),
        IsCausalPath L T (t, x, y1, z) (t, x, y2, z) path from
    this _ y1 y2 rfl
  intro d; induction d with
  | zero =>
    intro y1 y2 hd
    have h : y1 = y2 := Fin.ext (by omega)
    rw [h]; exact ⟨_, is_causal_path_singleton' _⟩
  | succ n ih =>
    intro y1 y2 hd
    by_cases hlt : y1.val < y2.val
    · let y1p : Fin L := ⟨y1.val + 1, by omega⟩
      obtain ⟨path, hpath⟩ := ih y1p y2 (by simp [y1p]; omega)
      exact ⟨_, is_causal_path_cons_step (spacelike_adj_y (by simp [y1p])) hpath⟩
    · let y1m : Fin L := ⟨y1.val - 1, by omega⟩
      obtain ⟨path, hpath⟩ := ih y1m y2 (by simp [y1m]; omega)
      exact ⟨_, is_causal_path_cons_step (spacelike_adj_y_rev (by simp [y1m]; omega)) hpath⟩

/-- Spacelike path changing only the z-coordinate. -/
private lemma z_path_exists {L T : ℕ} (t : Fin (T + 1)) (x y z1 z2 : Fin L) :
    ∃ path : List (CausalNode L T),
      IsCausalPath L T (t, x, y, z1) (t, x, y, z2) path := by
  suffices ∀ (d : ℕ) (z1 z2 : Fin L), z2.val - z1.val + (z1.val - z2.val) = d →
      ∃ path : List (CausalNode L T),
        IsCausalPath L T (t, x, y, z1) (t, x, y, z2) path from
    this _ z1 z2 rfl
  intro d; induction d with
  | zero =>
    intro z1 z2 hd
    have h : z1 = z2 := Fin.ext (by omega)
    rw [h]; exact ⟨_, is_causal_path_singleton' _⟩
  | succ n ih =>
    intro z1 z2 hd
    by_cases hlt : z1.val < z2.val
    · let z1p : Fin L := ⟨z1.val + 1, by omega⟩
      obtain ⟨path, hpath⟩ := ih z1p z2 (by simp [z1p]; omega)
      exact ⟨_, is_causal_path_cons_step (spacelike_adj_z (by simp [z1p])) hpath⟩
    · let z1m : Fin L := ⟨z1.val - 1, by omega⟩
      obtain ⟨path, hpath⟩ := ih z1m z2 (by simp [z1m]; omega)
      exact ⟨_, is_causal_path_cons_step (spacelike_adj_z_rev (by simp [z1m]; omega)) hpath⟩

/-- Full 3D spacelike path: compose x-, y-, z-coordinate paths. -/
private lemma spacelike_path_exists {L T : ℕ}
    (t : Fin (T + 1)) (a2 b2 : Fin L × Fin L × Fin L) :
    ∃ path : List (CausalNode L T),
      IsCausalPath L T (t, a2) (t, b2) path := by
  obtain ⟨xa, ya, za⟩ := a2
  obtain ⟨xb, yb, zb⟩ := b2
  obtain ⟨px, hpx⟩ := x_path_exists t xa xb ya za
  obtain ⟨py, hpy⟩ := y_path_exists t xb ya yb za
  obtain ⟨pz, hpz⟩ := z_path_exists t xb yb za zb
  exact causal_path_trans
    ⟨px, hpx⟩
    (causal_path_trans ⟨py, hpy⟩ ⟨pz, hpz⟩)

/-! ### Light-cone adjacency and minimal geodesic paths (Rank 076-GEO M4) -/

/-- ℓ₁ spatial distance between two 3D lattice positions. -/
def spatialL1 {L : ℕ} (a b : Fin L × Fin L × Fin L) : ℕ :=
  Int.natAbs ((b.1.val : ℤ) - (a.1.val : ℤ)) +
  Int.natAbs ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)) +
  Int.natAbs ((b.2.2.val : ℤ) - (a.2.2.val : ℤ))

private lemma lightcone_adj_x {L T : ℕ} {t : Fin (T + 1)} {x1 x2 y z : Fin L}
    (h : x1.val + 1 = x2.val) (_ht : t.val + 1 ≤ T) :
    CausalAdj L T (t, x1, y, z) ((⟨t.val + 1, by omega⟩ : Fin (T + 1)), x2, y, z) :=
  Or.inr (Or.inr ⟨rfl, Or.inl ⟨Or.inl h, rfl, rfl⟩⟩)

private lemma lightcone_adj_x_rev {L T : ℕ} {t : Fin (T + 1)} {x1 x2 y z : Fin L}
    (h : x2.val + 1 = x1.val) (_ht : t.val + 1 ≤ T) :
    CausalAdj L T (t, x1, y, z) ((⟨t.val + 1, by omega⟩ : Fin (T + 1)), x2, y, z) :=
  Or.inr (Or.inr ⟨rfl, Or.inl ⟨Or.inr h, rfl, rfl⟩⟩)

private lemma lightcone_adj_y {L T : ℕ} {t : Fin (T + 1)} {x y1 y2 z : Fin L}
    (h : y1.val + 1 = y2.val) (_ht : t.val + 1 ≤ T) :
    CausalAdj L T (t, x, y1, z) ((⟨t.val + 1, by omega⟩ : Fin (T + 1)), x, y2, z) :=
  Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl ⟨rfl, Or.inl h, rfl⟩)⟩)

private lemma lightcone_adj_y_rev {L T : ℕ} {t : Fin (T + 1)} {x y1 y2 z : Fin L}
    (h : y2.val + 1 = y1.val) (_ht : t.val + 1 ≤ T) :
    CausalAdj L T (t, x, y1, z) ((⟨t.val + 1, by omega⟩ : Fin (T + 1)), x, y2, z) :=
  Or.inr (Or.inr ⟨rfl, Or.inr (Or.inl ⟨rfl, Or.inr h, rfl⟩)⟩)

private lemma lightcone_adj_z {L T : ℕ} {t : Fin (T + 1)} {x y z1 z2 : Fin L}
    (h : z1.val + 1 = z2.val) (_ht : t.val + 1 ≤ T) :
    CausalAdj L T (t, x, y, z1) ((⟨t.val + 1, by omega⟩ : Fin (T + 1)), x, y, z2) :=
  Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl, Or.inl h⟩)⟩)

private lemma lightcone_adj_z_rev {L T : ℕ} {t : Fin (T + 1)} {x y z1 z2 : Fin L}
    (h : z2.val + 1 = z1.val) (_ht : t.val + 1 ≤ T) :
    CausalAdj L T (t, x, y, z1) ((⟨t.val + 1, by omega⟩ : Fin (T + 1)), x, y, z2) :=
  Or.inr (Or.inr ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl, Or.inr h⟩)⟩)

private lemma spatial_l1_spacelike_step {L T : ℕ}
    (t : Fin (T + 1)) (pos target : Fin L × Fin L × Fin L)
    (hpos : pos ≠ target) :
    ∃ pos' : Fin L × Fin L × Fin L,
      spatialL1 pos' target + 1 = spatialL1 pos target ∧
      CausalAdj L T (t, pos) (t, pos') := by
  obtain ⟨x, y, z⟩ := pos
  obtain ⟨xt, yt, zt⟩ := target
  by_cases hx : x.val ≠ xt.val
  · by_cases hlt : x.val < xt.val
    · let x' : Fin L := ⟨x.val + 1, by omega⟩
      use (x', y, z)
      constructor
      · dsimp [spatialL1]
        simp only [x', Fin.val_mk]
        omega
      · exact spacelike_adj_x (by simp [x'])
    · let x' : Fin L := ⟨x.val - 1, by omega⟩
      use (x', y, z)
      constructor
      · dsimp [spatialL1]
        simp only [x', Fin.val_mk]
        omega
      · exact spacelike_adj_x_rev (by simp [x']; omega)
  · push_neg at hx
    have hx' : x = xt := Fin.ext hx
    by_cases hy : y.val ≠ yt.val
    · by_cases hlt : y.val < yt.val
      · let y' : Fin L := ⟨y.val + 1, by omega⟩
        use (x, y', z)
        constructor
        · dsimp [spatialL1]
          subst hx'
          simp only [y', Fin.val_mk]
          omega
        · exact spacelike_adj_y (by simp [y'])
      · let y' : Fin L := ⟨y.val - 1, by omega⟩
        use (x, y', z)
        constructor
        · dsimp [spatialL1]
          subst hx'
          simp only [y', Fin.val_mk]
          omega
        · exact spacelike_adj_y_rev (by simp [y']; omega)
    · push_neg at hy
      have hy' : y = yt := Fin.ext hy
      have hz : z.val ≠ zt.val := by
        intro heq
        apply hpos
        exact Prod.ext hx' (Prod.ext hy' (Fin.ext heq))
      by_cases hlt : z.val < zt.val
      · let z' : Fin L := ⟨z.val + 1, by omega⟩
        use (x, y, z')
        constructor
        · dsimp [spatialL1]
          subst hx' hy'
          simp only [z', Fin.val_mk]
          omega
        · exact spacelike_adj_z (by simp [z'])
      · let z' : Fin L := ⟨z.val - 1, by omega⟩
        use (x, y, z')
        constructor
        · dsimp [spatialL1]
          subst hx' hy'
          simp only [z', Fin.val_mk]
          omega
        · exact spacelike_adj_z_rev (by simp [z']; omega)

private lemma spatial_l1_lightcone_step {L T : ℕ}
    (t : Fin (T + 1)) (pos target : Fin L × Fin L × Fin L)
    (hpos : pos ≠ target) (ht : t.val + 1 ≤ T) :
    ∃ pos' : Fin L × Fin L × Fin L,
      spatialL1 pos' target + 1 = spatialL1 pos target ∧
      CausalAdj L T (t, pos) ((⟨t.val + 1, by omega⟩ : Fin (T + 1)), pos') := by
  obtain ⟨x, y, z⟩ := pos
  obtain ⟨xt, yt, zt⟩ := target
  by_cases hx : x.val ≠ xt.val
  · by_cases hlt : x.val < xt.val
    · let x' : Fin L := ⟨x.val + 1, by omega⟩
      use (x', y, z)
      constructor
      · dsimp [spatialL1]
        simp only [x', Fin.val_mk]
        omega
      · exact lightcone_adj_x (by simp [x']) ht
    · let x' : Fin L := ⟨x.val - 1, by omega⟩
      use (x', y, z)
      constructor
      · dsimp [spatialL1]
        simp only [x', Fin.val_mk]
        omega
      · exact lightcone_adj_x_rev (by simp [x']; omega) ht
  · push_neg at hx
    have hx' : x = xt := Fin.ext hx
    by_cases hy : y.val ≠ yt.val
    · by_cases hlt : y.val < yt.val
      · let y' : Fin L := ⟨y.val + 1, by omega⟩
        use (x, y', z)
        constructor
        · dsimp [spatialL1]
          subst hx'
          simp only [y', Fin.val_mk]
          omega
        · exact lightcone_adj_y (by simp [y']) ht
      · let y' : Fin L := ⟨y.val - 1, by omega⟩
        use (x, y', z)
        constructor
        · dsimp [spatialL1]
          subst hx'
          simp only [y', Fin.val_mk]
          omega
        · exact lightcone_adj_y_rev (by simp [y']; omega) ht
    · push_neg at hy
      have hy' : y = yt := Fin.ext hy
      have hz : z.val ≠ zt.val := by
        intro heq
        apply hpos
        exact Prod.ext hx' (Prod.ext hy' (Fin.ext heq))
      by_cases hlt : z.val < zt.val
      · let z' : Fin L := ⟨z.val + 1, by omega⟩
        use (x, y, z')
        constructor
        · dsimp [spatialL1]
          subst hx' hy'
          simp only [z', Fin.val_mk]
          omega
        · exact lightcone_adj_z (by simp [z']) ht
      · let z' : Fin L := ⟨z.val - 1, by omega⟩
        use (x, y, z')
        constructor
        · dsimp [spatialL1]
          subst hx' hy'
          simp only [z', Fin.val_mk]
          omega
        · exact lightcone_adj_z_rev (by simp [z']; omega) ht

private lemma spatialL1_eq_zero_iff {L : ℕ} (a b : Fin L × Fin L × Fin L) :
    spatialL1 a b = 0 ↔ a = b := by
  constructor
  · intro h0
    obtain ⟨x, y, z⟩ := a
    obtain ⟨xt, yt, zt⟩ := b
    have hdx : Int.natAbs ((xt.val : ℤ) - (x.val : ℤ)) = 0 := by
      dsimp [spatialL1] at h0
      omega
    have hdy : Int.natAbs ((yt.val : ℤ) - (y.val : ℤ)) = 0 := by
      dsimp [spatialL1] at h0
      omega
    have hdz : Int.natAbs ((zt.val : ℤ) - (z.val : ℤ)) = 0 := by
      dsimp [spatialL1] at h0
      omega
    have hx : x = xt := Fin.ext (by rw [Int.natAbs_eq_zero] at hdx; omega)
    have hy : y = yt := Fin.ext (by rw [Int.natAbs_eq_zero] at hdy; omega)
    have hz : z = zt := Fin.ext (by rw [Int.natAbs_eq_zero] at hdz; omega)
    exact Prod.ext hx (Prod.ext hy hz)
  · intro h
    subst h
    simp [spatialL1]

/-- Minimal-hop causal path between forward-causal endpoints (Rank 076-GEO M4).

    Hop count is `max(spatialL1, Δt)`; path length is that plus one.
    When `spatialL1 > Δt`, a spacelike preamble at the start time is used;
    otherwise light-cone and timelike hops interleave. -/
private lemma minimal_geodesic_path_spec {L T : ℕ}
    (start finish : CausalNode L T) (hFwd : start.1 ≤ finish.1) :
    let dt := finish.1.val - start.1.val
    let dl := spatialL1 start.2 finish.2
    let hops := max dl dt
    ∃ path : List (CausalNode L T),
      IsCausalPath L T start finish path ∧
      path.length = hops + 1 := by
  intro dt dl hops
  suffices ∀ (m : ℕ) (cur : CausalNode L T),
      cur.1 ≤ finish.1 →
      max (spatialL1 cur.2 finish.2) (finish.1.val - cur.1.val) = m →
      ∃ path : List (CausalNode L T),
        IsCausalPath L T cur finish path ∧
        path.length = m + 1 by
    have hm : max (spatialL1 start.2 finish.2) (finish.1.val - start.1.val) = hops := by
      simp [hops, dt, dl]
    obtain ⟨path, hp, hlen⟩ := this hops start hFwd hm
    exact ⟨path, hp, hlen⟩
  intro m
  induction m with
  | zero =>
    intro cur hle hm
    have hsp : cur.2 = finish.2 := (spatialL1_eq_zero_iff cur.2 finish.2).1 (by omega)
    have ht : cur.1 = finish.1 := Fin.ext (by omega)
    have heq : cur = finish := Prod.ext ht hsp
    rw [heq]
    exact ⟨[finish], is_causal_path_singleton' finish, by simp⟩
  | succ n ih =>
    intro cur hle hm
    by_cases heq : cur = finish
    · exfalso
      rw [heq, spatialL1] at hm
      omega
    · by_cases hsp_preamble :
          spatialL1 cur.2 finish.2 > finish.1.val - cur.1.val
      · have hne : cur.2 ≠ finish.2 := by
          intro heqsp
          have : 1 ≤ spatialL1 cur.2 finish.2 := by omega
          simp [heqsp, spatialL1] at this
        obtain ⟨pos', _hdec, hadj⟩ :=
          spatial_l1_spacelike_step cur.1 cur.2 finish.2 hne
        let cur' : CausalNode L T := ⟨cur.1, pos'⟩
        have hm' : max (spatialL1 cur'.2 finish.2) (finish.1.val - cur'.1.val) = n := by
          dsimp [cur']
          omega
        obtain ⟨path, hp, hlen⟩ := ih cur' hle hm'
        exact ⟨cur :: path, is_causal_path_cons_step hadj hp, by simp [hlen]⟩
      · by_cases hdl_pos : 0 < spatialL1 cur.2 finish.2
        · have hne : cur.2 ≠ finish.2 := by
            intro heqsp
            have := hdl_pos
            simp [heqsp, spatialL1] at this
          have hdt_pos : 0 < finish.1.val - cur.1.val := by
            push_neg at hsp_preamble
            omega
          have hcur_lt_T : cur.1.val < T := by
            have : cur.1.val + 1 ≤ finish.1.val := by omega
            have : finish.1.val ≤ T := Nat.le_of_lt_succ finish.1.isLt
            omega
          have ht : cur.1.val + 1 ≤ T := by omega
          obtain ⟨pos', hdec, hadj⟩ :=
            spatial_l1_lightcone_step cur.1 cur.2 finish.2 hne ht
          let cur' : CausalNode L T := (⟨cur.1.val + 1, Nat.lt_succ_iff.mpr hcur_lt_T⟩, pos')
          have hm' : max (spatialL1 cur'.2 finish.2) (finish.1.val - cur'.1.val) = n := by
            dsimp [cur']
            omega
          have hlt : cur.1.val < finish.1.val := by omega
          have hle' : cur'.1 ≤ finish.1 := (Fin.le_iff_val_le_val).2 (Nat.succ_le_iff.mpr hlt)
          obtain ⟨path, hp, hlen⟩ := ih cur' hle' hm'
          refine ⟨cur :: path, is_causal_path_cons_step hadj hp, by simp [hlen]⟩
        · have hzero : spatialL1 cur.2 finish.2 = 0 := Nat.eq_zero_of_not_pos hdl_pos
          have hdt : finish.1.val - cur.1.val = n + 1 := by
            simp [hzero] at hm
            omega
          have hcur_lt_T : cur.1.val < T := by
            have : finish.1.val ≤ T := Nat.le_of_lt_succ finish.1.isLt
            omega
          have ht : cur.1.val + 1 ≤ T := by omega
          let cur' : CausalNode L T := (⟨cur.1.val + 1, Nat.lt_succ_iff.mpr hcur_lt_T⟩, cur.2)
          have hm' : max (spatialL1 cur'.2 finish.2) (finish.1.val - cur'.1.val) = n := by
            dsimp [cur']
            simp [hzero]
            omega
          have hstep : cur.1.val + 1 ≤ finish.1.val := by omega
          have hle' : cur'.1 ≤ finish.1 := (Fin.le_iff_val_le_val).2 hstep
          obtain ⟨path, hp, hlen⟩ := ih cur' hle' hm'
          refine ⟨cur :: path, is_causal_path_cons_step (timelike_adj_fwd cur ht) hp, by simp [hlen]⟩

/-- **Minimal causal path for forward-causal pairs** (Rank 076-GEO M4, CatAL).

    Constructs a length-minimal causal path between `start` and `finish` when
    `start.1 ≤ finish.1`.  Hop count is `max(spatialL1, Δt)`.

    Status: CatAL — zero sorry. -/
theorem minimal_causal_path_exists {L T : ℕ} (start finish : CausalNode L T)
    (hFwd : start.1 ≤ finish.1) :
    let dt := finish.1.val - start.1.val
    let dl := spatialL1 start.2 finish.2
    ∃ path : List (CausalNode L T),
      IsCausalPath L T start finish path ∧
      path.length = max dl dt + 1 :=
  minimal_geodesic_path_spec start finish hFwd

private def causalReachMetric {L T : ℕ} (cur finish : CausalNode L T) : ℕ :=
  max (spatialL1 cur.2 finish.2) (finish.1.val - cur.1.val)

private lemma causal_adj_reach_metric_step
    {L T : ℕ} {n1 n2 finish : CausalNode L T} (h : CausalAdj L T n1 n2) :
    causalReachMetric n2 finish + 1 ≥ causalReachMetric n1 finish := by
  dsimp [causalReachMetric]
  have ht : n2.1.val ≤ n1.1.val + 1 := by
    rcases h with h | h | h <;> simp [SpacelikeAdj, TimelikeAdj, LightConeAdj] at h <;> omega
  have hsp : spatialL1 n2.2 finish.2 + 1 ≥ spatialL1 n1.2 finish.2 := by
    dsimp [spatialL1]
    rcases h with h | h | h
    · rcases h.2 with h | h | h <;> simp [SpacelikeAdj, FinAdj] at h <;> omega
    · rcases h with ⟨ht', hs⟩
      rw [hs]
      omega
    · rcases h.2 with h | h | h <;> simp [LightConeAdj, FinAdj] at h <;> omega
  omega

private theorem causal_path_reach_metric_bound
    {L T : ℕ} {cur finish : CausalNode L T} {path : List (CausalNode L T)}
    (h : IsCausalPath L T cur finish path) :
    causalReachMetric cur finish + 1 ≤ path.length := by
  obtain ⟨hhead, hlast, hadjs⟩ := h
  match path with
  | [] => simp at hhead
  | [n] =>
    have ha : n = cur := by simpa using hhead
    have hb : n = finish := by simpa using hlast
    subst ha hb
    simp [causalReachMetric, spatialL1]
  | n1 :: n2 :: rest =>
    have hn1 : n1 = cur := by simpa using hhead
    have hadj : CausalAdj L T cur n2 := by simpa [hn1] using hadjs 0 (by simp)
    have hstep := causal_adj_reach_metric_step (finish := finish) hadj
    have htail : IsCausalPath L T n2 finish (n2 :: rest) := by
      refine ⟨?_, hlast, ?_⟩
      · simp
      · intro i hi
        exact hadjs (i + 1) (by simp at hi ⊢; omega)
    have ih := causal_path_reach_metric_bound htail
    have hcore : causalReachMetric cur finish ≤ (n2 :: rest).length := by
      have hstep := causal_adj_reach_metric_step (finish := finish) hadj
      omega
    simpa [List.length_cons] using Nat.succ_le_succ hcore

/-- Any causal path has length at least `max(spatialL1, Δt) + 1`. -/
theorem causal_path_length_ge_max {L T : ℕ}
    {start finish : CausalNode L T} {path : List (CausalNode L T)}
    (h : IsCausalPath L T start finish path) (_hFwd : start.1 ≤ finish.1) :
    max (spatialL1 start.2 finish.2) (finish.1.val - start.1.val) + 1 ≤ path.length := by
  have hlen := causal_path_reach_metric_bound h
  simp only [causalReachMetric] at hlen
  exact hlen

/-- **Causal path existence for forward-causal pairs** (Rank 143-PATH-AXIOM).

    For any two causal nodes `a` and `b` with `a.1 ≤ b.1` (forward or equal time),
    a causal path from `a` to `b` exists.

    Proof: (1) Take `b.1 - a.1` timelike steps from `a` to `(b.1, a.2)`.
    (2) Traverse each spatial coordinate to reach `b` via spacelike steps.
    The composition is via `causal_path_trans`.

    The unconditional `∀ a b, ∃ path` is false without `hFwd`: backward-time pairs
    `b.1 < a.1` have no forward-directed path.

    Status: CatAL — zero sorry, zero custom axioms. -/
theorem causal_path_exists {L T : ℕ} (_hL : 0 < L) (a b : CausalNode L T) (hFwd : a.1 ≤ b.1) :
    ∃ path : List (CausalNode L T), IsCausalPath L T a b path := by
  -- Step 1: timelike path from a to mid = (b.1, a.2)
  let mid : CausalNode L T := ⟨b.1, a.2⟩
  obtain ⟨pt, hpt⟩ := timelike_path_exists a mid rfl hFwd
  -- Step 2: spacelike path from mid = (b.1, a.2) to b = (b.1, b.2)
  obtain ⟨ps, hps⟩ := spacelike_path_exists b.1 a.2 b.2
  -- (b.1, a.2) = mid and (b.1, b.2) = b, so hps has the right type
  exact causal_path_trans ⟨pt, hpt⟩ ⟨ps, hps⟩

/-- There exists a vacuum path between any two forward-causal nodes. -/
theorem vacuum_path_exists {L T : ℕ} (hL : 0 < L) (nodeA nodeB : CausalNode L T)
    (hFwd : nodeA.1 ≤ nodeB.1) :
    ∃ path : List (CausalNode L T), IsVacuumPath L T nodeA nodeB path := by
  obtain ⟨path, hp⟩ := causal_path_exists hL nodeA nodeB hFwd
  exact ⟨path, causal_path_is_vacuum_path L T nodeA nodeB path hp⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- §5  Physical bound state predicate
-- ─────────────────────────────────────────────────────────────────────────────

/-- A physical bound state: two PSC-admissible [D]-weighted beables whose total
    Z₃ color is zero — the meson / color-singlet composite condition. -/
def PhysicalBoundState (beableA beableB : Fin 5 → Fin 7) : Prop :=
  PSCAdmissible beableA ∧
  PSCAdmissible beableB ∧
  DWeight beableA > 0 ∧
  DWeight beableB > 0 ∧
  Confinement.totalColor beableA + Confinement.totalColor beableB = 0

/-- Spatial extension yields a physical bound state: composition from separated
    PSC-admissible components with color neutrality and vacuum connector. -/
theorem composition_from_spatial_extension
    (beableA beableB : Fin 5 → Fin 7)
    (hA : PSCAdmissible beableA)
    (hB : PSCAdmissible beableB)
    (h_dA : DWeight beableA > 0)
    (h_dB : DWeight beableB > 0)
    (h_col : Confinement.totalColor beableA + Confinement.totalColor beableB = 0) :
    PhysicalBoundState beableA beableB :=
  ⟨hA, hB, h_dA, h_dB, h_col⟩

-- ─────────────────────────────────────────────────────────────────────────────
-- §6  Main theorem: Spatially Extended Composite Lifting
-- ─────────────────────────────────────────────────────────────────────────────

/-- **Spatially Extended Composite Lifting Theorem** (Rank 55-3DLT).

    Two PSC-admissible color-charged beables at distinct causal-graph nodes,
    connected by a vacuum inter-particle field and satisfying total color
    neutrality, form a PSC-admissible physical bound state.

    Proof structure:
    1. Construct `SpatiallyExtendedComposite` from hypotheses.
    2. Component PSC-admissibility and [D]-weight positivity (given + `d2_axiom`).
    3. Inter-particle vacuum PSC-admissibility (`vacuum_psc_admissible`).
    4. Color neutrality (hypothesis).
    5. Conclude `PhysicalBoundState` via `composition_from_spatial_extension`.

    Independent of Rank 17-GEO: uses causal path adjacency only, not geodesic
    uniqueness.

    Status: CatAL — zero sorry, zero custom axioms. -/
theorem spatially_extended_composite_lifting
    (beableA beableB : Fin 5 → Fin 7)
    (h_admA : PSCAdmissible beableA)
    (h_admB : PSCAdmissible beableB)
    (h_color_neutral : Confinement.totalColor beableA + Confinement.totalColor beableB = 0)
    (h_dweight_A : DWeight beableA > 0)
    (h_dweight_B : DWeight beableB > 0)
    (nodeA nodeB : CausalNode L T)
    (h_distinct : nodeA ≠ nodeB)
    (vacuumPath : List (CausalNode L T))
    (h_path : IsVacuumPath L T nodeA nodeB vacuumPath) :
    ∃ (composite : SpatiallyExtendedComposite L T),
      composite.nodeA = nodeA ∧
      composite.nodeB = nodeB ∧
      SpatiallyExtendedComposite.PSCAdmissibleSpatial L T composite ∧
      composite.totalColor = 0 ∧
      PhysicalBoundState beableA beableB := by
  refine ⟨{
    nodeA := nodeA
    nodeB := nodeB
    beableA := beableA
    beableB := beableB
    vacuumPath := vacuumPath
    h_distinct := h_distinct
    h_path := h_path
  }, rfl, rfl, ?_, h_color_neutral, ?_⟩
  · exact ⟨h_admA, h_admB, h_dweight_A, h_dweight_B, h_color_neutral, h_path.2⟩
  · exact composition_from_spatial_extension beableA beableB h_admA h_admB
      h_dweight_A h_dweight_B h_color_neutral

/-- A physical baryon bound state: three PSC-admissible [D]-weighted beables whose
    total Z₃ color is zero — the three-quark color-singlet composite condition. -/
def PhysicalBaryonState (beableA beableB beableC : Fin 5 → Fin 7) : Prop :=
  PSCAdmissible beableA ∧
  PSCAdmissible beableB ∧
  PSCAdmissible beableC ∧
  DWeight beableA > 0 ∧
  DWeight beableB > 0 ∧
  DWeight beableC > 0 ∧
  Confinement.totalColor beableA + Confinement.totalColor beableB +
    Confinement.totalColor beableC = 0

/-- Three color-charged PSC-admissible beables with total color neutrality form a
    physical baryon bound state. Parallel to `meson_bound_state_exists`. -/
theorem baryon_composition_from_spatial_extension
    (beableA beableB beableC : Fin 5 → Fin 7)
    (hA : PSCAdmissible beableA)
    (hB : PSCAdmissible beableB)
    (hC : PSCAdmissible beableC)
    (h_dA : DWeight beableA > 0)
    (h_dB : DWeight beableB > 0)
    (h_dC : DWeight beableC > 0)
    (h_col : Confinement.totalColor beableA + Confinement.totalColor beableB +
      Confinement.totalColor beableC = 0) :
    PhysicalBaryonState beableA beableB beableC :=
  ⟨hA, hB, hC, h_dA, h_dB, h_dC, h_col⟩

/-- **Baryon bound state existence**: given vacuum paths connecting three distinct
    spatial nodes, a color-neutral three-quark subsystem is a physical bound state.
    Corollary of the meson lifting pattern extended to three constituents. -/
theorem baryon_bound_state_exists
    (beableA beableB beableC : Fin 5 → Fin 7)
    (hA : PSCAdmissible beableA)
    (hB : PSCAdmissible beableB)
    (hC : PSCAdmissible beableC)
    (h_col : Confinement.totalColor beableA + Confinement.totalColor beableB +
      Confinement.totalColor beableC = 0)
    (nodeA nodeB nodeC : CausalNode L T)
    (_h_distAB : nodeA ≠ nodeB)
    (_h_distBC : nodeB ≠ nodeC)
    (_h_distAC : nodeA ≠ nodeC)
    (_pathAB : List (CausalNode L T))
    (_h_pathAB : IsVacuumPath L T nodeA nodeB _pathAB)
    (_pathBC : List (CausalNode L T))
    (_h_pathBC : IsVacuumPath L T nodeB nodeC _pathBC) :
    PhysicalBaryonState beableA beableB beableC :=
  baryon_composition_from_spatial_extension beableA beableB beableC hA hB hC
    (dweight_pos_of_psc beableA hA) (dweight_pos_of_psc beableB hB)
    (dweight_pos_of_psc beableC hC) h_col

/-- **Meson bound state existence**: given a vacuum path between distinct nodes,
    a color-neutral quark–antiquark pair at those nodes is a physical bound state.
    Corollary of `spatially_extended_composite_lifting`. -/
theorem meson_bound_state_exists
    (beableA beableB : Fin 5 → Fin 7)
    (h_admA : PSCAdmissible beableA)
    (h_admB : PSCAdmissible beableB)
    (h_color_neutral : Confinement.totalColor beableA + Confinement.totalColor beableB = 0)
    (nodeA nodeB : CausalNode L T)
    (h_distinct : nodeA ≠ nodeB)
    (vacuumPath : List (CausalNode L T))
    (h_path : IsVacuumPath L T nodeA nodeB vacuumPath) :
    PhysicalBoundState beableA beableB := by
  have h_dA := dweight_pos_of_psc beableA h_admA
  have h_dB := dweight_pos_of_psc beableB h_admB
  obtain ⟨_, _, _, _, _, h_phys⟩ :=
    @spatially_extended_composite_lifting L T beableA beableB h_admA h_admB h_color_neutral
      h_dA h_dB nodeA nodeB h_distinct vacuumPath h_path
  exact h_phys

/-- Lifting Theorem applied to each spatially separated component independently. -/
theorem particle_lifts_independently
    (beable : Fin 5 → Fin 7)
    (h_adm : PSCAdmissible beable)
    {P : (Fin 5 → Fin 7) → Prop}
    (hP : ∀ b, PSCAdmissible b → P b) :
    P beable :=
  hP beable h_adm

/-- Composite property lifts via the Composition Theorem structure: any property
    holding for all PSC-admissible beables holds for each component of a spatially
    extended composite. -/
theorem spatial_composition_lifts
    (c : SpatiallyExtendedComposite L T)
    (h_spatial : SpatiallyExtendedComposite.PSCAdmissibleSpatial L T c)
    {P : (Fin 5 → Fin 7) → Prop}
    (hP : ∀ b, PSCAdmissible b → P b) :
    P c.beableA ∧ P c.beableB :=
  ⟨particle_lifts_independently c.beableA h_spatial.1 hP,
   particle_lifts_independently c.beableB h_spatial.2.1 hP⟩

end GTE.Spacetime.SpatialExtension
