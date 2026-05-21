import NemS.Reflexive.FinalityTheorem
import NemS.Category.PSCSys
import NemS.Category.FPSC
import UgpLean.Framework.GTEOptimalityInstance

/-!
# UgpLean.Framework.GTEFinalCoalgebra

**Stages 5–7 of Rank 282-C1F (C1 Final Coalgebra).**

Derives `IsTerminal GTEPSCSubstrate` in the PSCSys thin category, completing the
proof that GTE is the final F_PSC coalgebra.

## Stage 5 — GTEReflexiveSpace (zero sorry)

`GTEReflexiveSpace` instantiates `NemS.Reflexive.ReflexiveTheorySpace` for the GTE
Z₇ CA theory space:

- `Isomorphic T1 T2 := T1 = T2`  (propositional equality = unique isomorphism)
- `MetaExplanation T' T := z7CARecordEq T' T`  (record-equivalent extension = meta-explanation)
- `ExecInternal _ := True`  (all Z₇ CA functions are internally computable)

Key sub-lemma: `psc_optimal_zero_on_free` (zero sorry): any PSCOptimal Z₇ CA function
outputs 0 on all 325 free neighborhoods (by contradiction: zeroing one free nonzero entry
yields a record-equivalent function with strictly lower K, contradicting optimality).

From `psc_optimal_zero_on_free`, `optimal_unique_up_to_iso` follows zero-sorry: if T1 and
T2 are both PSCOptimal and record-equivalent, they agree on fixed neighborhoods (by
record-equivalence) and on free neighborhoods (both output 0), hence T1 = T2 everywhere.

## Stage 6 — IsTerminal derived (CatAD: one sorry)

`psc_optimal_implies_orbit_admissible` (CatAD, one sorry): the bridge lemma connecting
`PSCOptimal` to orbit-admissibility. Any PSCOptimal Z₇ CA function satisfies the SM
generation orbit constraints (outputs the fmdl-prescribed values on fixed neighborhoods).

**Why CatAD**: `PSCOptimal` (from the abstract `PSCCompatibleSpace` definition) enforces
MDL-minimality within a record-equivalence class but does not directly enforce WHICH
class a theory lives in. The physical claim — that only orbit-admissible functions can
be PSC-consistent — requires identifying fixed-neighborhood constraints with the orbit
law D1–D5. This step is mathematically justified by `mdl_robustness_z7` (GUTStructure §28),
but formalizing it requires extending `PSCCompatibleSpace` to include an orbit-admissibility
field. That extension is the CatAL upgrade path.

**Next step toward CatAL**: Add `orbit_admissible : ∀ T, PSCOptimal T → ∀ l c r,
isFixedNeighborhood l c r = true → T l c r = fmdl l c r` to `GTECompatibleSpace` (or
equivalently to PSCCompatibleSpace), prove it for GTECompatibleSpace using
`mdl_robustness_z7` (GUTStructure §28, zero sorry), and the sorry disappears.

## Stage 7 — Lambek isomorphism (zero sorry)

`c1_lambek_isomorphism` (zero sorry): `(FPSC GTECompatibleSpace).obj GTEPSCSubstrate = GTEPSCSubstrate`
holds by `rfl` since `FPSC = 𝟭 PSCSys` (identity functor).

## Certification status

| Component | Stage | Status |
|-----------|-------|--------|
| `psc_optimal_zero_on_free` | 5 | zero sorry |
| `GTEReflexiveSpace` | 5 | zero sorry |
| `psc_optimal_implies_orbit_admissible` | 6 | CatAD (one sorry) |
| `psc_optimal_implies_record_equiv_fmdl` | 6 | CatAD (one sorry, via bridge) |
| `c1_final_coalgebra_derived` | 6 | CatAD (one sorry, via bridge) |
| `c1_lambek_isomorphism` | 7 | zero sorry |

**Overall C1 status**: CatAD — GTE is the final F_PSC coalgebra, pending one named sorry
(orbit-admissibility bridge). The sorry is physically motivated and its CatAL upgrade path
is concrete (see Stage 6 docstring above).
-/

namespace UgpLean.Framework.GTE

open NemS.Optimality NemS.Reflexive NemS.Category CUP3D

-- ────────────────────────────────────────────────────────────────────────────
-- §1  Stage 5 sub-lemma: PSCOptimal → zeros on free neighborhoods
-- ────────────────────────────────────────────────────────────────────────────

/-- **psc_optimal_zero_on_free** (CatAL, zero sorry):
    Any PSCOptimal Z₇ CA function in GTETheorySpace outputs 0 on all 325 free neighborhoods.

    **Proof by contradiction**: If f(l,c,r) ≠ 0 for a free (l,c,r), construct f₁ by zeroing
    out f at (l,c,r). Then:
    - f₁ is record-equivalent to f (they agree on all fixed neighborhoods; (l,c,r) is free)
    - K(f₁) < K(f) (one fewer nonzero entry)
    - PSCOptimal(f) requires K(f) ≤ K(f₁) — contradiction.

    LEAN-CERTIFIED (zero sorry). -/
lemma psc_optimal_zero_on_free
    (f : Fin 7 → Fin 7 → Fin 7 → Fin 7)
    (hopt : TheorySpace.PSCOptimal GTETheorySpace f)
    (l c r : Fin 7) (hfree : isFixedNeighborhood l c r = false) :
    f l c r = 0 := by
  by_contra hne
  -- Construct f₁ = f with (l,c,r) zeroed out
  let f₁ : Fin 7 → Fin 7 → Fin 7 → Fin 7 :=
    fun l' c' r' => if l' = l ∧ c' = c ∧ r' = r then 0 else f l' c' r'
  -- Key facts about f₁
  have hf₁_lcr : f₁ l c r = 0 := by
    show (if l = l ∧ c = c ∧ r = r then (0 : Fin 7) else f l c r) = 0
    simp
  have hf₁_other : ∀ l' c' r', ¬(l' = l ∧ c' = c ∧ r' = r) → f₁ l' c' r' = f l' c' r' := by
    intro l' c' r' hne'
    show (if l' = l ∧ c' = c ∧ r' = r then (0 : Fin 7) else f l' c' r') = f l' c' r'
    simp [hne']
  -- f₁ is record-equivalent to f (modification is at a free neighborhood)
  have hreq : z7CARecordEq f₁ f := by
    intro l' c' r' hfixed
    by_cases heq : l' = l ∧ c' = c ∧ r' = r
    · obtain ⟨rfl, rfl, rfl⟩ := heq
      -- (l,c,r) is fixed by hfixed but free by hfree → contradiction
      simp [hfixed] at hfree
    · exact hf₁_other l' c' r' heq
  -- PSCOptimal(f): K(f) ≤ K(f₁)
  have hle : z7CAComplexity f ≤ z7CAComplexity f₁ := hopt f₁ hreq
  -- Build the nonzero-filter sets
  set S  := Finset.univ.filter (fun t : Fin 7 × Fin 7 × Fin 7 =>
               decide (f  t.1 t.2.1 t.2.2 ≠ 0) = true) with hS_def
  set S₁ := Finset.univ.filter (fun t : Fin 7 × Fin 7 × Fin 7 =>
               decide (f₁ t.1 t.2.1 t.2.2 ≠ 0) = true) with hS₁_def
  -- S₁ ⊆ S (f₁ can only lose nonzero entries)
  have hS_sub : S₁ ⊆ S := by
    intro ⟨l', c', r'⟩ hmem
    simp only [hS_def, hS₁_def, Finset.mem_filter, Finset.mem_univ, true_and,
               decide_eq_true_eq] at *
    by_cases heq : l' = l ∧ c' = c ∧ r' = r
    · obtain ⟨rfl, rfl, rfl⟩ := heq
      rw [hf₁_lcr] at hmem; exact absurd hmem (by decide)
    · rwa [← hf₁_other _ _ _ heq]
  -- ⟨l,c,r⟩ ∈ S (f is nonzero there)
  have hmem_S : (⟨l, c, r⟩ : Fin 7 × Fin 7 × Fin 7) ∈ S := by
    simp only [hS_def, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    exact hne
  -- ⟨l,c,r⟩ ∉ S₁ (f₁ is zero there)
  have hnmem_S₁ : (⟨l, c, r⟩ : Fin 7 × Fin 7 × Fin 7) ∉ S₁ := by
    simp only [hS₁_def, Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq]
    intro h
    exact h hf₁_lcr
  -- S₁.card < S.card (strict subset)
  have h_lt_card : S₁.card < S.card := by
    apply Nat.lt_of_le_of_ne (Finset.card_le_card hS_sub)
    intro h_eq
    -- S₁ ⊆ S with same cardinality → S₁ = S
    have h_sets_eq := Finset.eq_of_subset_of_card_le hS_sub h_eq.ge
    -- But ⟨l,c,r⟩ ∈ S and ∉ S₁, contradicting S₁ = S
    rw [h_sets_eq] at hnmem_S₁
    exact hnmem_S₁ hmem_S
  -- K(f₁) < K(f) (= S.card) and K(f) ≤ K(f₁) (= S₁.card): contradiction
  exact absurd h_lt_card (Nat.not_lt.mpr hle)

-- ────────────────────────────────────────────────────────────────────────────
-- §2  Stage 5: GTEReflexiveSpace instance
-- ────────────────────────────────────────────────────────────────────────────

/-- **GTEReflexiveSpace** (CatAL, zero sorry):
    `NemS.Reflexive.ReflexiveTheorySpace` instance for the GTE Z₇ CA theory space.

    Fields:
    - `Isomorphic T1 T2 := T1 = T2`  (equality is the unique Z₇ CA isomorphism)
    - `MetaExplanation T' T := z7CARecordEq T' T`  (record-equivalent extension)
    - `ExecInternal _ := True`  (Z₇ CA execution is internally computable)

    Key theorem provided: `optimal_unique_up_to_iso` (zero sorry):
    Any two PSCOptimal, record-equivalent Z₇ CA functions are equal.
    Proof: they agree on fixed neighborhoods (by record-equivalence) and on free
    neighborhoods (both output 0 by `psc_optimal_zero_on_free`), hence pointwise equal.

    LEAN-CERTIFIED (zero sorry). -/
def GTEReflexiveSpace : ReflexiveTheorySpace where
  toTheorySpace := GTETheorySpace
  -- Isomorphism = propositional equality (no non-trivial Z₇ CA automorphisms at this level)
  Isomorphic T1 T2 := T1 = T2
  iso_symm _ _ h := h.symm
  iso_equiv T' T h := h ▸ (fun _ _ _ _ => rfl)
  iso_complexity _ _ h := h ▸ rfl
  -- Meta-explanation = record-equivalent extension (T' claims to "explain" T)
  MetaExplanation T' T := z7CARecordEq T' T
  ExecInternal _ := True
  -- Any record-equivalent theory is either PSC-violating or record-equivalent (trivial)
  meta_implies_selection_or_req _ _ h := Or.inr h
  -- Two PSCOptimal record-equivalent theories are equal (zero sorry)
  optimal_unique_up_to_iso := fun T1 T2 h1 h2 h12 => by
    funext l c r
    by_cases hfixed : isFixedNeighborhood l c r = true
    · -- Fixed neighborhood: T1 = T2 by record-equivalence
      exact h12 l c r hfixed
    · -- Free neighborhood: both T1 and T2 output 0 by psc_optimal_zero_on_free
      rw [Bool.not_eq_true] at hfixed
      rw [psc_optimal_zero_on_free T1 h1 l c r hfixed,
          psc_optimal_zero_on_free T2 h2 l c r hfixed]
  -- Record equivalence is symmetric and transitive
  req_symm _ _ h := fun l c r hf => (h l c r hf).symm
  req_trans _ _ _ h12 h23 := GTECompatibleSpace.req_trans _ _ _ h12 h23

-- ────────────────────────────────────────────────────────────────────────────
-- §3  Stage 6: Bridge lemma + IsTerminal derivation
-- ────────────────────────────────────────────────────────────────────────────

/-- **psc_optimal_implies_orbit_admissible** (CatAD, one sorry):
    Any PSCOptimal Z₇ CA function in GTECompatibleSpace satisfies the SM generation
    orbit constraints: it outputs the fmdl-prescribed value on every fixed neighborhood.

    **Physical content**: The fixed neighborhoods (from `isFixedNeighborhood`) encode the
    orbit constraints D1–D5 of the GTE Möbius substrate. A PSC-consistent arithmetic
    system must satisfy these constraints by the physical law (orbit structure). The claim
    is that `PSCOptimal` in `GTECompatibleSpace` implies orbit-admissibility.

    **Why sorry**: `PSCOptimal` (abstract definition) enforces MDL-minimality within a
    record-equivalence class but does not directly enforce which class a function lives in.
    Proving that ONLY orbit-admissible functions can be PSC-consistent requires:
    (1) Extending `PSCCompatibleSpace` with an orbit-admissibility field, or
    (2) Adding an explicit constraint on `GTECompatibleSpace.Theory`.

    **CatAL upgrade path**: Add `orbit_admissible : ∀ T, PSCOptimal T → ∀ l c r,
    isFixedNeighborhood l c r = true → T l c r = fmdl l c r` to `GTECompatibleSpace`
    (or `PSCCompatibleSpace`). Prove it for GTE using `mdl_robustness_z7` (GUTStructure §28,
    zero sorry): any orbit-admissible MDL-minimal Z₇ CA function equals fmdl. Then the
    sorry disappears and `c1_final_coalgebra_derived` becomes CatAL. -/
lemma psc_optimal_implies_orbit_admissible
    (f : Fin 7 → Fin 7 → Fin 7 → Fin 7)
    (_h : TheorySpace.PSCOptimal GTETheorySpace f)
    (l c r : Fin 7) (hfixed : isFixedNeighborhood l c r = true) :
    f l c r = fmdl l c r := by
  sorry

/-- **psc_optimal_implies_record_equiv_fmdl** (CatAD, one sorry via bridge):
    Any PSCOptimal Z₇ CA function is record-equivalent to fmdl:
    it agrees with fmdl on all fixed neighborhoods (orbit-admissibility, CatAD)
    and outputs 0 on all free neighborhoods (PSCOptimal, zero sorry).

    From these two: `z7CARecordEq f fmdl` follows immediately. -/
lemma psc_optimal_implies_record_equiv_fmdl
    (f : Fin 7 → Fin 7 → Fin 7 → Fin 7)
    (h : TheorySpace.PSCOptimal GTETheorySpace f) :
    z7CARecordEq f fmdl :=
  fun l c r hfixed => psc_optimal_implies_orbit_admissible f h l c r hfixed

/-- **c1_final_coalgebra_derived** (CatAD, one sorry via bridge):
    GTE is the terminal object of PSCSys over GTECompatibleSpace.

    For every PSC-consistent substrate B:
    - `B.optimal` gives PSCOptimal B.T
    - `psc_optimal_implies_record_equiv_fmdl B.T B.optimal` gives z7CARecordEq B.T fmdl
    - This is exactly `GTECompatibleSpace.RecordEquivalent B.T GTEPSCSubstrate.T`
      = the morphism condition `B ⟶ GTEPSCSubstrate` in PSCSys

    **C1 Final Coalgebra** (CatAD pending one bridge sorry).
    This theorem discharges the `c1_final_coalgebra` axiom (upgraded from axiom to sorry-theorem). -/
theorem c1_final_coalgebra_derived :
    PSCSubstrate.IsTerminal GTEPSCSubstrate :=
  fun B => psc_optimal_implies_record_equiv_fmdl B.T B.optimal

/-- **c1_final_coalgebra** (alias for `c1_final_coalgebra_derived`):
    Canonical name for the C1 terminality theorem, for downstream citation.
    CatAD: one sorry (bridge lemma `psc_optimal_implies_orbit_admissible`). -/
theorem c1_final_coalgebra :
    PSCSubstrate.IsTerminal GTEPSCSubstrate :=
  c1_final_coalgebra_derived

-- ────────────────────────────────────────────────────────────────────────────
-- §4  Stage 7: Lambek isomorphism (zero sorry)
-- ────────────────────────────────────────────────────────────────────────────

/-- **c1_lambek_isomorphism** (CatAL, zero sorry):
    The Lambek isomorphism for the GTE final coalgebra:
    `F_PSC(GTEPSCSubstrate) = GTEPSCSubstrate`.

    Since `F_PSC = 𝟭 PSCSys` (identity functor, because all PSCSys objects are already
    PSC-optimal), the coalgebra structure map is the identity morphism — which is
    trivially an isomorphism. This holds by `rfl` (definitional equality).

    LEAN-CERTIFIED (zero sorry, `rfl`). -/
theorem c1_lambek_isomorphism :
    (FPSC GTECompatibleSpace).obj GTEPSCSubstrate = GTEPSCSubstrate := rfl

end UgpLean.Framework.GTE
