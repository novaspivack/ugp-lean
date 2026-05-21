import NemS.Optimality.Terminality
import NemS.Category.PSCSys
import UgpLean.Framework.GTEFrameworkInstance
import UgpLean.Universality.CUP3DUniqueness

/-!
# UgpLean.Framework.GTEOptimalityInstance

**Stages 3–4 of Rank 282-C1F (C1 Final Coalgebra).**

Wires GTE's already-certified MDL minimality (CUP-12, zero sorry) into a
`NemS.Optimality.TheorySpace.PSCOptimal` instance and proves Semantic Terminality.

## Construction

The GTE Z₇ Theory Space (`GTETheorySpace`) formalises:
- **Theories**: Z₇ CA functions `f : Fin 7 → Fin 7 → Fin 7 → Fin 7`
- **Complexity K(f)**: count of neighborhoods with nonzero output (MDL bit count)
- **Record equivalence**: agreement on the 18 orbit-fixed neighborhoods (`isFixedNeighborhood`)
- **Extension**: same as record equivalence (adding free micro-parameters)
- **PSC failure**: activating any of the 325 free neighborhoods

The key certificates (all zero sorry, from CUP3DUniqueness §3):
- `fmdl_nonzero_only_at_fixed`: fmdl outputs nonzero only on fixed neighborhoods
- `fmdl_zero_on_free_neighborhoods`: fmdl outputs 0 on all 325 free neighborhoods

From these, `gte_psc_optimal` follows by a subset argument:
the active-neighborhood set of fmdl is contained in that of any record-equivalent f'.

## Certification status

| Component | Status |
|-----------|--------|
| `GTETheorySpace` | zero sorry |
| `gte_psc_optimal` | zero sorry |
| `GTEOptimalityInstance` | zero sorry |
| `gte_extension_dichotomy` | zero sorry |
| `gte_semantic_terminality` | zero sorry |
-/

namespace UgpLean.Framework.GTE

open NemS.Optimality
open CUP3D

-- ────────────────────────────────────────────────────────────────────────────
-- §2.1  GTE Theory Space components
-- ────────────────────────────────────────────────────────────────────────────

/-- MDL complexity of a Z₇ CA function: the number of input neighborhoods
    on which it produces nonzero output.
    PSCOptimality = minimizing this count among all record-equivalent functions.
    f_MDL's complexity = |{(l,c,r) : fmdl(l,c,r) ≠ 0}| (only the 18 fixed, active ones). -/
def z7CAComplexity (f : Fin 7 → Fin 7 → Fin 7 → Fin 7) : ℕ :=
  (Finset.univ.filter fun t : Fin 7 × Fin 7 × Fin 7 =>
    decide (f t.1 t.2.1 t.2.2 ≠ 0) = true).card

/-- Record equivalence: two Z₇ CA functions produce identical output on all
    orbit-fixed neighborhoods (the 18 `isFixedNeighborhood` constraints from the
    SM generation orbit {gen₁, gen₂, gen₃, vac} and the binary Rule 110 sublayer). -/
def z7CARecordEq (f g : Fin 7 → Fin 7 → Fin 7 → Fin 7) : Prop :=
  ∀ l c r : Fin 7, isFixedNeighborhood l c r = true → f l c r = g l c r

/-- Extension: f' extends f if they agree on all 18 fixed neighborhoods.
    f' may differ on any of the 325 free neighborhoods (micro-parameter freedom). -/
def z7CAExtends (f' f : Fin 7 → Fin 7 → Fin 7 → Fin 7) : Prop :=
  z7CARecordEq f' f

/-- PSC failure: f fails Perfect Self-Containment if it outputs nonzero on any
    free neighborhood, since that output is not determined by the orbit and Rule 110
    constraints and requires an external selector. -/
def z7CAFailsPSC (f : Fin 7 → Fin 7 → Fin 7 → Fin 7) : Prop :=
  ∃ l c r : Fin 7, isFixedNeighborhood l c r = false ∧ f l c r ≠ 0

-- ────────────────────────────────────────────────────────────────────────────
-- §2.2  GTETheorySpace: the NemS.Optimality.TheorySpace instance for GTE
-- ────────────────────────────────────────────────────────────────────────────

/-- **GTETheorySpace** (NemS.Optimality.TheorySpace):
    The space of Z₇ CA functions, equipped with MDL complexity, orbit-agreement
    record equivalence, micro-parameter extension, and PSC violation predicate.

    This is the theory space in which f_MDL is PSC-Optimal (Stage 3, Rank 282-C1F). -/
def GTETheorySpace : TheorySpace where
  Theory           := Fin 7 → Fin 7 → Fin 7 → Fin 7
  K                := z7CAComplexity
  RecordEquivalent := z7CARecordEq
  Extends          := z7CAExtends
  FailsPSC         := z7CAFailsPSC

-- ────────────────────────────────────────────────────────────────────────────
-- §2.3  Key structural lemmas (bridges CUP3DUniqueness to TheorySpace language)
-- ────────────────────────────────────────────────────────────────────────────

/-- Every neighborhood where f_MDL outputs nonzero is a fixed neighborhood.
    Certificate: `fmdl_nonzero_only_at_fixed` (CUP3DUniqueness §3, CatAL, zero sorry). -/
private lemma fmdl_active_is_fixed {l c r : Fin 7} (h : fmdl l c r ≠ 0) :
    isFixedNeighborhood l c r = true :=
  fmdl_nonzero_only_at_fixed l c r h

/-- Any record-equivalent f' agrees with f_MDL exactly on f_MDL's active neighborhoods,
    because those neighborhoods are all fixed. -/
private lemma record_eq_copies_fmdl_active
    (f' : Fin 7 → Fin 7 → Fin 7 → Fin 7)
    (hreq : z7CARecordEq f' fmdl)
    {l c r : Fin 7} (h : fmdl l c r ≠ 0) :
    f' l c r ≠ 0 := by
  rw [hreq l c r (fmdl_active_is_fixed h)]
  exact h

/-- The active-neighborhood Finset of f_MDL is a subset of that of any
    record-equivalent f'.  This is the key monotonicity fact for PSCOptimal. -/
private lemma fmdl_active_subset_of_record_eq
    (f' : Fin 7 → Fin 7 → Fin 7 → Fin 7)
    (hreq : z7CARecordEq f' fmdl) :
    (Finset.univ.filter fun t : Fin 7 × Fin 7 × Fin 7 =>
        decide (fmdl t.1 t.2.1 t.2.2 ≠ 0) = true) ⊆
    (Finset.univ.filter fun t : Fin 7 × Fin 7 × Fin 7 =>
        decide (f' t.1 t.2.1 t.2.2 ≠ 0) = true) := by
  intro ⟨l, c, r⟩ hmem
  simp only [Finset.mem_filter, Finset.mem_univ, true_and, decide_eq_true_eq] at hmem ⊢
  exact record_eq_copies_fmdl_active f' hreq hmem

-- ────────────────────────────────────────────────────────────────────────────
-- §2.4  PSC-Optimality of f_MDL (Stage 3 main theorem)
-- ────────────────────────────────────────────────────────────────────────────

/-- **gte_psc_optimal** (CatAL ★★★★, zero sorry):
    f_MDL is PSC-Optimal in the GTE Theory Space:
    `∀ f', RecordEquivalent f' fmdl → K(fmdl) ≤ K(f')`.

    **Proof sketch:**
    K(fmdl) = |{(l,c,r) : fmdl(l,c,r) ≠ 0}|.
    Any record-equivalent f' agrees with fmdl on all fixed neighborhoods.
    Since fmdl outputs nonzero ONLY on fixed neighborhoods
    (`fmdl_nonzero_only_at_fixed`, CUP3DUniqueness §3), f' must also output
    nonzero there.  Hence the active set of fmdl ⊆ the active set of f', so
    K(fmdl) ≤ K(f') by Finset.card_le_card.

    **Certificate chain (all zero sorry):**
    - `fmdl_nonzero_only_at_fixed` (CUP3DUniqueness §3, CatAL): fmdl active → fixed
    - `z7CARecordEq` (definition): f' agrees with fmdl on fixed neighborhoods
    - `Finset.card_le_card` (Mathlib): monotone cardinality for subsets

    LEAN-CERTIFIED (zero sorry). -/
theorem gte_psc_optimal : TheorySpace.PSCOptimal GTETheorySpace fmdl := by
  intro f' hreq
  -- Goal: GTETheorySpace.K fmdl ≤ GTETheorySpace.K f'
  -- By definition: z7CAComplexity fmdl ≤ z7CAComplexity f'
  show z7CAComplexity fmdl ≤ z7CAComplexity f'
  unfold z7CAComplexity
  exact Finset.card_le_card (fmdl_active_subset_of_record_eq f' hreq)

-- ────────────────────────────────────────────────────────────────────────────
-- §2.5  GTEOptimalityInstance — the Stage 3 certificate
-- ────────────────────────────────────────────────────────────────────────────

/-- **GTEOptimalityInstance** (CatAL, zero sorry):
    f_MDL is the PSC-Optimal theory in the GTE Theory Space.

    **Stage 3 certificate for Rank 282-C1F** (C1 Final Coalgebra).

    Physical content: among all Z₇ CA functions that respect the SM generation
    orbit constraints (the 18 isFixedNeighborhood equalities), f_MDL minimizes
    the MDL description length (active-neighborhood count).  Any extension that
    activates a free neighborhood either violates PSC or is redundant (by
    `semantic_terminality`, NemS.Optimality.Terminality, zero sorry).

    **Full certificate chain (all zero sorry):**
    - `mdl_robustness_z7` (GUTStructure §28, CatAL): MDL uniqueness of f_MDL
    - `fmdl_nonzero_only_at_fixed` (CUP3DUniqueness §3, CatAL): active → fixed
    - `fmdl_zero_on_free_neighborhoods` (CUP3DUniqueness §3, CatAL): free → 0
    - `gte_psc_optimal` (§2.4 above, CatAL): PSCOptimal for f_MDL

    LEAN-CERTIFIED (zero sorry). -/
def GTEOptimalityInstance : TheorySpace.PSCOptimal GTETheorySpace fmdl :=
  gte_psc_optimal

-- ────────────────────────────────────────────────────────────────────────────
-- §2.6  Stage 4: Semantic Terminality for GTE extensions (zero sorry)
-- ────────────────────────────────────────────────────────────────────────────

/-- **gte_extension_dichotomy** (trivial):
    In GTETheorySpace, `Extends = RecordEquivalent` by definition (both are
    `z7CARecordEq`), so every extension is already record-equivalent.
    ExtensionDichotomy holds via `Or.inl`. -/
private lemma gte_extension_dichotomy : GTETheorySpace.ExtensionDichotomy :=
  fun _ _ h => Or.inl h

/-- **gte_semantic_terminality** (CatAL ★★★★, zero sorry):
    Any extension T' of f_MDL is physically redundant (and possibly also fails PSC).

    **Proof:**
    Every extension of f_MDL in GTETheorySpace is record-equivalent to f_MDL by
    definition (Extends = RecordEquivalent = z7CARecordEq).  PSC-Optimality
    (`gte_psc_optimal`, §2.4) then gives K(fmdl) ≤ K(T') directly.
    Hence T' is Redundant (RecordEquivalent ∧ K(fmdl) ≤ K(T')).

    Note: `GTETheorySpace.ExtensionComplexity` does not hold universally across
    all theories in the GTE space (only for the PSC-optimal fmdl).  Rather than
    invoke `semantic_terminality` with that premise, we give a one-step direct
    proof using `gte_psc_optimal`, which is precisely the needed instance.

    **Certificate chain (all zero sorry):**
    - `gte_psc_optimal` (§2.4): K(fmdl) ≤ K(T') for all RecordEquivalent T'
    - `GTETheorySpace.Extends = GTETheorySpace.RecordEquivalent` (definitional)
    - `Redundant` (NemS.Optimality.Terminality): RecordEquivalent ∧ K T ≤ K T'

    LEAN-CERTIFIED (zero sorry). -/
theorem gte_semantic_terminality
    (T' : GTETheorySpace.Theory)
    (h_ext : GTETheorySpace.Extends T' fmdl) :
    GTETheorySpace.FailsPSC T' ∨ TheorySpace.Redundant GTETheorySpace T' fmdl :=
  Or.inr ⟨h_ext, gte_psc_optimal T' h_ext⟩

-- ────────────────────────────────────────────────────────────────────────────
-- §2.7  PSCSys objects: GTECompatibleSpace and GTEPSCSubstrate (Stage 1–2 of Rank 282-C1F)
-- ────────────────────────────────────────────────────────────────────────────

open NemS.Category

/-- **GTECompatibleSpace** (zero sorry):
    `GTETheorySpace` upgraded to a `PSCCompatibleSpace` by proving that
    `z7CARecordEq` is reflexive and transitive, and equipping it with the
    GTE orbit-admissibility predicate.

    - **Reflexivity**: `z7CARecordEq f f` holds since `f l c r = f l c r` trivially.
    - **Transitivity**: agreement on fixed neighborhoods is transitive by equality transitivity.
    - **orbit_admissible**: any theory `f` in this space must agree with `fmdl` on all
      fixed neighborhoods (the 18 SM generation orbit + Rule 110 constraints).
      This is `z7CARecordEq f fmdl` by definition.  It is required as part of the
      `PSCSubstrate` constructor and proved trivially for `fmdl` by `rfl`.

    This is the theory space in which `GTEPSCSubstrate` lives as a PSCSys object. -/
def GTECompatibleSpace : PSCCompatibleSpace where
  toTheorySpace := GTETheorySpace
  req_refl  _         := fun _ _ _ _ => rfl
  req_trans _ _ _ h12 h23 := fun l c r hf => (h12 l c r hf).trans (h23 l c r hf)
  -- orbit_admissible encodes the SM generation orbit + Rule 110 constraints:
  -- a theory is orbit-admissible iff it agrees with fmdl on all 18 fixed neighborhoods.
  orbit_admissible f  := ∀ l c r : Fin 7, isFixedNeighborhood l c r = true → f l c r = fmdl l c r

/-- **GTEPSCSubstrate** (zero sorry):
    The GTE Möbius substrate as an object in the PSCSys category.

    - Theory: `fmdl` (the Z₇ MDL-minimal CA function)
    - Optimality: `gte_psc_optimal` (Stage 3, Rank 282-C1F, zero sorry)
    - Orbit-admissibility: `fmdl` agrees with itself on all fixed neighborhoods (`rfl`)

    This is GTE's canonical object in PSCSys — the one claimed to be terminal (C1). -/
def GTEPSCSubstrate : PSCSubstrate GTECompatibleSpace :=
  ⟨fmdl, gte_psc_optimal, fun _ _ _ _ => rfl⟩

-- c1_final_coalgebra is proved in GTEFinalCoalgebra.lean (Stages 5–7, Rank 282-C1F).
-- Import UgpLean.Framework.GTEFinalCoalgebra to access:
--   c1_final_coalgebra_derived : PSCSubstrate.IsTerminal GTEPSCSubstrate  (CatAD, one sorry)
--   c1_final_coalgebra         : alias for c1_final_coalgebra_derived
--   c1_lambek_isomorphism      : (FPSC GTECompatibleSpace).obj GTEPSCSubstrate = GTEPSCSubstrate  (zero sorry)

end UgpLean.Framework.GTE
