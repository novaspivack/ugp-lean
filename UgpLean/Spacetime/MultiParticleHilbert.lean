import UgpLean.Spacetime.QECStabilizer
import UgpLean.Spacetime.MassGap
import UgpLean.Spacetime.OrbitMassHierarchy

namespace GTE.Spacetime.MultiParticle

open GTE.Lifting GTE.Spacetime.MassGap GTE.Spacetime.QEC
open UgpLean.Universality.LawvereZone CUP3D

/-!
# Multi-Particle Hilbert Space

Formalizes the algebraic structure of multi-beable states in the GTE
framework: the multi-particle state space built from the QEC code subspace
{vacuum, gen₁, gen₂, gen₃}.

## Scientific context

The 't Hooft cogwheel construction on the single $\mathbb{Z}_7^5$ visible
sector yields a 1-dimensional physical Hilbert space
$\mathcal{H}_{\rm phys} = \mathbb{C}|\text{vac}\rangle$ (P37).  A
multi-particle Hilbert space requires extending this construction to $N$
copies of the visible sector.  The present module formalizes the
**algebraic layer** of that extension: the finite-dimensional state space,
its DWeight-based norm, the mass observable, and the Kronecker basis inner
product.

The QEC code subspace (`QECStabilizer.lean`) provides the
single-particle ingredients:
- Code words: `{vacuum, gen₁, gen₂, gen₃}` — PSC-admissible beables
- DWeight: projection onto the code subspace (= 1 for code words)
- Stabilizer: `fmdl_step5` preserves the code subspace

The mass hierarchy (`OrbitMassHierarchy.lean`) provides
the physical mass assignments: gen₁ < gen₂ < gen₃ in all SM sectors.

## Results certified here (all CatAL, zero sorry)

| Theorem | Content |
|---------|---------|
| `code_word_cardinality` | Exactly 4 code words |
| `n_particle_state_count` | N-particle basis has 4^N elements |
| `multiDWeight_eq_one` | DWeight product = 1 on every multi-state |
| `multiDWeight_pos` | DWeight product > 0 on every multi-state |
| `multiMass_append` | Mass is additive under state concatenation |
| `multiMass_le` | Total mass ≤ 3 × particle number |
| `vacuum_mass_zero` | Vacuum sector contributes zero mass |
| `gen1_mass_pos` | gen₁ single-particle state has positive mass |
| `mass_hierarchy_three_states` | gen₃ > gen₂ > gen₁ > 0 (abstract units) |
| `smGenMass_multi_anchor` | Non-vacuum single-particle mass ≥ 1.8 MeV |
| `multiparticle_orbit_closure` | f_MDL preserves all code words in any multi-state |
| `inner_product_positive_definite` | Basis inner product is positive definite |
| `multiparticle_space_well_defined` | Bundle of all structural properties |

## Honest boundaries (CatAD)

- Hilbert space completion (ℓ² norm, continuum limit) remains open
- Connection to standard QFT Fock space: the Fock algebra creation/annihilation
  operators act on the tensor product ℋ_ring^⊗N; identifying f_MDL ring
  dynamics with QFT field modes requires the AFCA continuum limit
- The tensor-product factorization in the 't Hooft information-equivalence sense
  (§9.3 of `tHooft2016CA`) is CatAD pending the gauge identification upgrade

## Axiom inventory

| Component | Axioms |
|-----------|--------|
| `code_word_cardinality` | nativeDecide |
| All others | propext, Classical.choice, Quot.sound |
-/

-- ─────────────────────────────────────────────────────────────────────────────
-- §1  Code word type
-- ─────────────────────────────────────────────────────────────────────────────

/-- The GTE code word type: a beable in the QEC code subspace.

    These are the four PSC-admissible beables
    {vacuum, gen₁, gen₂, gen₃} ⊂ ℤ₇^5.
    They are the only physically realizable single-particle beable states. -/
abbrev CodeWord := { b : Fin 5 → Fin 7 // InCodeSubspace b }

-- The four canonical single-particle states
/-- The vacuum code word. -/
def cwVacuum : CodeWord := ⟨fmdl_vacuum5, vacuum_psc_admissible⟩
/-- The gen₁ code word (lightest non-vacuum particle). -/
def cwGen1 : CodeWord := ⟨fmdl_gen1_z7, gen1_psc_admissible⟩
/-- The gen₂ code word (middle-generation particle). -/
def cwGen2 : CodeWord := ⟨fmdl_gen2_z7, gen2_psc_admissible⟩
/-- The gen₃ code word (heaviest particle). -/
def cwGen3 : CodeWord := ⟨fmdl_gen3_z7, gen3_psc_admissible⟩

/-- Explicit bijection between the 4 GTE code words and Fin 4.

    Used to compute Fintype.card CodeWord = 4 without relying on
    native_decide (which fails due to a noncomputable CategoryTheory instance
    in the synthesized Fintype for Fin 5 → Fin 7 subtypes). -/
private noncomputable def codeWordEquiv : CodeWord ≃ Fin 4 where
  toFun cw :=
    if cw.1 = fmdl_vacuum5 then ⟨0, by norm_num⟩
    else if cw.1 = fmdl_gen1_z7 then ⟨1, by norm_num⟩
    else if cw.1 = fmdl_gen2_z7 then ⟨2, by norm_num⟩
    else ⟨3, by norm_num⟩
  invFun i :=
    if i.val = 0 then cwVacuum
    else if i.val = 1 then cwGen1
    else if i.val = 2 then cwGen2
    else cwGen3
  left_inv := by
    intro cw
    apply Subtype.ext
    rcases (qec_code_words cw.1).mp cw.2 with h | h | h | h
    all_goals
      simp only [h, ↓reduceIte, cwVacuum, cwGen1, cwGen2, cwGen3,
                 show fmdl_gen1_z7 ≠ fmdl_vacuum5 from by decide,
                 show fmdl_gen2_z7 ≠ fmdl_vacuum5 from by decide,
                 show fmdl_gen2_z7 ≠ fmdl_gen1_z7 from by decide,
                 show fmdl_gen3_z7 ≠ fmdl_vacuum5 from by decide,
                 show fmdl_gen3_z7 ≠ fmdl_gen1_z7 from by decide,
                 show fmdl_gen3_z7 ≠ fmdl_gen2_z7 from by decide,
                 show (1 : ℕ) ≠ 0 from by norm_num,
                 show (2 : ℕ) ≠ 0 from by norm_num,
                 show (2 : ℕ) ≠ 1 from by norm_num,
                 show (3 : ℕ) ≠ 0 from by norm_num,
                 show (3 : ℕ) ≠ 1 from by norm_num,
                 show (3 : ℕ) ≠ 2 from by norm_num]
  right_inv := by
    intro i
    fin_cases i <;>
      simp only [cwVacuum, cwGen1, cwGen2, cwGen3,
                 show fmdl_gen1_z7 ≠ fmdl_vacuum5 from by decide,
                 show fmdl_gen2_z7 ≠ fmdl_vacuum5 from by decide,
                 show fmdl_gen2_z7 ≠ fmdl_gen1_z7 from by decide,
                 show fmdl_gen3_z7 ≠ fmdl_vacuum5 from by decide,
                 show fmdl_gen3_z7 ≠ fmdl_gen1_z7 from by decide,
                 show fmdl_gen3_z7 ≠ fmdl_gen2_z7 from by decide,
                 show (1 : ℕ) ≠ 0 from by norm_num,
                 show (2 : ℕ) ≠ 0 from by norm_num,
                 show (2 : ℕ) ≠ 1 from by norm_num,
                 show (3 : ℕ) ≠ 0 from by norm_num,
                 show (3 : ℕ) ≠ 1 from by norm_num,
                 show (3 : ℕ) ≠ 2 from by norm_num,
                 ↓reduceIte, Fin.ext_iff, Fin.val_zero, Fin.val_one]

/-- **code_word_cardinality** (CatAL):
    There are exactly 4 GTE code words: {vacuum, gen₁, gen₂, gen₃}.

    Proof: via an explicit bijection with Fin 4 (using the orbit characterization
    from psc_admissible_iff_orbit). -/
theorem code_word_cardinality : Fintype.card CodeWord = 4 :=
  (Fintype.card_congr codeWordEquiv).trans (Fintype.card_fin 4)

-- ─────────────────────────────────────────────────────────────────────────────
-- §2  N-particle state space
-- ─────────────────────────────────────────────────────────────────────────────

/-- An N-particle state: a function assigning one code word to each of the
    N particle slots.  This is the basis-element description of the N-fold
    tensor product $\mathcal{H}_{\rm ring}^{\otimes N}$ restricted to
    code-subspace occupations. -/
abbrev NParticleState (n : ℕ) := Fin n → CodeWord

/-- **n_particle_state_count** (CatAL):
    The N-particle state space has exactly 4^N basis elements.

    Proof: the Fintype cardinality of (Fin N → CodeWord) is
    ∏ i : Fin N, card CodeWord = 4^N.

    Physical interpretation: each particle can occupy one of 4 code words,
    so N non-interacting particles yield a 4^N-dimensional Hilbert space at
    the algebraic (basis) level. -/
theorem n_particle_state_count (n : ℕ) : Fintype.card (NParticleState n) = 4^n := by
  simp only [NParticleState]
  rw [Fintype.card_pi]
  simp [code_word_cardinality, Finset.prod_const, Finset.card_univ, Fintype.card_fin]

-- ─────────────────────────────────────────────────────────────────────────────
-- §3  Variable-length multi-beable states
-- ─────────────────────────────────────────────────────────────────────────────

/-- A multi-beable state: an ordered list of code words.
    This represents a variable-occupancy multi-particle state.
    The empty list is the vacuum sector; a length-n list is an n-particle state. -/
abbrev MultiBeableState := List CodeWord

/-- The vacuum multi-state (zero particles). -/
def vacuumMultiState : MultiBeableState := []

/-- Embed a single code word as a one-particle state. -/
def singleParticle (cw : CodeWord) : MultiBeableState := [cw]

-- ─────────────────────────────────────────────────────────────────────────────
-- §4  DWeight product on multi-beable states
-- ─────────────────────────────────────────────────────────────────────────────

/-- The DWeight product of a multi-beable state.

    Defined as the product of individual DWeights.  For code-word states this
    is always 1, since `DWeight b = 1` for all PSC-admissible `b`. -/
noncomputable def multiDWeight (s : MultiBeableState) : ℝ :=
  (s.map (fun cw => DWeight cw.1)).prod

/-- Every code word has DWeight = 1. -/
private theorem code_word_dweight_eq_one (cw : CodeWord) : DWeight cw.1 = 1 := by
  have hpsc : PSCAdmissible cw.1 := cw.2
  simp [DWeight, hpsc]

/-- **multiDWeight_eq_one** (CatAL):
    The DWeight product of any multi-beable state is exactly 1.

    Proof: every code word contributes DWeight = 1; the product of 1s is 1. -/
theorem multiDWeight_eq_one (s : MultiBeableState) : multiDWeight s = 1 := by
  unfold multiDWeight
  apply List.prod_eq_one
  intro x hx
  simp only [List.mem_map] at hx
  obtain ⟨cw, _, rfl⟩ := hx
  exact code_word_dweight_eq_one cw

/-- **multiDWeight_pos** (CatAL):
    The DWeight product of any multi-beable state is strictly positive. -/
theorem multiDWeight_pos (s : MultiBeableState) : 0 < multiDWeight s := by
  rw [multiDWeight_eq_one]
  norm_num

-- ─────────────────────────────────────────────────────────────────────────────
-- §5  Mass observable on multi-beable states
-- ─────────────────────────────────────────────────────────────────────────────

/-- The total GTE mass of a multi-beable state.

    Defined as the sum of individual abstract orbit-index masses `GTE_mass`.
    The orbit index takes values in {0, 1, 2, 3} (vacuum = 0, gen₁ = 1,
    gen₂ = 2, gen₃ = 3), so total mass ∈ {0, …, 3N} for an N-particle state. -/
def multiMass (s : MultiBeableState) : ℕ :=
  (s.map (fun cw => GTE_mass cw.1)).sum

-- ─────────────────────────────────────────────────────────────────────────────
-- §6  Mass properties
-- ─────────────────────────────────────────────────────────────────────────────

/-- The vacuum multi-state has zero mass. -/
theorem multiMass_empty : multiMass vacuumMultiState = 0 := by
  simp [multiMass, vacuumMultiState]

/-- **multiMass_append** (CatAL):
    Mass is additive under particle concatenation.

    Proof: sum of concatenated maps = sum of individual sums. -/
theorem multiMass_append (s t : MultiBeableState) :
    multiMass (s ++ t) = multiMass s + multiMass t := by
  simp [multiMass, List.map_append, List.sum_append]

/-- Single-particle mass matches GTE_mass of the code word. -/
theorem multiMass_single (cw : CodeWord) :
    multiMass (singleParticle cw) = GTE_mass cw.1 := by
  simp [multiMass, singleParticle]

/-- Every code word has GTE_mass at most 3 (gen₃ is the maximum). -/
private theorem code_word_mass_le_three (cw : CodeWord) : GTE_mass cw.1 ≤ 3 := by
  rcases (qec_code_words cw.1).mp cw.2 with h | h | h | h <;> rw [h]
  · simp [GTE_mass]
  · simp [GTE_mass, show fmdl_gen1_z7 ≠ fmdl_vacuum5 from by decide]
  · simp [GTE_mass,
          show fmdl_gen2_z7 ≠ fmdl_vacuum5 from by decide,
          show fmdl_gen2_z7 ≠ fmdl_gen1_z7 from by decide]
  · simp [GTE_mass,
          show fmdl_gen3_z7 ≠ fmdl_vacuum5 from by decide,
          show fmdl_gen3_z7 ≠ fmdl_gen1_z7 from by decide,
          show fmdl_gen3_z7 ≠ fmdl_gen2_z7 from by decide]

/-- **multiMass_le** (CatAL):
    The total mass of an N-particle state is bounded by 3N.

    Proof: each code word contributes GTE_mass ≤ 3; sum over N particles
    gives total ≤ 3N. -/
theorem multiMass_le (s : MultiBeableState) : multiMass s ≤ 3 * s.length := by
  induction s with
  | nil => simp [multiMass]
  | cons cw rest ih =>
    have hm : GTE_mass cw.1 ≤ 3 := code_word_mass_le_three cw
    unfold multiMass at *
    simp only [List.map_cons, List.sum_cons, List.length_cons] at *
    omega

-- ─────────────────────────────────────────────────────────────────────────────
-- §7  Mass hierarchy and physical spectrum
-- ─────────────────────────────────────────────────────────────────────────────

/-- The vacuum single-particle state has zero mass. -/
theorem vacuum_mass_zero : multiMass (singleParticle cwVacuum) = 0 := by
  simp [multiMass, singleParticle, cwVacuum, GTE_mass]

/-- **gen1_mass_pos** (CatAL):
    The gen₁ single-particle state has strictly positive abstract mass. -/
theorem gen1_mass_pos : 0 < multiMass (singleParticle cwGen1) := by
  simp [multiMass, singleParticle, cwGen1, GTE_mass,
    show fmdl_gen1_z7 ≠ fmdl_vacuum5 from by decide]

/-- **mass_hierarchy_three_states** (CatAL):
    The three non-vacuum generation states are strictly ordered by mass:
    gen₃ > gen₂ > gen₁ > 0 in abstract GTE orbit-index units.

    This is the single-particle projection of `mass_hierarchy_gen3_gt_gen2_gt_gen1`
    (MassGap.lean §6), translated to the multi-state setting. -/
theorem mass_hierarchy_three_states :
    multiMass (singleParticle cwGen3) > multiMass (singleParticle cwGen2) ∧
    multiMass (singleParticle cwGen2) > multiMass (singleParticle cwGen1) ∧
    multiMass (singleParticle cwGen1) > 0 := by
  simp only [multiMass, singleParticle, cwGen1, cwGen2, cwGen3,
             List.map_cons, List.map_nil, List.sum_cons, List.sum_nil, add_zero]
  exact mass_hierarchy_gen3_gt_gen2_gt_gen1

/-- **smGenMass_multi_anchor** (CatAL):
    Every non-vacuum single-particle state carries physical mass
    ≥ up_quark_mass_lb_eV = 1.8 MeV (conservative PDG 2024 lower bound).

    This anchors the abstract orbit-index mass to the physical mass scale:
    every excited code word has mass ≥ Δ = 1.8 MeV (the universal beable
    floor from `gte_mass_formula_physical`). -/
theorem smGenMass_multi_anchor (cw : CodeWord) (h_vac : cw.1 ≠ fmdl_vacuum5) :
    smGenMass cw.1 ≥ up_quark_mass_lb_eV :=
  smGenMass_pos cw.1 cw.2 h_vac

-- ─────────────────────────────────────────────────────────────────────────────
-- §8  Stabilizer closure for multi-particle states
-- ─────────────────────────────────────────────────────────────────────────────

/-- **multiparticle_orbit_closure** (CatAL):
    The f_MDL stabilizer preserves every code word in a multi-beable state.

    This extends `qec_orbit_closure` (38-QEC) to multi-particle states:
    if every particle starts in the code subspace, the f_MDL step maps each
    particle to the code subspace. -/
theorem multiparticle_orbit_closure (s : MultiBeableState) :
    ∀ cw : CodeWord, cw ∈ s → InCodeSubspace (fmdl_step5 cw.1) :=
  fun cw _ => qec_orbit_closure cw.1 cw.2

-- ─────────────────────────────────────────────────────────────────────────────
-- §9  Basis inner product on N-particle states
-- ─────────────────────────────────────────────────────────────────────────────

/-- Kronecker basis inner product on N-particle code-word states.

    On the discrete N-particle basis, the inner product is
    ⟨ψ|φ⟩ = 1 if ψ = φ, else 0.
    This is the standard orthonormal inner product on a finite basis.

    For the continuous Hilbert space completion (complex amplitudes over the
    basis), this is the inner product of the basis vectors of the discrete
    ℂ-span of NParticleState n.  The full ℂ-linear extension and the Hilbert
    space completion remain CatAD pending the continuum limit infrastructure. -/
def basisInnerProduct {n : ℕ} (a b : NParticleState n) : ℕ :=
  if a = b then 1 else 0

/-- **inner_product_positive_definite** (CatAL):
    The Kronecker basis inner product satisfies positive definiteness:
    ⟨ψ|ψ⟩ = 1 > 0 for every N-particle state ψ.

    This is the basis-level certification that the inner product is
    non-degenerate on the N-particle state space. -/
theorem inner_product_positive_definite {n : ℕ} (a : NParticleState n) :
    basisInnerProduct a a = 1 := by
  simp [basisInnerProduct]

/-- Orthogonality: distinct N-particle basis states have inner product 0. -/
theorem inner_product_orthogonal {n : ℕ} (a b : NParticleState n) (h : a ≠ b) :
    basisInnerProduct a b = 0 := by
  simp [basisInnerProduct, h]

-- ─────────────────────────────────────────────────────────────────────────────
-- §10  Mass operator spectrum on N-particle states
-- ─────────────────────────────────────────────────────────────────────────────

/-- The total GTE mass of an N-particle basis state (sum of orbit indices). -/
def nParticleMass {n : ℕ} (s : NParticleState n) : ℕ :=
  Finset.univ.sum (fun i => GTE_mass (s i).1)

/-- **nParticleMass_nonneg** (CatAL):
    The mass of any N-particle basis state is non-negative. -/
theorem nParticleMass_nonneg {n : ℕ} (s : NParticleState n) : 0 ≤ nParticleMass s :=
  Nat.zero_le _

/-- **nParticleMass_le** (CatAL):
    The mass of any N-particle state is bounded by 3N. -/
theorem nParticleMass_le {n : ℕ} (s : NParticleState n) : nParticleMass s ≤ 3 * n := by
  unfold nParticleMass
  calc Finset.univ.sum (fun i => GTE_mass (s i).1)
      ≤ Finset.univ.sum (fun _ : Fin n => 3) := by
        apply Finset.sum_le_sum
        intro i _
        exact code_word_mass_le_three (s i)
    _ = 3 * n := by
        rw [Finset.sum_const, Finset.card_univ, Fintype.card_fin]
        simp [smul_eq_mul, mul_comm]

/-- **vacuum_nparticle_mass** (CatAL):
    The all-vacuum N-particle state has mass 0. -/
theorem vacuum_nparticle_mass (n : ℕ) :
    nParticleMass (fun _ : Fin n => cwVacuum) = 0 := by
  simp [nParticleMass, cwVacuum, GTE_mass]

-- ─────────────────────────────────────────────────────────────────────────────
-- §11  Summary bundle
-- ─────────────────────────────────────────────────────────────────────────────

/-- **multiparticle_space_well_defined** (CatAL):
    The GTE multi-particle state space is algebraically well-defined.

    Three certified structural properties:
    1. **Finite basis**: exactly 4 single-particle code words.
    2. **N-particle dimension**: 4^N basis states for N particles.
    3. **Normalized DWeight**: product DWeight = 1 on every multi-state.
    4. **Bounded mass spectrum**: total mass ≤ 3N for N particles.
    5. **Positive inner product**: basis states are orthonormal. -/
theorem multiparticle_space_well_defined (n : ℕ) :
    Fintype.card CodeWord = 4 ∧
    Fintype.card (NParticleState n) = 4^n ∧
    (∀ s : MultiBeableState, multiDWeight s = 1) ∧
    (∀ s : NParticleState n, nParticleMass s ≤ 3 * n) ∧
    (∀ a : NParticleState n, basisInnerProduct a a = 1) :=
  ⟨code_word_cardinality, n_particle_state_count n,
   multiDWeight_eq_one, nParticleMass_le, inner_product_positive_definite⟩

end GTE.Spacetime.MultiParticle
