import UgpLean.Spacetime.LiftingTheorem
import UgpLean.Universality.CasimirB0Relation
import UgpLean.Universality.GUTStructure
import UgpLean.TE22.ScanCertificate

/-!
# N_gen = 3: Three-Mechanism CatAL Unified Certificate

`N_gen = 3` is uniquely forced by three independent CatAL-certified mechanisms.
This module provides a **single formal proof** that the logical conjunction of all
three mechanisms holds at the certified GTE constants, and a **parametric uniqueness
theorem** showing that no other positive integer is consistent with each mechanism.

## The Three Mechanisms

| # | Mechanism | Key theorem | Module |
|---|-----------|-------------|--------|
| 1 | **Orbit period (CMCA/GoE):** the three-tape CMCA has exactly three distinct D-weighted orbit types; gen₁ is a Garden-of-Eden state with orbit period 3 | `three_generations_physical` | `LiftingTheorem` |
| 2 | **Casimir / β-function:** asymptotic freedom forces `b₀ = |Z₇| = 7`; the Casimir identity `b₀ = N_fam + N_gen − 1` with `N_fam = 5` uniquely determines `N_gen = 3` | `b0_casimir_relation` | `CasimirB0Relation` |
| 3 | **PSC Layer I enumeration:** an exhaustive native-decide search over all 34,560 discretized universes certifies that every PSC-admissible universe has `N_gen = 3` | `psc_enumeration_forces_ngen_3` | `TE22.ScanCertificate` |

All three are CatAL with zero sorry.

## Uniqueness

The Casimir mechanism provides the strongest uniqueness argument: given `b₀ = 7` and
`N_fam = 5`, the equation `b₀ = N_fam + n − 1` has the **unique** positive-integer
solution `n = 3`. This follows from `omega` without any domain-specific assumptions.

The PSC mechanism provides independent uniqueness: `psc_enumeration_forces_ngen_3`
certifies (via native_decide) that **no** PSC-admissible universe has `N_gen ≠ 3`.
-/

namespace UgpLean.Universality.NgenThreeMechanismsUnified

open GTE.Lifting
open GUTStructure
open UgpLean.Universality.BetaCoefficientIdentity
open UgpLean.Universality.CasimirB0Relation
open UgpLean.TE22
-- These are needed for the types used in three_generations_physical
-- (fmdl_step5 ∈ CUP3D, fmdl_vacuum5 ∈ LawvereZone, DWeight ∈ GTE.Lifting)
open CUP3D
open UgpLean.Universality.LawvereZone

-- ════════════════════════════════════════════════════════════════
-- §1  Casimir parametric uniqueness
-- ════════════════════════════════════════════════════════════════

/-- **ngen_unique_from_casimir** (CatAL — omega):
    The unique positive integer `n` satisfying the Casimir relation
    `b₀ = N_fam + n − 1` with `b₀ = 7` (= |Z₇|) and `N_fam = 5` is `n = 3`.

    This is the arithmetic core of Mechanism 2: asymptotic freedom fixes `b₀ = 7`
    and the family count `N_fam = 5` is independently certified; together they
    determine `N_gen` uniquely.

    LEAN-CERTIFIED (omega, zero sorry). -/
theorem ngen_unique_from_casimir (n : ℕ) (hn : 1 ≤ n)
    (h_b0 : (7 : ℕ) = 5 + n - 1) : n = 3 := by omega

/-- **ngen_unique_from_casimir_structural** (CatAL — decide + omega):
    Parametric uniqueness using the GTE structural constants: if a positive
    integer `n` satisfies `Z7_order = n_fam + n − 1`, then `n = n_gen`.

    LEAN-CERTIFIED (decide + omega, zero sorry). -/
theorem ngen_unique_from_casimir_structural (n : ℕ) (hn : 1 ≤ n)
    (h : Z7_order = n_fam + n - 1) : n = n_gen := by
  have hZ7 : Z7_order = 7 := by decide
  have hNfam : n_fam = 5 := su5_dim_matches_nfam
  have hNgen : n_gen = 3 := rfl
  rw [hZ7, hNfam] at h
  rw [hNgen]
  omega

-- ════════════════════════════════════════════════════════════════
-- §2  PSC parametric uniqueness
-- ════════════════════════════════════════════════════════════════

/-- **ngen_psc_only_three** (CatAL — native_decide):
    No PSC-admissible universe description has `N_gen ≠ 3`.
    Equivalently, `N_gen = 3` is the unique generation count consistent with
    the five Layer I PSC constraints over the 34,560-universe scan.

    This is Mechanism 3 restated as a uniqueness claim.

    LEAN-CERTIFIED (native_decide via psc_enumeration_forces_ngen_3, zero sorry). -/
theorem ngen_psc_only_three :
    ∀ u : UniverseParams, isPSCAdmissible u → ngen_val u.ngen = 3 :=
  psc_enumeration_forces_ngen_3

-- ════════════════════════════════════════════════════════════════
-- §3  Three-mechanism bundle
-- ════════════════════════════════════════════════════════════════

/-- **ngen_three_mechanisms_catal_unified** (CatAL — zero sorry):

    A **single formal proof** that three independent CatAL-certified mechanisms
    simultaneously force `N_gen = 3` at the certified GTE structural constants.

    **Mechanism 1 (orbit period / CMCA / GoE):**
    There exist three distinct D-weighted non-vacuum orbit types under `fmdl_step5`,
    forming the period-3 chain gen₁ → gen₂ → gen₃ → vacuum.  The orbit period is 3.
    Source: `three_generations_physical` (LiftingTheorem.lean, CatAL).

    **Mechanism 2 (Casimir / QCD β-function):**
    The Casimir relation `Z7_order = n_fam + n_gen − 1` holds at the certified
    constants `Z7_order = 7`, `n_fam = 5`, `n_gen = 3`.  Combined with the
    parametric uniqueness theorem `ngen_unique_from_casimir_structural`, this
    establishes that `N_gen = 3` is the **unique** solution.
    Source: `b0_casimir_relation` (CasimirB0Relation.lean, CatAL).

    **Mechanism 3 (PSC Layer I enumeration):**
    Every universe passing the five Layer I PSC constraints has `N_gen = 3`.
    Exhaustive `native_decide` over all 34,560 candidates, 12 survivors.
    Source: `psc_enumeration_forces_ngen_3` (TE22/ScanCertificate.lean, CatAL).

    **Uniqueness:**
    `ngen_unique_from_casimir_structural` shows that Mechanism 2 alone forces
    `n = n_gen` for any positive `n` satisfying the Casimir relation.  Mechanism 3
    independently certifies uniqueness via exhaustive enumeration.  Both converge
    on `n_gen = 3`.

    Cert: **CatAL — all components zero sorry**.  Mechanism 4 (cosmological constant
    bracket) is CatAD and is not included in this CatAL bundle.

    LEAN-CERTIFIED (three_generations_physical + b0_casimir_relation +
    psc_enumeration_forces_ngen_3, zero sorry). -/
theorem ngen_three_mechanisms_catal_unified :
    -- Mechanism 1: three distinct D-weighted orbit types (orbit period = 3)
    (∃ g1 g2 g3 : Fin 5 → Fin 7,
        g1 ≠ g2 ∧ g2 ≠ g3 ∧ g1 ≠ g3 ∧
        fmdl_step5 g1 = g2 ∧ fmdl_step5 g2 = g3 ∧ fmdl_step5 g3 = fmdl_vacuum5 ∧
        DWeight g1 > 0 ∧ DWeight g2 > 0 ∧ DWeight g3 > 0) ∧
    -- Mechanism 2: Casimir/β-function relation at certified GTE constants
    (Z7_order = n_fam + n_gen - 1) ∧
    -- Mechanism 3: PSC Layer I enumeration forces N_gen = 3 (all survivors)
    (∀ u : UniverseParams, isPSCAdmissible u → ngen_val u.ngen = 3) :=
  ⟨three_generations_physical, b0_casimir_relation, psc_enumeration_forces_ngen_3⟩

-- ════════════════════════════════════════════════════════════════
-- §4  Uniqueness corollary
-- ════════════════════════════════════════════════════════════════

/-- **ngen_three_is_unique_catal** (CatAL — omega + decide):
    `N_gen = 3` is the unique positive integer satisfying the three CatAL mechanisms
    simultaneously:
    - Mechanism 2 uniqueness: any n with `Z7_order = n_fam + n − 1` and n ≥ 1 satisfies n = 3.
    - Mechanism 3 uniqueness: no PSC-admissible universe has n_gen ≠ 3.

    LEAN-CERTIFIED (ngen_unique_from_casimir_structural + psc_enumeration_forces_ngen_3,
    zero sorry). -/
theorem ngen_three_is_unique_catal :
    -- Casimir uniqueness: no other positive integer satisfies the Casimir relation
    (∀ n : ℕ, 1 ≤ n → Z7_order = n_fam + n - 1 → n = n_gen) ∧
    -- PSC uniqueness: no PSC-admissible universe has N_gen ≠ 3
    (∀ u : UniverseParams, isPSCAdmissible u → ngen_val u.ngen = 3) :=
  ⟨fun n hn h => ngen_unique_from_casimir_structural n hn h,
   psc_enumeration_forces_ngen_3⟩

end UgpLean.Universality.NgenThreeMechanismsUnified
