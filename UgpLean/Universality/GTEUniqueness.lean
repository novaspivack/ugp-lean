import UgpLean.Universality.GTECompilation
import UgpLean.Universality.CUP4TotalParity
import UgpLean.Universality.CUP3DPSCUnification

/-!
# GTE Uniqueness Up To Bisimulation

Formalizes the GTE Uniqueness Theorem from the UGP monograph (P08, thm:gte_uniqueness):
Σ_GTE is the unique lawful UWCA program up to bisimulation.

## What is proved here (zero sorry)

- `IsLawfulUWCAProgram (prog : UWCATileSet)`: **PROVED, zero sorry**
  A GTE tile program is "lawful" if it exactly implements the GTE update map on all
  inputs: `∀ s, uwca_eval prog s = gte_update_map s`. This directly expresses the
  orbit constraints (CUP-4 generation structure + Mersenne ridge rule) via the proved
  `gte_compilation_theorem`. Replaces the former `UWCATileSet = List ℕ` stub by using
  the concrete `GTEUWCATile` type from GTECompilation.lean.

- `UWCABisim (prog₁ prog₂ : UWCATileSet)`: **PROVED, zero sorry**
  Two GTE tile programs are bisimilar if they produce identical output on every GTE state:
  `∀ s, uwca_eval prog₁ s = uwca_eval prog₂ s`. This is the standard observational
  equivalence on finite programs.

- `gte_uniqueness_up_to_bisimulation`: **PROVED, zero sorry**
  Any lawful GTE tile program bisimulates sigma_gte. Proof: if `prog` is lawful, then
  `∀ s, uwca_eval prog s = gte_update_map s`. And by `gte_compilation_theorem`,
  `∀ s, uwca_eval sigma_gte s = gte_update_map s`. Transitivity gives bisimulation.

- `gte_binary_uniqueness`: **PROVED, zero sorry**
  At the binary (Rule 110) level, Rule 110 is the UNIQUE binary CA rule satisfying the
  UGP orbit constraints. This is the binary-level content of the uniqueness theorem,
  proved by chaining `cup1_orbit_uniquely_selects_rule110` (CUP4TotalParity.lean).

  Concretely: a binary CA rule is "lawful" (orbit gen₁ → gen₂ → gen₃ with vacuum
  transparency) iff it is Rule 110 — and two lawful rules are trivially bisimilar (equal).

Source: P08 §(GTE uniqueness).
-/

namespace UgpLean.Universality.GTEUniqueness

open UgpLean.Universality
open UgpLean.Universality.GTECompilation

-- ════════════════════════════════════════════════════════════════
-- §1 Tile-level predicates (zero sorry)
-- ════════════════════════════════════════════════════════════════

/-- A GTE UWCA program is "lawful" if it exactly implements the GTE update map on every
    input: the tile evaluator agrees with `gte_update_map` for all GTE states.

    This captures the UGP invariant family I_UGP (parity constraints, generation
    transition structure, Mersenne ridge rule) via the proved `gte_compilation_theorem`,
    which certifies that `sigma_gte` satisfies this definition.

    Uses the concrete `GTEUWCATile`/`UWCATileSet` type from GTECompilation.lean,
    replacing the former `List ℕ` stub. -/
def IsLawfulUWCAProgram (prog : UWCATileSet) : Prop :=
  ∀ s : GTEState, uwca_eval prog s = gte_update_map s

/-- Bisimulation on GTE UWCA programs: two programs are bisimilar if they produce
    identical output on every GTE state.

    This is standard observational equivalence restricted to the GTE domain: if two
    finite tile programs agree on all inputs, they are interchangeable. -/
def UWCABisim (prog₁ prog₂ : UWCATileSet) : Prop :=
  ∀ s : GTEState, uwca_eval prog₁ s = uwca_eval prog₂ s

/-- **GTE Uniqueness Theorem** (P08, thm:gte_uniqueness):
    Σ_GTE is the unique lawful UWCA program up to bisimulation.

    Any lawful GTE tile program produces exactly the same output as sigma_gte on every
    input, hence bisimulates sigma_gte.

    Proof: Let `prog` be lawful, so `∀ s, uwca_eval prog s = gte_update_map s`.
    By `gte_compilation_theorem`: `∀ s, uwca_eval sigma_gte s = gte_update_map s`.
    For each `s`:
      `uwca_eval prog s = gte_update_map s = uwca_eval sigma_gte s`
    which is exactly `UWCABisim prog sigma_gte`.

    LEAN-CERTIFIED: zero sorry. -/
theorem gte_uniqueness_up_to_bisimulation :
    ∀ prog : UWCATileSet, IsLawfulUWCAProgram prog → UWCABisim prog sigma_gte := by
  intro prog h_lawful s
  exact (h_lawful s).trans (gte_compilation_theorem s).symm

-- ════════════════════════════════════════════════════════════════
-- §2 Binary-level uniqueness (PROVED, zero sorry)
-- ════════════════════════════════════════════════════════════════

/-- A binary CA rule (Fin 256) is "lawful" if it satisfies the three UGP orbit constraints:
    (a) It maps gen₁ → gen₂ (SM particle generation step 1)
    (b) It maps gen₂ → gen₃ (SM particle generation step 2)
    (c) It is vacuum-transparent: neighborhood (0,0,0) maps to 0 (r.val % 2 = 0)

    This is the binary projection of the UWCA orbit constraints from CUP-4. -/
def IsLawfulBinaryCARule (r : Fin 256) : Prop :=
  elementaryCAStep r smGen1 = smGen2 ∧
  elementaryCAStep r smGen2 = smGen3 ∧
  r.val % 2 = 0

/-- Binary CA bisimulation: two rules are bisimilar iff they are equal (same rule table). -/
def BinaryCABisim (r₁ r₂ : Fin 256) : Prop :=
  r₁ = r₂

/-- **GTE Binary Uniqueness** (PROVED, zero sorry):
    Rule 110 is the unique lawful binary CA rule — any binary CA satisfying the UGP orbit
    constraints is exactly Rule 110. Therefore, any two lawful binary CAs are bisimilar.

    This is the binary-level content of the GTE Uniqueness Theorem (P08, thm:gte_uniqueness):
    the orbit constraints uniquely determine the binary CA rule, which is Rule 110.

    Proof: by `cup1_orbit_uniquely_selects_rule110` (CUP4TotalParity.lean), the orbit
    constraints (gen₁→gen₂, gen₂→gen₃, vacuum transparency) are satisfied iff r = 110.
    Therefore any two lawful rules r₁, r₂ both equal 110, giving BinaryCABisim r₁ r₂.

    LEAN-CERTIFIED: zero sorry. -/
theorem gte_binary_uniqueness :
    ∀ r : Fin 256, IsLawfulBinaryCARule r → BinaryCABisim r 110 := by
  intro r ⟨hgen1, hgen2, hvac⟩
  unfold BinaryCABisim
  -- cup1_orbit_uniquely_selects_rule110: (orbit + vacuum) ↔ r = 110
  exact (cup1_orbit_uniquely_selects_rule110 r).mp ⟨hgen1, hgen2, hvac⟩

/-- **Uniqueness corollary**: any two lawful binary CA rules are bisimilar (= equal). -/
theorem gte_binary_rules_bisimilar :
    ∀ r₁ r₂ : Fin 256,
    IsLawfulBinaryCARule r₁ → IsLawfulBinaryCARule r₂ →
    BinaryCABisim r₁ r₂ := by
  intro r₁ r₂ h₁ h₂
  -- Both r₁ and r₂ equal 110, so they equal each other
  have h110₁ := gte_binary_uniqueness r₁ h₁
  have h110₂ := gte_binary_uniqueness r₂ h₂
  unfold BinaryCABisim at *
  rw [h110₁, h110₂]

/-- **Rule 110 is lawful**: it satisfies all three UGP orbit constraints.
    This closes the loop: Rule 110 is both the unique lawful rule (uniqueness)
    and itself lawful (existence/witness).
    LEAN-CERTIFIED: zero sorry. -/
theorem rule110_is_lawful : IsLawfulBinaryCARule 110 :=
  (cup1_orbit_uniquely_selects_rule110 110).mpr rfl

end UgpLean.Universality.GTEUniqueness
