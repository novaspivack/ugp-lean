import UgpLean.Universality.Rule110
import Mathlib.Data.Fintype.Pi

/-!
# UgpLean.Universality.CUP4TotalParity — CUP-4: SM Generation Structure as Rule 110 Orbit

The total-parity morphism φ : GTE_triple → Fin 2, defined by φ(a,b,c) = (a+b+c) mod 2,
maps the three SM particle generations to a valid Rule 110 orbit on a Z₅ ring
(periodic 5-cell cellular automaton).

**CUP-4**: the binary skeleton of the GTE generational cascade IS Rule 110, lifted to
the SM particle spectrum via the total-parity projection φ.

**CUP-8** (corollary): every SM generation-3 particle has odd total parity under φ.

**CUP-9** (Z₅ symmetry): all 5 cyclic rotations of the gen-1 ring state produce valid
Rule 110 orbits, confirming the 5 families form a closed ring (not a linear chain).

Particle ordering (index):
  0 = charged_lepton (e⁻, μ, τ)
  1 = u_quark        (u, c, t)
  2 = d_quark        (d, s, b)
  3 = neutrino_RH    (νeR, νμR, ντR)
  4 = neutrino_LH    (νeL, νμL, ντL)

Boundary conditions: **periodic (ring)** — cell 4 wraps to cell 0.
Only periodic BCs produce commutativity; fixed-0 and fixed-1 BCs both fail.

Reference: total_parity morphism; boundary-condition analysis.
-/

namespace UgpLean.Universality

-- ════════════════════════════════════════════════════════════════
-- §1  Rule 110 helper and periodic-ring step function
-- ════════════════════════════════════════════════════════════════

/-- Rule 110 applied to a single (left, center, right) triple of Fin 2 bits.
    Neighbourhood index = L·4 + C·2 + R; output 1 iff index ∈ {1,2,3,5,6}. -/
private def rule110Cell (l c r : Fin 2) : Fin 2 :=
  match l.val * 4 + c.val * 2 + r.val with
  | 1 => 1  -- 001
  | 2 => 1  -- 010
  | 3 => 1  -- 011
  | 5 => 1  -- 101
  | 6 => 1  -- 110
  | _ => 0  -- 000, 100, 111

/-- One step of Rule 110 on a 5-cell ring with periodic boundary conditions.
    Uses Fin addition (modular) so cell 4 wraps to cell 0 automatically.
    Left neighbor = (i + 4) mod 5 = (i − 1) mod 5. -/
def rule110StepPeriodic (cells : Fin 5 → Fin 2) : Fin 5 → Fin 2 :=
  fun i => rule110Cell (cells (i + 4)) (cells i) (cells (i + 1))

-- ════════════════════════════════════════════════════════════════
-- §2  SM particle generation parity encodings under φ = total_parity
-- ════════════════════════════════════════════════════════════════

/-- Generation-1 total-parity bits [1,1,0,0,1]:
    e⁻ odd, u odd, d even, νR even, νL odd. -/
def smGen1 : Fin 5 → Fin 2
  | 0 => 1  -- e⁻
  | 1 => 1  -- u
  | 2 => 0  -- d
  | 3 => 0  -- νR
  | 4 => 1  -- νL

/-- Generation-2 total-parity bits [0,1,0,1,1]:
    μ even, c odd, s even, ν_μR odd, ν_μL odd. -/
def smGen2 : Fin 5 → Fin 2
  | 0 => 0  -- μ
  | 1 => 1  -- c
  | 2 => 0  -- s
  | 3 => 1  -- ν_μR
  | 4 => 1  -- ν_μL

/-- Generation-3 total-parity bits [1,1,1,1,1] — all odd parity (CUP-8):
    τ odd, t odd, b odd, ν_τR odd, ν_τL odd. -/
def smGen3 : Fin 5 → Fin 2 := fun _ => 1

-- ════════════════════════════════════════════════════════════════
-- §3  CUP-4 core theorems
-- ════════════════════════════════════════════════════════════════

/-- **CUP-4 Step 1**: one Rule 110 step on the Z₅ ring maps gen-1 to gen-2. -/
theorem cup4_gen1_to_gen2 : rule110StepPeriodic smGen1 = smGen2 := by
  funext i; fin_cases i <;> native_decide

/-- **CUP-4 Step 2**: one Rule 110 step on the Z₅ ring maps gen-2 to gen-3. -/
theorem cup4_gen2_to_gen3 : rule110StepPeriodic smGen2 = smGen3 := by
  funext i; fin_cases i <;> native_decide

/-- **CUP-8**: every SM generation-3 particle has odd total parity under φ.
    Follows immediately from smGen3 = fun _ => 1. -/
theorem cup8_gen3_all_odd : ∀ i : Fin 5, smGen3 i = 1 :=
  fun _ => rfl

/-- **CUP-4 directional orbit**: the orbit gen1 → gen2 → gen3 is strictly forward.
    After gen-3 = [1,1,1,1,1], one Rule 110 step produces [0,0,0,0,0] ≠ gen-1. -/
theorem cup4_orbit_not_cyclic : rule110StepPeriodic smGen3 ≠ smGen1 := by
  intro h
  have h0 : rule110StepPeriodic smGen3 0 = smGen1 0 := congr_fun h 0
  exact absurd h0 (by native_decide)

-- ════════════════════════════════════════════════════════════════
-- §4  CUP-9: Z₅ cyclic symmetry
-- ════════════════════════════════════════════════════════════════

/-- Cyclic rotation of a 5-cell ring by k positions.
    Uses Fin addition (modular), so rotation wraps automatically. -/
def rotate5 (cells : Fin 5 → Fin 2) (k : Fin 5) : Fin 5 → Fin 2 :=
  fun i => cells (i + k)

/-- **CUP-9 (Z₅ ring symmetry)**: all 5 cyclic rotations of smGen1 yield valid Rule 110
    orbits that map to the corresponding rotation of smGen2.
    The 5 particle families form a closed ring; there is no preferred "first" family. -/
theorem cup9_z5_symmetry (k : Fin 5) :
    rule110StepPeriodic (rotate5 smGen1 k) = rotate5 smGen2 k := by
  funext i; fin_cases i <;> fin_cases k <;> native_decide

-- ════════════════════════════════════════════════════════════════
-- §5  Summary: the full two-step CUP-4 orbit
-- ════════════════════════════════════════════════════════════════

/-- **CUP-4 orbit summary**: two consecutive Rule 110 steps on the Z₅ ring
    carry gen-1 to gen-3 via gen-2, with gen-3 the all-ones attractor. -/
theorem cup4_full_orbit :
    rule110StepPeriodic (rule110StepPeriodic smGen1) = smGen3 :=
  cup4_gen1_to_gen2 ▸ cup4_gen2_to_gen3

-- ════════════════════════════════════════════════════════════════
-- §6  Generalised elementary CA step (all 256 rules)
-- ════════════════════════════════════════════════════════════════

/-- Apply elementary CA rule `r : Fin 256` to a (left, center, right) neighbourhood.
    Bit index `idx = l·4 + c·2 + r` is extracted from `r.val` via right-shift and mod 2. -/
private def elementaryCACell (r : Fin 256) (lft ctr rgt : Fin 2) : Fin 2 :=
  ⟨(r.val >>> (lft.val * 4 + ctr.val * 2 + rgt.val)) % 2, Nat.mod_lt _ (by omega)⟩

/-- One step of an arbitrary elementary CA rule `r` on a 5-cell Z₅ ring (periodic BCs).
    This is the generalisation of `rule110StepPeriodic` to all 256 elementary CA rules. -/
def elementaryCAStep (r : Fin 256) (cells : Fin 5 → Fin 2) : Fin 5 → Fin 2 :=
  fun i => elementaryCACell r (cells (i + 4)) (cells i) (cells (i + 1))

/-- Pointwise agreement: `elementaryCACell 110` agrees with `rule110Cell` on every
    (left, center, right) triple. They use the same bit-table, just expressed differently. -/
private theorem elementaryCACell_110_eq (lft ctr rgt : Fin 2) :
    elementaryCACell 110 lft ctr rgt = rule110Cell lft ctr rgt := by
  fin_cases lft <;> fin_cases ctr <;> fin_cases rgt <;> decide

/-- `elementaryCAStep 110` agrees with `rule110StepPeriodic` for all ring states. -/
theorem elementaryCAStep_110_eq :
    elementaryCAStep 110 = rule110StepPeriodic := by
  funext cells i
  simp only [elementaryCAStep, rule110StepPeriodic]
  exact elementaryCACell_110_eq (cells (i + 4)) (cells i) (cells (i + 1))

-- ════════════════════════════════════════════════════════════════
-- §7  CUP-4 Uniqueness: Rule 110 uniquely selected among 256 rules
-- ════════════════════════════════════════════════════════════════

/-- **Valid rule set** (iff characterisation): the elementary CA rules r : Fin 256
    for which the two-step orbit smGen1 →^r smGen2 →^r smGen3 holds on the Z₅ ring
    are exactly Rules 110 and 111.

    Rules 110 and 111 differ only in their output on neighbourhood 000 (all-zero),
    which never appears in this orbit.  Every other rule fails at least one step. -/
theorem cup4_valid_rules :
    ∀ r : Fin 256,
    (elementaryCAStep r smGen1 = smGen2 ∧ elementaryCAStep r smGen2 = smGen3) ↔
    (r = 110 ∨ r = 111) := by
  native_decide

/-- There are exactly 2 elementary CA rules producing the correct two-step orbit. -/
theorem cup4_valid_rules_card :
    ((Finset.univ (α := Fin 256)).filter (fun r =>
      elementaryCAStep r smGen1 = smGen2 ∧ elementaryCAStep r smGen2 = smGen3)).card = 2 := by
  native_decide

/-- Rule 110 and Rule 111 differ only in bit 0 — how they handle neighbourhood 000:
    Rule 110 maps 000 → 0 (vacuum-transparent); Rule 111 maps 000 → 1. -/
theorem cup4_rule110_vs_111 :
    (110 : Fin 256).val % 2 = 0 ∧ (111 : Fin 256).val % 2 = 1 := by decide

/-- **CUP-4 Parity Uniqueness**: among all 256 elementary CA rules, Rule 110 is the
    *unique* rule that both
    (a) produces the correct two-step SM generation orbit smGen1 → smGen2 → smGen3, and
    (b) is **vacuum-transparent**: it maps the all-zero neighbourhood 000 → 0.

    Rule 111 satisfies (a) but not (b); it maps 000 → 1, creating output from vacuum.
    No other rule satisfies (a) at all.

    This establishes that Rule 110 is canonically and uniquely selected by the SM
    generation structure among all 256 elementary CA rules. -/
theorem cup4_parity_uniqueness :
    ∀ r : Fin 256,
    (elementaryCAStep r smGen1 = smGen2 ∧
     elementaryCAStep r smGen2 = smGen3 ∧
     r.val % 2 = 0) ↔ r = 110 := by
  native_decide

/-- Consistency corollary: Rule 110 satisfies all three conditions of parity uniqueness. -/
theorem cup4_rule110_canonical :
    elementaryCAStep 110 smGen1 = smGen2 ∧
    elementaryCAStep 110 smGen2 = smGen3 ∧
    (110 : Fin 256).val % 2 = 0 := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- §8  N_gen = 3: orbit structure gives exactly 3 non-vacuum states
-- ════════════════════════════════════════════════════════════════

/-- **gen₃ maps to vacuum**: one Rule 110 step on smGen3 = [1,1,1,1,1] produces
    the all-zeros state (vacuum). The orbit terminates; gen₃ is the final
    non-vacuum state before the absorbing vacuum.

    Computation: neighborhood (1,1,1) has index 7, and Rule 110 maps bit 7 → 0.
    Every cell therefore outputs 0. -/
theorem cup4_gen3_to_vacuum :
    rule110StepPeriodic smGen3 = (fun _ => (0 : Fin 2)) := by
  funext i; fin_cases i <;> native_decide

/-- **Three generations are pairwise distinct**: smGen1, smGen2, smGen3 are all
    different 5-cell ring states. -/
theorem cup4_three_gens_distinct :
    smGen1 ≠ smGen2 ∧ smGen2 ≠ smGen3 ∧ smGen1 ≠ smGen3 := by
  exact ⟨by native_decide, by native_decide, by native_decide⟩

/-- **CUP-4 orbit gives N_gen = 3**: The two-step Rule 110 orbit establishes exactly
    3 distinct non-vacuum states (gen₁, gen₂, gen₃) followed by the vacuum absorber.

    The chain:
    (a) gen₁ → gen₂ → gen₃  (CUP-4, two distinct forward steps)
    (b) gen₃ → vacuum        (all-ones maps to all-zeros under Rule 110)
    (c) gen₁ ≠ gen₂ ≠ gen₃  (pairwise distinct)
    Therefore: exactly 3 non-vacuum states = N_gen = 3.

    Note: in the BINARY context, gen₁ is NOT a Garden of Eden state (it has 2
    binary predecessors outside the orbit). The GoE property holds in the Z₇ fmdl
    context (see CUP3DUniqueness.fmdl_gen1_is_garden_of_eden). -/
theorem cup4_orbit_gives_three_generations :
    smGen1 ≠ smGen2 ∧ smGen2 ≠ smGen3 ∧ smGen1 ≠ smGen3 ∧
    rule110StepPeriodic smGen1 = smGen2 ∧
    rule110StepPeriodic smGen2 = smGen3 ∧
    rule110StepPeriodic smGen3 = (fun _ => (0 : Fin 2)) :=
  ⟨cup4_three_gens_distinct.1,
   cup4_three_gens_distinct.2.1,
   cup4_three_gens_distinct.2.2,
   cup4_gen1_to_gen2,
   cup4_gen2_to_gen3,
   cup4_gen3_to_vacuum⟩

-- ════════════════════════════════════════════════════════════════
-- §9  Alias: cup1_orbit_uniquely_selects_rule110
-- ════════════════════════════════════════════════════════════════

/-- **CUP-1 / Orbit uniquely selects Rule 110**: alias of cup4_parity_uniqueness.

    Among all 256 elementary binary CA rules, Rule 110 is the UNIQUE rule that
    (a) satisfies the SM orbit gen₁ → gen₂ → gen₃, AND
    (b) is vacuum-transparent: neighborhood (0,0,0) maps to 0.

    The SM orbit algebraically determines Rule 110. -/
theorem cup1_orbit_uniquely_selects_rule110 :
    ∀ r : Fin 256,
    (elementaryCAStep r smGen1 = smGen2 ∧
     elementaryCAStep r smGen2 = smGen3 ∧
     r.val % 2 = 0) ↔ r = 110 :=
  cup4_parity_uniqueness

end UgpLean.Universality
