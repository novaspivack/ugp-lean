import UgpLean.Universality.GTECompilation
import UgpLean.Universality.GTEComputability
import UgpLean.Universality.UWCASimulation
import UgpLean.Universality.TwoLayerConfluence
import UgpLean.Universality.CookRule110Ref

/-!
# UgpLean.Universality.HypothesisB — Single Universal Substrate

Formalizes **Hypothesis B (Single Substrate)**: both the fMDL winding sector and the
GTE mass cascade sector are realized as UWCA-type programs — the UWCA tile architecture
is the single universal substrate underlying both dynamics.

## Mathematical Content

The UWCA architecture underlies two sectors of the physical theory:

1. **fMDL binary sector**: The C-bit of each UWCA site, mapped to Fin 7 via
   `boolToFin7`, gives the fMDL winding state. One tape-level UWCA round (`uwcaRound`,
   Rule 110) maps to one fMDL step. Coherence diagram:
   ```
     Tape L  --uwcaRound--> Tape L
       |                       |
     pi_fmdl               pi_fmdl    (proved, zero sorry)
       |                       |
     Fin 7   --fmdl_at---->  Fin 7
   ```

2. **GTE arithmetic sector**: The GTE update map T is realized exactly by the
   one-tile finite UWCA program `sigma_gte` (proved in GTECompilation.lean). The
   coherence is at the GTE tile architecture level:
   ```
     GTEState  --uwca_eval sigma_gte-->  GTEState
        |                                   |
       id                                  id    (proved, zero sorry)
        |                                   |
     GTEState  --gte_update_map--------> GTEState
   ```
   using `id` as the projection (GTEState is its own substrate for this sector).

## Architecture note

The fMDL sector coherence is at the *tape level* (Rule 110 UWCA on `Tape L`).
The GTE sector coherence is at the *arithmetic tile level* (`uwca_eval sigma_gte` on
`GTEState`). These are two concrete instantiations of the UWCA tile architecture.
A tape-level GTE coherence `pi_gte (uwcaRound tape) = gte_update_map (pi_gte tape)`
would additionally require embedding GTE arithmetic in Rule 110 — a full simulation
theorem that, while true in principle (Rule 110 is universal), is not formalized here.
The `pi_gte` function below is defined concretely via bit extraction to make it
available as infrastructure for that future direction.

## Status — FULLY PROVED (zero sorry)

- `pi_gte`: **DEFINED** (concrete bit extraction, zero sorry).
- `fmdl_sector_coherence`: **PROVED, zero sorry**.
- `gte_sector_coherence`: **PROVED, zero sorry** — at GTE arithmetic UWCA level,
  directly from `gte_compilation_theorem`.
- `single_substrate_coherence`: **PROVED, zero sorry**.
- `hypothesis_b_single_substrate`: **PROVED, zero sorry**.

See also: GTECompilation.lean (sigma_gte, gte_compilation_theorem, hypothesis_a_complete).
Reference: P08 §4.3; P28 §11.
-/

namespace UgpLean.Universality.HypothesisB

open UgpLean
open UgpLean.Universality
open UgpLean.Universality.TwoLayerConfluence
open UgpLean.Universality.GTECompilation
open CUP3D

-- ════════════════════════════════════════════════════════════════
-- §1 UWCA substrate and projections
-- ════════════════════════════════════════════════════════════════

/-- The UWCA substrate: a finite tape of UWCA sites.
    This is the single universal computation layer in UGP. -/
abbrev UWCASubstrate (L : ℕ) := Tape L

/-- Projection from the UWCA substrate to the fMDL binary sector at position i.
    Reads the C-bit of the site and maps it to Fin 7 (the fMDL state space).
    The C-bit is the "visible" bit that represents the physical winding number (0 or 1). -/
def pi_fmdl {L : ℕ} (tape : UWCASubstrate L) (i : Fin L) : Fin 7 :=
  boolToFin7 (tape i).C

/-- The fMDL step at position i of a UWCA tape.
    Applies fmdl to the C-bits of the left neighbor, center, and right neighbor sites.
    This is how fMDL dynamics appear when projected from the UWCA substrate. -/
def fmdl_at {L : ℕ} [NeZero L] (tape : UWCASubstrate L) (i : Fin L) : Fin 7 :=
  let hL := Nat.pos_of_ne_zero (NeZero.ne L)
  let left   := (tape ⟨(i.val + L - 1) % L, Nat.mod_lt _ hL⟩).C
  let center := (tape i).C
  let right  := (tape ⟨(i.val + 1) % L, Nat.mod_lt _ hL⟩).C
  fmdl (boolToFin7 left) (boolToFin7 center) (boolToFin7 right)

/-- Read k consecutive C-bits from a tape starting at position `start`,
    decoded as a little-endian binary natural number.
    Positions ≥ L contribute 0 (natural zero-padding for short tapes). -/
def tapeBitsToNat {L : ℕ} (tape : UWCASubstrate L) (start width : ℕ) : ℕ :=
  (List.range width).foldl (fun acc j =>
    let idx := start + j
    if h : idx < L then
      if (tape ⟨idx, h⟩).C then acc + 2 ^ j else acc
    else acc) 0

/-- Projection from the UWCA substrate to the GTE arithmetic sector.

    Decodes the tape's C-bits as three 16-bit little-endian natural numbers:
      - a-component: tape C-bits [0 .. 15]
      - b-component: tape C-bits [16 .. 31]
      - c-component: tape C-bits [32 .. 47]
    If the tape has fewer than 48 sites the missing positions contribute 0.

    This is a concrete total function — no sorry.  The GTE sector coherence
    (`gte_sector_coherence`) is proved at the GTE arithmetic UWCA level using
    `gte_compilation_theorem` (see §3).  A tape-level coherence
    `pi_gte (uwcaRound tape) = gte_update_map (pi_gte tape)` would additionally
    require embedding GTE arithmetic in Rule 110 (a full simulation theorem);
    that direction is open. -/
def pi_gte {L : ℕ} (tape : UWCASubstrate L) : GTEState :=
  ⟨tapeBitsToNat tape 0  16,
   tapeBitsToNat tape 16 16,
   tapeBitsToNat tape 32 16⟩

-- ════════════════════════════════════════════════════════════════
-- §2 fMDL sector coherence (zero sorry)
-- ════════════════════════════════════════════════════════════════

/-- **fMDL Sector Coherence** (zero sorry):
    The fMDL projection commutes with UWCA dynamics in the binary sector.

    In the binary sector (tape.inBinarySector), one UWCA round at position i
    produces the fMDL output: pi_fmdl after the round = fmdl_at before the round.

    Proof chain:
    1. `pi_fmdl (uwcaRound tape) i = boolToFin7 ((uwcaRound tape i).C)`
       (by definition of pi_fmdl)
    2. `(uwcaRound tape i).C = rule110Output (neighborhoodIndex left center right)`
       (by uwca_sweep_implements_rule110, in binary sector)
    3. `boolToFin7 (rule110Output idx) = rule110OutputFin7 left center right`
       (by definition — both are `if rule110Output idx then 1 else 0`)
    4. `rule110OutputFin7 left center right = fmdl (boolToFin7 left) (boolToFin7 center) (boolToFin7 right)`
       (by rule110_two_layer_confluence.symm)
    5. `fmdl (boolToFin7 left) (boolToFin7 center) (boolToFin7 right) = fmdl_at tape i`
       (by definition of fmdl_at)

    LEAN-CERTIFIED: zero sorry, zero custom axioms. -/
theorem fmdl_sector_coherence {L : ℕ} [NeZero L]
    (tape : UWCASubstrate L) (h : tape.inBinarySector) (i : Fin L) :
    pi_fmdl (uwcaRound tape) i = fmdl_at tape i := by
  simp only [pi_fmdl, fmdl_at]
  -- Step 2: use UWCA simulation to replace (uwcaRound tape i).C with rule110Output
  rw [uwca_sweep_implements_rule110 tape h i]
  -- Step 3+4: boolToFin7 (rule110Output idx) = rule110OutputFin7 l c r = fmdl ...
  -- Both steps follow by definitional equality + rule110_two_layer_confluence.symm
  exact (rule110_two_layer_confluence _ _ _).symm

/-- Corollary: in the binary sector, one UWCA round is the fMDL step at every site. -/
theorem fmdl_substrate_coherence_all {L : ℕ} [NeZero L]
    (tape : UWCASubstrate L) (h : tape.inBinarySector) :
    ∀ i, pi_fmdl (uwcaRound tape) i = fmdl_at tape i :=
  fun i => fmdl_sector_coherence tape h i

-- ════════════════════════════════════════════════════════════════
-- §3 GTE sector coherence (zero sorry — arithmetic UWCA level)
-- ════════════════════════════════════════════════════════════════

/-- **GTE Sector Coherence** (zero sorry, arithmetic UWCA level).

    At the GTE tile architecture level, the finite tile evaluator `uwca_eval sigma_gte`
    is exactly the GTE update map: the identity projection commutes with both.

    The commutative diagram:
      GTEState  --uwca_eval sigma_gte-->  GTEState
         |                                   |
        id                                  id
         |                                   |
      GTEState  --gte_update_map-------->  GTEState

    This is an immediate consequence of `gte_compilation_theorem`
    (GTECompilation.lean, zero sorry): `∀ s, uwca_eval sigma_gte s = gte_update_map s`.

    **Architecture note.** The tape-level version
      `pi_gte (uwcaRound tape) = gte_update_map (pi_gte tape)`
    would require embedding GTE arithmetic in Rule 110 — a full simulation argument
    (Rule 110 universality applied to GTE arithmetic).  That is a deeper theorem not
    formalized here; it is left as an open direction.  The present arithmetic-level
    coherence is the certified content of Hypothesis B's GTE side.

    LEAN-CERTIFIED: zero sorry, zero custom axioms. -/
theorem gte_sector_coherence (s : GTEState) :
    uwca_eval sigma_gte s = gte_update_map s :=
  gte_compilation_theorem s

-- ════════════════════════════════════════════════════════════════
-- §4 Single substrate coherence and Hypothesis B (zero sorry)
-- ════════════════════════════════════════════════════════════════

/-- **Hypothesis B — Single Universal Substrate Coherence** (zero sorry).

    Both the fMDL winding sector and the GTE arithmetic sector are realized as
    UWCA-type programs — two concrete instantiations of the UWCA tile architecture:

    **fMDL sector (tape level):**
    `pi_fmdl (uwcaRound tape) i = fmdl_at tape i`
    The boolean tape UWCA (`uwcaRound`, Rule 110) with the C-bit projection `pi_fmdl`
    implements fMDL dynamics at every site in the binary sector.
    LEAN-CERTIFIED: zero sorry, zero custom axioms.

    **GTE sector (arithmetic tile level):**
    `uwca_eval sigma_gte s = gte_update_map s`
    The GTE tile program `sigma_gte` (1 tile) with identity projection implements
    the GTE arithmetic update map exactly.
    LEAN-CERTIFIED: zero sorry, zero custom axioms.

    Together these certify Hypothesis B: the UWCA tile architecture is the single
    computational substrate underlying both UGP dynamical sectors.

    See: hypothesis_a_complete (GTECompilation.lean) for the companion four-component
    Hypothesis A. -/
theorem single_substrate_coherence :
    -- fMDL sector: tape-level coherence (proved, zero sorry)
    (∀ {L : ℕ} [NeZero L] (tape : UWCASubstrate L) (_ : tape.inBinarySector) (i : Fin L),
     pi_fmdl (uwcaRound tape) i = fmdl_at tape i) ∧
    -- GTE sector: arithmetic-level coherence (proved, zero sorry)
    (∀ s : GTEState, uwca_eval sigma_gte s = gte_update_map s) :=
  ⟨fun tape h i => fmdl_sector_coherence tape h i, gte_sector_coherence⟩

/-- **Hypothesis B — Single Universal Substrate** (existential form, zero sorry).

    There exist projections from UWCA substrates to the two physical sectors such that
    both dynamics cohere:
    - A tape-level UWCA projection for fMDL (the `pi_fmdl` function)
    - An arithmetic tile-level UWCA projection for GTE (the identity on `GTEState`)

    Both coherence relations hold with zero sorry, zero custom axioms.

    LEAN-CERTIFIED: zero sorry, zero custom axioms. -/
theorem hypothesis_b_single_substrate :
    (∃ (project_fmdl : ∀ {L : ℕ}, UWCASubstrate L → Fin L → Fin 7),
      ∀ {L : ℕ} [NeZero L] (tape : UWCASubstrate L) (_ : tape.inBinarySector) (i : Fin L),
        project_fmdl tape i = pi_fmdl tape i ∧
        project_fmdl (uwcaRound tape) i = fmdl_at tape i) ∧
    (∃ (project_gte : GTEState → GTEState),
      ∀ s : GTEState,
        project_gte s = s ∧
        project_gte (uwca_eval sigma_gte s) = gte_update_map (project_gte s)) :=
  ⟨⟨@pi_fmdl, fun tape h i => ⟨rfl, fmdl_sector_coherence tape h i⟩⟩,
   ⟨id,        fun s        => ⟨rfl, gte_compilation_theorem s⟩⟩⟩

-- ════════════════════════════════════════════════════════════════
-- §5 Multi-step tape iteration and infinite tape infrastructure
-- ════════════════════════════════════════════════════════════════

/-- N-step iteration of the UWCA round (Rule 110) on a finite tape.
    `rule110_n_steps n tape` applies `uwcaRound` exactly n times. -/
def rule110_n_steps {L : ℕ} [NeZero L] : ℕ → Tape L → Tape L
  | 0,     tape => tape
  | n + 1, tape => rule110_n_steps n (uwcaRound tape)

/-!
### Why an infinite tape for the GTE embedding

For the tape-level GTE theorem, we need `encode : GTEState → Tape` and
`decode : Tape → GTEState` such that `decode ∘ encode = id` on **all** GTEStates.

`GTEState = Triple` has components `a b c : ℕ` — a countably infinite domain.
Any finite tape `Tape L = Fin L → UWCASite` has exactly `|UWCASite|^L` elements
(finite for finite L). Since `|GTEState| = ℵ₀ > |Tape L|` for any fixed L, no
injection `GTEState → Tape L` exists, and `decode ∘ encode = id` cannot hold for
all GTEStates on a fixed-length finite tape.

The resolution: use `InfTape = ℕ → Bool`, a one-sided infinite boolean tape.
`|InfTape| = 2^ℵ₀ > ℵ₀ = |GTEState|`, so injections exist (set-theoretically).
The infinite tape is also the natural substrate for Cook (2004)'s universality proof:
Rule 110 on an infinite tape simulates any Turing machine.
-/

/-- A one-sided infinite boolean tape: a function `ℕ → Bool`.
    This is the natural substrate for Turing-machine simulations and Cook (2004)'s
    Rule 110 universality. Its cardinality `2^ℵ₀` exceeds `|GTEState| = ℵ₀`, so
    injective encodings of GTEState into InfTape exist. -/
def InfTape := ℕ → Bool

/-- One Rule 110 step on an infinite one-sided tape.
    Site 0 uses a vacuum (false) left boundary; all other sites use their true neighbor.
    This matches the standard one-sided-infinite Rule 110 model. -/
def infTapeStep (tape : InfTape) : InfTape :=
  fun i =>
    let left   := if i = 0 then false else tape (i - 1)
    let center := tape i
    let right  := tape (i + 1)
    rule110Output (neighborhoodIndex left center right)

/-- N Rule 110 steps on an infinite tape. -/
def infRule110Steps : ℕ → InfTape → InfTape
  | 0,     tape => tape
  | n + 1, tape => infRule110Steps n (infTapeStep tape)

-- ════════════════════════════════════════════════════════════════
-- §6 GTE tape-level embedding: axiom and theorem
-- ════════════════════════════════════════════════════════════════

/-!
### Tape-Level GTE Simulation Theorem

`gte_embeds_in_rule110` is now derived from two explicit, named components:

1. **`GTEComputability.gte_update_map_nat_computable`** (zero sorry):
   `gte_update_map_nat : ℕ → ℕ` (the Cantor-encoding of `gte_update_map`) is primitive
   recursive, hence computable. Proved via `Primrec.nat_mod`, `Primrec.nat_div`,
   `Primrec.nat_sub`, `Primrec.nat_add`, `Primrec₂.natPair`, `Primrec.unpair`.

2. **`GTEComputability.rule110_simulates_computable`** (named axiom):
   Any total computable ℕ → ℕ function embeds in Rule 110. This is Cook (2004)'s
   Turing universality theorem at the tape level. The formalization gap is
   SPEC_069_C1R Milestones 3–5 in `rule110-lean`.

The old `gte_in_rule110_sim_ax` is **removed**. `#print axioms gte_embeds_in_rule110`
now lists only `GTEComputability.rule110_simulates_computable` (plus Lean universe axioms).

Note: the tape type is `Rule110.InfTape = ℕ → Bool`, which is definitionally the same
as `InfTape = ℕ → Bool` in this file. The coercion below is trivial.
-/

/-- Both `rule110Output` definitions agree on all 8 neighborhoods. -/
private theorem rule110Output_eq (i : Fin 8) :
    rule110Output i = Rule110.rule110Output i := by
  fin_cases i <;> rfl

/-- Both `neighborhoodIndex` definitions agree for all Bool triples. -/
private theorem neighborhoodIndex_eq (l c r : Bool) :
    neighborhoodIndex l c r = Rule110.neighborhoodIndex l c r := by
  rcases l <;> rcases c <;> rcases r <;> rfl

/-- The two `infTapeStep` definitions agree pointwise. -/
private theorem infTapeStep_eq (tape : InfTape) (i : ℕ) :
    infTapeStep tape i = Rule110.infTapeStep tape i := by
  simp only [infTapeStep, Rule110.infTapeStep]
  rw [rule110Output_eq, neighborhoodIndex_eq]

/-- The local `infRule110Steps` equals `Rule110.infRule110Steps` (zero sorry). -/
theorem infRule110Steps_eq_Rule110 (n : ℕ) (tape : InfTape) :
    infRule110Steps n tape = Rule110.infRule110Steps n tape := by
  induction n generalizing tape with
  | zero => rfl
  | succ n ih =>
    simp only [infRule110Steps, Rule110.infRule110Steps_succ]
    rw [← ih]
    congr 1
    funext i
    exact infTapeStep_eq tape i

open GTEComputability in
/-- **GTE Embeds in Rule 110** (tape-level unification).

    Derived from two honest, named components:
    - `gte_update_map_nat_computable` (zero sorry): GTE arithmetic is computable.
    - `rule110_simulates_computable` (named axiom): Cook (2004) — Rule 110 simulates
      any computable function.

    The old `gte_in_rule110_sim_ax` is **removed**. `#print axioms gte_embeds_in_rule110`
    now shows only `rule110_simulates_computable`. -/
theorem gte_embeds_in_rule110 :
    ∃ (encode : GTEState → InfTape)
      (decode : InfTape → GTEState)
      (N : ℕ),
      (∀ s, decode (encode s) = s) ∧
      (∀ s, decode (infRule110Steps N (encode s)) = gte_update_map s) := by
  obtain ⟨enc, dec, N, hrt, hsim⟩ :=
    gte_embeds_in_rule110_via_computability
  exact ⟨enc, dec, N, hrt,
         fun s => by rw [infRule110Steps_eq_Rule110]; exact hsim s⟩

-- ════════════════════════════════════════════════════════════════
-- §7 Hypothesis B — Tape-Level Unification (zero sorry)
-- ════════════════════════════════════════════════════════════════

/-- **Hypothesis B — Tape-Level Unification** (zero sorry, one explicit axiom).

    A single Rule 110 tape simultaneously realizes **both** UGP dynamical sectors:

    **fMDL sector** (finite tape, `pi_fmdl` projection):
      One UWCA round (Rule 110 step on `Tape L`) computes the fMDL charge update at
      every site in the binary sector. The projection `pi_fmdl` reads the C-bit.
      Source: `fmdl_sector_coherence` — proved zero sorry, zero axioms.

    **GTE sector** (infinite tape, `InfTape` encoding):
      N Rule 110 steps on the encoded GTE state produce the next GTE state. The encoding
      maps GTEState into `InfTape = ℕ → Bool` with a faithful round-trip.
      Source: `gte_embeds_in_rule110` — proved zero sorry, one axiom (gte_in_rule110_sim_ax).

    Together: the Rule 110 Boolean tape is the **single universal computational substrate** —
    it simultaneously computes the SM charge sector (fMDL winding, finite tape) and the mass
    cascade sector (GTE arithmetic, infinite tape). This is the tape-level completion of
    Hypothesis B: both UGP sectors reduce to one Rule 110 computation.

    **Note on tape types**: The fMDL sector uses finite `Tape L` (natural for a periodic
    lattice of L sites); the GTE sector uses `InfTape` (natural for Turing simulation).
    Both are concretely-typed instantiations of the Boolean Rule 110 CA.

    **Status**: zero sorry. One explicit named axiom (`gte_in_rule110_sim_ax`) stands in
    for Cook (2004)'s tape encoding formalization — the same gap as §3a. -/
theorem hypothesis_b_tape_level :
    -- fMDL sector: finite tape coherence (zero sorry, zero axioms)
    (∀ {L : ℕ} [NeZero L] (tape : UWCASubstrate L) (_ : tape.inBinarySector) (i : Fin L),
      pi_fmdl (uwcaRound tape) i = fmdl_at tape i) ∧
    -- GTE sector: infinite tape simulation (zero sorry, one axiom)
    (∃ (encode : GTEState → InfTape)
       (decode : InfTape → GTEState)
       (N : ℕ),
       (∀ s, decode (encode s) = s) ∧
       (∀ s, decode (infRule110Steps N (encode s)) = gte_update_map s)) :=
  ⟨fun tape h i => fmdl_sector_coherence tape h i, gte_embeds_in_rule110⟩

end UgpLean.Universality.HypothesisB
