import UgpLean.Spacetime.LiftingTheorem
import UgpLean.Universality.CookComputableBridge
import UgpLean.Universality.ChiralPairVA

namespace GTE.Universality

/-!
# Universal Simulation Theorems

Rule 110 is Turing-universal (Cook 2004). This file formalizes the chain of
consequences that follow from that established result:

1. Rule 110 can simulate any total computable `ℕ → ℕ` function (Cook 2004,
   via the Cook composition bridge already proved in `CookComputableBridge`)
2. Rule 110 can simulate any other local binary CA rule on a periodic ring
   (universality chain)
3. Rule 110 can simulate itself (self-simulation → FCA is implementable)
4. An asynchronous version of Rule 110 (AFCA substrate) exists and is
   computationally equivalent to the synchronous version

Reference:
  Cook, M. (2004). "Universality in Elementary Cellular Automata."
  Complex Systems 15(1):1–40.

## Certification status

- `rule110_turing_complete`: **theorem**, zero new axioms. Proved directly from
  `CookComputableBridge.rule110_simulates_computable` (the same Cook-composition
  route used by `PhiMDLUniversality.phimdl_turing_universal` and
  `GTEComputability.gte_embeds_in_rule110_via_computability`).
- `universal_ca_simulates_any_ca`: **axiom**, real non-vacuous content — the
  target CA's rule table `g` and its periodic-ring evolution `caRingRun L g n`
  appear directly in the conclusion. This is the CA-embedding generalization of
  Cook's theorem (an arbitrary local rule's block dynamics compiled into a Rule
  110 glider program); the general compiler is not yet formalized in Lean, only
  Cook's original TM-to-Rule-110 compiler
  (`Rule110.CookUniversalityTop.rule110_turing_universal_from_cook`).
- `fca_implementable_in_rule110`: **theorem**, zero new axioms — direct instance
  of `universal_ca_simulates_any_ca` at `g := ChiralPairVA.rule110` (true
  self-simulation, using Rule 110's own rule table, not an unrelated stand-in).
- `async_rule110_exists`: **axiom**, real non-vacuous content — asserts that
  some asynchronous update schedule's evolution equals the synchronous
  evolution `caRingRun L ChiralPairVA.rule110 n`, not a blanket `True`.
- `afca_exists`: **theorem**, zero new axioms — composes the two axioms above:
  the asynchronous evolution equals the Rule-110-embedded synchronous
  evolution.

A prior version of this module stated all five results with conclusion type
`∃ _, True` (or transitively derived from one), satisfiable by a constant
witness with zero connection to Rule 110, Cook's theorem, self-simulation, or
asynchrony; see the removed axiom/theorem bodies in version control history for
the exact prior (vacuous) statements. None of these five names are cited by any
paper in this research programme.
-/

open UgpLean.Universality.CookComputableBridge

-- ─────────────────────────────────────────────────────────────────────────────
-- §1  Rule 110 Turing completeness (proved; zero new axioms)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Rule 110 is Turing-complete: every total computable `ℕ → ℕ` function is
    simulated by some Rule 110 tape configuration after finitely many steps,
    with an explicit encode/decode pair witnessing correctness on the input.

    Direct instance of `CookComputableBridge.rule110_simulates_computable`
    (Cook composition axiom `cook_rule110_simulates_computable`, already
    disclosed in `Assumptions.md` as A6). -/
theorem rule110_turing_complete (f : ℕ → ℕ) (hf : Computable f) :
    ∃ (encode : ℕ → Rule110.InfTape) (decode : Rule110.InfTape → ℕ) (N : ℕ),
      (∀ n, decode (encode n) = n) ∧
      (∀ n, decode (Rule110.infRule110Steps N (encode n)) = f n) :=
  rule110_simulates_computable f hf

-- ─────────────────────────────────────────────────────────────────────────────
-- §2  Periodic-ring dynamics for an arbitrary local binary CA rule
-- ─────────────────────────────────────────────────────────────────────────────

/-- Global step of an arbitrary local binary CA rule `g` on a periodic ring of
    size `L + 1` (cell `i`'s neighbors are `i - 1` and `i + 1` mod `L + 1`),
    mirroring the periodic-ring pattern already used for the Z₇ generation
    orbit (`CUP3DUniqueness.fmdl_step5`). -/
def caRingStep (L : ℕ) (g : Fin 2 → Fin 2 → Fin 2 → Fin 2) (cfg : Fin (L + 1) → Fin 2) :
    Fin (L + 1) → Fin 2 :=
  fun i => g (cfg (i - 1)) (cfg i) (cfg (i + 1))

/-- `n`-step synchronous evolution of `g` on a size-`(L + 1)` periodic ring. -/
def caRingRun (L : ℕ) (g : Fin 2 → Fin 2 → Fin 2 → Fin 2) (n : ℕ) :
    (Fin (L + 1) → Fin 2) → Fin (L + 1) → Fin 2 :=
  (caRingStep L g)^[n]

-- ─────────────────────────────────────────────────────────────────────────────
-- §3  Universal CA simulation (axiom; real, non-vacuous content)
-- ─────────────────────────────────────────────────────────────────────────────

/-- **Rule 110 can simulate any other local binary CA rule** on a periodic
    ring, via a Rule 110 embedding that reproduces the target rule's `n`-step
    ring evolution `caRingRun L g n` exactly. Unlike the module's prior
    `∃ _, True` statement, `g`, `L`, and `n` all appear directly in the
    conclusion: the claim is falsifiable for any specific choice of embedding
    and step count, not satisfied by an unconstrained witness.

    Status: real, disclosed physics/CS axiom — the CA-embedding generalization
    of Cook's theorem. Not yet formalized as a theorem: doing so requires a
    general Rule-110 "compiler" for arbitrary local rules, analogous to but
    more general than the specific TM compiler in `rule110-lean`
    (`Rule110.CookUniversalityTop`). -/
axiom universal_ca_simulates_any_ca
    (g : Fin 2 → Fin 2 → Fin 2 → Fin 2) (L n : ℕ) :
    ∃ (rule110Steps : ℕ) (embed : (Fin (L + 1) → Fin 2) → Rule110.InfTape)
      (extract : Rule110.InfTape → Fin (L + 1) → Fin 2),
      ∀ cfg : Fin (L + 1) → Fin 2,
        extract (Rule110.infRule110Steps rule110Steps (embed cfg)) = caRingRun L g n cfg

-- ─────────────────────────────────────────────────────────────────────────────
-- §4  FCA self-simulation (theorem; derived, zero new axioms)
-- ─────────────────────────────────────────────────────────────────────────────

/-- The FCA (Fractal CA = Rule 110 simulating Rule 110) is implementable.

    Direct instance of `universal_ca_simulates_any_ca` at `g := ChiralPairVA.rule110`
    — Rule 110's own rule table, not an unrelated stand-in rule (a prior version
    of this theorem invoked the universality chain with an arbitrary XOR-style
    rule `fun a b c => (a + b + c) % 2` that has no connection to Rule 110, even
    though the theorem's purpose is to witness Rule 110's *self*-simulation). -/
theorem fca_implementable_in_rule110 (L n : ℕ) :
    ∃ (rule110Steps : ℕ) (embed : (Fin (L + 1) → Fin 2) → Rule110.InfTape)
      (extract : Rule110.InfTape → Fin (L + 1) → Fin 2),
      ∀ cfg : Fin (L + 1) → Fin 2,
        extract (Rule110.infRule110Steps rule110Steps (embed cfg)) =
          caRingRun L ChiralPairVA.rule110 n cfg :=
  universal_ca_simulates_any_ca ChiralPairVA.rule110 L n

-- ─────────────────────────────────────────────────────────────────────────────
-- §5  Asynchronous ring dynamics and async/sync equivalence (axiom; real content)
-- ─────────────────────────────────────────────────────────────────────────────

/-- An asynchronous update schedule: which subset of ring cells update at each
    discrete time step. -/
def UpdateSchedule (L : ℕ) := ℕ → Finset (Fin (L + 1))

/-- One asynchronous step of rule `g` under schedule `sched` at time `t`: only
    cells named by `sched t` are updated via `caRingStep`; all other cells hold
    their previous value. -/
def caRingAsyncStep (L : ℕ) (g : Fin 2 → Fin 2 → Fin 2 → Fin 2)
    (sched : UpdateSchedule L) (t : ℕ) (cfg : Fin (L + 1) → Fin 2) : Fin (L + 1) → Fin 2 :=
  fun i => if i ∈ sched t then caRingStep L g cfg i else cfg i

/-- `t`-step asynchronous evolution of `g` on a size-`(L + 1)` ring under
    schedule `sched`. -/
def caRingAsyncRun (L : ℕ) (g : Fin 2 → Fin 2 → Fin 2 → Fin 2) (sched : UpdateSchedule L) :
    ℕ → (Fin (L + 1) → Fin 2) → Fin (L + 1) → Fin 2
  | 0, cfg => cfg
  | t + 1, cfg => caRingAsyncStep L g sched t (caRingAsyncRun L g sched t cfg)

/-- **An asynchronous version of Rule 110 exists and is computationally
    equivalent to the synchronous version**, on a periodic ring: for every ring
    size `L + 1` and step count `n`, there is an asynchronous update schedule
    whose evolution, after some number of asynchronous ticks, equals the
    synchronous `n`-step ring evolution `caRingRun L ChiralPairVA.rule110 n`
    for every initial configuration. Unlike the module's prior `∃ _, True`
    statement, the async and sync evolutions are asserted *equal* as functions,
    not merely both "exist".

    Status: real, disclosed CS axiom (cf. Fatès 2014, "A guided tour of
    asynchronous cellular automata", LNCS 8155, for the general
    synchronous→asynchronous equivalence result this specializes). Not yet
    formalized as a theorem in this repository. -/
axiom async_rule110_exists (L n : ℕ) :
    ∃ (sched : UpdateSchedule L) (asyncSteps : ℕ),
      ∀ cfg : Fin (L + 1) → Fin 2,
        caRingAsyncRun L ChiralPairVA.rule110 sched asyncSteps cfg =
          caRingRun L ChiralPairVA.rule110 n cfg

-- ─────────────────────────────────────────────────────────────────────────────
-- §6  AFCA existence (theorem; derived, zero new axioms)
-- ─────────────────────────────────────────────────────────────────────────────

/-- The AFCA (Asynchronous Fractal CA) exists: composing `async_rule110_exists`
    (asynchronous Rule 110 matches synchronous Rule 110) with
    `fca_implementable_in_rule110` (synchronous Rule 110 embeds in Rule 110 via
    the universal-CA-simulation route) gives an asynchronous schedule whose
    evolution equals a Rule-110-embedded evolution for every initial
    configuration — the asynchronous implementation of the FCA hierarchy. -/
theorem afca_exists (L n : ℕ) :
    ∃ (sched : UpdateSchedule L) (asyncSteps rule110Steps : ℕ)
      (embed : (Fin (L + 1) → Fin 2) → Rule110.InfTape)
      (extract : Rule110.InfTape → Fin (L + 1) → Fin 2),
      ∀ cfg : Fin (L + 1) → Fin 2,
        caRingAsyncRun L ChiralPairVA.rule110 sched asyncSteps cfg =
          extract (Rule110.infRule110Steps rule110Steps (embed cfg)) := by
  obtain ⟨sched, asyncSteps, hasync⟩ := async_rule110_exists L n
  obtain ⟨rule110Steps, embed, extract, hsync⟩ := fca_implementable_in_rule110 L n
  exact ⟨sched, asyncSteps, rule110Steps, embed, extract,
    fun cfg => by rw [hasync, hsync]⟩

end GTE.Universality
