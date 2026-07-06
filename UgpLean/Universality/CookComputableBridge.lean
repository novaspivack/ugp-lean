import Mathlib.Computability.Partrec

import Rule110
import Rule110.CookUniversalityTop

/-!
# Cook Rule 110 → computable-function bridge

Connects the **proved** operational Cook universality theorem in `rule110-lean` to the
`Computable (ℕ → ℕ)` simulation interface used by `GTEComputability` and `PhiMDLUniversality`.

## What is proved in `rule110-lean` (zero sorry, five classical bridge axioms)

`Rule110.CookUniversalityTop.rule110_turing_universal_from_cook`: every compiled TM microstep is
matched by a CTS trace whose Rule 110 evolution satisfies C3′′ origin readback.

## Named axiom (composition + forward-cone decode)

`cook_rule110_simulates_computable` packages the classical composition of Cook operational
universality with universal TM / partial-recursive compilation (Mathlib `PartrecToTM2`;
FinTM2→CTS compilation open in `rule110-lean`).

The decode witness satisfies **forward light-cone invariance**: its value depends only on tape
cells at indices `j ≥ N` after `N` Rule 110 steps.  This matches Cook output-region placement
and composes with the proved Φ_MDL ↔ Rule 110 forward-cone agreement
(`PhiMDLUniversality.phimdl_inftape_agrees_at_forward_cone`).
-/

namespace UgpLean.Universality.CookComputableBridge

/-- Re-export of Cook's operational universality top theorem. -/
def cook_tm_operational_universality := Rule110.rule110_turing_universal_from_cook

/-- **Named axiom (Cook composition + forward-cone decode).**

    Every total computable `ℕ → ℕ` function is simulated on Rule 110 `InfTape` after `N` steps,
    with a decode map whose value depends only on cells at indices `j ≥ N`.

    **Proved component:** `cook_tm_operational_universality`
    (`Rule110.CookUniversalityTop.rule110_turing_universal_from_cook`).

    **Open composition gap:** FinTM2 compilation of partial-recursive programs and explicit
    output-region extraction (Milestones in `rule110-lean` / Mathlib `PartrecToTM2` chain).

    **Forward-cone clause:** Cook encodings place output in the forward light cone; the ℤ/ℕ
    tape equivalence (`z7kg_nat_int_tape_equivalence`) holds at indices `j ≥ N`. -/
axiom cook_rule110_simulates_computable (f : ℕ → ℕ) (hf : Computable f) :
    ∃ (encode : ℕ → Rule110.InfTape)
      (decode : Rule110.InfTape → ℕ)
      (N : ℕ),
      (∀ n, decode (encode n) = n) ∧
      (∀ n, decode (Rule110.infRule110Steps N (encode n)) = f n) ∧
      (∀ (n : ℕ) (t1 t2 : Rule110.InfTape),
        (∀ j, N ≤ j → t1 j = t2 j) → decode t1 = decode t2)

/-- Rule 110 simulates every total computable `ℕ → ℕ` function (Cook composition axiom). -/
theorem rule110_simulates_computable (f : ℕ → ℕ) (hf : Computable f) :
    ∃ (encode : ℕ → Rule110.InfTape)
      (decode : Rule110.InfTape → ℕ)
      (N : ℕ),
      (∀ n, decode (encode n) = n) ∧
      (∀ n, decode (Rule110.infRule110Steps N (encode n)) = f n) := by
  obtain ⟨encode, decode, N, hrt, hsim, _⟩ := cook_rule110_simulates_computable f hf
  exact ⟨encode, decode, N, hrt, hsim⟩

end UgpLean.Universality.CookComputableBridge
