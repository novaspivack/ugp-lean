import UgpLean.Universality.Rule110
import UgpLean.Universality.UWCA
import UgpLean.Universality.UWCASimulation

/-!
# UgpLean.Universality.UWCAembedsRule110 — UWCA Simulates Rule 110

UWCA simulates Rule 110 exactly on the binary sector.

## The simulation proof

The proof is in `UWCASimulation`. It establishes via a 4-pass construction
(P1 neighbor distribution, P2 minterm detection, P3 OR-accumulation, P4 commit)
that one UWCA round computes exactly one Rule 110 step at each site. Key theorems:

- `uwca_P3_eq_rule110`: after passes P1–P3, N_i = rule110Output(L, C, R)
  Proved by exhaustive case analysis over all 8 neighborhoods.
- `uwca_sweep_implements_rule110`: after one full round, C_i^new = f₁₁₀(C_{i-1}, C_i, C_{i+1})
- `uwca_sector_invariant`: the binary sector is preserved by each round
- `uwca_tile_verification`: full 8-case truth table machine-verified

## Scope

Rule 110 is **one particular finite tile program** the UWCA can execute.
Turing universality of the substrate is proved separately via the register-machine
route in `UWCARegisterUniversality.lean` — not via Rule 110 NAND completeness
or Cook (2004).

Reference: UGP Main Thm 3.1, P48 §sec:uwca
-/

namespace UgpLean.Universality

/-- **UWCA simulates Rule 110 on the binary sector** (real proof, zero sorry).

    One synchronous UWCA round (passes P1–P4) implements one Rule 110 step.

    See `UWCASimulation.uwca_sweep_implements_rule110` for the full theorem. -/
theorem uwca_simulates_rule110_real :
    ∀ (L : ℕ) [NeZero L] (tape : Tape L)
      (_h : tape.inBinarySector) (i : Fin L),
    (uwcaRound tape i).C =
      rule110Output (neighborhoodIndex
        (tape ⟨(i.val + L - 1) % L, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne L))⟩).C
        (tape i).C
        (tape ⟨(i.val + 1) % L, Nat.mod_lt _ (Nat.pos_of_ne_zero (NeZero.ne L))⟩).C) :=
  fun _L _ tape h i => uwca_sweep_implements_rule110 tape h i

/-- Legacy name: Rule 110 embeds in the UWCA binary sweep. -/
theorem uwca_simulates_rule110 : UWCA_simulates_rule110_binary :=
  fun _L _ tape h i => uwca_sweep_implements_rule110 tape h i

end UgpLean.Universality
