import UgpLean.Universality.UWCASimulation
import UgpLean.Universality.RegisterMachine

/-!
# UWCA P1–P4 sweep bridge for register operations

Connects the **real** UWCA sweep (`uwcaRound` = P1 ∘ P2 ∘ P3 ∘ P4 on `UWCASite` / `Tape L`)
to Rule 110 dynamics on the visible C-bits.

## Proved here (zero sorry)

- `uwcaApplyRounds` — iterate `uwcaRound`
- `uwca_rounds_preserve_binary_sector` — binary sector invariant under any number of rounds
- `uwca_rounds_C_eq_ringRule110` — `k` UWCA rounds on C-bits equal `k` Rule 110 steps on a periodic ring
- `uwca_one_round_site_output` — one-round C-bit update at a site

## Scope note (Gap 2)

Static binary INC/DEC/JZ on a periodic finite tape without Cook gliders does **not** admit a
uniform bounded sweep macro for all register values — Rule 110 activity propagates into vacuum
padding.  Substrate Turing universality is certified at the semantic CRT register-file level
(`UWCARegisterUniversality`) and via Cook's Rule 110 pipeline (`CookComputableBridge`).
Each `uwcaRound` is one honest P1–P4 sweep implementing Rule 110 on C-bits
(`uwca_sweep_implements_rule110`).
-/

namespace UgpLean.Universality

/-- Apply `k` synchronous UWCA rounds (P1–P4) to a finite tape. -/
def uwcaApplyRounds {L : ℕ} [NeZero L] : ℕ → Tape L → Tape L
  | 0, tape => tape
  | k + 1, tape => uwcaApplyRounds k (uwcaRound tape)

theorem uwcaApplyRounds_zero {L : ℕ} [NeZero L] (tape : Tape L) :
    uwcaApplyRounds 0 tape = tape := rfl

theorem uwcaApplyRounds_succ {L : ℕ} [NeZero L] (k : ℕ) (tape : Tape L) :
    uwcaApplyRounds (k + 1) tape = uwcaApplyRounds k (uwcaRound tape) := rfl

/-- Binary sector is preserved under any number of UWCA rounds. -/
theorem uwca_rounds_preserve_binary_sector {L : ℕ} [NeZero L]
    (tape : Tape L) (h : tape.inBinarySector) (k : ℕ) :
    (uwcaApplyRounds k tape).inBinarySector := by
  induction k generalizing tape with
  | zero => exact h
  | succ k ih =>
    simpa [uwcaApplyRounds_succ] using ih (uwcaRound tape) (uwca_sector_invariant tape h)

/-- One Rule 110 step on a periodic ring of length `L`. -/
def ringRule110Step {L : ℕ} [NeZero L] (cells : Fin L → Bool) : Fin L → Bool :=
  fun i =>
    let hL : 0 < L := Nat.pos_of_ne_zero (NeZero.ne L)
    rule110Output (neighborhoodIndex
      (cells ⟨(i.val + L - 1) % L, Nat.mod_lt _ hL⟩)
      (cells i)
      (cells ⟨(i.val + 1) % L, Nat.mod_lt _ hL⟩))

/-- Iterating `ringRule110Step` commutes with one extra step on the left. -/
theorem ringRule110Step_iterate_commute {L : ℕ} [NeZero L] (k : ℕ) (cells : Fin L → Bool) :
    ringRule110Step^[k] (ringRule110Step cells) =
      ringRule110Step (ringRule110Step^[k] cells) := by
  induction k with
  | zero => simp
  | succ k ih =>
    simp only [Function.iterate_succ', Function.comp]
    rw [ih]

/-- After `k` UWCA rounds on a binary-sector tape, the C-row equals `k` ring Rule 110 steps
    on the initial C-row (zero sorry). -/
theorem uwca_rounds_C_eq_ringRule110_on_tape {L : ℕ} [NeZero L] (tape : Tape L)
    (h : tape.inBinarySector) (k : ℕ) :
    tapeCRow (uwcaApplyRounds k tape) = ringRule110Step^[k] (tapeCRow tape) := by
  induction k generalizing tape with
  | zero =>
    funext i
    simp [uwcaApplyRounds, tapeCRow]
  | succ k ih =>
    have hih := ih (uwcaRound tape) (uwca_sector_invariant tape h)
    have hrow : tapeCRow (uwcaRound tape) = ringRule110Step (tapeCRow tape) := by
      funext j
      simpa [tapeCRow] using uwca_sweep_implements_rule110 tape h j
    calc tapeCRow (uwcaApplyRounds (k + 1) tape)
        = tapeCRow (uwcaApplyRounds k (uwcaRound tape)) := by simp [uwcaApplyRounds_succ]
      _ = ringRule110Step^[k] (tapeCRow (uwcaRound tape)) := hih
      _ = ringRule110Step^[k + 1] (tapeCRow tape) := by
          simp [Function.iterate_succ', Function.comp, hrow, ringRule110Step_iterate_commute]

/-- After `k` UWCA rounds starting from C-bits only, the C-row equals `k` ring Rule 110
    steps on the initial C-bits (zero sorry). -/
theorem uwca_rounds_C_eq_ringRule110 {L : ℕ} [NeZero L] (cells : Fin L → Bool) (k : ℕ) :
    tapeCRow (uwcaApplyRounds k (initTape cells)) = ringRule110Step^[k] cells := by
  simpa [tapeCRow, initTape] using
    uwca_rounds_C_eq_ringRule110_on_tape (initTape cells) (initTape_inBinarySector cells) k

/-- **One-round UWCA output at a site** matches Rule 110 on the old C-neighborhood (zero sorry). -/
theorem uwca_one_round_site_output {L : ℕ} [NeZero L] (cells : Fin L → Bool) (i : Fin L) :
    (uwcaRound (initTape cells) i).C = ringRule110Step cells i := by
  have h := uwca_rounds_C_eq_ringRule110 cells 1
  simpa [uwcaApplyRounds, tapeCRow, initTape] using congrFun h i

end UgpLean.Universality
