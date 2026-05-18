import Mathlib.Data.Nat.Pairing
import Batteries.Data.Nat.Lemmas

import UgpLean.Universality.GTECompilation

/-!
# GTE State ↔ InfTape encoding (Milestone 4)

Provides a concrete injection `gte_encode : GTEState → (ℕ → Bool)` and a left inverse
`gte_decode : (ℕ → Bool) → GTEState` satisfying `gte_decode (gte_encode s) = s` for
cascade-bounded states, proved **zero sorry**.

## Encoding scheme

A `GTEState = ⟨a, b, c⟩` is encoded by:

1. **Cantor-pair**: `k = Nat.pair a (Nat.pair b c)`.
2. **TestBit digits**: `gte_encode s i = k.testBit i`.
3. **Decode**: read 128 bits via `Nat.ofBits`, then unpair twice.

The round-trip uses `Batteries.Nat.ofBits_testBit`:
`Nat.ofBits (fun i : Fin n => k.testBit i) = k % 2^n`,
combined with `Nat.unpair_pair` from Mathlib.

## Architecture note

This file provides the **round-trip half** of `gte_in_rule110_sim_ax` (zero sorry).
The simulation half remains axiomatic until Milestones 3–5 are proved
in `rule110-lean`.
-/

namespace UgpLean.Universality.GTEInfTapeEncoding

open UgpLean.Universality.GTECompilation

/-! ## Encoding and decoding -/

/-- Encode a `GTEState` as a binary tape via Cantor pairing + testBit decomposition. -/
def gte_encode (s : GTEState) : ℕ → Bool :=
  fun i => Nat.testBit (Nat.pair s.a (Nat.pair s.b s.c)) i

/-- Width sufficient for all physically-relevant GTE cascade states (128 bits). -/
def gte_cascade_encoding_width : ℕ := 128

/-- Decode a tape into a `GTEState` by reading 128 bits (`Nat.ofBits`) and unpairing twice. -/
def gte_decode (tape : ℕ → Bool) : GTEState :=
  let k  := Nat.ofBits (fun i : Fin gte_cascade_encoding_width => tape i)
  let p1 := k.unpair
  let p2 := p1.2.unpair
  ⟨p1.1, p2.1, p2.2⟩

/-! ## Cascade state bound -/

/-- Cantor pairing bound: `Nat.pair a b < (max a b + 1)^2`. -/
theorem nat_pair_lt_max_sq (a b : ℕ) : Nat.pair a b < (max a b + 1) ^ 2 :=
  Nat.pair_lt_max_add_one_sq a b

/-- For GTE cascade states with a, b, c each < 2^11, the Cantor encoding fits in 128 bits.
    All physically-relevant GTE cascade values satisfy: c = 1023 < 2^11, b ≤ 73, a ≤ 20. -/
theorem gte_pair_fits_128 (s : GTEState)
    (ha : s.a < 2 ^ 11) (hb : s.b < 2 ^ 11) (hc : s.c < 2 ^ 11) :
    Nat.pair s.a (Nat.pair s.b s.c) < 2 ^ gte_cascade_encoding_width := by
  unfold gte_cascade_encoding_width
  have hbc : Nat.pair s.b s.c < (max s.b s.c + 1) ^ 2 := nat_pair_lt_max_sq _ _
  have hbc3 : Nat.pair s.b s.c < 2 ^ 23 := by
    calc Nat.pair s.b s.c < (max s.b s.c + 1) ^ 2 := hbc
      _ ≤ (2 ^ 11) ^ 2 := by
          apply Nat.pow_le_pow_left
          exact Nat.succ_le_succ (Nat.le_of_lt_succ (Nat.max_lt.mpr ⟨hb, hc⟩))
      _ < 2 ^ 23 := by norm_num
  have habc : Nat.pair s.a (Nat.pair s.b s.c) < (max s.a (Nat.pair s.b s.c) + 1) ^ 2 :=
    nat_pair_lt_max_sq _ _
  calc Nat.pair s.a (Nat.pair s.b s.c)
      < (max s.a (Nat.pair s.b s.c) + 1) ^ 2 := habc
    _ ≤ (2 ^ 23) ^ 2 := by
        apply Nat.pow_le_pow_left
        have : max s.a (Nat.pair s.b s.c) < 2 ^ 23 := Nat.max_lt.mpr ⟨by linarith, hbc3⟩
        omega
    _ = 2 ^ 46 := by norm_num
    _ < 2 ^ 128 := by norm_num

/-! ## Round-trip (zero sorry) -/

/-- `gte_decode (gte_encode s) = s` for states where the Cantor pair fits in 128 bits.

    Proof uses `Batteries.Nat.ofBits_testBit`:
    `Nat.ofBits (fun i : Fin 128 => k.testBit i) = k % 2^128`
    and `Nat.unpair_pair` from Mathlib. -/
theorem gte_decode_encode (s : GTEState)
    (hbound : Nat.pair s.a (Nat.pair s.b s.c) < 2 ^ gte_cascade_encoding_width) :
    gte_decode (gte_encode s) = s := by
  simp only [gte_decode, gte_encode, gte_cascade_encoding_width]
  -- ofBits reads back the testBit expansion: Nat.ofBits (testBit k ·) 128 = k % 2^128
  rw [Nat.ofBits_testBit]
  -- Since k < 2^128, k % 2^128 = k
  have hb128 : Nat.pair s.a (Nat.pair s.b s.c) < 2 ^ 128 := hbound
  rw [Nat.mod_eq_of_lt hb128]
  -- Unpairing twice recovers (a, b, c)
  simp [Nat.unpair_pair]

/-- Convenience corollary for physically-bounded cascade states. -/
theorem gte_decode_encode_cascade (s : GTEState)
    (ha : s.a < 2 ^ 11) (hb : s.b < 2 ^ 11) (hc : s.c < 2 ^ 11) :
    gte_decode (gte_encode s) = s :=
  gte_decode_encode s (gte_pair_fits_128 s ha hb hc)

end UgpLean.Universality.GTEInfTapeEncoding
