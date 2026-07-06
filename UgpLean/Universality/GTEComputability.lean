import Mathlib.Computability.Primrec.Basic
import Mathlib.Data.Nat.Pairing

import Rule110

import UgpLean.Universality.CookComputableBridge
import UgpLean.Universality.GTECompilation
import UgpLean.Universality.GTEInfTapeEncoding

/-!
# GTE update map is computable (Milestone 4 — Strategy C)

Proves `Computable gte_update_map_nat`, the ℕ → ℕ encoding of `gte_update_map`.
Together with `CookComputableBridge.cook_rule110_simulates_computable` this replaces the opaque
bridge axiom `gte_in_rule110_sim_ax` with a cleaner decomposition:

    gte_update_map_nat is computable  (proved here, zero sorry)
    +
    any computable ℕ → ℕ function embeds in Rule 110  (Cook composition axiom)
    ⟹  gte_embeds_in_rule110  (Cook-dependent path)

## Two computability routes for GTE

### Cook-dependent path (this file)
`gte_embeds_in_rule110_via_computability` derives the Rule 110 embedding via
`CookComputableBridge.cook_rule110_simulates_computable`, which packages Cook (2004)'s
operational universality (`rule110_turing_universal_from_cook` in `rule110-lean`, zero sorry
modulo five classical bridge axioms) composed with universal TM compilation.

### Φ_MDL path (PhiMDLUniversality)
`phimdl_turing_universal` derives Φ_MDL Turing universality from the same Cook composition
axiom plus the proved stepwise Φ_MDL ↔ Rule 110 simulation (`phimdl_law_description_execution`).
The former unsound Shannon / finite-Boolean route has been removed.

## Encoding of GTEState as ℕ

Uses the same Cantor pairing as `GTEInfTapeEncoding`:
  `gte_encode_nat s = Nat.pair s.a (Nat.pair s.b s.c)`
  `gte_decode_nat n = let (a, bc) := n.unpair; let (b, c) := bc.unpair; ⟨a, b, c⟩`

## What `gte_update_map` computes

From `GTECompilation.lean`, `gte_update_map s = (gteTransition 10 1 none s).1`:
  GTE odd step at level 10: `(a, b, c) ↦ (c % b − 11, b − (c % b + c / b), 1023)`
All operations are standard ℕ (saturating subtraction).
-/

namespace UgpLean.Universality.GTEComputability

open UgpLean.Universality.CookComputableBridge
open UgpLean.Universality.GTECompilation
open UgpLean.Universality.GTEInfTapeEncoding

/-! ## ℕ ↔ GTEState encoding (via Cantor pairing) -/

/-- Encode a GTEState as a single ℕ via Cantor pairing. -/
def gte_encode_nat (s : GTEState) : ℕ := Nat.pair s.a (Nat.pair s.b s.c)

/-- Decode a ℕ back to a GTEState via Cantor unpairing. -/
def gte_decode_nat (n : ℕ) : GTEState :=
  let p1 := n.unpair
  let p2 := p1.2.unpair
  ⟨p1.1, p2.1, p2.2⟩

theorem gte_encode_decode_nat (s : GTEState) : gte_decode_nat (gte_encode_nat s) = s := by
  simp [gte_encode_nat, gte_decode_nat, Nat.unpair_pair]

/-! ## gte_update_map_nat (ℕ → ℕ) -/

/-- The GTE update map as a ℕ → ℕ function (through Cantor encoding). -/
def gte_update_map_nat (n : ℕ) : ℕ := gte_encode_nat (gte_update_map (gte_decode_nat n))

/-- Unfolded form: `gte_update_map_nat n = Nat.pair (c%b − 11) (Nat.pair (b − (c%b + c/b)) 1023)`
    where `b = (n.unpair.2).unpair.1`, `c = (n.unpair.2).unpair.2`. -/
theorem gte_update_map_nat_eq (n : ℕ) :
    gte_update_map_nat n =
      let b := n.unpair.2.unpair.1
      let c := n.unpair.2.unpair.2
      Nat.pair (c % b - 11) (Nat.pair (b - (c % b + c / b)) 1023) := by
  simp only [gte_update_map_nat, gte_encode_nat, gte_decode_nat, gte_update_map, gteTransition,
             gteQuotient, gteRemainder, oddStepC, oddStepA, oddStepB]
  norm_num [show (1 : ℕ) % 2 = 1 from rfl]

/-! ## Primrec proof -/

/-- `b` component extractor: `n ↦ n.unpair.2.unpair.1` -/
private def extract_b : ℕ → ℕ := fun n => n.unpair.2.unpair.1
/-- `c` component extractor: `n ↦ n.unpair.2.unpair.2` -/
private def extract_c : ℕ → ℕ := fun n => n.unpair.2.unpair.2

/-- `gte_update_map_nat` is primitive recursive.
    The ℕ → ℕ function is a composition of:
    `Nat.unpair` (twice), `Nat.div`, `Nat.mod`, `Nat.sub`, `Nat.add`, `Nat.pair` (twice),
    and constants 11 and 1023 — all primitive recursive in Mathlib. -/
theorem gte_update_map_nat_primrec : Primrec gte_update_map_nat := by
  -- Component extractors using explicit Nat.unpair applications
  -- bc  = (Nat.unpair n).2
  have hbc : Primrec (fun n : ℕ => (Nat.unpair n).2) :=
    Primrec.snd.comp Primrec.unpair
  -- b  = (Nat.unpair (Nat.unpair n).2).1
  have hb : Primrec (fun n : ℕ => (Nat.unpair (Nat.unpair n).2).1) :=
    Primrec.fst.comp (Primrec.unpair.comp hbc)
  -- c  = (Nat.unpair (Nat.unpair n).2).2
  have hc : Primrec (fun n : ℕ => (Nat.unpair (Nat.unpair n).2).2) :=
    Primrec.snd.comp (Primrec.unpair.comp hbc)
  -- m  = c % b
  have hm : Primrec (fun n : ℕ => (Nat.unpair (Nat.unpair n).2).2 % (Nat.unpair (Nat.unpair n).2).1) :=
    Primrec.nat_mod.comp hc hb
  -- q  = c / b
  have hq : Primrec (fun n : ℕ => (Nat.unpair (Nat.unpair n).2).2 / (Nat.unpair (Nat.unpair n).2).1) :=
    Primrec.nat_div.comp hc hb
  -- a' = m - 11
  have ha' : Primrec (fun n : ℕ => (Nat.unpair (Nat.unpair n).2).2 % (Nat.unpair (Nat.unpair n).2).1 - 11) :=
    Primrec.nat_sub.comp hm (Primrec.const 11)
  -- m+q = m + q
  have hmq : Primrec (fun n : ℕ =>
      (Nat.unpair (Nat.unpair n).2).2 % (Nat.unpair (Nat.unpair n).2).1 +
      (Nat.unpair (Nat.unpair n).2).2 / (Nat.unpair (Nat.unpair n).2).1) :=
    Primrec.nat_add.comp hm hq
  -- b' = b - (m+q)
  have hb' : Primrec (fun n : ℕ =>
      (Nat.unpair (Nat.unpair n).2).1 -
      ((Nat.unpair (Nat.unpair n).2).2 % (Nat.unpair (Nat.unpair n).2).1 +
       (Nat.unpair (Nat.unpair n).2).2 / (Nat.unpair (Nat.unpair n).2).1)) :=
    Primrec.nat_sub.comp hb hmq
  -- inner pair = Nat.pair b' 1023
  have hpair_inner : Primrec (fun n : ℕ =>
      Nat.pair ((Nat.unpair (Nat.unpair n).2).1 -
                ((Nat.unpair (Nat.unpair n).2).2 % (Nat.unpair (Nat.unpair n).2).1 +
                 (Nat.unpair (Nat.unpair n).2).2 / (Nat.unpair (Nat.unpair n).2).1)) 1023) :=
    Primrec₂.comp Primrec₂.natPair hb' (Primrec.const 1023)
  -- full result = Nat.pair a' (Nat.pair b' 1023)
  have hfull : Primrec (fun n : ℕ =>
      Nat.pair
        ((Nat.unpair (Nat.unpair n).2).2 % (Nat.unpair (Nat.unpair n).2).1 - 11)
        (Nat.pair ((Nat.unpair (Nat.unpair n).2).1 -
                   ((Nat.unpair (Nat.unpair n).2).2 % (Nat.unpair (Nat.unpair n).2).1 +
                    (Nat.unpair (Nat.unpair n).2).2 / (Nat.unpair (Nat.unpair n).2).1)) 1023)) :=
    Primrec₂.comp Primrec₂.natPair ha' hpair_inner
  exact hfull.of_eq fun n => by simp [gte_update_map_nat_eq]

/-- **GTE update map is computable** (zero sorry). -/
theorem gte_update_map_nat_computable : Computable gte_update_map_nat :=
  gte_update_map_nat_primrec.to_comp

/-! ## Rule 110 simulation (Cook composition axiom in `CookComputableBridge`) -/

/-! ## Lifting from ℕ to GTEState -/

/-- `gte_update_map` embeds in Rule 110 — **Cook-dependent path**.

    A direct consequence of computability and Cook's universality (`rule110_simulates_computable`),
    using the Cantor encoding from ℕ ↔ GTEState.
    Uses `Rule110.InfTape` (= `ℕ → Bool`) as the tape type.

    **Note**: This is the Cook-dependent path.  Φ_MDL Turing universality is
    `phimdl_turing_universal` in `UgpLean.Universality.PhiMDLUniversality`. -/
theorem gte_embeds_in_rule110_via_computability :
    ∃ (encode : GTEState → Rule110.InfTape)
      (decode : Rule110.InfTape → GTEState)
      (N : ℕ),
      (∀ s, decode (encode s) = s) ∧
      (∀ s, decode (Rule110.infRule110Steps N (encode s)) = gte_update_map s) := by
  obtain ⟨enc_nat, dec_nat, N, hroundtrip, hsim⟩ :=
    rule110_simulates_computable gte_update_map_nat gte_update_map_nat_computable
  refine ⟨fun s => enc_nat (gte_encode_nat s),
          fun tape => gte_decode_nat (dec_nat tape),
          N, ?_, ?_⟩
  · intro s
    -- dec_nat (enc_nat (gte_encode_nat s)) = gte_encode_nat s  (from hroundtrip)
    -- gte_decode_nat (gte_encode_nat s) = s  (from gte_encode_decode_nat)
    simp only [hroundtrip, gte_encode_decode_nat]
  · intro s
    simp only
    rw [show Rule110.infRule110Steps N (enc_nat (gte_encode_nat s)) =
          Rule110.infRule110Steps N (enc_nat (gte_encode_nat s)) from rfl]
    rw [show dec_nat (Rule110.infRule110Steps N (enc_nat (gte_encode_nat s))) =
          gte_update_map_nat (gte_encode_nat s) from hsim (gte_encode_nat s)]
    simp [gte_update_map_nat, gte_encode_decode_nat]

end UgpLean.Universality.GTEComputability
