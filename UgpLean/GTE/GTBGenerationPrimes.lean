import Mathlib
import UgpLean.GTE.MirrorDualConjecture
import UgpLean.GTE.UniquenessCertificates

/-!
# UgpLean.GTE.GTBGenerationPrimes — Lean Certificates for GTE Topological Baryogenesis

## Context: GTE Topological Baryogenesis

Three generation-analog ridges n=10, 13, 16 admit mirror-dual prime-lock pairs.
This module certifies the prime-lock structure underlying the GTB η_{B+L,pre} formula.

The η_{B+L,pre} formula:
  η_{B+L,pre} = N_f × ∏_i P_gen_i  where N_f = 3 (anomaly cancellation)
                                     P_gen_i = 1/(ln(c₁_min_i) · ln(c₁_max_i))

Using the MDL-minimal mirror pair at each generation ridge:
  Gen 1 (n=10): c₁ ∈ {823, 2137},    P_gen1 ≈ 1.943 × 10⁻²
  Gen 2 (n=13): c₁ ∈ {9007, 27817},  P_gen2 ≈ 1.073 × 10⁻²
  Gen 3 (n=16): c₁ ∈ {46681, 2489143}, P_gen3 ≈ 6.316 × 10⁻³

  η_{B+L,pre} ≈ 3 × 1.317 × 10⁻⁶ = 3.95 × 10⁻⁶  (target: 3 × 10⁻⁶, +31.7% off)

The formula is structurally grounded, at correct order of magnitude (32% deviation from target 3×10⁻⁶).

## What is certified here

1. `gen1_prime_pair`: c₁ values {823, 2137} at n=10 are both prime.
2. `gen2_prime_pair`: c₁ values {9007, 27817} at n=13 are both prime.
3. `gen3_prime_pair`: c₁ values {46681, 2489143} at n=16 are both prime.
4. `all_generation_c1_prime`: All six generation c₁ values are simultaneously prime.
5. `gen1_mirror_dual`: (24,42) is a MirrorDualPair at n=10.
6. `gen2_mirror_dual`: (56,146) is a MirrorDualPair at n=13.
7. `gen3_mirror_dual_mdl`: (42,1560) is the MDL-minimal MirrorDualPair at n=16.
8. `all_generation_mirror_pairs`: All three MDL-minimal generation mirror pairs hold.
9. `generation_c1_mdl_values`: The MDL-minimal c₁ seeds at n=10,13,16 are 823, 9007, 46681.
10. `generation_c1_mirror_values`: The mirror c₁ values are 2137, 27817, 2489143.

## Confidence

All theorems: zero sorry. Proofs by native_decide (reuses facts from
UniquenessCertificates and MirrorDualConjecture).

## Scientific status

The primality certificates here are machine-verified (native_decide).
The η_{B+L,pre} formula is structurally motivated, 32% off target.
The connection η = N_f × ∏ P_gen_i requires additional derivation (singular series
correction S_GTE not yet computed).
-/

namespace UgpLean.GTE.GTBGenerationPrimes

open UgpLean

-- ════════════════════════════════════════════════════════════════
-- §1  Primality of generation c₁ values
-- ════════════════════════════════════════════════════════════════

/-- Generation 1 (n=10) mirror-dual c₁ values {823, 2137} are both prime.
    These are the canonical Lepton Seed prime-lock values.
    Already in UniquenessCertificates.mdl_c1_n10_is_823; repeated here
    in GTB context for clarity. -/
theorem gen1_prime_pair : Nat.Prime 823 ∧ Nat.Prime 2137 := by
  obtain ⟨_, _, _, h1, h2⟩ := mdl_c1_n10_is_823
  exact ⟨h1, h2⟩

/-- Generation 2 (n=13) mirror-dual c₁ values {9007, 27817} are both prime.
    The correct mirror c₁ at n=13 is 27817 (Lean-certified). -/
theorem gen2_prime_pair : Nat.Prime 9007 ∧ Nat.Prime 27817 := by
  obtain ⟨_, _, _, h1, h2⟩ := mdl_c1_n13_is_9007
  exact ⟨h1, h2⟩

/-- Generation 3 (n=16) MDL-minimal mirror-dual c₁ values {46681, 2489143} are both prime.
    The MDL-minimal pair gives c₁ values {46681, 2489143}. -/
theorem gen3_prime_pair : Nat.Prime 46681 ∧ Nat.Prime 2489143 := by
  obtain ⟨_, _, _, h1, h2⟩ := mdl_c1_n16_is_46681
  exact ⟨h1, h2⟩

/-- All six generation c₁ values are simultaneously prime.
    These are the prime-lock capacities at the three generation-analog ridges
    n=10, 13, 16 under the MDL-minimal mirror-dual selection principle. -/
theorem all_generation_c1_prime :
    Nat.Prime 823 ∧ Nat.Prime 2137 ∧
    Nat.Prime 9007 ∧ Nat.Prime 27817 ∧
    Nat.Prime 46681 ∧ Nat.Prime 2489143 := by
  exact ⟨gen1_prime_pair.1, gen1_prime_pair.2,
         gen2_prime_pair.1, gen2_prime_pair.2,
         gen3_prime_pair.1, gen3_prime_pair.2⟩

-- ════════════════════════════════════════════════════════════════
-- §2  Mirror-dual pair certificates at generation ridges
-- ════════════════════════════════════════════════════════════════

/-- Generation 1: (24,42) is a MirrorDualPair at ridge n=10.
    This means 24×42 = 1008 = 2^10−16, both ≥16, 24<42,
    and both c1Val(24,42)=2137 and c1Val(42,24)=823 are prime. -/
theorem gen1_mirror_dual : MirrorDualPair 10 24 42 :=
  mirror_dual_n10

/-- Generation 2: (56,146) is the unique MirrorDualPair at ridge n=13.
    56×146 = 8176 = 2^13−16, both ≥16, 56<146,
    c1Val(56,146)=27817 (prime) and c1Val(146,56)=9007 (prime). -/
theorem gen2_mirror_dual : MirrorDualPair 13 56 146 :=
  mirror_dual_n13

/-- Generation 3: (42,1560) is the MDL-minimal MirrorDualPair at ridge n=16.
    42×1560 = 65520 = 2^16−16, both ≥16, 42<1560,
    c1Val(42,1560)=2489143 (prime) and c1Val(1560,42)=46681 (prime).
    (n=16 has three mirror-dual pairs; this is the MDL-minimal one.) -/
theorem gen3_mirror_dual_mdl : MirrorDualPair 16 42 1560 :=
  mirror_dual_n16_a

/-- All three MDL-minimal generation mirror pairs hold simultaneously. -/
theorem all_generation_mirror_pairs :
    MirrorDualPair 10 24 42 ∧
    MirrorDualPair 13 56 146 ∧
    MirrorDualPair 16 42 1560 :=
  ⟨gen1_mirror_dual, gen2_mirror_dual, gen3_mirror_dual_mdl⟩

-- ════════════════════════════════════════════════════════════════
-- §3  MDL seed and mirror c₁ values
-- ════════════════════════════════════════════════════════════════

/-- The MDL-minimal c₁ seed values at the three generation ridges are
    823, 9007, 46681 — and they are strictly increasing (as expected from
    monotonicity of the prime-lock scale). -/
theorem generation_c1_mdl_values :
    c1Val 42 24 = 823 ∧
    c1Val 146 56 = 9007 ∧
    c1Val 1560 42 = 46681 ∧
    823 < 9007 ∧ 9007 < 46681 := by
  refine ⟨?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

/-- The mirror c₁ values (larger branch) at the three generation ridges are
    2137, 27817, 2489143. -/
theorem generation_c1_mirror_values :
    c1Val 24 42 = 2137 ∧
    c1Val 56 146 = 27817 ∧
    c1Val 42 1560 = 2489143 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ════════════════════════════════════════════════════════════════
-- §4  b₁ (generation seed ladder index) values
-- ════════════════════════════════════════════════════════════════

/-- The b₁ values at the three generation ridges are 73, 209, 1609.
    (b₁ = b₂ + q₂ + 7 at each mirror pair.) -/
theorem generation_b1_values :
    b1FromPair 24 42 = 73 ∧
    b1FromPair 56 146 = 209 ∧
    b1FromPair 42 1560 = 1609 := by
  refine ⟨?_, ?_, ?_⟩ <;> native_decide

-- ════════════════════════════════════════════════════════════════
-- §5  Summary theorem
-- ════════════════════════════════════════════════════════════════

/-- **GTB Generation Prime Certificate:**
    The three generation-analog ridges n=10, 13, 16 each admit a
    Lean-certified mirror-dual prime-lock pair, and all six c₁ values
    involved are prime. This certifies the prime-lock structure
    underlying the GTB η_{B+L,pre} formula.

    CAVEAT: The η formula η = N_f × ∏ P_gen_i = 3.95×10⁻⁶ is
    structurally motivated (32% off target 3×10⁻⁶). The primality facts
    here are machine-verified. The singular series correction S_GTE is not yet computed. -/
theorem gtb_generation_prime_certificate :
    -- All six prime-lock c₁ values are prime
    Nat.Prime 823 ∧ Nat.Prime 2137 ∧
    Nat.Prime 9007 ∧ Nat.Prime 27817 ∧
    Nat.Prime 46681 ∧ Nat.Prime 2489143 ∧
    -- All three generation ridges have certified mirror-dual pairs
    MirrorDualPair 10 24 42 ∧
    MirrorDualPair 13 56 146 ∧
    MirrorDualPair 16 42 1560 ∧
    -- MDL-minimal c₁ seeds are 823, 9007, 46681 (strictly increasing)
    c1Val 42 24 = 823 ∧
    c1Val 146 56 = 9007 ∧
    c1Val 1560 42 = 46681 ∧
    -- Mirror c₁ values are 2137, 27817, 2489143
    c1Val 24 42 = 2137 ∧
    c1Val 56 146 = 27817 ∧
    c1Val 42 1560 = 2489143 := by
  refine ⟨gen1_prime_pair.1, gen1_prime_pair.2,
         gen2_prime_pair.1, gen2_prime_pair.2,
         gen3_prime_pair.1, gen3_prime_pair.2,
         gen1_mirror_dual, gen2_mirror_dual, gen3_mirror_dual_mdl,
         ?_, ?_, ?_, ?_, ?_, ?_⟩ <;> native_decide

-- ════════════════════════════════════════════════════════════════
-- §6  Ridge structure and distinctness (additional certificates)
-- ════════════════════════════════════════════════════════════════

/-- Per-ridge prime pair certificate at n=10 (aliases gen1_prime_pair for clarity). -/
theorem gen_c1_primes_n10 : Nat.Prime 823 ∧ Nat.Prime 2137 := gen1_prime_pair

/-- Per-ridge prime pair certificate at n=13 (aliases gen2_prime_pair for clarity). -/
theorem gen_c1_primes_n13 : Nat.Prime 9007 ∧ Nat.Prime 27817 := gen2_prime_pair

/-- Per-ridge prime pair certificate at n=16, MDL pair (aliases gen3_prime_pair). -/
theorem gen_c1_primes_n16_mdl : Nat.Prime 46681 ∧ Nat.Prime 2489143 := gen3_prime_pair

/-- **Ridge spacing equals N_c = 3.**
    The three generation ridges n=10, 13, 16 are spaced by exactly 3,
    the number of QCD color charges. -/
theorem gtb_ridge_spacing_equals_Nc :
    let n₁ : ℕ := 10
    let n₂ : ℕ := 13
    let n₃ : ℕ := 16
    let N_c : ℕ := 3
    n₂ - n₁ = N_c ∧ n₃ - n₂ = N_c := by
  norm_num

/-- The three generation ridge levels are distinct naturals. -/
theorem gtb_generation_ridges_distinct :
    (10 : ℕ) ≠ 13 ∧ (13 : ℕ) ≠ 16 ∧ (10 : ℕ) ≠ 16 := by
  norm_num

/-- **The six generation c₁ primes are pairwise distinct.**
    Confirms that each ridge level and each branch produces a unique prime. -/
theorem gtb_six_primes_pairwise_distinct :
    (823 : ℕ) ≠ 2137   ∧ (823 : ℕ) ≠ 9007   ∧ (823 : ℕ) ≠ 27817  ∧
    (823 : ℕ) ≠ 46681  ∧ (823 : ℕ) ≠ 2489143 ∧
    (2137 : ℕ) ≠ 9007  ∧ (2137 : ℕ) ≠ 27817  ∧ (2137 : ℕ) ≠ 46681 ∧
    (2137 : ℕ) ≠ 2489143 ∧
    (9007 : ℕ) ≠ 27817 ∧ (9007 : ℕ) ≠ 46681  ∧ (9007 : ℕ) ≠ 2489143 ∧
    (27817 : ℕ) ≠ 46681 ∧ (27817 : ℕ) ≠ 2489143 ∧
    (46681 : ℕ) ≠ 2489143 := by
  norm_num

/-- **Three certified generation ridges exist with N_c-spaced structure.**
    At each of the three ridges n=10, 13, 16, two distinct prime c₁ values
    are machine-certified. The ridges are evenly spaced by N_c = 3. -/
theorem gtb_three_generations :
    Nat.Prime 823 ∧ Nat.Prime 2137 ∧ (823 : ℕ) ≠ 2137 ∧
    Nat.Prime 9007 ∧ Nat.Prime 27817 ∧ (9007 : ℕ) ≠ 27817 ∧
    Nat.Prime 46681 ∧ Nat.Prime 2489143 ∧ (46681 : ℕ) ≠ 2489143 ∧
    (13 : ℕ) - 10 = 3 ∧ (16 : ℕ) - 13 = 3 :=
  ⟨gen_c1_primes_n10.1, gen_c1_primes_n10.2, by norm_num,
   gen_c1_primes_n13.1, gen_c1_primes_n13.2, by norm_num,
   gen_c1_primes_n16_mdl.1, gen_c1_primes_n16_mdl.2, by norm_num,
   by norm_num, by norm_num⟩

end UgpLean.GTE.GTBGenerationPrimes
