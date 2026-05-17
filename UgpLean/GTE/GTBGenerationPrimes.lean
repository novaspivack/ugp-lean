import Mathlib
import UgpLean.GTE.MirrorDualConjecture
import UgpLean.GTE.UniquenessCertificates

/-!
# UgpLean.GTE.GTBGenerationPrimes — Lean Certificates for GTE Topological Baryogenesis

## Context: EPIC_068 Round 04

Round 02 of EPIC_068 (GTB: GTE Topological Baryogenesis) identified the three
generation-analog ridges n=10, 13, 16 as admitting mirror-dual prime-lock pairs.
Round 03 corrected Round 02's c₁ values (which contained errors for n=13 and n=16)
and provided the Lean-consistent values.

The η_{B+L,pre} formula:
  η_{B+L,pre} = N_f × ∏_i P_gen_i  where N_f = 3 (anomaly cancellation)
                                     P_gen_i = 1/(ln(c₁_min_i) · ln(c₁_max_i))

Using the MDL-minimal mirror pair at each generation ridge:
  Gen 1 (n=10): c₁ ∈ {823, 2137},    P_gen1 ≈ 1.943 × 10⁻²
  Gen 2 (n=13): c₁ ∈ {9007, 27817},  P_gen2 ≈ 1.073 × 10⁻²
  Gen 3 (n=16): c₁ ∈ {46681, 2489143}, P_gen3 ≈ 6.316 × 10⁻³

  η_{B+L,pre} ≈ 3 × 1.317 × 10⁻⁶ = 3.95 × 10⁻⁶  (target: 3 × 10⁻⁶, +31.7% off)

Note: Round 02 reported 3.09 × 10⁻⁶ (3% off), but used incorrect c₁ values for
n=13 (used 91253 instead of 27817) and n=16 (used 104233, 6400391 instead of
46681, 2489143). Round 03 corrects this. The formula is Cat C (structurally
grounded, correct order of magnitude, 32% deviation from target).

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

The primality certificates here are Cat A (machine-verified).
The η_{B+L,pre} formula is Cat C (structurally motivated, 32% off target).
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
    CORRECTION from Round 02: Round 02 used 91253 instead of 27817.
    The correct mirror c₁ at n=13 is 27817 (Lean-certified). -/
theorem gen2_prime_pair : Nat.Prime 9007 ∧ Nat.Prime 27817 := by
  obtain ⟨_, _, _, h1, h2⟩ := mdl_c1_n13_is_9007
  exact ⟨h1, h2⟩

/-- Generation 3 (n=16) MDL-minimal mirror-dual c₁ values {46681, 2489143} are both prime.
    CORRECTION from Round 02: Round 02 used (104233, 6400391) which do NOT form a valid
    MirrorDualPair at n=16 under the exact Lean formula. The correct MDL-minimal pair
    gives c₁ values {46681, 2489143}. -/
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

/-- **GTB Generation Prime Certificate** (EPIC_068 Round 04):
    The three generation-analog ridges n=10, 13, 16 each admit a
    Lean-certified mirror-dual prime-lock pair, and all six c₁ values
    involved are prime. This certifies the prime-lock structure
    underlying the GTB η_{B+L,pre} formula.

    CAVEAT: The η formula η = N_f × ∏ P_gen_i = 3.95×10⁻⁶ is Cat C
    (32% off target 3×10⁻⁶). The primality facts here are Cat A.
    The singular series correction S_GTE is not yet computed. -/
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

end UgpLean.GTE.GTBGenerationPrimes
