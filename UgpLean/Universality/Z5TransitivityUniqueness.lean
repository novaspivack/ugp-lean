import UgpLean.Universality.CUP4TotalParity
import Mathlib.Data.Fintype.Pi

/-!
# Z₅ Transitivity Uniqueness — CA-Internal Reason for Five Families

This module proves that p = 5 is the unique prime (among all primes ≤ 23) such that
there exists a Hamming-weight-3 binary vector of length p whose ALL p cyclic rotations
terminate at the all-ones vector in exactly 2 Rule 110 steps on a p-cell periodic ring.

## The property (full transitivity)

A Hamming-3 vector v on a p-cell ring has **full Z_p transitivity** under Rule 110 iff
for every rotation k ∈ {0,…,p−1}:

  rotate(v, k) →^{R110} s₁ →^{R110} all-ones(p)

i.e. two applications of Rule 110 carry every cyclic rotation to the all-ones attractor.

## Main results

- `z5_gen2_rotations_to_allones`: All 5 rotations of smGen2 reach smGen3 in 1 step.
- `z5_full_transitivity_smGen1`: All 5 rotations of smGen1 reach smGen3 in 2 steps.
- `z5_weight3_full_transitivity_count`: Exactly 5 weight-3 vectors on the 5-ring have
  full transitivity — the 5 rotations of smGen1.
- For each prime p ∈ {2,3,7,11,13,17,19,23}: NO rotation of ANY Hamming-3 vector of
  length p reaches all-ones in 2 steps (total 2-step isolation at weight 3).
- `z5_transitivity_uniqueness`: p = 5 is the unique prime ≤ 23 with a Hamming-3
  full-transitivity class under Rule 110.

## Physical significance

CUP-9 proves the 5 SM families form a Z₅ ring. This module answers *why* 5: p = 5 is the
unique prime for which Rule 110 acts with full Z_p transitivity on all cyclic rotations of a
Hamming-weight-3 vector in a 2-step orbit to all-ones. P01's SM family count and this CA
transitivity uniqueness independently yield p = 5 — mutual structural confirmation.

## Computational basis

Python sweep: `research-sandbox/z5_transitivity_check.py` (run time < 1 second for all primes ≤ 23).
Results table:
  p=2  — no wt-3 vectors exist
  p=3  — 1 cyclic class, 0 full-transitive (all-ones → all-zeros in 1 step)
  p=5  — 2 cyclic classes, **1 full-transitive** (smGen1 family; 1 class reaches all-ones in 1 step)
  p=7  — 5 classes, 0 transitive (not even partial; no rotation reaches all-ones in 2 steps)
  p=11 — 15 classes, 0 transitive
  p=13 — 22 classes, 0 transitive
  p=17 — 40 classes, 0 transitive
  p=19 — 51 classes, 0 transitive
  p=23 — 77 classes, 0 transitive

All Lean theorems: zero sorry, proved by native_decide (certified machine computation).
-/

namespace UgpLean.Universality

-- ════════════════════════════════════════════════════════════════
-- §1  General Rule 110 step for p-cell periodic rings
-- ════════════════════════════════════════════════════════════════

/-- Rule 110 lookup: given (left, center, right) bits, return the Rule 110 output bit.
    Reusable for any ring size — does NOT depend on p = 5. -/
private def rule110BitG (l c r : Fin 2) : Fin 2 :=
  ⟨(110 >>> (l.val * 4 + c.val * 2 + r.val)) % 2, Nat.mod_lt _ (by omega)⟩

/-- One step of Rule 110 on a p-cell periodic ring (p > 0 required).
    Left neighbor of cell i is (i + p − 1) mod p = (i − 1) mod p.
    This generalises `rule110StepPeriodic` from CUP4TotalParity (which fixes p = 5). -/
def rule110Ring (p : Nat) (hp : 0 < p) (cells : Fin p → Fin 2) : Fin p → Fin 2 :=
  fun i =>
    let lIdx := ⟨(i.val + p - 1) % p, Nat.mod_lt _ hp⟩
    let rIdx := ⟨(i.val + 1)  % p, Nat.mod_lt _ hp⟩
    rule110BitG (cells lIdx) (cells i) (cells rIdx)

-- ════════════════════════════════════════════════════════════════
-- §2  Cyclic shift for p-cell rings
-- ════════════════════════════════════════════════════════════════

/-- Cyclic shift by k positions: position i of the result holds the value of the
    original at position (i + k) mod p.
    Matches the convention of `rotate5` in CUP4TotalParity for p = 5. -/
def cyclicShiftRing (p : Nat) (hp : 0 < p) (k : Fin p) (cells : Fin p → Fin 2) : Fin p → Fin 2 :=
  fun i => cells ⟨(i.val + k.val) % p, Nat.mod_lt _ hp⟩

-- ════════════════════════════════════════════════════════════════
-- §3  All-ones vector and Hamming weight
-- ════════════════════════════════════════════════════════════════

/-- The all-ones vector on a p-cell ring. -/
def allOnesRing (p : Nat) : Fin p → Fin 2 := fun _ => 1

/-- Hamming weight (count of 1-bits) of a p-cell binary ring vector.
    Counts positions i where v i = 1 using Finset.filter + Finset.card
    (avoids Finset.sum import requirement). -/
def hammingWeightRing (p : Nat) (v : Fin p → Fin 2) : Nat :=
  ((Finset.univ (α := Fin p)).filter (fun i => v i = 1)).card

/-- smGen1 has Hamming weight 3: three odd-parity particles in generation 1
    ([1,1,0,0,1] → 1+1+0+0+1 = 3). -/
theorem smGen1_hamming_weight_3 : hammingWeightRing 5 smGen1 = 3 := by native_decide

-- ════════════════════════════════════════════════════════════════
-- §4  Positive result: p = 5 full Z₅ transitivity
-- ════════════════════════════════════════════════════════════════

/-- All 5 cyclic rotations of smGen2 reach the all-ones attractor smGen3 in 1 Rule 110 step.
    This deepens CUP-9: rotate(gen₁,k) → rotate(gen₂,k) (CUP-9), AND
    rotate(gen₂,k) → gen₃ (this theorem). Together they give 2-step transitivity for gen₁. -/
theorem z5_gen2_rotations_to_allones (k : Fin 5) :
    rule110StepPeriodic (rotate5 smGen2 k) = smGen3 := by
  funext i; fin_cases i <;> fin_cases k <;> native_decide

/-- All 5 cyclic rotations of smGen1 reach the all-ones attractor smGen3 in 2 Rule 110 steps.
    Proof chain: rotate(gen₁,k) →^{CUP-9} rotate(gen₂,k) →^{z5_gen2_rotations_to_allones} gen₃. -/
theorem z5_full_transitivity_smGen1 (k : Fin 5) :
    rule110StepPeriodic (rule110StepPeriodic (rotate5 smGen1 k)) = smGen3 :=
  cup9_z5_symmetry k ▸ z5_gen2_rotations_to_allones k

/-- Among the C(5,3) = 10 Hamming-3 vectors on the 5-cell ring (2 cyclic classes),
    exactly 5 have the 2-step all-ones property: precisely the 5 rotations of smGen1.
    The other class ([0,1,0,1,1] and its rotations) reaches all-ones in 1 step, not 2. -/
theorem z5_weight3_full_transitivity_count :
    (Finset.univ (α := Fin 5 → Fin 2)).filter (fun v =>
      hammingWeightRing 5 v = 3 ∧
      ∀ k : Fin 5, rule110StepPeriodic (rule110StepPeriodic (rotate5 v k)) = smGen3)
    = Finset.image (fun k => rotate5 smGen1 k) Finset.univ := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- §5  Negative results: primes p ≠ 5 have zero Hamming-3 transitivity
-- ════════════════════════════════════════════════════════════════
-- For ALL primes p in {2, 3, 7, 11, 13, 17, 19, 23}:
-- NOT EVEN ONE rotation of any Hamming-3 vector reaches all-ones in 2 steps.
-- This is strictly stronger than mere absence of a full-transitivity class.

/-- p = 2: no Hamming-3 vectors exist (p < 3 is required for weight 3). -/
theorem no_hamming3_vectors_p2 :
    ∀ v : Fin 2 → Fin 2, hammingWeightRing 2 v ≠ 3 := by
  native_decide

/-- p = 3: the unique Hamming-3 vector [1,1,1] maps to all-zeros in 1 Rule 110 step
    (neighbourhood (1,1,1) has index 7; Rule 110 maps bit 7 → 0).
    Two steps: [1,1,1] → [0,0,0] → [0,0,0] ≠ [1,1,1] = all-ones(3).
    No rotation reaches all-ones in 2 steps. -/
theorem no_hamming3_transitivity_p3 :
    ∀ v : Fin 3 → Fin 2, hammingWeightRing 3 v = 3 →
      ∀ k : Fin 3,
        rule110Ring 3 (by omega) (rule110Ring 3 (by omega) (cyclicShiftRing 3 (by omega) k v)) ≠
          allOnesRing 3 := by
  native_decide

/-- p = 7: no rotation of any weight-3 vector reaches all-ones in 2 steps (5 classes, 0 transitive). -/
theorem no_hamming3_transitivity_p7 :
    ∀ v : Fin 7 → Fin 2, hammingWeightRing 7 v = 3 →
      ∀ k : Fin 7,
        rule110Ring 7 (by omega) (rule110Ring 7 (by omega) (cyclicShiftRing 7 (by omega) k v)) ≠
          allOnesRing 7 := by
  native_decide

/-- p = 11: no weight-3 transitivity (15 cyclic classes, none transitive). -/
theorem no_hamming3_transitivity_p11 :
    ∀ v : Fin 11 → Fin 2, hammingWeightRing 11 v = 3 →
      ∀ k : Fin 11,
        rule110Ring 11 (by omega) (rule110Ring 11 (by omega) (cyclicShiftRing 11 (by omega) k v)) ≠
          allOnesRing 11 := by
  native_decide

/-- p = 13: no weight-3 transitivity (22 cyclic classes, none transitive). -/
theorem no_hamming3_transitivity_p13 :
    ∀ v : Fin 13 → Fin 2, hammingWeightRing 13 v = 3 →
      ∀ k : Fin 13,
        rule110Ring 13 (by omega) (rule110Ring 13 (by omega) (cyclicShiftRing 13 (by omega) k v)) ≠
          allOnesRing 13 := by
  native_decide

/-- p = 17: no weight-3 transitivity (40 cyclic classes, none transitive).
    native_decide enumerates all 2^17 = 131,072 binary vectors; weight check filters to 680
    Hamming-3 vectors; transitivity check is instantaneous. -/
theorem no_hamming3_transitivity_p17 :
    ∀ v : Fin 17 → Fin 2, hammingWeightRing 17 v = 3 →
      ∀ k : Fin 17,
        rule110Ring 17 (by omega) (rule110Ring 17 (by omega) (cyclicShiftRing 17 (by omega) k v)) ≠
          allOnesRing 17 := by
  native_decide

/-- p = 19: no weight-3 transitivity (51 cyclic classes, none transitive).
    native_decide enumerates all 2^19 = 524,288 binary vectors. -/
theorem no_hamming3_transitivity_p19 :
    ∀ v : Fin 19 → Fin 2, hammingWeightRing 19 v = 3 →
      ∀ k : Fin 19,
        rule110Ring 19 (by omega) (rule110Ring 19 (by omega) (cyclicShiftRing 19 (by omega) k v)) ≠
          allOnesRing 19 := by
  native_decide

/-- p = 23: no weight-3 transitivity (77 cyclic classes, none transitive).
    native_decide enumerates all 2^23 = 8,388,608 binary vectors (weight filter passes 1771).
    Native OCaml compilation makes this tractable (estimated < 60 seconds). -/
theorem no_hamming3_transitivity_p23 :
    ∀ v : Fin 23 → Fin 2, hammingWeightRing 23 v = 3 →
      ∀ k : Fin 23,
        rule110Ring 23 (by omega) (rule110Ring 23 (by omega) (cyclicShiftRing 23 (by omega) k v)) ≠
          allOnesRing 23 := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- §6  Main theorem: Z₅ transitivity uniqueness (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- **Z₅ Transitivity Uniqueness (CatAL, zero sorry)**: Among all primes p ≤ 23, p = 5 is the
    unique prime for which there exists a Hamming-weight-3 binary vector of length p such that
    ALL p cyclic rotations of that vector terminate at the all-ones vector in exactly 2 Rule 110
    steps on a p-cell periodic ring.

    The witness for p = 5 is smGen1 = [1,1,0,0,1] (the gen-1 parity vector from CUP-4).

    For all other small primes {2, 3, 7, 11, 13, 17, 19, 23}: not only is there no
    full-transitivity class, but NO rotation of ANY Hamming-3 vector reaches all-ones in 2 steps
    (total 2-step isolation at Hamming weight 3). This is a complete null result.

    Physical significance: CUP-9 establishes the 5 SM families form a Z₅ ring (from P01's
    N_fam = 5). This theorem gives a CA-internal structural reason: p = 5 is the unique prime
    ring size for which Rule 110 acts with full transitivity on all cyclic rotations of a
    Hamming-weight-3 vector. The P01 family count and this CA theorem independently converge
    on p = 5 — mutual structural confirmation of the five-family structure. -/
theorem z5_transitivity_uniqueness :
    -- Positive: p = 5, smGen1 has full Z₅ transitivity (all 5 rotations → all-ones in 2 steps)
    (∀ k : Fin 5,
       rule110StepPeriodic (rule110StepPeriodic (rotate5 smGen1 k)) = smGen3) ∧
    -- p = 2: vacuously true (no weight-3 vectors of length 2 exist)
    (∀ v : Fin 2 → Fin 2, hammingWeightRing 2 v ≠ 3) ∧
    -- p = 3: all-ones → all-zeros in 1 step; 2-step orbit misses all-ones
    (∀ v : Fin 3 → Fin 2, hammingWeightRing 3 v = 3 →
       ∀ k : Fin 3,
         rule110Ring 3 (by omega) (rule110Ring 3 (by omega) (cyclicShiftRing 3 (by omega) k v)) ≠
           allOnesRing 3) ∧
    -- p = 7: 5 cyclic classes, none transitive
    (∀ v : Fin 7 → Fin 2, hammingWeightRing 7 v = 3 →
       ∀ k : Fin 7,
         rule110Ring 7 (by omega) (rule110Ring 7 (by omega) (cyclicShiftRing 7 (by omega) k v)) ≠
           allOnesRing 7) ∧
    -- p = 11: 15 classes, none transitive
    (∀ v : Fin 11 → Fin 2, hammingWeightRing 11 v = 3 →
       ∀ k : Fin 11,
         rule110Ring 11 (by omega) (rule110Ring 11 (by omega) (cyclicShiftRing 11 (by omega) k v)) ≠
           allOnesRing 11) ∧
    -- p = 13: 22 classes, none transitive
    (∀ v : Fin 13 → Fin 2, hammingWeightRing 13 v = 3 →
       ∀ k : Fin 13,
         rule110Ring 13 (by omega) (rule110Ring 13 (by omega) (cyclicShiftRing 13 (by omega) k v)) ≠
           allOnesRing 13) ∧
    -- p = 17: 40 classes, none transitive
    (∀ v : Fin 17 → Fin 2, hammingWeightRing 17 v = 3 →
       ∀ k : Fin 17,
         rule110Ring 17 (by omega) (rule110Ring 17 (by omega) (cyclicShiftRing 17 (by omega) k v)) ≠
           allOnesRing 17) ∧
    -- p = 19: 51 classes, none transitive
    (∀ v : Fin 19 → Fin 2, hammingWeightRing 19 v = 3 →
       ∀ k : Fin 19,
         rule110Ring 19 (by omega) (rule110Ring 19 (by omega) (cyclicShiftRing 19 (by omega) k v)) ≠
           allOnesRing 19) ∧
    -- p = 23: 77 classes, none transitive
    (∀ v : Fin 23 → Fin 2, hammingWeightRing 23 v = 3 →
       ∀ k : Fin 23,
         rule110Ring 23 (by omega) (rule110Ring 23 (by omega) (cyclicShiftRing 23 (by omega) k v)) ≠
           allOnesRing 23) :=
  ⟨z5_full_transitivity_smGen1,
   no_hamming3_vectors_p2,
   no_hamming3_transitivity_p3,
   no_hamming3_transitivity_p7,
   no_hamming3_transitivity_p11,
   no_hamming3_transitivity_p13,
   no_hamming3_transitivity_p17,
   no_hamming3_transitivity_p19,
   no_hamming3_transitivity_p23⟩

-- ════════════════════════════════════════════════════════════════
-- §7  Deepening: exact count and structural characterization for p = 5
-- ════════════════════════════════════════════════════════════════

/-- For the 5-cell ring, all 5 cyclic rotations of smGen2 reach smGen3 in 1 step.
    Combined with z5_full_transitivity_smGen1 and cup9_z5_symmetry, this means:
    the gen-1 orbit is "doubly transitive" — Z₅ symmetry holds at BOTH steps 1 and 2. -/
theorem z5_gen2_also_fully_transitive (k : Fin 5) :
    rule110StepPeriodic (rotate5 smGen2 k) = smGen3 :=
  z5_gen2_rotations_to_allones k

/-- The unique Hamming-3 orbit class with full Z₅ transitivity is smGen1's class.
    The other weight-3 class ([0,1,0,1,1] and rotations) reaches all-ones in 1 step
    but the SECOND step from all-ones is all-zeros — missing the 2-step property. -/
theorem z5_class2_one_step_allones :
    rule110StepPeriodic (fun i : Fin 5 => if i.val = 1 ∨ i.val = 3 ∨ i.val = 4 then 1 else 0) =
      smGen3 := by
  native_decide

end UgpLean.Universality
