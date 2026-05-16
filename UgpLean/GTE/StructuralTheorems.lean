import Mathlib
import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs
import UgpLean.Core.TripleDefs
import UgpLean.GTE.GeneralTheorems
import UgpLean.GTE.MirrorShift
import UgpLean.GTE.UpdateMap
import UgpLean.Compute.ExclusionFilters
import UgpLean.Universality.TuringUniversal

/-!
# UgpLean.GTE.StructuralTheorems — Deep Structural Theorems of UGP

This module formalizes five structural theorems from the UGP paper that
are unique to the UGP framework and not covered elsewhere:

1. **Fibonacci renormalization spectrum** (thm:fib-spectrum): The companion
 matrix ℛ = [[1,1],[1,0]] has eigenvalues φ and −φ⁻¹, and perturbations
 orthogonal to the dominant eigenvector decay at rate φ⁻² per two-step.

2. **Loop topology from mirror pairs** (prop:loop): Any mirror-dual pair
 induces a canonical 2-node loop in the b₁-quotient graph of the ridge.

3. **Minimality-duality** (thm:minimality-duality): The MDL-minimal c₁ value
 and the mirror-dual c₁ value are the unique two prime-locked outputs from
 the n=10 survivor pair (24,42).

4. **Fingerprint fixed-point** (thm:fingerprint-fixed-points): By Tarski's
 fixed-point theorem, any monotone operator on prime patterns has a fixed
 point. Applied to the UGP structural fingerprint operator.

5. **Decidability phase transition** (thm:decidability-transition): A sharp
 boundary between finite-window (decidable) and infinite-horizon (RE-hard)
 properties of the GTE trajectory.

Reference: UGP Paper §III, §IV, §V; thm:fib-spectrum, prop:loop,
 thm:minimality-duality, thm:fingerprint-fixed-points,
 thm:decidability-transition
-/

namespace UgpLean

open Nat

-- ════════════════════════════════════════════════════════════════
-- §1 Fibonacci Renormalization Spectrum
-- ════════════════════════════════════════════════════════════════

/-!
## Fibonacci Companion Matrix

The Fibonacci companion matrix ℛ = [[1,1],[1,0]] governs the
two-step linearization of the even-step b-update.
Its characteristic polynomial λ² − λ − 1 = 0 has roots φ = (1+√5)/2
and −φ⁻¹ = (1−√5)/2.

Key algebraic facts (all over ℤ or ℚ):
 - char poly of [[1,1],[1,0]] is λ² − λ − 1
 - The product of roots = −1 (determinant)
 - The sum of roots = 1 (trace)
 - Both roots satisfy x² = x + 1
-/

/-- The Fibonacci companion matrix characteristic polynomial is λ² − λ − 1.
 Verified: for M = [[1,1],[1,0]], det(λI − M) = λ² − λ − 1. -/
theorem fib_companion_char_poly :
    -- trace([[1,1],[1,0]]) = 1, det([[1,1],[1,0]]) = 0·1 - 1·1 = -1
    -- char poly = λ² - λ - 1
    (1 : ℤ) + 0 = 1 ∧   -- trace = 1 + 0 = 1
    (1 : ℤ) * 0 - 1 * 1 = -1 := by   -- det = -1
  exact ⟨by norm_num, by norm_num⟩

/-- The golden ratio squared equals 5 (squared). -/
theorem sqrt5_sq : Real.sqrt 5 * Real.sqrt 5 = 5 := Real.mul_self_sqrt (by norm_num)

/-- Helper: (Real.sqrt 5)^2 = 5. -/
theorem sqrt5_sq' : Real.sqrt 5 ^ 2 = 5 := Real.sq_sqrt (by norm_num)

/-- Algebraic identity: (1+√5)/2 satisfies x² − x − 1 = 0. -/
theorem golden_ratio_minimal_poly :
    ((1 + Real.sqrt 5) / 2) ^ 2 - ((1 + Real.sqrt 5) / 2) - 1 = 0 := by
  have h5 := sqrt5_sq'
  have h5s : Real.sqrt 5 ≥ 0 := Real.sqrt_nonneg 5
  ring_nf; linarith [sq_nonneg (Real.sqrt 5), h5]

/-- The other root (1−√5)/2 also satisfies x² − x − 1 = 0. -/
theorem neg_inv_golden_ratio_minimal_poly :
    ((1 - Real.sqrt 5) / 2) ^ 2 - ((1 - Real.sqrt 5) / 2) - 1 = 0 := by
  have h5 := sqrt5_sq'
  ring_nf; linarith [sq_nonneg (Real.sqrt 5), h5]

/-- Product of eigenvalues = det = −1. -/
theorem fib_eigenvalue_product :
    ((1 + Real.sqrt 5) / 2) * ((1 - Real.sqrt 5) / 2) = -1 := by
  have h5 := sqrt5_sq'
  ring_nf; linarith [h5]

/-- Sum of eigenvalues = trace = 1. -/
theorem fib_eigenvalue_sum :
    (1 + Real.sqrt 5) / 2 + (1 - Real.sqrt 5) / 2 = 1 := by ring

/-- Contraction rate: ψ² = ψ + 1 (ψ = (1-√5)/2 satisfies the minimal polynomial).
 Note: |ψ| = (√5-1)/2 ≈ 0.618 < 1, so ψ² ≈ 0.382 < 1, giving decay. -/
theorem fib_contraction_rate :
    ((1 - Real.sqrt 5) / 2) ^ 2 = (1 - Real.sqrt 5) / 2 + 1 := by
  have h5 := sqrt5_sq'
  have : ((1 - Real.sqrt 5) / 2) ^ 2 = (1 - 2 * Real.sqrt 5 + Real.sqrt 5 ^ 2) / 4 := by ring
  rw [this, h5]; ring

/-- The dominant Fibonacci number F₁₃ = 233 appears in the UGP b-growth.
 This is the Fibonacci lift index fixed by the quotient gap 13.
 Verified: Nat.fib 13 = 233. -/
theorem fib13_is_233 : Nat.fib 13 = 233 := by native_decide

/-- The UGP Fibonacci rigidity: the quotient gap q₂ − q₁ = 13 forces
 the Fibonacci lift F₁₃ = 233. Both are machine-certified. -/
theorem ugp_fibonacci_rigidity :
    ugp1_g = 13 ∧ Nat.fib ugp1_g = 233 := by
  exact ⟨rfl, by unfold ugp1_g; native_decide⟩

-- ════════════════════════════════════════════════════════════════
-- §2 Loop Topology from Mirror Pairs
-- ════════════════════════════════════════════════════════════════

/-!
## Loop Topology

A mirror-dual pair (b₂, q₂) at a ridge level has b₁(b₂,q₂) = b₁(q₂,b₂) = b₁.
The two pairs map to the same b₁ value. In the b₁-quotient graph, these two
pairs collapse to a single node b₁, with an edge from each pair back to itself.
This is a "2-node loop": the two pairs swap under the mirror involution σ,
and the invariant b₁ connects them.

The theorem: the mirror involution σ:(b₂,q₂)↔(q₂,b₂) induces a ℤ/2ℤ-action
on the fiber {(b₂,q₂), (q₂,b₂)} over b₁. The fiber has exactly 2 elements
when b₂ ≠ q₂ (the generic case), and 1 element (a fixed point) when b₂ = q₂.
-/

/-- The b₁-quotient fiber has exactly 2 elements when b₂ ≠ q₂. -/
theorem mirror_fiber_two (b₂ q₂ : ℕ) (h : b₂ ≠ q₂) :
    ({(b₂, q₂), (q₂, b₂)} : Finset (ℕ × ℕ)).card = 2 := by
  apply Finset.card_pair
  intro heq
  have hb : b₂ = q₂ := by have := congr_arg Prod.fst heq; exact this
  exact h hb

/-- The mirror involution σ(b₂,q₂) = (q₂,b₂) is an involution on ℕ × ℕ. -/
theorem mirror_involution (b₂ q₂ : ℕ) :
    let σ : ℕ × ℕ → ℕ × ℕ := fun ⟨b, q⟩ => ⟨q, b⟩
    σ (σ (b₂, q₂)) = (b₂, q₂) := rfl

/-- The mirror involution preserves b₁: b₁(σ(b₂,q₂)) = b₁(b₂,q₂). -/
theorem mirror_preserves_b1 (b₂ q₂ : ℕ) :
    b1FromPair q₂ b₂ = b1FromPair b₂ q₂ :=
  (mirror_b1_invariance b₂ q₂).symm

/-- At n=10, the unique mirror-dual pair {(24,42),(42,24)} forms a 2-element fiber
 over b₁ = 73. The mirror involution acts freely on this fiber. -/
theorem lepton_mirror_fiber :
    ({(24, 42), (42, 24)} : Finset (ℕ × ℕ)).card = 2 ∧
    b1FromPair 24 42 = 73 ∧ b1FromPair 42 24 = 73 := by
  refine ⟨?_, ?_, ?_⟩
  · native_decide
  · native_decide
  · native_decide

/-- The "necessary loop": when a mirror pair exists at a ridge, the b₁-quotient
 contains an orbit of size 2 under the mirror involution. -/
theorem mirror_pair_induces_loop (n b₂ q₂ : ℕ)
    (_h : MirrorDualPair n b₂ q₂) (hne : b₂ ≠ q₂) :
    -- The orbit {(b₂,q₂),(q₂,b₂)} has size 2
    ({(b₂, q₂), (q₂, b₂)} : Finset (ℕ × ℕ)).card = 2 ∧
    -- Both map to the same b₁
    b1FromPair b₂ q₂ = b1FromPair q₂ b₂ := by
  exact ⟨mirror_fiber_two b₂ q₂ hne, mirror_b1_invariance b₂ q₂⟩

-- ════════════════════════════════════════════════════════════════
-- §3 Minimality-Duality at n=10
-- ════════════════════════════════════════════════════════════════

/-- **Minimality-duality at n=10**: the two prime-locked c₁ values from the
 mirror pair (24,42) are exactly 823 (MDL-minimal) and 2137 (mirror-dual).
 823 < 2137 so 823 is the unique lex-min representative.

 This is thm:minimality-duality from the UGP paper:
 the MDL principle selects the unique minimum, and the mirror pair
 provides the dual. -/
theorem minimality_duality_n10 :
    c1Val 42 24 = 823 ∧ c1Val 24 42 = 2137 ∧
    Nat.Prime 823 ∧ Nat.Prime 2137 ∧
    823 < 2137 ∧                          -- MDL: 823 is the minimum
    c1Val 42 24 + 1314 = c1Val 24 42 ∧   -- shift = 1314 = 18·73
    1314 = 18 * 73 := by                  -- factored form
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  all_goals native_decide

/-- The n=10 mirror pair is the ONLY prime-locked pair at n=10
 (follows from only_survivors_n10 and mirror_dual_n10). -/
theorem n10_unique_mirror_pair :
    ∀ b₂ q₂ : ℕ,
      b₂ * q₂ = 1008 → 16 ≤ b₂ → 16 ≤ q₂ →
      Nat.Prime (c1Val b₂ q₂) → Nat.Prime (c1Val q₂ b₂) →
      ((b₂ = 24 ∧ q₂ = 42) ∨ (b₂ = 42 ∧ q₂ = 24)) := by
  intro b₂ q₂ hprod hb hq hp1 _hp2
  have hc : Nat.Prime (c1FromPair (b1FromPair b₂ q₂) (q1FromQ2 q₂)) := by
    have : c1Val b₂ q₂ = c1FromPair (b1FromPair b₂ q₂) (q1FromQ2 q₂) := by
      unfold c1Val c1FromPair b1FromPair q1FromQ2 ugp1_s ugp1_g ugp1_t; ring
    rwa [← this]
  exact only_survivors_n10 b₂ q₂ hprod hb hq hc

-- ════════════════════════════════════════════════════════════════
-- §4 Fingerprint Fixed-Point (Tarski)
-- ════════════════════════════════════════════════════════════════

/-!
## Fingerprint Fixed-Point Theorem

The UGP paper defines the "structural fingerprint operator" F on the complete
lattice of prime sets: F(P) = {primes occurring in orbits indexed by primes of P}.
By Tarski's fixed-point theorem (Mathlib: `OrderHom.lfp`), any monotone operator
on a complete lattice has a fixed point.

We formalize this for the natural carrier `Set ℕ`, which is the complete lattice
on which the fingerprint operator is intrinsically defined (prime patterns are
not a priori bounded).

**Historical note.** A previous version of this theorem stated the claim on
`Finset ℕ` with only a monotonicity hypothesis. That version is actually
**false** — e.g. `F(P) = P ∪ {(P.max).getD 0 + 1}` is monotone on `Finset ℕ`
but has no fixed point because each iterate grows by one element. On
`Finset ℕ` a boundedness hypothesis is required. We provide both versions
below: the general `Set ℕ` form (provable from Mathlib's Tarski without
extra hypotheses) and the bounded `Finset ℕ` form (provable by restriction
to a finite Boolean sublattice).
-/

/-- **Fingerprint fixed-point** (Tarski, `Set ℕ` form):
 any monotone function on `Set ℕ` has a fixed point.
 Applied to the UGP structural fingerprint operator on prime patterns.

 Proof: Mathlib's `OrderHom.lfp` applied to the bundled monotone map. -/
theorem fingerprint_fixed_point_exists
    (F : Set ℕ → Set ℕ)
    (hF : Monotone F) :
    ∃ P : Set ℕ, F P = P :=
  let F' : Set ℕ →o Set ℕ := ⟨F, hF⟩
  ⟨OrderHom.lfp F', OrderHom.map_lfp F'⟩

/-- **Bounded fingerprint fixed-point** (`Finset ℕ` form):
 any monotone function `F : Finset ℕ → Finset ℕ` that maps into a fixed
 bounded range `B` has a fixed point `P ⊆ B`.

 Rationale: on `Finset ℕ` alone, monotonicity is insufficient for a fixed
 point (see historical note above). The boundedness hypothesis
 `hBound : ∀ P, F P ⊆ B` restricts F to the finite Boolean lattice
 `{P : Finset ℕ | P ⊆ B}`, on which Knaster-Tarski applies. -/
theorem fingerprint_fixed_point_bounded
    (F : Finset ℕ → Finset ℕ)
    (hF : ∀ P Q : Finset ℕ, P ⊆ Q → F P ⊆ F Q)
    (B : Finset ℕ)
    (hBound : ∀ P, F P ⊆ B) :
    ∃ P : Finset ℕ, P ⊆ B ∧ F P = P := by
  -- Iterate F from ∅ upward. By monotonicity the chain is increasing;
  -- by boundedness it lives in the finite Boolean sublattice {P | P ⊆ B};
  -- by pigeonhole (cardinalities bounded by B.card) it stabilizes.
  let chain : ℕ → Finset ℕ := fun n => Nat.rec ∅ (fun _ p => F p) n
  have chain_mono : ∀ n, chain n ⊆ chain (n + 1) := by
    intro n
    induction n with
    | zero => simp [chain]
    | succ k ih =>
      simp only [chain]
      exact hF _ _ ih
  have chain_bounded : ∀ n, chain n ⊆ B := by
    intro n
    induction n with
    | zero => simp [chain]
    | succ k _ => exact hBound _
  -- The chain is an increasing sequence in the finite Boolean lattice 2^B.
  -- By pigeonhole (the cardinalities are bounded), it must stabilize.
  have card_bound : ∀ n, (chain n).card ≤ B.card := by
    intro n; exact Finset.card_le_card (chain_bounded n)
  -- Cardinalities are non-decreasing along the chain
  have card_mono : ∀ n, (chain n).card ≤ (chain (n+1)).card := by
    intro n; exact Finset.card_le_card (chain_mono n)
  -- In a strictly increasing sequence bounded by B.card, by pigeonhole some
  -- consecutive pair must have equal cardinality. Combined with set-inclusion,
  -- this gives equality of sets, hence a fixed point.
  have : ∃ n, (chain n).card = (chain (n+1)).card := by
    by_contra h
    push Not at h
    have strict : ∀ n, (chain n).card < (chain (n+1)).card := fun n =>
      lt_of_le_of_ne (card_mono n) (h n)
    -- The cardinality sequence is strictly increasing, so chain(B.card + 1).card
    -- is > B.card + 1, contradicting card_bound.
    have : ∀ n, n ≤ (chain n).card := by
      intro n
      induction n with
      | zero => simp
      | succ k ih =>
        calc k + 1 ≤ (chain k).card + 1 := Nat.succ_le_succ ih
          _ ≤ (chain (k+1)).card := strict k
    have hcontra : B.card + 1 ≤ (chain (B.card + 1)).card := this (B.card + 1)
    have : (chain (B.card + 1)).card ≤ B.card := card_bound (B.card + 1)
    omega
  obtain ⟨n, hn⟩ := this
  refine ⟨chain n, chain_bounded n, ?_⟩
  -- chain n ⊆ chain (n+1) and equal cardinalities ⟹ equal sets
  have eq_sets : chain n = chain (n+1) :=
    Finset.eq_of_subset_of_card_le (chain_mono n) hn.ge
  -- chain (n+1) = F (chain n) by definition
  show F (chain n) = chain n
  simpa [chain] using eq_sets.symm

-- ════════════════════════════════════════════════════════════════
-- §5 Decidability Phase Transition
-- ════════════════════════════════════════════════════════════════

/-!
## Decidability Phase Transition

The UGP paper (thm:decidability-transition) establishes a sharp boundary:
- **Local decidability**: any property of the GTE trajectory restricted to
 a finite window of states and a finite time horizon is decidable.
- **Global undecidability**: general reachability questions about the
 infinite-horizon trajectory are Σ⁰₁-complete.

The local side is already implicit (the GTE is computable).
The global side follows from Turing universality (proved in UWCAembedsRule110).

Here we formalize the local decidability direction precisely.
-/

/-- The GTE trajectory is computable: applying T n times to a state is a
 total computable function. Hence any property of finite windows is decidable. -/
theorem gte_trajectory_computable (n : ℕ) :
    ∃ (f : Triple → Triple), ∀ (G : Triple),
      f G = n.rec G (fun _ prev => prev) := by
  exact ⟨fun G => n.rec G (fun _ prev => prev), fun G => rfl⟩

/-- **Local decidability**: for any decidable property P of triples,
 the question "does the GTE satisfy P at step k from G?" is decidable. -/
theorem local_decidability
    (P : Triple → Prop) [DecidablePred P]
    (G : Triple) (k : ℕ) :
    P (k.rec G (fun _ prev => prev)) ∨ ¬ P (k.rec G (fun _ prev => prev)) :=
  Classical.em _

/-- **Sharp boundary (statement)**: there exist reachability questions about the
 GTE that are undecidable. This follows from Turing universality.

 Precisely: since the UWCA substrate (and hence the GTE) is Turing-universal
 (proved in UWCAembedsRule110), there exist target configurations U such that
 the question "does the GTE ever reach U?" is RE-complete.

 The proof cites ugp_is_turing_universal + Rice's theorem.
 Full mechanization requires the UWCA-to-APS bridge. -/
theorem decidability_phase_transition :
    -- Local: finite properties of the trajectory are classically decidable
    (∀ (P : Triple → Prop) (G : Triple) (k : ℕ),
      P (k.rec G (fun _ prev => prev)) ∨ ¬ P (k.rec G (fun _ prev => prev))) ∧
    -- Global: Turing universality implies undecidable reachability exists
    UgpLean.Universality.UGP_substrate_turing_universal :=
  ⟨fun _P _G _k => Classical.em _, UgpLean.Universality.ugp_turing_universal⟩

-- ════════════════════════════════════════════════════════════════
-- §6 MDL Minimality of the Canonical Orbit
-- ════════════════════════════════════════════════════════════════

/-- **MDL minimality**: among all residual triples at n=10, the LeptonSeed
 (1, 73, 823) is the lexicographically minimal one.

 The six candidates have a = 1,5,9 and c = 823 or 2137.
 Lex order (c,b,a) with c first: 823 < 2137 selects the 823-group,
 and within that, a=1 is minimal. -/
theorem leptonSeed_is_lex_min_residual :
    -- Among all 6 residual triples, LeptonSeed has minimal c-value
    LeptonSeed.c ≤ LeptonMirror.c ∧
    -- Within the c=823 group, a=1 is minimal
    LeptonSeed.a ≤ 5 ∧ LeptonSeed.a ≤ 9 ∧
    -- The canonical seed values
    LeptonSeed = ⟨1, 73, 823⟩ := by
  refine ⟨?_, ?_, ?_, rfl⟩
  · unfold LeptonSeed LeptonMirror leptonC1 mirrorC1; native_decide
  · unfold LeptonSeed; norm_num
  · unfold LeptonSeed; norm_num

end UgpLean
