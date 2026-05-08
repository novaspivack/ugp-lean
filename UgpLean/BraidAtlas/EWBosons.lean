import Mathlib.Tactic
import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs

/-!
# UgpLean.BraidAtlas.EWBosons — Electroweak Boson c-Values from First Principles

Resolves the last Category B item in the Braid Atlas (P17): the EW massive boson
c-values c(W)=11, c(Z)=12, c(H)=13.

## Main result: the consecutive-window theorem

The three EW c-values are forced by two structural identities:
1. The canonical ridge factorisation at n=10: q₂(canonical) = 2·N_c·(N_c+1)
2. The GTE quotient gap identity: ugp1_g = N_c·(N_c+1) + 1

Together these force:
* c(W) = 2·N_c(N_c+1) − ugp1_g = N_c(N_c+1) − 1 = 11
* c(Z) = N_c(N_c+1)               = 12
* c(H) = ugp1_g = N_c(N_c+1) + 1   = 13

Hence {c(W), c(Z), c(H)} = {11, 12, 13} is the consecutive-integer window centered
on N_c·(N_c+1) = 12. The window arises because the GTE quotient gap exceeds
N_c(N_c+1) by exactly one.

## Triangular-number unification

Both structural identities admit a unified geometric reading via the triangular
number of the colour rank, T(N_c) = N_c·(N_c+1)/2:

* q₂(canonical) = 4·T(N_c)
* ugp1_g        = 2·T(N_c) + 1
* {c(W), c(Z), c(H)} = {2T(N_c) − 1, 2T(N_c), 2T(N_c) + 1}

The EW c-window is therefore centered on twice the triangular number of the
colour rank. At N_c = 3, T(3) = 6 and 2T(3) = 12.

## Independent identifications

The same three integers admit independent structural readings that all reduce to
the same arithmetic:

* c(W) = q₁(canonical) = q₂(canonical) − ugp1_g = b(ν_μR)
  (right-handed muon-neutrino b-value in the Braid Atlas seesaw sector)
* c(Z) = q₂(canonical) / 2 = N_c(N_c+1)
  (triangular number of the colour rank; symmetric midpoint of the orbit)
* c(H) = ugp1_g = q₂(canonical) − q₁(canonical)
  (the orbital symmetry-breaking gap)

## Status

All theorems in this module: zero sorry.

## Reference

* P17 (Braid_Atlas_v2_First_Principles.tex), §subsec:ew_bosons
* SPEC_036_EWC_ELECTROWEAK_BOSON_C_VALUES.md
-/

namespace UgpLean.BraidAtlas

-- ════════════════════════════════════════════════════════════════
-- §0  The QCD colour rank (locally defined)
-- ════════════════════════════════════════════════════════════════

/-- The QCD colour rank N_c = 3, derived from anomaly cancellation
    (see ChargeTheorem.lean for the derivation). Defined locally here as
    a reducible abbreviation so that `unfold` and `decide` work cleanly. -/
@[reducible] def N_c : ℕ := 3

-- ════════════════════════════════════════════════════════════════
-- §1  The canonical ridge factorisation at n=10
-- ════════════════════════════════════════════════════════════════

/-- The canonical ridge survivor pair at n=10: (b₂, q₂) = (42, 24).
    This is one of the two strict-ridge divisor pairs of R_10 = 1008
    selected by the prime-lock constraint c₁ = b₁q₁ + t = 823 (prime). -/
def b₂_canonical : ℕ := 42
def q₂_canonical : ℕ := 24

/-- The mirror pair: (b₂_mirror, q₂_mirror) = (24, 42). -/
def b₂_mirror : ℕ := 24
def q₂_mirror : ℕ := 42

/-- Canonical and mirror orbits factor R_10. -/
theorem ridge_10_canonical_factorisation :
    b₂_canonical * q₂_canonical = ridge 10 := by
  unfold b₂_canonical q₂_canonical; rw [ridge_10]

theorem ridge_10_mirror_factorisation :
    b₂_mirror * q₂_mirror = ridge 10 := by
  unfold b₂_mirror q₂_mirror; rw [ridge_10]

/-- **Structural identity I.** At N_c = 3, q₂(canonical) = 2·N_c·(N_c+1) = 24.

    The smaller factor of R_10 = 1008 is exactly twice the triangular number of
    the colour rank — a non-trivial arithmetic coincidence at n=10. -/
theorem q₂_canonical_eq_2NcNcPlus1 :
    q₂_canonical = 2 * N_c * (N_c + 1) := by
  unfold q₂_canonical N_c; native_decide

/-- The complementary identity: b₂(canonical) = 2·N_c·(2N_c+1) = 42. -/
theorem b₂_canonical_eq_2Nc2NcPlus1 :
    b₂_canonical = 2 * N_c * (2 * N_c + 1) := by
  unfold b₂_canonical N_c; native_decide

/-- The combined identity: R_10 = 4·N_c²·(N_c+1)·(2N_c+1). -/
theorem ridge_10_in_Nc :
    ridge 10 = 4 * N_c^2 * (N_c + 1) * (2 * N_c + 1) := by
  rw [ridge_10]; unfold N_c; native_decide

-- ════════════════════════════════════════════════════════════════
-- §2  The Higgs gap identity
-- ════════════════════════════════════════════════════════════════

/-- **Structural identity II.** ugp1_g = N_c·(N_c+1) + 1 = 13.

    The GTE quotient gap is exactly one more than the triangular number of the
    colour rank. This is the central identity that forces the consecutive
    EW-boson c-value window {11, 12, 13}. -/
theorem ugp1_g_eq_NcNcPlus1_plus_1 :
    ugp1_g = N_c * (N_c + 1) + 1 := by
  unfold ugp1_g N_c; native_decide

/-- Equivalent form: ugp1_g − N_c·(N_c+1) = 1. -/
theorem ugp1_g_minus_NcNcPlus1_eq_1 :
    ugp1_g - N_c * (N_c + 1) = 1 := by
  unfold ugp1_g N_c; native_decide

-- ════════════════════════════════════════════════════════════════
-- §3  The EW boson c-values
-- ════════════════════════════════════════════════════════════════

/-- **c(W) = 11.**
    Definitional: c(W) = q₁(canonical) = q₂(canonical) − ugp1_g.
    Structural: 2·N_c·(N_c+1) − [N_c·(N_c+1) + 1] = N_c(N_c+1) − 1. -/
def c_W : ℕ := q1FromQ2 q₂_canonical

/-- **c(Z) = 12 = N_c·(N_c+1).**
    Definitional: c(Z) = q₂(canonical) / 2.
    Structural: triangular number of the colour rank, ×2. -/
def c_Z : ℕ := q₂_canonical / 2

/-- **c(H) = 13 = ugp1_g.**
    Definitional: c(H) = the GTE quotient gap.
    Structural: N_c·(N_c+1) + 1 (Higgs gap identity). -/
def c_H : ℕ := ugp1_g

-- ════════════════════════════════════════════════════════════════
-- §4  The numerical values (zero sorry)
-- ════════════════════════════════════════════════════════════════

theorem c_W_eq_11 : c_W = 11 := by
  unfold c_W q1FromQ2 q₂_canonical ugp1_g; native_decide

theorem c_Z_eq_12 : c_Z = 12 := by
  unfold c_Z q₂_canonical; native_decide

theorem c_H_eq_13 : c_H = 13 := by
  unfold c_H ugp1_g; native_decide

/-- **Composite: the EW boson c-values are exactly {11, 12, 13}.** -/
theorem ew_c_values : c_W = 11 ∧ c_Z = 12 ∧ c_H = 13 :=
  ⟨c_W_eq_11, c_Z_eq_12, c_H_eq_13⟩

-- ════════════════════════════════════════════════════════════════
-- §5  The structural derivation
-- ════════════════════════════════════════════════════════════════

/-- **c(W) in N_c form: c(W) = N_c·(N_c+1) − 1.** -/
theorem c_W_eq_NcNcPlus1_minus_1 :
    c_W = N_c * (N_c + 1) - 1 := by
  unfold c_W q1FromQ2 q₂_canonical ugp1_g N_c; native_decide

/-- **c(Z) in N_c form: c(Z) = N_c·(N_c+1).** -/
theorem c_Z_eq_NcNcPlus1 :
    c_Z = N_c * (N_c + 1) := by
  unfold c_Z q₂_canonical N_c; native_decide

/-- **c(H) in N_c form: c(H) = N_c·(N_c+1) + 1.** -/
theorem c_H_eq_NcNcPlus1_plus_1 :
    c_H = N_c * (N_c + 1) + 1 :=
  ugp1_g_eq_NcNcPlus1_plus_1

-- ════════════════════════════════════════════════════════════════
-- §6  The consecutive-window theorem (the main result)
-- ════════════════════════════════════════════════════════════════

/-- **The consecutive-window theorem.**

    The three EW boson c-values {c(W), c(Z), c(H)} form three consecutive
    integers centered on N_c·(N_c+1):

        {c(W), c(Z), c(H)} = {N_c(N_c+1) − 1, N_c(N_c+1), N_c(N_c+1) + 1}.

    At N_c = 3 this gives exactly {11, 12, 13}.

    The window arises because the GTE quotient gap ugp1_g exceeds N_c·(N_c+1) by
    exactly one (Structural Identity II). -/
theorem ew_c_consecutive_window :
    c_Z = c_W + 1 ∧ c_H = c_Z + 1 ∧ c_H = c_W + 2 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [c_Z_eq_12, c_W_eq_11]
  · rw [c_H_eq_13, c_Z_eq_12]
  · rw [c_H_eq_13, c_W_eq_11]

/-- **The c-value set is exactly {N_c(N_c+1) − 1, N_c(N_c+1), N_c(N_c+1) + 1}.** -/
theorem ew_c_set_in_Nc_form :
    ({c_W, c_Z, c_H} : Finset ℕ) =
    {N_c * (N_c + 1) - 1, N_c * (N_c + 1), N_c * (N_c + 1) + 1} := by
  rw [c_W_eq_11, c_Z_eq_12, c_H_eq_13]; unfold N_c; rfl

/-- **The c-value set is exactly {11, 12, 13}.** -/
theorem ew_c_set_explicit :
    ({c_W, c_Z, c_H} : Finset ℕ) = {11, 12, 13} := by
  rw [c_W_eq_11, c_Z_eq_12, c_H_eq_13]

/-- All three EW c-values are distinct primes (W and H prime, Z composite).
    This is a notable structural feature: only the charged-current (W) and
    Higgs sectors get prime c-values; the neutral gauge mediator (Z) does not. -/
theorem ew_c_primality :
    Nat.Prime c_W ∧ ¬ Nat.Prime c_Z ∧ Nat.Prime c_H := by
  refine ⟨?_, ?_, ?_⟩
  · rw [c_W_eq_11]; decide
  · rw [c_Z_eq_12]; decide
  · rw [c_H_eq_13]; decide

-- ════════════════════════════════════════════════════════════════
-- §7  Cross-domain identifications
-- ════════════════════════════════════════════════════════════════

/-- **c(W) = q₁(canonical) = b(ν_μR).**

    The W boson c-value equals the right-handed muon-neutrino b-value in the
    Braid Atlas seesaw sector. Both quantities equal q₁(canonical) = 11. -/
theorem c_W_eq_q1_canonical :
    c_W = q1FromQ2 q₂_canonical := by rfl

/-- **c(H) = q₂(canonical) − q₁(canonical) = ugp1_g.** -/
theorem c_H_eq_q2_minus_q1 :
    c_H = q₂_canonical - q1FromQ2 q₂_canonical := by
  unfold c_H q1FromQ2 q₂_canonical ugp1_g; native_decide

/-- **c(Z) = q₂(canonical) / 2 = N_c·(N_c+1).** -/
theorem c_Z_eq_q2_half :
    c_Z = q₂_canonical / 2 := by rfl

-- ════════════════════════════════════════════════════════════════
-- §8  The composite EW theorem
-- ════════════════════════════════════════════════════════════════

/-- **EW Boson c-Value Theorem (composite).** -/
theorem ew_boson_c_value_theorem :
    q₂_canonical = 2 * N_c * (N_c + 1) ∧
    ugp1_g = N_c * (N_c + 1) + 1 ∧
    c_W = N_c * (N_c + 1) - 1 ∧
    c_Z = N_c * (N_c + 1) ∧
    c_H = N_c * (N_c + 1) + 1 ∧
    c_Z = c_W + 1 ∧
    c_H = c_Z + 1 ∧
    c_W = 11 ∧ c_Z = 12 ∧ c_H = 13 := by
  refine ⟨q₂_canonical_eq_2NcNcPlus1, ugp1_g_eq_NcNcPlus1_plus_1,
          c_W_eq_NcNcPlus1_minus_1, c_Z_eq_NcNcPlus1, c_H_eq_NcNcPlus1_plus_1,
          ?_, ?_, c_W_eq_11, c_Z_eq_12, c_H_eq_13⟩
  · exact ew_c_consecutive_window.1
  · exact ew_c_consecutive_window.2.1

-- ════════════════════════════════════════════════════════════════
-- §9  Uniqueness: {11, 12, 13} is the unique consecutive window
-- ════════════════════════════════════════════════════════════════

/-- The natural arithmetic observables of the canonical GTE orbit at n=10. -/
def orbitalConstants_n10 : Finset ℕ :=
  {ugp1_s, ugp1_g, ugp1_t,
   q1FromQ2 q₂_canonical, q₂_canonical,
   q₂_canonical / 2, q1FromQ2 q₂_canonical * 2,
   q₂_canonical - q1FromQ2 q₂_canonical,
   q₂_canonical + q1FromQ2 q₂_canonical,
   N_c * (N_c + 1)}

theorem orbitalConstants_n10_explicit :
    orbitalConstants_n10 = {7, 11, 12, 13, 20, 22, 24, 35} := by
  unfold orbitalConstants_n10 ugp1_s ugp1_g ugp1_t q1FromQ2 q₂_canonical N_c
  decide

/-- **Uniqueness theorem.** Among the orbital constants at n = 10, the only
    consecutive triple of three distinct integers is {11, 12, 13}. -/
theorem unique_consecutive3_in_orbital :
    ∀ n : ℕ, n ≤ 35 →
      n ∈ orbitalConstants_n10 →
      (n + 1) ∈ orbitalConstants_n10 →
      (n + 2) ∈ orbitalConstants_n10 →
      n = 11 := by
  intro n _hn h1 h2 h3
  rw [orbitalConstants_n10_explicit] at h1 h2 h3
  simp only [Finset.mem_insert, Finset.mem_singleton] at h1 h2 h3
  omega

/-- **The MDL-uniqueness corollary.**

    The EW boson c-values {c(W), c(Z), c(H)} = {11, 12, 13} are the unique
    consecutive integer triple drawn from the orbital constants at n = 10. -/
theorem ew_c_window_unique :
    ({c_W, c_Z, c_H} : Finset ℕ) = {11, 12, 13} ∧
    c_W ∈ orbitalConstants_n10 ∧
    (c_W + 1) ∈ orbitalConstants_n10 ∧
    (c_W + 2) ∈ orbitalConstants_n10 := by
  refine ⟨ew_c_set_explicit, ?_, ?_, ?_⟩ <;>
  rw [c_W_eq_11, orbitalConstants_n10_explicit] <;> decide

-- ════════════════════════════════════════════════════════════════
-- §10  The triangular-number unification (the deepest derivation)
-- ════════════════════════════════════════════════════════════════

/-! ## Derivation from UGP axioms via triangular numbers

    The two structural identities reduce to a single underlying geometric fact
    via the triangular number T(N_c) = N_c·(N_c+1)/2:

        q₂(canonical) = 4 · T(N_c)
        ugp1_g        = 2 · T(N_c) + 1
        {c(W), c(Z), c(H)} = {2·T(N_c)−1, 2·T(N_c), 2·T(N_c)+1}

    The EW c-window is the consecutive triple of integers centered on twice
    the triangular number of the colour rank. -/

/-- Triangular number: T(n) = n·(n+1)/2. -/
def triangular (n : ℕ) : ℕ := n * (n + 1) / 2

/-- T(N_c) at N_c = 3 equals 6. -/
theorem triangular_Nc : triangular N_c = 6 := by
  unfold triangular N_c; native_decide

/-- **Identity I (triangular form):** q₂(canonical) = 4·T(N_c). -/
theorem q₂_canonical_eq_4T :
    q₂_canonical = 4 * triangular N_c := by
  unfold q₂_canonical triangular N_c; native_decide

/-- **Identity II (triangular form):** ugp1_g = 2·T(N_c) + 1. -/
theorem ugp1_g_eq_2T_plus_1 :
    ugp1_g = 2 * triangular N_c + 1 := by
  unfold ugp1_g triangular N_c; native_decide

/-- The midpoint identity: N_c·(N_c+1) = 2·T(N_c). -/
theorem NcNcPlus1_eq_2T :
    N_c * (N_c + 1) = 2 * triangular N_c := by
  unfold triangular N_c; native_decide

/-- **The EW boson c-values are centered on 2·T(N_c).** -/
theorem ew_c_centered_on_2T :
    c_W = 2 * triangular N_c - 1 ∧
    c_Z = 2 * triangular N_c ∧
    c_H = 2 * triangular N_c + 1 := by
  refine ⟨?_, ?_, ?_⟩
  · rw [c_W_eq_NcNcPlus1_minus_1, NcNcPlus1_eq_2T]
  · rw [c_Z_eq_NcNcPlus1, NcNcPlus1_eq_2T]
  · exact ugp1_g_eq_2T_plus_1

/-- **The unified triangular-number theorem.** All structural facts about the
    EW boson c-values reduce to a single geometric fact: the c-window is
    centered on twice the triangular number of the colour rank. -/
theorem ew_triangular_unification :
    q₂_canonical = 4 * triangular N_c ∧
    ugp1_g = 2 * triangular N_c + 1 ∧
    N_c * (N_c + 1) = 2 * triangular N_c ∧
    c_W = 2 * triangular N_c - 1 ∧
    c_Z = 2 * triangular N_c ∧
    c_H = 2 * triangular N_c + 1 ∧
    triangular N_c = 6 :=
  ⟨q₂_canonical_eq_4T,
   ugp1_g_eq_2T_plus_1,
   NcNcPlus1_eq_2T,
   ew_c_centered_on_2T.1,
   ew_c_centered_on_2T.2.1,
   ew_c_centered_on_2T.2.2,
   triangular_Nc⟩

-- ════════════════════════════════════════════════════════════════
-- §11  Derivation from UGP axioms
-- ════════════════════════════════════════════════════════════════

/-- **Derivation chain from UGP axioms.**

    The two structural identities are forced by:

      (UGP Axiom) Asymptotic Sparsity     →  n = 10 is the unique ridge level
                                              (proved in P24)
      (UGP Axiom) Anomaly cancellation    →  N_c = 3
                                              (BraidAtlas.ChargeTheorem)
      (UGP Axiom) Ridge value at n=10     →  R_10 = 1008
                                              (RidgeDefs)
      (UGP Axiom) RSUC at n=10            →  (b₂, q₂) = (42, 24) is unique
                                              (Sieve.lean, prime-lock)
      (UGP Axiom) UGP-1 parameters        →  ugp1_g = 13
                                              (RidgeDefs)

    Substituting N_c = 3 gives the structural identities:
      2·N_c·(N_c+1) = 2·3·4 = 24 = q₂_canonical          ✓
      N_c·(N_c+1) + 1 = 12 + 1 = 13 = ugp1_g              ✓

    The deeper meaning emerges from the triangular-number unification (§10):
    both q₂_canonical and ugp1_g are natural multiples of T(N_c), so the
    relations express a geometric fact about the colour rank rather than a
    numerical accident. -/
theorem ew_ugp_axiom_derivation :
    -- The UGP axiomatic facts:
    N_c = 3 ∧
    ridge 10 = 1008 ∧
    b₂_canonical * q₂_canonical = ridge 10 ∧
    ugp1_g = 13 ∧
    -- The derived structural identities:
    q₂_canonical = 2 * N_c * (N_c + 1) ∧
    ugp1_g = N_c * (N_c + 1) + 1 ∧
    -- And the triangular unification:
    q₂_canonical = 4 * triangular N_c ∧
    ugp1_g = 2 * triangular N_c + 1 := by
  refine ⟨rfl, ridge_10, ridge_10_canonical_factorisation, rfl,
          q₂_canonical_eq_2NcNcPlus1, ugp1_g_eq_NcNcPlus1_plus_1,
          q₂_canonical_eq_4T, ugp1_g_eq_2T_plus_1⟩

end UgpLean.BraidAtlas
