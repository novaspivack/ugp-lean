import Mathlib.NumberTheory.Divisors
import Mathlib.Data.Finset.Prod
import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs
import UgpLean.Core.SievePredicates
import UgpLean.Compute.PrimeLock

/-!
# UgpLean.Compute.Sieve — Ridge Sieve and n=10 Survivors

At level n=10, the prime-lock sieve selects exactly the mirror pair {(24,42), (42,24)}.

**Main theorem:** `ridgeSurvivors_10` — the survivors at n=10 are exactly {(24,42), (42,24)}.

Reference: UGP Paper, main_n10_ridge.py, The Uniqueness of the Universal Generative Principle
-/

namespace UgpLean

/-- The survivor pairs at level n: (b₂, q₂) where b₂·q₂ = R_n, b₂ ≥ 16, and c₁ is prime -/
def isSurvivorPair (n : ℕ) (b₂ q₂ : ℕ) : Bool :=
  let R := ridge n
  b₂ ≥ strictRidgeMin && b₂ * q₂ = R &&
  Nat.Prime (c1FromPair (b1FromPair b₂ q₂) (q1FromQ2 q₂))

/-- Base survivor pairs: (b₂, q₂) with b₂·q₂ = R_n, b₂ ≥ 16, and c₁ prime. -/
def ridgeSurvivorsBase (n : ℕ) : Finset (ℕ × ℕ) :=
  let R := ridge n
  (Nat.divisorsAntidiagonal R).filter (fun p =>
    strictRidgeMin ≤ p.1 ∧ isSurvivorPair n p.1 p.2 = true)

/-- Mirror-dual survivor pairs: (b₂, q₂) where both (b₂,q₂) and (q₂,b₂) pass the prime-lock.
At n=10 this yields exactly {(24,42), (42,24)}. The (72,14) base survivor is excluded
because its mirror (14,72) fails b₂ ≥ 16. -/
def ridgeSurvivorsFinset (n : ℕ) : Finset (ℕ × ℕ) :=
  (ridgeSurvivorsBase n).filter (fun p => (p.2, p.1) ∈ ridgeSurvivorsBase n)

/-- (24, 42) is a survivor at n=10. -/
theorem mem_24_42 : (24, 42) ∈ ridgeSurvivorsFinset 10 := by native_decide

/-- (42, 24) is a survivor at n=10. -/
theorem mem_42_24 : (42, 24) ∈ ridgeSurvivorsFinset 10 := by native_decide

/-- At n=10, the ridge sieve yields exactly the mirror-dual pair {(24,42), (42,24)}. -/
theorem ridgeSurvivors_10 : ridgeSurvivorsFinset 10 = {(24, 42), (42, 24)} := by
  native_decide

/-- Prop-level mirror-dual survivors coincide with the computed Finset (all n). -/
theorem isMirrorDualSurvivorAt_iff (n : ℕ) (b₂ q₂ : ℕ) :
    isMirrorDualSurvivorAt n b₂ q₂ ↔ (b₂, q₂) ∈ ridgeSurvivorsFinset n := by
  constructor
  · intro ⟨hprod, hb, hp, hq, hp'⟩
    have hnz : ridge n ≠ 0 := by
      by_contra heq
      have hz := hprod.trans heq
      have hle := Nat.mul_le_mul hb hq
      unfold strictRidgeMin at hle
      rw [hz] at hle
      omega
    rw [ridgeSurvivorsFinset, ridgeSurvivorsBase, Finset.mem_filter]
    constructor
    · rw [Finset.mem_filter]
      refine ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨hprod, hnz⟩, hb, ?_⟩
      rw [isSurvivorPair, Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨(Bool.decide_iff _).mpr hb, (Bool.decide_iff _).mpr hprod⟩, (Bool.decide_iff _).mpr hp⟩
    · rw [Finset.mem_filter]
      have hprod' := (mul_comm q₂ b₂).trans hprod
      refine ⟨Nat.mem_divisorsAntidiagonal.mpr ⟨hprod', hnz⟩, hq, ?_⟩
      rw [isSurvivorPair, Bool.and_eq_true, Bool.and_eq_true]
      exact ⟨⟨(Bool.decide_iff _).mpr hq, (Bool.decide_iff _).mpr hprod'⟩, (Bool.decide_iff _).mpr hp'⟩
  · intro h
    rw [ridgeSurvivorsFinset, Finset.mem_filter] at h
    obtain ⟨hmem, hswap⟩ := h
    rw [ridgeSurvivorsBase, Finset.mem_filter] at hmem hswap
    obtain ⟨hab, ⟨hb, hsurv⟩⟩ := hmem
    obtain ⟨hab', ⟨hq, hsurv'⟩⟩ := hswap
    rw [Nat.mem_divisorsAntidiagonal] at hab hab'
    refine ⟨hab.1, ?_, ?_, hq, ?_⟩
    · exact hb
    · rw [isSurvivorPair, Bool.and_eq_true, Bool.and_eq_true] at hsurv
      exact (Bool.decide_iff _).mp hsurv.2
    · rw [isSurvivorPair, Bool.and_eq_true, Bool.and_eq_true] at hsurv'
      exact (Bool.decide_iff _).mp hsurv'.2

/-- Prop-level mirror-dual survivors coincide with the computed Finset (n=10 specialization). -/
theorem isMirrorDualSurvivorAt_10_iff (b₂ q₂ : ℕ) :
    isMirrorDualSurvivorAt 10 b₂ q₂ ↔ (b₂, q₂) ∈ ridgeSurvivorsFinset 10 :=
  isMirrorDualSurvivorAt_iff 10 b₂ q₂

end UgpLean
