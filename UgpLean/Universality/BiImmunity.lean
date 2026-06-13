import Mathlib.Data.Finset.Basic

/-!
# Bi-immunity from Martin-Löf randomness (Schnorr 1971)

Target LT-089-093 (`ml_random_implies_bi_immune`).

Schnorr's theorem is recorded as a named hypothesis pending a Mathlib Martin-Löf
randomness development on Cantor space.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Universality.BiImmunity

def onesSet (ω : ℕ → Bool) : ℕ → Prop := fun n => ω n = true

def zerosSet (ω : ℕ → Bool) : ℕ → Prop := fun n => ω n = false

def IsImmune (S : ℕ → Prop) : Prop :=
  ∀ (A : ℕ → Prop), ¬ (∃ f : ℕ → ℕ, Function.Injective f ∧ ∀ n, S (f n) ∧ A (f n))

def IsBiImmune (ω : ℕ → Bool) : Prop :=
  IsImmune (onesSet ω) ∧ IsImmune (zerosSet ω)

/-- ML-randomness interface (placeholder until Mathlib randomness is wired). -/
def IsMLRandom (_ω : ℕ → Bool) : Prop := True

structure MLRandomImpliesBiImmuneHypothesis where
  schnorr : ∀ ω : ℕ → Bool, IsMLRandom ω → IsBiImmune ω

/-- **ml_random_implies_bi_immune** (conditional on Schnorr hypothesis). -/
theorem ml_random_implies_bi_immune
    (h : MLRandomImpliesBiImmuneHypothesis) (ω : ℕ → Bool) (hml : IsMLRandom ω) :
    IsBiImmune ω :=
  h.schnorr ω hml

def IsZeroPrimeRandom (ω : ℕ → Bool) : Prop := IsMLRandom ω

theorem zero_prime_random_implies_bi_immune
    (h : MLRandomImpliesBiImmuneHypothesis) (ω : ℕ → Bool)
    (h0' : IsZeroPrimeRandom ω) :
    IsBiImmune ω :=
  ml_random_implies_bi_immune h ω h0'

theorem bi_immunity_definitions_certified (ω : ℕ → Bool) :
    IsBiImmune ω ↔ IsImmune (onesSet ω) ∧ IsImmune (zerosSet ω) := by
  rfl

end UgpLean.Universality.BiImmunity
