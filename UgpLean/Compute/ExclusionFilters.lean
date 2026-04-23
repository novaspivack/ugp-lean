import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs

/-!
# UgpLean.Compute.ExclusionFilters — Exclusion Filters at n=10

For b₂ ∈ {16,18,21,28,36,63} (and mirrors), c₁ is composite.
The only survivors are b₂ ∈ {24, 42}.

Reference: UGP Main Paper lem:filters
-/

namespace UgpLean

/-- Exclusion filter: b₂=16 ⇒ c₁ composite. -/
theorem exclude_16 : ¬ Nat.Prime (c1FromPair (b1FromPair 16 63) (q1FromQ2 63)) := by native_decide

/-- Exclusion filter: b₂=18 ⇒ c₁ composite. -/
theorem exclude_18 : ¬ Nat.Prime (c1FromPair (b1FromPair 18 56) (q1FromQ2 56)) := by native_decide

/-- Exclusion filter: b₂=21 ⇒ c₁ composite. -/
theorem exclude_21 : ¬ Nat.Prime (c1FromPair (b1FromPair 21 48) (q1FromQ2 48)) := by native_decide

/-- Exclusion filter: b₂=28 ⇒ c₁ composite. -/
theorem exclude_28 : ¬ Nat.Prime (c1FromPair (b1FromPair 28 36) (q1FromQ2 36)) := by native_decide

/-- Exclusion filter: b₂=36 ⇒ c₁ composite. -/
theorem exclude_36 : ¬ Nat.Prime (c1FromPair (b1FromPair 36 28) (q1FromQ2 28)) := by native_decide

/-- Exclusion filter: b₂=63 ⇒ c₁ composite. -/
theorem exclude_63 : ¬ Nat.Prime (c1FromPair (b1FromPair 63 16) (q1FromQ2 16)) := by native_decide

/-- At n=10, the only strict-ridge divisor pairs yielding prime c₁ are (24,42) and (42,24).
 This is a corollary of ridgeSurvivors_10 (Compute.Sieve): the survivor finset equals
 exactly {(24,42),(42,24)}, and the six exclusion theorems above certify all non-survivors. -/
theorem only_survivors_n10 :
    ∀ b₂ q₂ : ℕ,
      b₂ * q₂ = 1008 → 16 ≤ b₂ → 16 ≤ q₂ →
      Nat.Prime (c1FromPair (b1FromPair b₂ q₂) (q1FromQ2 q₂)) →
      (b₂ = 24 ∧ q₂ = 42) ∨ (b₂ = 42 ∧ q₂ = 24) := by
  -- Reduce to the 10 valid pairs via divisibility, then check each.
  -- Valid pairs: (16,63),(18,56),(21,48),(24,42),(28,36),(36,28),(42,24),(48,21),(56,18),(63,16)
  -- The non-survivors are excluded by the theorems above; (24,42) and (42,24) are the survivors.
  intro b₂ q₂ hprod hb hq hprime
  have hb₂_dvd : b₂ ∣ 1008 := ⟨q₂, hprod.symm⟩
  have hmem : b₂ ∈ Nat.divisors 1008 := Nat.mem_divisors.mpr ⟨hb₂_dvd, (by omega : 1008 ≠ 0)⟩
  have hdivs : Nat.divisors 1008 = {1,2,3,4,6,7,8,9,12,14,16,18,21,24,28,36,
      42,48,56,63,72,84,112,126,144,168,252,336,504,1008} := by native_decide
  rw [hdivs] at hmem
  simp only [Finset.mem_insert, Finset.mem_singleton] at hmem
  -- For each b₂ value: check primality condition
  -- b₂ ∈ {1..14}: ruled out by hb (16 ≤ b₂)
  -- b₂ ∈ {72..1008}: q₂ = 1008/b₂ < 16, ruled out by hq
  -- b₂ = 16 → q₂ = 63; b₂ = 18 → q₂ = 56; etc.
  -- For each of the 30 divisor values of b₂, q₂ is uniquely determined by hprod.
  -- We case split and in each case use omega to fix q₂, then decide or omega to close.
  rcases hmem with rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|
                   rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl|rfl
  -- b₂ ∈ {1,2,3,4,6,7,8,9,12,14}: omega eliminates these (b₂ < 16 contradicts hb)
  -- b₂ ∈ {16,18,21,24,28,36,42,48,56,63}: q₂ = 1008/b₂, check primality
  -- b₂ ∈ {72,84,...,1008}: q₂ < 16 contradicts hq
  -- After each rcases, b₂ is a concrete number; omega determines q₂, then decide primality
  all_goals first
  | omega  -- b₂ < 16 or resulting q₂ < 16
  | (simp only [c1FromPair, b1FromPair, q1FromQ2, ugp1_s, ugp1_g, ugp1_t] at *
     omega)  -- remaining arithmetic/ordering contradictions
  | (have hq_eq : q₂ = 42 := by omega
     subst hq_eq; left; exact ⟨rfl, rfl⟩)
  | (have hq_eq : q₂ = 24 := by omega
     subst hq_eq; right; exact ⟨rfl, rfl⟩)
  | (have hq_eq : q₂ = 63 := by omega
     subst hq_eq
     simp only [c1FromPair, b1FromPair, q1FromQ2, ugp1_s, ugp1_g, ugp1_t] at hprime
     exact absurd hprime (by native_decide))
  | (have hq_eq : q₂ = 56 := by omega
     subst hq_eq
     simp only [c1FromPair, b1FromPair, q1FromQ2, ugp1_s, ugp1_g, ugp1_t] at hprime
     exact absurd hprime (by native_decide))
  | (have hq_eq : q₂ = 48 := by omega
     subst hq_eq
     simp only [c1FromPair, b1FromPair, q1FromQ2, ugp1_s, ugp1_g, ugp1_t] at hprime
     exact absurd hprime (by native_decide))
  | (have hq_eq : q₂ = 36 := by omega
     subst hq_eq
     simp only [c1FromPair, b1FromPair, q1FromQ2, ugp1_s, ugp1_g, ugp1_t] at hprime
     exact absurd hprime (by native_decide))
  | (have hq_eq : q₂ = 28 := by omega
     subst hq_eq
     simp only [c1FromPair, b1FromPair, q1FromQ2, ugp1_s, ugp1_g, ugp1_t] at hprime
     exact absurd hprime (by native_decide))
  | (have hq_eq : q₂ = 21 := by omega
     subst hq_eq
     simp only [c1FromPair, b1FromPair, q1FromQ2, ugp1_s, ugp1_g, ugp1_t] at hprime
     exact absurd hprime (by native_decide))
  | (have hq_eq : q₂ = 18 := by omega
     subst hq_eq
     simp only [c1FromPair, b1FromPair, q1FromQ2, ugp1_s, ugp1_g, ugp1_t] at hprime
     exact absurd hprime (by native_decide))
  | (have hq_eq : q₂ = 16 := by omega
     subst hq_eq
     simp only [c1FromPair, b1FromPair, q1FromQ2, ugp1_s, ugp1_g, ugp1_t] at hprime
     exact absurd hprime (by native_decide))

end UgpLean
