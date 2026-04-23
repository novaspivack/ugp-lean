import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs

/-!
# UgpLean.Core.RidgeRigidity — Ridge Lock and Gap Rigidity

Ridge remainder lock: m₂=15 at n=10 (c₂=2^n-1, b₂|R_n).
Quotient-gap rigidity: q₂-q₁=13 under prime-lock.

Reference: UGP Main Paper lem:m2, thm:gap13-all, prop:rema-gap
-/

namespace UgpLean

/-- At n=10, c₂ = 2^n - 1 = 1023. For b₂|R with b₂≥16, m₂ = c₂ % b₂ = 15.
 Since 1023 = 15 + 1008 and b₂|1008, we have 1023 ≡ 15 (mod b₂). -/
theorem ridge_remainder_lock (b₂ : ℕ) (hb : b₂ ∣ ridge 10) (hmin : strictRidgeMin ≤ b₂) :
    (2^10 - 1) % b₂ = 15 := by
  rw [ridge_10] at hb
  have heq : (2:ℕ)^10 - 1 = 15 + 1008 := by native_decide
  rw [heq, Nat.add_mod, Nat.mod_eq_zero_of_dvd hb, add_zero, Nat.mod_mod]
  exact Nat.mod_eq_of_lt (by unfold strictRidgeMin at hmin; omega)

/-- At n=10, for the canonical b₂=42: m₂ = 1023 % 42 = 15. -/
theorem m2_canonical : (2^10 - 1) % 42 = 15 := by native_decide

/-- Quotient gap: q₂ - q₁ = 13 for UGP-1 when q₂ ≥ 13 (q₁ = q₂ - 13). -/
theorem quotient_gap_13 (q₂ : ℕ) (hq : 13 ≤ q₂) : q₂ - (q1FromQ2 q₂) = 13 := by
  unfold q1FromQ2 ugp1_g; omega

/-- For n=10 survivors (42,24) and (24,42): q₂ - q₁ = 13. -/
theorem survivor_gap_42_24 : 24 - q1FromQ2 24 = 13 := by native_decide
theorem survivor_gap_24_42 : 42 - q1FromQ2 42 = 13 := by native_decide

/-- Remainder-gap identity: m₁=20 (from c₁=b₁q₁+20), so q₂-q₁ = m₁-7 = 13. -/
theorem remainder_gap_identity : ugp1_t = 20 ∧ ugp1_s = 7 ∧ ugp1_t - ugp1_s = 13 := by
  unfold ugp1_t ugp1_s; exact ⟨rfl, rfl, rfl⟩

end UgpLean
