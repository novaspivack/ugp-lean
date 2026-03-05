import UgpLean.Compute.Sieve
import UgpLean.Core.RidgeDefs

/-!
# UgpLean.Compute.SieveExtended — Extended Sieve n∈[5,30]

Stage 1 sieve: scan ridge levels n from 5 to 30 for mirror-dual survivors.
At n=10: exactly 2 pairs {(24,42), (42,24)}.
Ridge at n=4 is 0, so we start at n=5.

Reference: Uniqueness of UGP, UGP_LEAN_PROGRAM_ROADMAP §3.5
-/

namespace UgpLean

/-- Range of ridge levels for Stage 1 sieve (n=5 to 30 inclusive). -/
def sieveRange : Finset ℕ := (Finset.range 31).filter (fun n => 5 ≤ n)

theorem sieveRange_mem_10 : 10 ∈ sieveRange := by native_decide

/-- Mirror-dual survivor count at level n. -/
def mirrorDualCount (n : ℕ) : ℕ := (ridgeSurvivorsFinset n).card

/-- At n=10, mirror-dual count is 2. -/
theorem mirrorDualCount_10 : mirrorDualCount 10 = 2 := by
  rw [mirrorDualCount, ridgeSurvivors_10]
  native_decide

/-- At n=10, the two survivors are exactly (24,42) and (42,24). -/
theorem ridgeSurvivors_10_card : (ridgeSurvivorsFinset 10).card = 2 := by
  rw [ridgeSurvivors_10]; native_decide

end UgpLean
