import UgpLean.Core.SievePredicates
import UgpLean.Classification.TheoremA
import UgpLean.Classification.TheoremB
import UgpLean.Compute.DecidablePredicates

/-!
# UgpLean.Classification.RSUC — Residual Seed Uniqueness Theorem

Combines Theorem A (structural) and Theorem B (finite classification) to prove RSUC.

Reference: UGP_LEAN_PROGRAM_ROADMAP §3, Paper 25
-/

namespace UgpLean

/-- RSUC: Under the Unified Sieve, the residual set is exactly the 6 mirror-dual triples,
and MDL selects the Lepton Seed (1, 73, 823). -/
theorem rsuc_theorem (t : Triple) (h : UnifiedAdmissible t) :
    t ∈ Residual ∧ (∀ u ∈ Residual, lexLt LeptonSeed u ∨ LeptonSeed = u) :=
  ⟨Finset.mem_filter.mpr ⟨theoremA t h, (decUnifiedAdmissible_correct t).mpr h⟩,
    mdl_selects_LeptonSeed⟩

end UgpLean
