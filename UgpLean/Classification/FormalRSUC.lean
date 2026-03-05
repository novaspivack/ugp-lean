import UgpLean.Core.SievePredicates
import UgpLean.Core.TripleDefs
import UgpLean.Classification.Bounds
import UgpLean.Classification.TheoremA
import UgpLean.Classification.TheoremB
import UgpLean.Classification.RSUC
import UgpLean.Compute.DecidablePredicates

/-!
# UgpLean.Classification.FormalRSUC — Pure Formal RSUC + Interpretation

RSUC in two layers:
1. **RSUC_formal**: Unconditional classification for (SF₀, QL₀, RA₀)
2. **Interpretation**: Physics predicates imply formal predicates

Reference: Advisor recommendations (two-layer RSUC), Paper 25
-/

namespace UgpLean

/-- RSUC formal: For (SF₀, QL₀, RA₀), the residual is exactly the 6 mirror-dual triples. -/
theorem rsuc_formal (t : Triple) (h : SF₀ t ∧ QL₀ t ∧ RA₀ t) :
    t ∈ Residual ∧ (∀ u ∈ Residual, lexLt LeptonSeed u ∨ LeptonSeed = u) := by
  have hadm : UnifiedAdmissible t := ⟨h.1, h.2.1, (RelationalAnchorAt_10_iff t).mpr h.2.2⟩
  exact rsuc_theorem t hadm

/-- Canonical representative: for t ∈ Residual, canon(t) = LeptonSeed (the lex-min). -/
theorem canon_of_residual (t : Triple) (h : t ∈ Residual) :
    canon t = LeptonSeed := by
  rw [theoremB] at h
  simp only [Candidates, Finset.mem_insert, Finset.mem_singleton] at h
  unfold canon leptonB leptonC1 mirrorC1 LeptonSeed
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals native_decide

/-- RSUC with canonical representative: for all admissible t, canon(t) = LeptonSeed. -/
theorem rsuc_canon (t : Triple) (h : UnifiedAdmissible t) : canon t = LeptonSeed :=
  canon_of_residual t (Finset.mem_filter.mpr ⟨theoremA t h, (decUnifiedAdmissible_correct t).mpr h⟩)

end UgpLean
