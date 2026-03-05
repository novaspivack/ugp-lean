import UgpLean.Classification.RSUC
import UgpLean.Instance.NemSBridge

/-!
# UgpLean.Papers.Paper25 — NEMS Paper 25 Citable Stubs

Citable linking for Paper 25 (Unified Rigidity).
Each theorem references the actual Lean theorem.

Reference: NEMS_PAPERS/25_Unified_Rigidity/Unified_Rigidity.tex
-/

namespace UgpLean.Paper25

/-- Paper 25, RSUC: Under the Unified Sieve, the residual set equals the 6 mirror-dual triples
and MDL selects the Lepton Seed. See `UgpLean.rsuc_theorem`. -/
theorem rsuc : ∀ t : GTESpace, UnifiedAdmissible t →
    t ∈ Residual ∧ (∀ u ∈ Residual, lexLt LeptonSeed u ∨ LeptonSeed = u) :=
  rsuc_theorem

end UgpLean.Paper25
