import UgpLean.Core.TripleDefs
import UgpLean.Core.SievePredicates
import UgpLean.Classification.TheoremB
import UgpLean.Classification.RSUC

/-!
# UgpLean.Instance.NemSBridge — NEMS Paper 25 Bridge

Exposes the GTESpace triple type, UnifiedAdmissible, and RSUC for nems-lean.

Reference: PAPER_25_UPGRADE_PLAN §II, UGP_LEAN_PROGRAM_ROADMAP §2.5
-/

namespace UgpLean

/-- Triple type for GTE (used by Paper 25). -/
abbrev GTESpace := Triple

/-- Re-export RSUC for Paper 25 citation. -/
theorem rsuc : ∀ t : GTESpace, UnifiedAdmissible t →
    t ∈ Residual ∧ (∀ u ∈ Residual, lexLt LeptonSeed u ∨ LeptonSeed = u) :=
  rsuc_theorem

end UgpLean
