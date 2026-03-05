import UgpLean.Core.TripleDefs
import UgpLean.Core.MirrorDefs
import UgpLean.Core.SievePredicates
import UgpLean.Classification.Bounds
import UgpLean.Compute.DecidablePredicates
import UgpLean.Compute.Sieve

/-!
# UgpLean.Classification.TheoremB — Finite Classification

Residual = Candidates.filter decUnifiedAdmissible equals the 6 triples; MDL selects LeptonSeed.
ResidualAt n generalizes to arbitrary ridge level n.

Reference: UGP_LEAN_PROGRAM_ROADMAP §3.2, §1.4
-/

namespace UgpLean

/-- For t ∈ CandidatesAt n, QuarterLockRigidAt and RelationalAnchorAt hold by construction (from the
  survivor pair); only SemanticFloor varies. So UnifiedAdmissibleAt n t ↔ SemanticFloor t. -/
theorem mem_CandidatesAt_imp_sieve (n : ℕ) (t : Triple) (h : t ∈ CandidatesAt n) :
    UnifiedAdmissibleAt n t ↔ SemanticFloor t := by
  constructor
  · intro ⟨hSF, _, _⟩; exact hSF
  · intro hSF
    rw [CandidatesAt, Finset.mem_biUnion] at h
    obtain ⟨p, hp, ht⟩ := h
    have hsurv := (isMirrorDualSurvivorAt_iff n p.1 p.2).mpr hp
    have hsurv' : isMirrorDualSurvivorAt n p.2 p.1 := by
      rw [isMirrorDualSurvivorAt_iff]
      rw [ridgeSurvivorsFinset, Finset.mem_filter] at hp ⊢
      obtain ⟨h1, h2⟩ := hp
      exact ⟨h2, h1⟩
    rw [Finset.mem_insert, Finset.mem_insert, Finset.mem_insert, Finset.mem_insert,
      Finset.mem_insert, Finset.mem_singleton] at ht
    rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    · exact ⟨hSF, ⟨p.1, p.2, hsurv, rfl, rfl⟩, ⟨p.1, p.2, hsurv, rfl, Or.inl rfl⟩⟩
    · exact ⟨hSF, ⟨p.2, p.1, hsurv', by simp only [b1FromPair, add_comm], rfl⟩, ⟨p.1, p.2, hsurv, rfl, Or.inr rfl⟩⟩
    · exact ⟨hSF, ⟨p.1, p.2, hsurv, rfl, rfl⟩, ⟨p.1, p.2, hsurv, rfl, Or.inl rfl⟩⟩
    · exact ⟨hSF, ⟨p.2, p.1, hsurv', by simp only [b1FromPair, add_comm], rfl⟩, ⟨p.1, p.2, hsurv, rfl, Or.inr rfl⟩⟩
    · exact ⟨hSF, ⟨p.1, p.2, hsurv, rfl, rfl⟩, ⟨p.1, p.2, hsurv, rfl, Or.inl rfl⟩⟩
    · exact ⟨hSF, ⟨p.2, p.1, hsurv', by simp only [b1FromPair, add_comm], rfl⟩, ⟨p.1, p.2, hsurv, rfl, Or.inr rfl⟩⟩

/-- Residual at level n: candidates at n that pass the unified sieve. At n=10 equals Residual. -/
def ResidualAt (n : ℕ) : Finset Triple :=
  (CandidatesAt n).filter (fun t => decSemanticFloor t = true)

/-- Residual set: candidates that pass all three sieves. -/
def Residual : Finset Triple :=
  Candidates.filter (fun t => decUnifiedAdmissible t = true)

/-- For t ∈ Candidates, decUnifiedAdmissible t = decSemanticFloor t (QuarterLock and RelationalAnchor
  hold for the 6 triples). -/
theorem decUnifiedAdmissible_of_mem_Candidates (t : Triple) (h : t ∈ Candidates) :
    decUnifiedAdmissible t = decSemanticFloor t := by
  simp only [Candidates, Finset.mem_insert, Finset.mem_singleton] at h
  rcases h with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  all_goals native_decide

/-- At n=10, ResidualAt equals Residual. -/
theorem ResidualAt_10_eq_Residual : ResidualAt 10 = Residual := by
  rw [ResidualAt, Residual, CandidatesAt_10_eq]
  ext t
  simp only [Finset.mem_filter]
  constructor
  · intro ⟨hC, hdec⟩
    refine ⟨hC, ?_⟩
    rw [decUnifiedAdmissible_of_mem_Candidates t hC]; exact hdec
  · intro ⟨hC, hdec⟩
    refine ⟨hC, ?_⟩
    rw [← decUnifiedAdmissible_of_mem_Candidates t hC]; exact hdec

/-- Theorem B: Residual equals the 6 mirror-dual triples. -/
theorem theoremB : Residual = Candidates := by
  ext t
  simp only [Residual, Candidates, Finset.mem_filter]
  constructor
  · intro h; exact h.1
  · intro ht
    have hmem := ht
    simp only [Finset.mem_insert, Finset.mem_singleton] at ht
    refine ⟨hmem, ?_⟩
    rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
      ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
    all_goals native_decide

/-- MDL selects LeptonSeed: it is the lex-min in Residual. -/
theorem mdl_selects_LeptonSeed : ∀ t ∈ Residual, lexLt LeptonSeed t ∨ LeptonSeed = t := by
  rw [theoremB]
  intro t ht
  simp only [Candidates, Finset.mem_insert, Finset.mem_singleton] at ht
  rcases ht with ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ |
    ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩ | ⟨rfl, rfl, rfl⟩
  · right; rfl
  · left; unfold lexLt; native_decide
  · left; unfold lexLt; native_decide
  · left; unfold lexLt; native_decide
  · left; unfold lexLt; native_decide
  · left; unfold lexLt; native_decide

end UgpLean
