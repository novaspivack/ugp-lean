import UgpLean.Core.TripleDefs
import UgpLean.Core.MirrorDefs
import UgpLean.Core.SievePredicates
import UgpLean.Classification.Bounds
import UgpLean.Compute.Sieve
import UgpLean.Compute.DecidablePredicates

/-!
# UgpLean.Classification.TheoremA — Structural Reduction

For any n, if t satisfies UnifiedAdmissibleAt n, then t ∈ CandidatesAt n.
At n=10 this yields the classical Theorem A.

Reference: UGP_LEAN_PROGRAM_ROADMAP §3.1
-/

namespace UgpLean

/-- Theorem A (n=10): Any unified-admissible triple lies in the 6-element candidate family. -/
theorem theoremA (t : Triple) (h : UnifiedAdmissible t) : t ∈ Candidates := by
  simp only [UnifiedAdmissible] at h
  obtain ⟨ha, _, hRA⟩ := h
  obtain ⟨hb, hc⟩ := (RelationalAnchorAt_10_iff t).mp hRA
  have ha' : t.a = 1 ∨ t.a = 5 ∨ t.a = 9 := by
    have := ha.1
    simp only [Finset.mem_insert, Finset.mem_singleton] at this
    exact this
  rcases ha' with ha1 | ha2 | ha3
  · rcases hc with hc1 | hc2
    · rw [@Triple.ext t ⟨1, leptonB, leptonC1⟩ ha1 hb hc1]; simp only [Candidates, Finset.mem_insert, Finset.mem_singleton]; native_decide
    · rw [@Triple.ext t ⟨1, leptonB, mirrorC1⟩ ha1 hb hc2]; simp only [Candidates, Finset.mem_insert, Finset.mem_singleton]; native_decide
  · rcases hc with hc1 | hc2
    · rw [@Triple.ext t ⟨5, leptonB, leptonC1⟩ ha2 hb hc1]; simp only [Candidates, Finset.mem_insert, Finset.mem_singleton]; native_decide
    · rw [@Triple.ext t ⟨5, leptonB, mirrorC1⟩ ha2 hb hc2]; simp only [Candidates, Finset.mem_insert, Finset.mem_singleton]; native_decide
  · rcases hc with hc1 | hc2
    · rw [@Triple.ext t ⟨9, leptonB, leptonC1⟩ ha3 hb hc1]; simp only [Candidates, Finset.mem_insert, Finset.mem_singleton]; native_decide
    · rw [@Triple.ext t ⟨9, leptonB, mirrorC1⟩ ha3 hb hc2]; simp only [Candidates, Finset.mem_insert, Finset.mem_singleton]; native_decide

/-- Theorem A (general): Any unified-admissible triple at level n lies in the candidate family.
For n=10, follows from theoremA; for other n, structural reduction via biUnion. -/
theorem theoremA_general (n : ℕ) (t : Triple) (h : UnifiedAdmissibleAt n t) : t ∈ CandidatesAt n := by
  by_cases hn : n = 10
  · subst hn
    rw [CandidatesAt_10_eq]
    exact theoremA t h
  · obtain ⟨⟨ha, _hb, _hc⟩, ⟨b₂, q₂, hsurv, hb, hc⟩, _⟩ := h
    rw [isMirrorDualSurvivorAt_iff] at hsurv
    rw [CandidatesAt, Finset.mem_biUnion]
    use (b₂, q₂)
    constructor
    · exact hsurv
    · have ha' : t.a = 1 ∨ t.a = 5 ∨ t.a = 9 := by
        simp only [Finset.mem_insert, Finset.mem_singleton] at ha; exact ha
      rcases ha' with ha1 | ha2 | ha3
      · exact Finset.mem_insert.mpr (Or.inl (@Triple.ext t _ ha1 hb hc))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (@Triple.ext t _ ha2 hb hc))))))
      · exact Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inr (Finset.mem_insert.mpr (Or.inl (@Triple.ext t _ ha3 hb hc))))))))))

end UgpLean
