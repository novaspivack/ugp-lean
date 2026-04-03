import UgpLean.Core.TripleDefs
import UgpLean.Core.MirrorDefs
import UgpLean.Core.SievePredicates
import UgpLean.Compute.Sieve

/-!
# UgpLean.Classification.Bounds — Explicit Candidate Family 𝒩

Bounded RSUC certification: at level n, candidates are (a, b₁, c) for a ∈ {1,5,9} and (b₁,c)
from mirror-dual survivor pairs at n. At n=10 this yields the 6 triples with b=73, c ∈ {823, 2137}.

Reference: PAPER_25_UPGRADE_PLAN, pipeline.py
-/

namespace UgpLean

/-- Candidates at level n: triples (a, b₁, c) where (b₂,q₂) ∈ ridgeSurvivorsFinset n,
  b₁ = b1FromPair b₂ q₂, c is either c₁ from (b₂,q₂) or (q₂,b₂), and a ∈ {1,5,9}. -/
def CandidatesAt (n : ℕ) : Finset Triple :=
  (ridgeSurvivorsFinset n).biUnion (fun p =>
    let b₁ := b1FromPair p.1 p.2
    let c1 := c1FromPair (b1FromPair p.1 p.2) (q1FromQ2 p.2)
    let c2 := c1FromPair (b1FromPair p.2 p.1) (q1FromQ2 p.1)
    {⟨1, b₁, c1⟩, ⟨1, b₁, c2⟩, ⟨5, b₁, c1⟩, ⟨5, b₁, c2⟩, ⟨9, b₁, c1⟩, ⟨9, b₁, c2⟩})

/-- The 6 candidate triples at n=10: (a, 73, c) for a ∈ {1,5,9}, c ∈ {823, 2137}. -/
def Candidates : Finset Triple :=
  {⟨1, leptonB, leptonC1⟩, ⟨1, leptonB, mirrorC1⟩, ⟨5, leptonB, leptonC1⟩,
   ⟨5, leptonB, mirrorC1⟩, ⟨9, leptonB, leptonC1⟩, ⟨9, leptonB, mirrorC1⟩}

/-- At n=10, CandidatesAt 10 matches the legacy Candidates definition. -/
theorem CandidatesAt_10_eq : CandidatesAt 10 = Candidates := by
  rw [Candidates, CandidatesAt, ridgeSurvivors_10]
  simp only [b1FromPair, q1FromQ2, c1FromPair,
    leptonB, leptonC1, mirrorC1, ugp1_s, ugp1_g, ugp1_t]
  native_decide

/-- Candidates equals CandidatesAt 10. -/
theorem Candidates_eq_CandidatesAt_10 : Candidates = CandidatesAt 10 :=
  (CandidatesAt_10_eq).symm

/-- Candidates has exactly 6 elements. -/
theorem Candidates_card : Candidates.card = 6 := by native_decide

end UgpLean
