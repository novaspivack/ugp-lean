import UgpLean.Core.TripleDefs
import UgpLean.Core.MirrorDefs
import UgpLean.Core.SievePredicates
import UgpLean.Compute.Sieve

/-!
# UgpLean.Compute.DecidablePredicates — Decidable Versions of Sieve Predicates

Bool/compute versions with correctness lemmas. Used for filtering in Theorem B.

Reference: UGP_LEAN_PROGRAM_ROADMAP §4.2, §4.1
-/

namespace UgpLean

/-- Decidable Semantic Floor. -/
def decSemanticFloor (t : Triple) : Bool :=
  t.a ∈ ({1, 5, 9} : Finset ℕ) && t.b ≥ 40 && t.c ≥ 800

/-- Decidable Quarter-Lock (for n=10: b=73, c∈{823,2137}). -/
def decQuarterLockRigid (t : Triple) : Bool :=
  t.b = leptonB && (t.c = leptonC1 || t.c = mirrorC1)

/-- Relational Anchor: t has a mirror partner (t.b=73, t.c∈{823,2137}). -/
def decRelationalAnchor (t : Triple) : Bool :=
  t.b = leptonB && (t.c = leptonC1 || t.c = mirrorC1)

/-- Decidable Unified Admissible. -/
def decUnifiedAdmissible (t : Triple) : Bool :=
  decSemanticFloor t && decQuarterLockRigid t && decRelationalAnchor t

/-- At n=10, RelationalAnchorAt matches the invariance form. -/
theorem RelationalAnchorAt_10_iff (t : Triple) :
    RelationalAnchorAt 10 t ↔ RelationalAnchor t := by
  constructor
  · intro ⟨b₂, q₂, hsurv, hb, hc⟩
    rw [isMirrorDualSurvivorAt_iff, ridgeSurvivors_10, Finset.mem_insert, Finset.mem_singleton] at hsurv
    rcases hsurv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · simp only [pair_24_42_values, pair_42_24_values, leptonC1, mirrorC1] at hb hc
      exact ⟨hb, Or.comm.mp hc⟩
    · simp only [pair_42_24_values, pair_24_42_values, leptonC1, mirrorC1] at hb hc
      exact ⟨hb, hc⟩
  · intro ⟨hb, hc⟩
    use 42, 24
    rw [isMirrorDualSurvivorAt_iff]
    refine ⟨mem_42_24, hb.trans (pair_42_24_values).1.symm, ?_⟩
    simp only [pair_42_24_values, pair_24_42_values, leptonC1, mirrorC1]
    exact hc

/-- QuarterLockRigidAt implies RelationalAnchorAt. -/
theorem QuarterLockRigidAt_imp_RelationalAnchorAt (n : ℕ) (t : Triple) (h : QuarterLockRigidAt n t) :
    RelationalAnchorAt n t := by
  obtain ⟨b₂, q₂, hsurv, hb, hc⟩ := h
  use b₂, q₂
  exact ⟨hsurv, hb, Or.inl hc⟩

/-- QuarterLockRigid implies RelationalAnchor: algebraic family triples satisfy b=73, c∈{823,2137}. -/
theorem QuarterLockRigid_imp_RelationalAnchor (t : Triple) (h : QuarterLockRigid t) :
    RelationalAnchor t := (RelationalAnchorAt_10_iff t).mp (QuarterLockRigidAt_imp_RelationalAnchorAt 10 t h)

theorem decSemanticFloor_correct (t : Triple) :
    decSemanticFloor t = true ↔ SemanticFloor t := by
  simp only [decSemanticFloor, SemanticFloor, Bool.and_eq_true, decide_eq_true_eq]
  constructor
  · intro ⟨⟨ha, hb⟩, hc⟩
    exact ⟨ha, hb, hc⟩
  · intro ⟨ha, hb, hc⟩
    exact ⟨⟨ha, hb⟩, hc⟩

theorem decRelationalAnchor_correct (t : Triple) :
    decRelationalAnchor t = true ↔ RelationalAnchor t := by
  simp only [decRelationalAnchor, RelationalAnchor, Bool.and_eq_true, Bool.or_eq_true, decide_eq_true_eq]

/-- RelationalAnchor implies existence of mirror partner (invariance form). -/
theorem RelationalAnchor_has_mirror (t : Triple) (h : RelationalAnchor t) :
    ∃ t', MirrorEquiv t t' := by
  obtain ⟨hb, hc⟩ := h
  rcases hc with heq | heq
  · exact ⟨⟨t.a, t.b, mirrorC1⟩, rfl, rfl, Or.inl ⟨heq, rfl⟩⟩
  · exact ⟨⟨t.a, t.b, leptonC1⟩, rfl, rfl, Or.inr ⟨heq, rfl⟩⟩

theorem decQuarterLockRigid_correct (t : Triple) :
    decQuarterLockRigid t = true ↔ QuarterLockRigid t := by
  simp only [decQuarterLockRigid, QuarterLockRigid, Bool.and_eq_true, Bool.or_eq_true,
    decide_eq_true_eq]
  constructor
  · intro ⟨hb, hc⟩
    rcases hc with heq | heq
    · use 42, 24
      refine ⟨(isMirrorDualSurvivorAt_10_iff _ _).mpr mem_42_24, ?_, ?_⟩
      · rw [(pair_42_24_values).1, ← (lepton_values).1]; exact hb
      · rw [(pair_42_24_values).1, (pair_42_24_values).2.1, (pair_42_24_values).2.2, ← (lepton_values).2.1]; exact heq
    · use 24, 42
      refine ⟨(isMirrorDualSurvivorAt_10_iff _ _).mpr mem_24_42, ?_, ?_⟩
      · rw [(pair_24_42_values).1, ← (lepton_values).1]; exact hb
      · rw [(pair_24_42_values).1, (pair_24_42_values).2.1, (pair_24_42_values).2.2, ← (lepton_values).2.2]; exact heq
  · intro ⟨b₂, q₂, hsurv, hb, hc⟩
    rw [isMirrorDualSurvivorAt_10_iff, ridgeSurvivors_10, Finset.mem_insert, Finset.mem_singleton] at hsurv
    rcases hsurv with ⟨rfl, rfl⟩ | ⟨rfl, rfl⟩
    · exact ⟨hb, Or.inr hc⟩
    · exact ⟨hb, Or.inl hc⟩

theorem decUnifiedAdmissible_correct (t : Triple) :
    decUnifiedAdmissible t = true ↔ UnifiedAdmissible t := by
  simp only [decUnifiedAdmissible, UnifiedAdmissible, UnifiedAdmissibleAt, Bool.and_eq_true]
  constructor
  · intro ⟨⟨h1, h2⟩, h3⟩
    exact ⟨(decSemanticFloor_correct t).mp h1, (decQuarterLockRigid_correct t).mp h2,
      (RelationalAnchorAt_10_iff t).mpr ((decRelationalAnchor_correct t).mp h3)⟩
  · intro ⟨h1, h2, h3⟩
    exact ⟨⟨(decSemanticFloor_correct t).mpr h1, (decQuarterLockRigid_correct t).mpr h2⟩,
      (decRelationalAnchor_correct t).mpr ((RelationalAnchorAt_10_iff t).mp h3)⟩

end UgpLean
