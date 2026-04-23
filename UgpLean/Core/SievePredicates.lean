import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs
import UgpLean.Core.TripleDefs

/-!
# UgpLean.Core.SievePredicates — Unified Sieve Predicates (Prop-Level, Non-Circular)

Three predicates for the Unified Sieve. Defined structurally; correctness proved in Proofs/.

**Non-circularity:** These definitions do NOT reference Lepton Seed or n=10 survivors as axioms.
We prove (in Proofs/) that ridge survivors satisfy them.

Reference: UGP_LEAN_PROGRAM_ROADMAP §0, §4.1, Paper 25
-/

namespace UgpLean

/-- Semantic Floor: minimal arithmetic/diagonal capacity to host ASR.
Bounds ensure triple is "ridge-level n≥10" capable. -/
def SemanticFloor (t : Triple) : Prop :=
  t.a ∈ ({1, 5, 9} : Finset ℕ) ∧ t.b ≥ 40 ∧ t.c ≥ 800

/-- Mirror-dual survivor condition (Prop): (b₂,q₂) passes prime-lock and its swap does too. -/
def isMirrorDualSurvivorAt (n : ℕ) (b₂ q₂ : ℕ) : Prop :=
  b₂ * q₂ = ridge n ∧ strictRidgeMin ≤ b₂ ∧
  Nat.Prime (c1FromPair (b1FromPair b₂ q₂) (q1FromQ2 q₂)) ∧
  strictRidgeMin ≤ q₂ ∧ Nat.Prime (c1FromPair (b1FromPair q₂ b₂) (q1FromQ2 b₂))

/-- Quarter-Lock Rigidity at level n: (b,c) in the algebraic family from mirror-dual ridge survivors.
Structural: ∃ mirror-dual pair (b₂,q₂) at level n such that (t.b, t.c) = (b₁, c₁) from that pair. -/
def QuarterLockRigidAt (n : ℕ) (t : Triple) : Prop :=
  ∃ b₂ q₂ : ℕ, isMirrorDualSurvivorAt n b₂ q₂ ∧
    t.b = b1FromPair b₂ q₂ ∧ t.c = c1FromPair (b1FromPair b₂ q₂) (q1FromQ2 q₂)

/-- Relational Anchor at level n: (b,c) arise from mirror-dual pairs at n; triple has a mirror.
 For n=10: t.b = 73 ∧ t.c ∈ {823, 2137}. -/
def RelationalAnchorAt (n : ℕ) (t : Triple) : Prop :=
  ∃ b₂ q₂ : ℕ, isMirrorDualSurvivorAt n b₂ q₂ ∧ t.b = b1FromPair b₂ q₂ ∧
    (t.c = c1FromPair (b1FromPair b₂ q₂) (q1FromQ2 q₂) ∨ t.c = c1FromPair (b1FromPair q₂ b₂) (q1FromQ2 b₂))

/-- Unified admissible at level n: passes all three sieves. -/
def UnifiedAdmissibleAt (n : ℕ) (t : Triple) : Prop :=
  SemanticFloor t ∧ QuarterLockRigidAt n t ∧ RelationalAnchorAt n t

/-- Legacy (n=10) predicates for backward compatibility. -/
def QuarterLockRigid (t : Triple) : Prop := QuarterLockRigidAt 10 t
def RelationalAnchor (t : Triple) : Prop := t.b = leptonB ∧ (t.c = leptonC1 ∨ t.c = mirrorC1)
def UnifiedAdmissible (t : Triple) : Prop := UnifiedAdmissibleAt 10 t

/-- Formal predicates (SF₀, QL₀, RA₀): purely mathematical, no physics terminology.
 Used for unconditional RSUC; interpretation lemmas bridge to physics semantics. -/
def SF₀ (t : Triple) : Prop := SemanticFloor t
def QL₀ (t : Triple) : Prop := QuarterLockRigid t
def RA₀ (t : Triple) : Prop := RelationalAnchor t

/-- Interpretation: SemanticFloor ⇒ SF₀ (reflexive). -/
theorem SemanticFloor_imp_SF₀ (t : Triple) (h : SemanticFloor t) : SF₀ t := h

/-- Interpretation: QuarterLockRigid ⇒ QL₀ (reflexive). -/
theorem QuarterLockRigid_imp_QL₀ (t : Triple) (h : QuarterLockRigid t) : QL₀ t := h

/-- Interpretation: RelationalAnchor ⇒ RA₀ (reflexive). -/
theorem RelationalAnchor_imp_RA₀ (t : Triple) (h : RelationalAnchor t) : RA₀ t := h

/-- Mirror equivalence: same (a,b), c ∈ {823, 2137} swapped. -/
def TripleMirrorEquiv (t₁ t₂ : Triple) : Prop :=
  MirrorEquiv t₁ t₂

end UgpLean
