import UgpLean.Core.TripleDefs
import UgpLean.GTE.Evolution

/-!
# UgpLean.GTE.Orbit — Canonical 3-Step Orbit

The canonical lepton orbit at n=10:
(1,73,823) → (9,42,1023) → (5,275,65535).

Reference: gte_triples_explainer.tex §3, UGP Main Paper
-/

namespace UgpLean

/-- The three triples of the canonical orbit. -/
def canonicalOrbit : List Triple :=
  [LeptonSeed, canonicalGen2, canonicalGen3]

/-- Canonical orbit has 3 elements. -/
theorem canonicalOrbit_length : canonicalOrbit.length = 3 := rfl

/-- First element is Lepton Seed. -/
theorem canonicalOrbit_head : canonicalOrbit.head! = LeptonSeed := rfl

/-- The orbit encodes the three lepton generations (e, μ, τ). -/
theorem canonical_orbit_three_steps :
    LeptonSeed.a = 1 ∧ LeptonSeed.b = 73 ∧ LeptonSeed.c = 823 ∧
    canonicalGen2.a = 9 ∧ canonicalGen2.b = 42 ∧ canonicalGen2.c = 1023 ∧
    canonicalGen3.a = 5 ∧ canonicalGen3.b = 275 ∧ canonicalGen3.c = 65535 := by
  unfold LeptonSeed canonicalGen2 canonicalGen3 leptonB leptonC1
  exact ⟨rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl, rfl⟩

/-- Canonical orbit: LeptonSeed → canonicalGen2 → canonicalGen3. -/
theorem canonical_orbit_def : canonicalOrbit = [LeptonSeed, canonicalGen2, canonicalGen3] := rfl

end UgpLean
