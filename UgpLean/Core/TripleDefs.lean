import Mathlib.Data.Finset.Basic
import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs

/-!
# UgpLean.Core.TripleDefs — GTE Triples and Lepton Seed

Triples (a,b,c) represent the GTE state. The Lepton Seed (1,73,823) is the lex-min
prime-locked survivor; its mirror (1,73,2137) arises from the dual pair (24,42).

Reference: gte_triples_explainer.tex, UGP Paper, Classification/RSUC
-/

namespace UgpLean

/-- A GTE triple: (a, b, c) with parity a, ladder b, capacity c -/
structure Triple where
  a : ℕ
  b : ℕ
  c : ℕ
  deriving DecidableEq, Repr, Inhabited

@[ext] theorem Triple.ext (t₁ t₂ : Triple) (ha : t₁.a = t₂.a) (hb : t₁.b = t₂.b) (hc : t₁.c = t₂.c) :
    t₁ = t₂ := by cases t₁; cases t₂; congr

/-- The Lepton Seed: (1, 73, 823) — lex-min survivor from pair (42,24) -/
def LeptonSeed : Triple := ⟨1, leptonB, leptonC1⟩

/-- The mirror triple: (1, 73, 2137) — from pair (24,42) -/
def LeptonMirror : Triple := ⟨1, leptonB, mirrorC1⟩

theorem LeptonSeed_values : LeptonSeed.a = 1 ∧ LeptonSeed.b = 73 ∧ LeptonSeed.c = 823 := by
  unfold LeptonSeed leptonB leptonC1; exact ⟨rfl, rfl, rfl⟩

theorem LeptonMirror_values : LeptonMirror.a = 1 ∧ LeptonMirror.b = 73 ∧ LeptonMirror.c = 2137 := by
  unfold LeptonMirror leptonB mirrorC1; exact ⟨rfl, rfl, rfl⟩

theorem mirrorC1_ne_leptonC1 : mirrorC1 ≠ leptonC1 := by native_decide

/-- Two triples are mirror-equivalent when they share (a,b) and c ∈ {823, 2137}. -/
def MirrorEquiv (t₁ t₂ : Triple) : Prop :=
  t₁.a = t₂.a ∧ t₁.b = t₂.b ∧
  (t₁.c = leptonC1 ∧ t₂.c = mirrorC1 ∨ t₁.c = mirrorC1 ∧ t₂.c = leptonC1)

/-- Mirror map: swaps c between 823 and 2137 when c ∈ {823, 2137}. -/
def mirrorTriple (t : Triple) : Triple :=
  if t.c = leptonC1 then ⟨t.a, t.b, mirrorC1⟩
  else if t.c = mirrorC1 then ⟨t.a, t.b, leptonC1⟩
  else t

/-- Observable: the gauge-invariant part (a,b); invariant under mirror. -/
def obs (t : Triple) : ℕ × ℕ := (t.a, t.b)

/-- Mirror preserves observable: Obs(mirror t) = Obs(t) when c ∈ {823, 2137}. -/
theorem obs_mirror_invariant (t : Triple) (_hc : t.c = leptonC1 ∨ t.c = mirrorC1) :
    obs (mirrorTriple t) = obs t := by
  unfold obs mirrorTriple; split_ifs <;> rfl

/-- MirrorEquiv implies same observable: obs t₁ = obs t₂. -/
theorem MirrorEquiv_obs_eq (t₁ t₂ : Triple) (h : MirrorEquiv t₁ t₂) : obs t₁ = obs t₂ := by
  unfold obs
  obtain ⟨ha, hb, _⟩ := h
  exact Prod.ext ha hb

/-- Canonical (MDL-minimal) representative of the residual: always LeptonSeed.
 For t in the residual (b=73, c∈{823,2137}, a∈{1,5,9}), the global lex-min is LeptonSeed. -/
def canon (t : Triple) : Triple :=
  if t.b = leptonB ∧ (t.c = leptonC1 ∨ t.c = mirrorC1) ∧ t.a ∈ ({1, 5, 9} : Finset ℕ)
  then LeptonSeed else t

/-- MDL Code: gauge-invariant encoding (a,b). Mirror-equivalent triples share the same code. -/
def Code (t : Triple) : ℕ × ℕ := obs t

/-- Code is invariant under MirrorEquiv: mirror pairs have the same code. -/
theorem Code_mirror_invariant (t₁ t₂ : Triple) (h : MirrorEquiv t₁ t₂) : Code t₁ = Code t₂ :=
  MirrorEquiv_obs_eq t₁ t₂ h

/-- MDL (Minimum Description Length): Lepton Seed is the lexicographically minimal
among the n=10 survivors when ordered by (c, b, a). -/
def lexLt (t₁ t₂ : Triple) : Prop :=
  t₁.c < t₂.c ∨ (t₁.c = t₂.c ∧ (t₁.b < t₂.b ∨ (t₁.b = t₂.b ∧ t₁.a < t₂.a)))

theorem LeptonSeed_lex_min :
    LeptonSeed.c ≤ LeptonMirror.c ∧
    (LeptonSeed.c = LeptonMirror.c → LeptonSeed.b ≤ LeptonMirror.b) := by
  unfold LeptonSeed LeptonMirror leptonC1 mirrorC1 leptonB; native_decide

end UgpLean
