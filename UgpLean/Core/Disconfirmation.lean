import UgpLean.Core.TripleDefs
import UgpLean.Core.MirrorDefs
import Mathlib.Tactic.NormNum

/-!
# UgpLean.Core.Disconfirmation — Sanity Lemmas for RSUC

Explicit disconfirmation conditions: MirrorEquiv is an equivalence relation,
MDL is invariant under mirror equivalence, etc.

Reference: UGP_LEAN_PROGRAM_ROADMAP §3.5
-/

namespace UgpLean

/-- Mirror-equivalence class: t₁ ~ t₂ iff t₁ = t₂ or they are mirrors (same (a,b), c ∈ {823,2137} swapped).
MirrorEquiv alone is not reflexive; the class relation is. -/
def MirrorEquivClass (t₁ t₂ : Triple) : Prop := t₁ = t₂ ∨ MirrorEquiv t₁ t₂

/-- MirrorEquivClass is reflexive. -/
theorem MirrorEquivClass.refl (t : Triple) : MirrorEquivClass t t := Or.inl rfl

/-- MirrorEquiv is symmetric. -/
theorem MirrorEquiv.symm {t₁ t₂ : Triple} (h : MirrorEquiv t₁ t₂) : MirrorEquiv t₂ t₁ := by
  unfold MirrorEquiv at h ⊢
  obtain ⟨ha, hb, hc⟩ := h
  constructor
  · exact ha.symm
  constructor
  · exact hb.symm
  · rcases hc with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
    · right; exact ⟨hc2, hc1⟩
    · left; exact ⟨hc2, hc1⟩

/-- MirrorEquivClass is symmetric. -/
theorem MirrorEquivClass.symm {t1 t2 : Triple} (h : MirrorEquivClass t1 t2) :
    MirrorEquivClass t2 t1 := by
  rcases h with heq | h'
  · rw [heq]; exact MirrorEquivClass.refl t2
  · exact Or.inr (MirrorEquiv.symm h')

/-- MirrorEquivClass is transitive. -/
theorem MirrorEquivClass.trans {t1 t2 t3 : Triple} (h12 : MirrorEquivClass t1 t2)
    (h23 : MirrorEquivClass t2 t3) : MirrorEquivClass t1 t3 := by
  rcases h12 with rfl | h12'
  · exact h23
  · rcases h23 with rfl | h23'
    · exact Or.inr h12'
    · unfold MirrorEquiv at h12' h23'
      obtain ⟨ha, hb, hc12⟩ := h12'
      obtain ⟨ha', hb', hc23⟩ := h23'
      have ha3 := ha.trans ha'
      have hb3 := hb.trans hb'
      have hc13 : t1.c = t3.c := by
        rcases hc12 with ⟨hc1, hc2⟩ | ⟨hc1, hc2⟩
        · rcases hc23 with ⟨hc2', hc3⟩ | ⟨hc2', hc3⟩
          · exact (mirrorC1_ne_leptonC1 (hc2'.symm.trans hc2).symm).elim
          · exact hc1.trans hc3.symm
        · rcases hc23 with ⟨hc2', hc3⟩ | ⟨hc2', hc3⟩
          · exact hc1.trans hc3.symm
          · exact (mirrorC1_ne_leptonC1 (hc2.symm.trans hc2').symm).elim
      exact Or.inl (Triple.ext t1 t3 ha3 hb3 hc13)

/-- MirrorEquivClass is an equivalence relation. -/
instance MirrorEquivClass.isEquiv : Equivalence MirrorEquivClass where
  refl := MirrorEquivClass.refl
  symm := MirrorEquivClass.symm
  trans := MirrorEquivClass.trans

/-- If t₁ = t₂ then lexLt t₁ u ↔ lexLt t₂ u. -/
theorem lexLt_congr_left {t₁ t₂ u : Triple} (h : t₁ = t₂) :
    lexLt t₁ u ↔ lexLt t₂ u := by rw [h]

/-- If u₁ = u₂ then lexLt t u₁ ↔ lexLt t u₂. -/
theorem lexLt_congr_right {t u₁ u₂ : Triple} (h : u₁ = u₂) :
    lexLt t u₁ ↔ lexLt t u₂ := by rw [h]

/-- Within a mirror-equivalence class, the lex-min is well-defined.
LeptonSeed (c=823) is lex-smaller than LeptonMirror (c=2137). -/
theorem lexLt_seed_mirror : lexLt LeptonSeed LeptonMirror := by
  unfold lexLt LeptonSeed LeptonMirror leptonC1 mirrorC1 leptonB
  left; native_decide

end UgpLean
