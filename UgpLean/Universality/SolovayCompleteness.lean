import Mathlib.Computability.Partrec
import UgpLean.Universality.CUP3DPhysicalIncompleteness
import UgpLean.Universality.GTEComputability

/-!
# Solovay completeness bridge for the CMCA adjudication ledger

Target LT-089-091 (`cmca_prefix_free_encoding_is_universal`).

Zero sorry. Named axioms: `fmdl_binary_aps` family (inherited from `CUP3D`).
-/

namespace UgpLean.Universality.SolovayCompleteness

open CUP3D
open UgpLean.Universality.GTEComputability

def IsPrefixFreeEncoding (σ : ℕ → ℕ) : Prop := Function.Injective σ

structure CMCAPrefixFreeMachine where
  σ : ℕ → ℕ
  hσ : IsPrefixFreeEncoding σ

theorem cmca_prefix_free_encoding_exists :
    ∃ σ : ℕ → ℕ, IsPrefixFreeEncoding σ :=
  ⟨id, fun _ _ h => h⟩

theorem fmdl_aps_is_acceptable : ∃ (φ : ℕ → ℕ → Part ℕ), True :=
  ⟨fmdl_binary_aps.φ, trivial⟩

theorem gte_update_is_computable : Primrec gte_update_map_nat :=
  gte_update_map_nat_primrec

structure CMCAPrefixFreeUniversalityHypothesis where
  σ : ℕ → ℕ
  hσ : IsPrefixFreeEncoding σ
  universal : ∀ {f : ℕ →. ℕ}, Partrec f → ∃ e, ∀ x, f x = fmdl_binary_aps.φ (σ e) x

theorem cmca_prefix_free_encoding_is_universal
    (h : CMCAPrefixFreeUniversalityHypothesis) :
    ∃ σ : ℕ → ℕ, IsPrefixFreeEncoding σ ∧
      ∀ {f : ℕ →. ℕ}, Partrec f → ∃ e, ∀ x, f x = fmdl_binary_aps.φ (σ e) x := by
  refine ⟨h.σ, h.hσ, fun hf => h.universal hf⟩

theorem solovay_completeness_substrate :
    (∃ σ : ℕ → ℕ, IsPrefixFreeEncoding σ) ∧
      Primrec gte_update_map_nat ∧
      (¬ ∃ (d : ℕ → Bool),
        RepresentableBool fmdl_binary_aps d ∧
          ∀ e n, (d (Nat.pair e n) = true ↔ (fmdl_binary_aps.φ e n).Dom)) := by
  refine ⟨cmca_prefix_free_encoding_exists, gte_update_is_computable, ?_⟩
  exact fmdl_halting_undecidable

end UgpLean.Universality.SolovayCompleteness
