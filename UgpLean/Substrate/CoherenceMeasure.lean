import UgpLean.Substrate.Substrate
import UgpLean.Substrate.PSCPreservingTransformation

/-!
# Coherence Measure [D] — Rank 070-107 Phase 1

Encodes P34 §6 **D2** (Presentation Invariance at configuration space):
any PSC-preserving transformation leaves the coherence measure **[D]** invariant.

## Axioms

| Name | Content | Source |
|---|---|---|
| `d2_universal` | `IsPSCPreserving f → D(fρ, fw) = D(ρ, w)` | P34 §6 D2 universal form |

Phase 2 connects `IsPSCPreserving` to Lagrangian content; the D2 axiom statement is permanent.
-/

namespace UgpLean.Substrate

variable {S : Substrate}

/-- **Axiom (P34 §6 D2 — universal form):** Any PSC-preserving map on configurations
    leaves the coherence measure **[D]** invariant.

    This is Presentation Invariance at the configuration-space level: observables
    selected by [D] are invariant under all transformations preserving PSC structure.

    The substantive content that Lorentz boosts are PSC-preserving is Lemma 2
    (`PSCStructureLorentzPreserved.lean`, Phase 2). -/
axiom d2_universal (hS : S.psc_consistent) (f : S.config → S.config)
    (hf : IsPSCPreserving f) :
  ∀ ρ w : S.config, S.coherence (f ρ) (f w) = S.coherence ρ w

/-- Sanity check: D2 applied to the identity map (zero sorry). -/
theorem d2_universal_id (hS : S.psc_consistent) (ρ w : S.config) :
    S.coherence (id ρ) (id w) = S.coherence ρ w :=
  d2_universal hS id id_is_psc_preserving ρ w

end UgpLean.Substrate
