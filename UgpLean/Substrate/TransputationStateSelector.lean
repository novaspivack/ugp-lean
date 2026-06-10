import Mathlib.Tactic
import Mathlib.Algebra.BigOperators.Fin
import Mathlib.Data.Complex.Basic
import UgpLean.Substrate.Substrate
import UgpLean.Substrate.CoherenceMeasure
import UgpLean.Substrate.PSCPreservingTransformation
import UgpLean.Substrate.QECStabilizer
import UgpLean.Universality.BornRuleMDL
import UgpLean.Universality.BeableWindingPartitionInstance

/-!
# Transputation State Selector

Operational form of transputation $\mathbb{P}^\top$ on P34's $[D]$-class axioms:

$$\mathbb{P}^\top_D(w) := \arg\min_{\rho \in \mathcal{R}(A)} D(\rho \mid w).$$

The selector role is carried by **D3 ∧ D4 ∧ D5** (not D3 alone). D4 supplies unique
minimizer existence; D5 supplies Born-consistent sector marginals at the minimum; D3
(non-effectiveness) is certified via the TPC-above-decidable proxy from the QEC bridge.

## Proved (zero sorry, CatAL conditional on $[D]$-class axioms)

- `TransputationSelectorExists` — unique argmin $\rho^*$ (D4)
- `transputation_is_state_selector` — $\rho^*$ has Born marginals and partitions unity (D5)
- `transputation_state_selector_bundle` — master conjunction
- `two_function_picture` — $\mathbb{P}(\text{outcome}=k \mid w) = (\mathcal{B}\circ \mathbb{P}^\top_D)(w)_k$

No new physics axioms beyond P34's existing $[D]$ programme: D4 and D5 enter as
fields of `DClass`; D2 reuses `d2_universal`; D3 reuses `d3_tpc_above_decidable`.

Conditional on Conjecture C2 (unique physical $D \in [D]$): selector family collapses
to a single function — tracked as Rank C2-CLOSURE.
-/

namespace UgpLean.Substrate

open UgpLean.Universality.BornRuleMDL
open UgpLean.Universality.BeableWindingPartitionInstance
open UgpLean.Substrate.QEC
open GUTStructure TPCPowerClass DUniqueness
open scoped BigOperators

variable {S : Substrate}

-- ════════════════════════════════════════════════════════════════
-- §1  D4 — unique coherence minimizer (selection completeness)
-- ════════════════════════════════════════════════════════════════

/-- $\rho$ minimizes coherence **[D]** relative to record $w$. -/
def IsCoherenceMinimizer (ρ w : S.config) : Prop :=
  ∀ ρ' : S.config, S.coherence ρ' w ≥ S.coherence ρ w

/-- **D4 (P34 §6):** for every record class $w$, **[D]** achieves a unique minimum. -/
def SatisfiesD4 (S : Substrate) : Prop :=
  ∀ w : S.config, ∃! ρ, IsCoherenceMinimizer (S := S) ρ w

/-- Alias for rank-board reporting (D4 selector well-definedness). -/
abbrev TransputationSelectorExistsProp (S : Substrate) : Prop := SatisfiesD4 S

-- ════════════════════════════════════════════════════════════════
-- §2  Born-sector interface for D5 at the selected state
-- ════════════════════════════════════════════════════════════════

/-- Sector amplitude data on substrate configurations (kink-basis coefficients). -/
structure BornSectorInterface (S : Substrate) where
  coeffs : S.config → Fin 7 → ℂ
  sectorProb : S.config → Fin 7 → ℝ
  born_eq : ∀ ρ k, sectorProb ρ k = Complex.normSq (coeffs ρ k)

/-- **D5 (P34 §6):** at a coherence minimizer, sector marginals equal $|c_k|^2$. -/
def SatisfiesD5 (S : Substrate) (born : BornSectorInterface S) : Prop :=
  ∀ ρ w, IsCoherenceMinimizer (S := S) ρ w →
    (∀ k : Fin 7, born.sectorProb ρ k = Complex.normSq (born.coeffs ρ k)) ∧
    ((Finset.univ : Finset (Fin 7)).sum (born.sectorProb ρ) = 1)

-- ════════════════════════════════════════════════════════════════
-- §3  [D]-class bundle (D1–D5 on substrate)
-- ════════════════════════════════════════════════════════════════

/-- A member of P34's $[D]$-class: bundles D1–D5 axioms on substrate `S`. -/
structure DClass (S : Substrate) where
  d1_nonneg : ∀ ρ w, 0 ≤ S.coherence ρ w
  d2_psc_invariant : ∀ (_hS : S.psc_consistent) (f : S.config → S.config),
    IsPSCPreserving f → ∀ ρ w, S.coherence (f ρ) (f w) = S.coherence ρ w
  d4_unique_min : SatisfiesD4 S
  born : BornSectorInterface S
  d5_born_marginals : SatisfiesD5 S born
  d5_normalized_at_min : ∀ ρ w, IsCoherenceMinimizer (S := S) ρ w →
    (Finset.univ : Finset (Fin 7)).sum (fun k => Complex.normSq (born.coeffs ρ k)) = 1

/-- **Operational transputation selector** $\mathbb{P}^\top_D(w) := \arg\min_\rho D(\rho\mid w)$. -/
noncomputable def transputation (D : DClass S) (w : S.config) : S.config :=
  (D.d4_unique_min w).choose

theorem transputation_is_minimizer (D : DClass S) (w : S.config) :
    IsCoherenceMinimizer (S := S) (transputation D w) w :=
  (D.d4_unique_min w).choose_spec.1

theorem transputation_minimizer_unique (D : DClass S) (w : S.config) (ρ : S.config)
    (h : IsCoherenceMinimizer (S := S) ρ w) : ρ = transputation D w :=
  (D.d4_unique_min w).choose_spec.2 ρ h

/-- **TransputationSelectorExists** (D4, CatAL conditional):
    for every record $w$, a unique coherence minimizer $\rho^*$ exists. -/
theorem TransputationSelectorExists (D : DClass S) (w : S.config) :
    ∃! ρ, IsCoherenceMinimizer (S := S) ρ w :=
  D.d4_unique_min w

theorem transputation_eq_unique_min (D : DClass S) (w : S.config) :
    transputation D w = (D.d4_unique_min w).choose :=
  rfl

/-- Composed outcome probability $(\mathcal{B}\circ \mathbb{P}^\top_D)(w)_k$. -/
noncomputable def composedOutcomeProb (D : DClass S) (w : S.config) (k : Fin 7) : ℝ :=
  D.born.sectorProb (transputation D w) k

/-- **Born rule** $\mathcal{B}$ as the squared-modulus map on sector coefficients. -/
def bornRule (coeffs : Fin 7 → ℂ) (k : Fin 7) : ℝ :=
  Complex.normSq (coeffs k)

/-- **two_function_picture** (CatAL conditional):
    measurement outcome probabilities factor as Born rule applied to the
    transputation-selected state:
    $\mathbb{P}(\text{outcome}=k\mid w) = (\mathcal{B}\circ \mathbb{P}^\top_D)(w)_k$. -/
theorem two_function_picture (D : DClass S) (w : S.config) (k : Fin 7) :
    composedOutcomeProb D w k = bornRule (D.born.coeffs (transputation D w)) k := by
  unfold composedOutcomeProb bornRule
  exact D.born.born_eq (transputation D w) k

/-- **transputation_is_state_selector** (D5, CatAL conditional):
    the transputation-selected state has Born-distributed sector marginals summing to 1,
    and the selector lies in the transputation layer (D3 proxy: TPC above decidable). -/
theorem transputation_is_state_selector (D : DClass S) (w : S.config) :
    let ρ := transputation D w
    (∀ k : Fin 7, D.born.sectorProb ρ k = Complex.normSq (D.born.coeffs ρ k)) ∧
    ((Finset.univ : Finset (Fin 7)).sum (D.born.sectorProb ρ) = 1) ∧
    (level_decidable < level_tpc) := by
  dsimp
  have hmin : IsCoherenceMinimizer (S := S) (transputation D w) w :=
    transputation_is_minimizer D w
  have hborn := D.d5_born_marginals (transputation D w) w hmin
  exact ⟨hborn.1, hborn.2, d3_tpc_above_decidable⟩

/-- **transputation_state_selector_bundle** (master, CatAL conditional):
    packages D4 unique selection, operational $\mathbb{P}^\top_D$, Born composition, and D3. -/
theorem transputation_state_selector_bundle (D : DClass S) (w : S.config) :
    (∃! ρ, IsCoherenceMinimizer (S := S) ρ w) ∧
    IsCoherenceMinimizer (S := S) (transputation D w) w ∧
    (∀ k : Fin 7,
      composedOutcomeProb D w k = Complex.normSq (D.born.coeffs (transputation D w) k)) ∧
    ((Finset.univ : Finset (Fin 7)).sum (composedOutcomeProb D w) = 1) ∧
    (level_decidable < level_tpc) ∧
    (n_d_constraints = 5) := by
  have hborn := D.d5_born_marginals (transputation D w) w (transputation_is_minimizer D w)
  refine ⟨D.d4_unique_min w, transputation_is_minimizer D w, ?_, hborn.2, ?_, ?_⟩
  · intro k; exact two_function_picture D w k
  · exact d3_tpc_above_decidable
  · exact d5_is_fifth_constraint

-- ════════════════════════════════════════════════════════════════
-- §4  D2 re-export and abstract Born ∘ selector typing
-- ════════════════════════════════════════════════════════════════

/-- D2 on a `DClass` member: PSC-preserving maps leave [D] invariant. -/
theorem dclass_d2_psc_invariant (D : DClass S) (hS : S.psc_consistent)
    (f : S.config → S.config) (hf : IsPSCPreserving f) (ρ w : S.config) :
    S.coherence (f ρ) (f w) = S.coherence ρ w :=
  D.d2_psc_invariant hS f hf ρ w

/-- Abstract **Born ∘ Transputation** functional: record → sector probability vector. -/
noncomputable def bornAfterTransputation (D : DClass S) (w : S.config) : Fin 7 → ℝ :=
  fun k => composedOutcomeProb D w k

theorem born_after_transputation_eq_born_rule (D : DClass S) (w : S.config) (k : Fin 7) :
    bornAfterTransputation D w k = bornRule (D.born.coeffs (transputation D w)) k :=
  two_function_picture D w k

-- ════════════════════════════════════════════════════════════════
-- §5  Concrete composition with unconditional Born rule (76-BORN-UNCOND)
-- ════════════════════════════════════════════════════════════════

section BeableBornComposition

/-- For any normalized coefficient vector, the Born rule produces sector probabilities
    matching $|c_k|^2$. This is the $\mathcal{B}$ factor in the two-function picture;
    pairing with `transputation` supplies the $\mathbb{P}^\top$ factor. -/
theorem born_rule_composes_with_selector_coeffs (coeffs : Fin 7 → ℂ)
    (hnorm : (Finset.univ : Finset (Fin 7)).sum (fun w => Complex.normSq (coeffs w)) = 1)
    (k : Fin 7) :
    ∃ (h : BeableAmplitudeHypothesis),
      h.sectorProb k = Complex.normSq (coeffs k) ∧
      (Finset.univ : Finset (Fin 7)).sum h.sectorProb = 1 := by
  rcases born_rule_unconditional coeffs hnorm with ⟨h, hprob, hsum⟩
  exact ⟨h, hprob k, hsum⟩

/-- **Two-function beable witness:** given selector output coefficients `ρ*`, Born rule
    yields outcome probabilities $|c_k(\rho^*)|^2$ — the $\mathcal{B}\circ \mathbb{P}^\top$
    composition on the kink Hilbert space. -/
theorem two_function_beable_witness (selectedCoeffs : Fin 7 → ℂ)
    (hnorm : (Finset.univ : Finset (Fin 7)).sum
      (fun k => Complex.normSq (selectedCoeffs k)) = 1) (k : Fin 7) :
    ∃ (h : BeableAmplitudeHypothesis),
      h.sectorProb k = bornRule selectedCoeffs k ∧
      (Finset.univ : Finset (Fin 7)).sum h.sectorProb = 1 := by
  rcases born_rule_unconditional selectedCoeffs hnorm with ⟨h, hprob, hsum⟩
  exact ⟨h, by simpa [bornRule] using hprob k, hsum⟩

end BeableBornComposition

end UgpLean.Substrate
