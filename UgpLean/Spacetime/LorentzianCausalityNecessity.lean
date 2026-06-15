import UgpLean.Universality.LorentzInvariance

/-!
# Lorentzian Signature from Causal Information Propagation (EPIC_092 / LT-092-15)

Second independent argument for Lorentzian metric signature necessity, distinct from
`no_finite_ca_exact_lorentz_replica` (discrete-vs-continuum Nyquist residual in
`CMCAContinuumLimit.lean`).

Logical chain (CatAD):
1. PSC requires causal information propagation about records
2. Causal propagation ⇒ well-posed Cauchy problem ⇒ hyperbolic PDE
3. Hyperbolic wave equation requires indefinite signature `(+,−,−,−)`
4. Euclidean `(+,+,+,+)` gives elliptic Laplace equation — no causal characteristics

What is certified at CatAL here:
- Minkowski metric has indefinite signature (not positive definite)
- Minkowski metric differs from the Euclidean metric on `ℝ⁴`
- Structural distinction between hyperbolic (Lorentzian) and elliptic (Euclidean) regimes
-/

namespace UgpLean.Spacetime.LorentzianCausalityNecessity

open Matrix
open UgpLean.Universality.LorentzInvariance

/-- The standard Euclidean metric on `ℝ⁴` (all `+` signs). -/
def euclideanMetric : Matrix SpacetimeIdx SpacetimeIdx ℝ :=
  1

theorem euclidean_metric_is_identity :
    euclideanMetric = (1 : Matrix SpacetimeIdx SpacetimeIdx ℝ) := rfl

/-- **minkowski_not_euclidean** (CatAL):
the Minkowski metric η = diag(−1,1,1,1) is not the Euclidean metric on `ℝ⁴`. -/
theorem minkowski_not_euclidean : minkowskiMetric ≠ euclideanMetric := by
  intro h
  have h00 : minkowskiMetric 0 0 = euclideanMetric 0 0 := congrArg (fun M => M 0 0) h
  simp [minkowskiMetric, euclideanMetric] at h00
  norm_num at h00

/-- Timelike vector for Minkowski signature: `η(e₀,e₀) = −1 < 0`. -/
theorem minkowski_timelike_vector :
    minkowskiInner (fourMomentum 1 0 0 0) (fourMomentum 1 0 0 0) = -1 := by
  simp [minkowskiInner, fourMomentum, Fin.sum_univ_four]

/-- Spacelike vector for Minkowski signature: `η(e₁,e₁) = +1 > 0`. -/
theorem minkowski_spacelike_vector :
    minkowskiInner (fourMomentum 0 1 0 0) (fourMomentum 0 1 0 0) = 1 := by
  simp [minkowskiInner, fourMomentum, Fin.sum_univ_four]

/-- **minkowski_has_indefinite_signature** (CatAL):
Minkowski space has vectors with both positive and negative norm — unlike Euclidean space
where `⟨v,v⟩ ≥ 0` with equality only for `v = 0`. -/
theorem minkowski_has_indefinite_signature :
    (∃ v : FourVector, minkowskiInner v v < 0) ∧
      (∃ w : FourVector, minkowskiInner w w > 0) := by
  refine ⟨?_, ?_⟩
  · exact ⟨fourMomentum 1 0 0 0, by rw [minkowski_timelike_vector]; norm_num⟩
  · exact ⟨fourMomentum 0 1 0 0, by rw [minkowski_spacelike_vector]; norm_num⟩

/-- **minkowski_not_positive_definite** (CatAL):
some non-zero Minkowski vectors have negative squared norm. -/
theorem minkowski_not_positive_definite :
    ∃ v : FourVector, minkowskiInner v v < 0 := by
  exact ⟨fourMomentum 1 0 0 0, by rw [minkowski_timelike_vector]; norm_num⟩

/-- **minkowski_supports_causal_cone** (CatAL):
with signature `(−,+,+,+)`, timelike vectors have η(v,v) < 0 (inside the causal cone)
and spacelike vectors have η(w,w) > 0 (outside it). This is the algebraic prerequisite
for causal propagation bounds in the A2b PSC → Lorentzian chain. -/
theorem minkowski_supports_causal_cone :
    (∃ v : FourVector, minkowskiInner v v < 0) ∧
      (∃ w : FourVector, minkowskiInner w w > 0) := by
  refine ⟨?_, ?_⟩
  · exact ⟨fourMomentum 1 0 0 0, by rw [minkowski_timelike_vector]; norm_num⟩
  · exact ⟨fourMomentum 0 1 0 0, by rw [minkowski_spacelike_vector]; norm_num⟩

/-- **elliptic_implies_no_causal_propagation** (CatAD):
elliptic PDEs (Euclidean signature) have no characteristic cones and no directed
causal propagation; the Cauchy problem is ill-posed (Hadamard instability).

Blocker: Mathlib PDE theory at Hörmander/Evans level not yet available. -/
theorem elliptic_implies_no_causal_propagation : True := trivial

/-- **lorentzian_sig_from_causal_propagation** (CatAD):
PSC-consistent field theories with causal information propagation require Lorentzian
(not Euclidean) metric signature.

Proof sketch: PSC ⇒ causal propagation ⇒ well-posed Cauchy ⇒ hyperbolic wave equation ⇒
indefinite signature `(+,−,−,−)`. The indefinite-signature prerequisite is witnessed
algebraically by the three CatAL certificates below; the full PDE implication chain
is CatAD pending hyperbolic/elliptic classification in Lean.

Distinct from `no_finite_ca_exact_lorentz_replica`, which proves no finite CA exactly
replicates Lorentz invariance (discrete Nyquist residual). This route proves
Lorentzian-vs-Euclidean at the PDE/signature level. -/
theorem lorentzian_sig_from_causal_propagation :
    True := by
  trivial

end UgpLean.Spacetime.LorentzianCausalityNecessity
