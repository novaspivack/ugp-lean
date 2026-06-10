import UgpLean.Universality.LorentzInvariance

/-!
# Φ_MDL Lagrangian Lorentz Scalarity

Certifies that the Φ_MDL Klein–Gordon Lagrangian density is a Lorentz scalar:
`ℒ_Φ_MDL = −½ η^{μν} ∂_μΦ ∂_νΦ − V(Φ)`.

The kinetic term uses `minkowskiInner` on four-momentum; the Z₇ potential depends only
on the scalar field value and is unchanged under O(1,3) boosts on momentum labels.

## Main theorem (zero sorry)

| Theorem | Content |
|---|---|
| `phimdl_lagrangian_is_lorentz_scalar` | `ℒ(φ,p) = ℒ(φ, Λ·p)` for Lorentz Λ |
| `lorentz_act_preserves_config_lagrangian` | `ℒ_cfg(φ) = ℒ_cfg(Λ·φ)` for field derivatives |
-/

namespace UgpLean.Substrate.LagrangianLorentzScalar

open Matrix
open UgpLean.Universality.LorentzInvariance

/-- A Lorentz boost acting on Φ_MDL configurations and momenta. -/
structure LorentzBoost where
  matrix : Matrix SpacetimeIdx SpacetimeIdx ℝ
  isLorentz : IsLorentz matrix

/-- Four-momentum label for on-shell Lagrangian evaluation. -/
abbrev MomentumVector := FourVector

/-- Φ_MDL Klein–Gordon configuration: scalar field and spacetime gradient. -/
structure KGConfig where
  phi : ℝ
  dphi : FourVector

/-- Lorentz action on a KG configuration: φ is a scalar; ∂φ transforms as a four-vector. -/
def lorentzBoostActConfig (lb : LorentzBoost) (cfg : KGConfig) : KGConfig :=
  { phi := cfg.phi
    dphi := lb.matrix *ᵥ cfg.dphi }

/-- Lorentz action on four-momentum. -/
def lorentzBoostActMomentum (lb : LorentzBoost) (p : MomentumVector) : MomentumVector :=
  lb.matrix *ᵥ p

/-- Two configurations are Lorentz-related when one is the boost of the other. -/
def is_lorentz_related (cfg psi : KGConfig) : Prop :=
  ∃ (lb : LorentzBoost), psi = lorentzBoostActConfig lb cfg

/-- Z₇-symmetric potential `V(Φ)` — depends only on the scalar field value. -/
noncomputable def phimdl_potential (phi : ℝ) : ℝ :=
  phi ^ 2

/-- Configuration-level Lagrangian `−½ η(∂φ,∂φ) − V(φ)` (zero sorry). -/
noncomputable def phimdl_config_lagrangian (cfg : KGConfig) : ℝ :=
  -(1 / 2 : ℝ) * minkowskiInner cfg.dphi cfg.dphi - phimdl_potential cfg.phi

/-- **Φ_MDL Lagrangian density** evaluated with kinetic term `−½ η(p,p)` and `V(Φ)`.
    On-shell, `η(p,p)` matches the mass-shell constraint from `LorentzInvariance`. -/
noncomputable def phimdl_lagrangian (cfg : KGConfig) (p : MomentumVector) : ℝ :=
  -(1 / 2 : ℝ) * minkowskiInner p p - phimdl_potential cfg.phi

/-- **Lemma 1:** `ℒ_Φ_MDL` is a Lorentz scalar under momentum-space O(1,3) action (zero sorry). -/
theorem phimdl_lagrangian_is_lorentz_scalar (lb : LorentzBoost) (cfg : KGConfig) (p : MomentumVector) :
    phimdl_lagrangian cfg p = phimdl_lagrangian cfg (lorentzBoostActMomentum lb p) := by
  dsimp [phimdl_lagrangian, lorentzBoostActMomentum, phimdl_potential]
  rw [lorentz_transform_preserves_inner lb.isLorentz p p]

/-- Lorentz boosts preserve the configuration Lagrangian (derivative term uses η). -/
theorem lorentz_act_preserves_config_lagrangian (lb : LorentzBoost) (cfg : KGConfig) :
    phimdl_config_lagrangian cfg = phimdl_config_lagrangian (lorentzBoostActConfig lb cfg) := by
  dsimp [phimdl_config_lagrangian, lorentzBoostActConfig, phimdl_potential]
  rw [lorentz_transform_preserves_inner lb.isLorentz cfg.dphi cfg.dphi]

theorem lorentz_act_is_lorentz_related (lb : LorentzBoost) (cfg : KGConfig) :
    is_lorentz_related cfg (lorentzBoostActConfig lb cfg) :=
  ⟨lb, rfl⟩

/-- Standard x-boost packaged as a `LorentzBoost`. -/
noncomputable def standardLorentzBoostX (beta : ℝ) (hbeta : |beta| < 1) : LorentzBoost :=
  { matrix := Universality.LorentzInvariance.lorentzBoostX beta
    isLorentz := lorentz_boost_preserves_metric hbeta }

end UgpLean.Substrate.LagrangianLorentzScalar
