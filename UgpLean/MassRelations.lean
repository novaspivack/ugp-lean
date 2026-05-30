import UgpLean.MassRelations.UpLeptonCyclotomic
import UgpLean.MassRelations.KoideAngle
import UgpLean.MassRelations.LeptonMassPrediction
import UgpLean.MassRelations.ClaimCBridge
import UgpLean.MassRelations.DownRational
import UgpLean.MassRelations.ClebschGordan
import UgpLean.MassRelations.SU3FlavorCartan
import UgpLean.MassRelations.BinaryCascade
import UgpLean.MassRelations.FroggattNielsen
import UgpLean.MassRelations.CartanFlavonPotential
import UgpLean.MassRelations.Z2OrbifoldDepth
import UgpLean.MassRelations.HeavyFermionTower
import UgpLean.MassRelations.KoideClosedForm
import UgpLean.MassRelations.KoideNewtonFlow
import UgpLean.MassRelations.KoideS3DiscreteIdentities
import UgpLean.MassRelations.KoideYukawaAmplitude
import UgpLean.MassRelations.KoideEqualNormReformulation
import UgpLean.MassRelations.KoideIrrepEqualNorm
import UgpLean.MassRelations.KoideGenerationCyclicSymmetry
import UgpLean.MassRelations.KoideSectorAngle
import UgpLean.MassRelations.PhysicalMasses
import UgpLean.MassRelations.SeesawIndex
import UgpLean.MassRelations.CKMTheta23
import UgpLean.MassRelations.CKMMixing
import UgpLean.MassRelations.CKMCPPhase
import UgpLean.MassRelations.NeutrinoMassRatio
import UgpLean.MassRelations.NeutrinoVacuumSectorL2

/-!
# UgpLean.MassRelations — Charged-Fermion Mass Structural Relations

This module formalizes the two UGP-native structural mass relations
discovered in the team-meeting research ( and):

**Relation 1 (up-to-lepton, cyclotomic):**

 log(m_{u_g} / m_{lep_g}) = (π/6)·2^g + β for g = 1, 2, 3

with β a small UGP-atom constant (best fit β = π/8 at 0.44% max-frac-err).

**Relation 2 (down-type, rational):**

 log(m_{d_g}) = (13/9)·log(m_{u_g}) + (-7/6)·log(m_{lep_g}) + (-5/14)

**Joint consequence (MDL compression 9:2):** the 9 charged-fermion masses
reduce to 2 independent inputs (m_e, m_μ).

## Status of proofs

- α = π/6, β = π/8, and the down-type coefficients (13/9, -7/6, -5/14)
 have **rational-valued identities proved** at Lean-decidable level.
- β-free and γ-free inter-generational **linearity identities proved**
 using `ring` and `linarith`.
- **Structural derivations** (why these specific UGP-atom values appear)
 are currently goal-statements for Priority 1 research.

See also:
- `UgpLean.MassRelations.UpLeptonCyclotomic` — TT formula module
- `UgpLean.MassRelations.DownRational` — VV formula module
- `UgpLean.MassRelations.ClebschGordan` — GUT Lie-group integer table + VV three-factor structural theorems
- `UgpLean.MassRelations.SU3FlavorCartan` — Claim A (α = π/6 from A_2 geometry)
- `UgpLean.MassRelations.BinaryCascade` — Claim B candidate: TT formula as binary phase cascade with 2^g doubling per step
- `UgpLean.MassRelations.FroggattNielsen` — Claim C UV completion: two-flavon FN model with doubled charges reproducing TT exactly
- `UgpLean.MassRelations.CartanFlavonPotential` — Claim C sub-(ii): Z_6 × Z_16-invariant flavon potential whose minima reproduce the Round-21 transcendental flavon VEVs
- `UgpLean.MassRelations.Z2OrbifoldDepth` — Claim C sub-(i): Z_2-orbifold-depth interpretation of the doubled FN charges (1, 2, 4)
- `UgpLean.MassRelations.HeavyFermionTower` — Claim C alternative UV completion: heavy-fermion-tower model EFT-dual to FN-doubled
- `UgpLean.MassRelations.KoideClosedForm` — Priority 7 : Koide algebraic closed form and cyclotomic-12 identification; proves (2+√3) = 4·cos²(π/12), (1+√3)² = 8·cos²(π/12), and the +root `r_τ = 2(r_e+r_μ) + √3·√(r_e²+4r_e r_μ+r_μ²)` satisfies the Koide constraint
- `UgpLean.MassRelations.KoideNewtonFlow` — Priority 7 /IV: UGP-native S_3-equivariant Newton-step Koide flow `U(v) = v - (q(v)/|∇q|²)·∇q`; proves S_3-equivariance (under all three generators swap12, swap13, rot123), null-cone fixed-point property, and ties to KoideClosedForm's +root
- `UgpLean.MassRelations.PhysicalMasses` — Priority 8 Phase C: end-to-end physical-mass bridge. Given (m_e, m_μ) as input, defines `predictedLepton`, `predictedUpType`, `predictedDownType` via TT+VV+Koide closed form; proves TT formula, VV formula, and Koide identity hold by construction on the predicted physical masses; proves positivity of all predicted masses; proves predicted lepton vector is fixed point of R34 Newton-step Koide flow. This module upgrades the previously `True → trivial` FormulaHolds placeholders to real theorems on Lean-valued physical-mass predictions, closing the E_base Lean bridge ( §D.4) except for the residual m_μ anchor (see R35 lab notes for empirical MAP at DL ≤ 3)
- `UgpLean.MassRelations.CKMMixing` — CDM mechanism: derives the effective Cabibbo FN charge Δa_eff = α_d = 1 + rank(SU(5))/N_c² = 13/9 and proves |V_us|_CDM = ε₁^(α_d) = exp(−13π/27) ≈ 0.2203 (PDG 0.2245; 1.9% off). All theorems zero sorry. Constituent lemmas: `fn_vevs_are_potential_minima` (ε₁ structurally fixed), `VV_from_GUT_group_theory` (α_d from GUT group theory).
-/

namespace UgpLean.MassRelations

-- Re-export the main formulas for discoverability.

export UgpLean.MassRelations.UpLeptonCyclotomic (UpLeptonFormula)
export UgpLean.MassRelations.DownRational (DownRationalFormula CombinedFormula)

end UgpLean.MassRelations
