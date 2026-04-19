import UgpLean.MassRelations.UpLeptonCyclotomic
import UgpLean.MassRelations.DownRational
import UgpLean.MassRelations.ClebschGordan
import UgpLean.MassRelations.SU3FlavorCartan
import UgpLean.MassRelations.BinaryCascade

/-!
# UgpLean.MassRelations — Charged-Fermion Mass Structural Relations

This module formalizes the two UGP-native structural mass relations
discovered in the 2026-04-19 team-meeting research (COMP-P01-TT and
COMP-P01-VV):

**Relation 1 (up-to-lepton, cyclotomic):**

    log(m_{u_g} / m_{lep_g}) = (π/6)·2^g + β     for g = 1, 2, 3

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
  are currently goal-statements for Priority 1 Round 12 research.

See also:
- `UgpLean.MassRelations.UpLeptonCyclotomic` — TT formula module
- `UgpLean.MassRelations.DownRational` — VV formula module
- `UgpLean.MassRelations.ClebschGordan` — GUT Lie-group integer table + Round 17–18 VV three-factor structural theorems
- `UgpLean.MassRelations.SU3FlavorCartan` — Round 13 Claim A (α = π/6 from A_2 geometry)
- `UgpLean.MassRelations.BinaryCascade` — Round 19 Claim B candidate: TT formula as binary phase cascade with 2^g doubling per step
-/

namespace UgpLean.MassRelations

-- Re-export the main formulas for discoverability.

export UgpLean.MassRelations.UpLeptonCyclotomic (UpLeptonFormula)
export UgpLean.MassRelations.DownRational (DownRationalFormula CombinedFormula)

end UgpLean.MassRelations
