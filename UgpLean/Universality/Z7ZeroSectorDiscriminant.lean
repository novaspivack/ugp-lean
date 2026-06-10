import UgpLean.Universality.GTPNeutralDiscrimination
import UgpLean.Universality.CUP3DUniqueness

/-!
# UgpLean.Universality.Z7ZeroSectorDiscriminant — Unified Z₇=0 Sector Discriminant

This file proves the **unified first-principles discriminant** for all SM particles
with Z₇ winding W_B = 0. Six SM particles (or groups) share this property:

  γ     — photon (massless, W_B=0)
  νₑ    — electron neutrino (W_B=0, GTE triple b=1, a=1)
  νμ    — muon neutrino (W_B=0, GTE triple b=1, a=9)
  ντ    — tau neutrino (W_B=0, GTE triple b=1, a=5)
  Z     — neutral weak boson (W_B=0, GTE triple b=3, c=12)
  H⁰    — Higgs scalar (W_B=0, GTE triple b=3, c=13)

Gluons also have W_B=0 but carry non-zero Z₃ color charge (F₂₁ Berry holonomy);
their discrimination via the color criterion is noted but remains PROVISIONAL pending
full F₂₁ Berry holonomy Lean certification.

## The discriminant hierarchy

**Layer 0 — f_MDL fixed-point criterion (identifies γ uniquely):**
  f_MDL(k,k,k) = k ↔ k = 0.
  Unique solution: k = 0 (vacuum/photon). No other Z₇ winding class is a uniform
  fixed point of f_MDL. Certifies γ = CA ether.
  (Proved: `CUP3D.fmdl_unique_uniform_fixed_point`, `CUP3D.photon_is_ca_ether`)

**Layer 1 — GTE triple b-index (neutrino vs EW sector):**
  b = 1 → neutrino sector {νₑ, νμ, ντ}
  b = 3 → electroweak sector {Z, H⁰}
  (Proved: `GTPNeutralDiscrimination.z_boson_b_index_distinct_from_neutrinos`)

**Layer 2 — Fine discrimination:**
  Neutrino sector (b=1): a ∈ {1, 9, 5} distinguishes νₑ, νμ, ντ.
  EW sector (b=3): c = 12 → Z; c = 13 → H⁰.
  (Proved: `GTPNeutralDiscrimination.neutrino_a_indices_distinct`,
            `GTPNeutralDiscrimination.z_higgs_c_distinct`)

**Species formula arithmetic (neutrino as unique W_B=0 SM fermion):**
  In W_B = 4k mod 7 with k ∈ {1,...,7}: k = 7 is the unique W_B=0 solution.
  New theorem `k7_unique_winding_zero_fermion` (CatAL, proved by `decide`).

## Master theorem

`z7_zero_sector_unified_discriminant` combines the above into a single
conjunction. All proofs: zero sorry.
-/

namespace Z7ZeroSectorDiscriminant

open CUP3D GTPNeutralDiscrimination

-- ────────────────────────────────────────────────────────────────────────────
-- §1  Species formula: k = 7 is the unique non-vacuum W_B = 0 SM fermion
-- ────────────────────────────────────────────────────────────────────────────

/-- **k7_unique_winding_zero_fermion** (CatAL, zero sorry).

    In the Level A/B species formula W_B = 4k mod 7, applied to SM fermion
    occupation numbers k ∈ {1,...,7}:

      4 * k % 7 = 0  ↔  k = 7

    The unique SM fermion with W_B = 0 has occupation number k = 7 (neutrino).
    No other non-vacuum occupation k ∈ {1,...,6} gives W_B = 0.

    Physical significance: among the four SM fermion species
    (k=1: charged lepton W_B=4; k=4: up-quark W_B=2; k=5: down-quark W_B=6;
    k=7: neutrino W_B=0), the neutrino is the sole W_B=0 fermion species.
    This arithmetic uniqueness is a first-principles consequence of the
    Z₇ species formula.

    LEAN-CERTIFIED (decide, all k ∈ {1,...,7} exhaustively checked, zero sorry). -/
theorem k7_unique_winding_zero_fermion :
    ∀ k : Nat, 1 ≤ k → k ≤ 7 → (4 * k % 7 = 0 ↔ k = 7) := by decide

/-- **k7_unique_winding_zero_in_fin8** — Fin 8 variant of the species uniqueness.

    For every non-zero k : Fin 8, W_B = 4k mod 7 = 0 ↔ k.val = 7.

    LEAN-CERTIFIED (decide, zero sorry). -/
theorem k7_unique_winding_zero_in_fin8 :
    ∀ k : Fin 8, k.val ≠ 0 → (4 * k.val % 7 = 0 ↔ k.val = 7) := by decide

/-- **nu_is_unique_winding_zero_sm_fermion**: Explicit conjunction form.
    k=7 gives W_B=0; no other k ∈ {1,...,6} does.

    LEAN-CERTIFIED (decide, zero sorry). -/
theorem nu_is_unique_winding_zero_sm_fermion :
    4 * 7 % 7 = 0 ∧
    (4 * 1 % 7 ≠ 0) ∧ (4 * 2 % 7 ≠ 0) ∧ (4 * 3 % 7 ≠ 0) ∧
    (4 * 4 % 7 ≠ 0) ∧ (4 * 5 % 7 ≠ 0) ∧ (4 * 6 % 7 ≠ 0) := by decide

-- ────────────────────────────────────────────────────────────────────────────
-- §2  Sector b-indices: EW (b=3) vs neutrino (b=1)
-- ────────────────────────────────────────────────────────────────────────────

/-- **neutrino_sector_b_index**: All three neutrino GTE triples have b = 1. -/
theorem neutrino_sector_b_index :
    nu_e_triple.b = 1 ∧ nu_mu_triple.b = 1 ∧ nu_tau_triple.b = 1 := by
  native_decide

/-- **ew_sector_b_index**: Z and Higgs both have b = 3 (EW ladder index). -/
theorem ew_sector_b_index :
    z_boson_triple.b = 3 ∧ higgs_triple.b = 3 := by
  native_decide

/-- **neutrino_ew_sectors_disjoint**: Neutrino b=1 and EW b=3 are disjoint. -/
theorem neutrino_ew_sectors_disjoint :
    nu_e_triple.b ≠ z_boson_triple.b ∧ nu_e_triple.b ≠ higgs_triple.b ∧
    nu_mu_triple.b ≠ z_boson_triple.b ∧ nu_mu_triple.b ≠ higgs_triple.b ∧
    nu_tau_triple.b ≠ z_boson_triple.b ∧ nu_tau_triple.b ≠ higgs_triple.b := by
  native_decide

-- ────────────────────────────────────────────────────────────────────────────
-- §3  EW sector c-values: Z at c=12 = c_H − 1 vs Higgs at c=13 = c_H
-- ────────────────────────────────────────────────────────────────────────────

/-- **cH_is_13**: Higgs branch capacity c_H = 13. -/
theorem cH_is_13 : higgs_triple.c = 13 := by native_decide

/-- **cZ_is_cH_minus_one**: Z boson capacity c_Z = 12 = c_H − 1. -/
theorem cZ_is_cH_minus_one : z_boson_triple.c = higgs_triple.c - 1 := by native_decide

/-- **z_higgs_c_values**: Z has c=12, Higgs has c=13, differing by 1. -/
theorem z_higgs_c_values :
    z_boson_triple.c = 12 ∧ higgs_triple.c = 13 ∧ z_boson_triple.c + 1 = higgs_triple.c := by
  native_decide

-- ────────────────────────────────────────────────────────────────────────────
-- §4  Extended discriminant function including the photon (none → label 0)
-- ────────────────────────────────────────────────────────────────────────────

/-- Discriminant for the full colorless Z₇=0 sector including photon.

    Input: `Option GTETriple` — `none` for the photon (no triple; fixed-point state),
    `some t` for GTE-triple-bearing particles.

    Labels:
      0 = photon (γ)   — none (vacuum / f_MDL fixed point)
      1 = νₑ           — b=1, a=1
      2 = νμ           — b=1, a=9
      3 = ντ           — b=1, a=5 (c < 0)
      4 = Z boson      — b=3, c=12
      5 = Higgs (H⁰)  — b=3, c=13
      ≥6 = unknown     — unrecognized triple
-/
def z7_zero_sector_label (mt : Option GTETriple) : Nat :=
  match mt with
  | none   => 0
  | some t => neutral_particle_discriminant t + 1

/-- **photon_label_zero**: The photon label is 0. -/
theorem photon_label_zero : z7_zero_sector_label none = 0 := rfl

/-- **gtp_particles_label_pos**: Every GTE-triple-bearing particle gets label ≥ 1,
    strictly distinguishable from the photon label. -/
theorem gtp_particles_label_pos (t : GTETriple) :
    z7_zero_sector_label (some t) ≥ 1 := by
  simp [z7_zero_sector_label]

/-- **z7_zero_sector_labels**: The five GTE-triple-bearing particles receive
    labels 1–5 under the extended discriminant. -/
theorem z7_zero_sector_labels :
    z7_zero_sector_label (some nu_e_triple)    = 1 ∧
    z7_zero_sector_label (some nu_mu_triple)   = 2 ∧
    z7_zero_sector_label (some nu_tau_triple)  = 3 ∧
    z7_zero_sector_label (some z_boson_triple) = 4 ∧
    z7_zero_sector_label (some higgs_triple)   = 5 := by
  native_decide

/-- **photon_label_distinct_from_gtp**: The photon label (0) is distinct from all
    GTE-triple-bearing particle labels. -/
theorem photon_label_distinct_from_gtp :
    z7_zero_sector_label none ≠ z7_zero_sector_label (some nu_e_triple)    ∧
    z7_zero_sector_label none ≠ z7_zero_sector_label (some nu_mu_triple)   ∧
    z7_zero_sector_label none ≠ z7_zero_sector_label (some nu_tau_triple)  ∧
    z7_zero_sector_label none ≠ z7_zero_sector_label (some z_boson_triple) ∧
    z7_zero_sector_label none ≠ z7_zero_sector_label (some higgs_triple) := by
  native_decide

-- ────────────────────────────────────────────────────────────────────────────
-- §5  Master theorem: Unified Z₇=0 colorless sector discriminant (CatAL)
-- ────────────────────────────────────────────────────────────────────────────

/-- **z7_zero_sector_unified_discriminant** — Unified first-principles discriminant
    for the W_B = 0 SM particles in the colorless (Q_χ = 0) sector.

    Assembles complete discrimination of six Z₇=0 colorless SM states
    (γ, νₑ, νμ, ντ, Z, H⁰) from three independent first-principles criteria:

    **(I) Layer 0 — f_MDL fixed-point (photon):**
      fmdl(k,k,k) = k ↔ k = 0. The photon (k=0) is the unique uniform fixed
      point of f_MDL over Z₇. Every non-zero winding class is an excitation
      above the vacuum; only k=0 reproduces itself from a uniform background.
      Source: `CUP3D.fmdl_unique_uniform_fixed_point` (CatAL, CUP3DUniqueness.lean).

    **(II) Layers 1–2 — GTE triple discrimination (ν, Z, H):**
      All five GTE-triple-bearing colorless particles (νₑ, νμ, ντ, Z, H⁰) have
      pairwise distinct triples. A two-level structure:
        b = 1 → neutrino sector; b = 3 → EW sector.
        Within ν: a ∈ {1,9,5} for νₑ/νμ/ντ.
        Within EW: c = 12 (Z) vs c = 13 (H⁰ = Higgs boundary c_H).
      Source: `GTPNeutralDiscrimination.gte_triple_neutral_discrimination` (CatAL).

    **(III) Species formula arithmetic (neutrino uniqueness as W_B=0 fermion):**
      In the species formula W_B = 4k mod 7 over SM fermion occupations k ∈ {1,...,7},
      k = 7 is the unique non-vacuum solution to W_B = 0. The neutrino is the sole
      W_B=0 SM fermion species.
      Source: `k7_unique_winding_zero_fermion` (CatAL, new; proved by `decide`).

    **(IV) Extended label injectivity:**
      The six-label function `z7_zero_sector_label` (photon=0, ν=1–3, Z=4, H=5)
      assigns each colorless W_B=0 particle a distinct non-negative integer label.

    **Note on gluons:** Gluons have W_B=0 but Q_χ ≠ 0 (Z₃ color from F₂₁ Berry
    holonomy, PROVISIONAL-STRONG). The color discriminant
    Q_χ ≠ 0 → gluon is not CatAL; gluon identification is excluded from
    this theorem.

    All conjuncts: zero sorry. CatAL for the colorless W_B=0 sector. -/
theorem z7_zero_sector_unified_discriminant :
    -- (I) Photon: unique f_MDL uniform fixed point
    (∀ k : Fin 7, fmdl k k k = k ↔ k = 0) ∧
    -- (II) GTE triple discrimination (ν, Z, H — all 10 pairs + discriminant function)
    ((nu_e_triple ≠ nu_mu_triple ∧ nu_e_triple ≠ nu_tau_triple ∧
      nu_e_triple ≠ z_boson_triple ∧ nu_e_triple ≠ higgs_triple ∧
      nu_mu_triple ≠ nu_tau_triple ∧ nu_mu_triple ≠ z_boson_triple ∧
      nu_mu_triple ≠ higgs_triple ∧ nu_tau_triple ≠ z_boson_triple ∧
      nu_tau_triple ≠ higgs_triple ∧ z_boson_triple ≠ higgs_triple) ∧
     (neutral_particle_discriminant nu_e_triple   = 0 ∧
      neutral_particle_discriminant nu_mu_triple  = 1 ∧
      neutral_particle_discriminant nu_tau_triple = 2 ∧
      neutral_particle_discriminant z_boson_triple = 3 ∧
      neutral_particle_discriminant higgs_triple  = 4) ∧
     (z_boson_triple.b = 3 ∧ higgs_triple.b = 3 ∧
      nu_e_triple.b = 1 ∧ nu_mu_triple.b = 1 ∧ nu_tau_triple.b = 1)) ∧
    -- (III) Species formula: k=7 unique W_B=0 SM fermion occupation
    (∀ k : Nat, 1 ≤ k → k ≤ 7 → (4 * k % 7 = 0 ↔ k = 7)) ∧
    -- (IV) Extended label injectivity (photon label 0 vs GTP labels 1–5)
    (z7_zero_sector_label none ≠ z7_zero_sector_label (some nu_e_triple)    ∧
     z7_zero_sector_label none ≠ z7_zero_sector_label (some nu_mu_triple)   ∧
     z7_zero_sector_label none ≠ z7_zero_sector_label (some nu_tau_triple)  ∧
     z7_zero_sector_label none ≠ z7_zero_sector_label (some z_boson_triple) ∧
     z7_zero_sector_label none ≠ z7_zero_sector_label (some higgs_triple)) := by
  exact ⟨fmdl_unique_uniform_fixed_point,
         gte_triple_neutral_discrimination,
         k7_unique_winding_zero_fermion,
         by native_decide⟩

end Z7ZeroSectorDiscriminant
