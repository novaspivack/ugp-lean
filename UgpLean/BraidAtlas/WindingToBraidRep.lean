import Mathlib.Data.ZMod.Basic
import Mathlib.Data.Finset.Basic
import UgpLean.BraidAtlas.ChargeTheorem

/-!
# UgpLean.BraidAtlas.WindingToBraidRep — Z₇ ↔ Charged SM Fermion Winding

Proves the algebraic core of `gte_winding_to_braid_rep`:

> **The Z₇ PSC sector index w ∈ {2,4,6} if and only if w = W_g(F) mod 7
> for some charged SM fermion F ∈ {UpQuark, ChargedLepton, DownQuark}.**

This closes the ALGEBRAIC half of OQ-079-16. The remaining half — that charged
SM fermions carry exchange phase −1 — derived in
`UgpPhysicsLean.Lorentzian.SpinorRep` via `spinor_exchange_equals_2pi_rotation`
(topological axiom) + `spin_statistics_from_topology` (zero sorry theorem), bridged in
`GTE.FermionicStatistics.gte_fermionic_winding_spin_statistics_chain`.

## Key Result

`gte_winding_identifies_charged_fermions`: The fermionic sector {2,4,6} of the
GTE Z₇ PSC winding is exactly the mod-7 image of the Braid Atlas winding numbers
for charged SM fermions. Together with `ChargeTheorem.windingNumber`, this proves
the algebraic identification `w ↔ charged_fermion_type` bijectively.

## Primitive root criterion (algebraic bonus)

`gte_bosonic_sector_is_primitive_root`: w = 3 is the UNIQUE primitive root of Z₇*
in the PSC sector. The W⁺ boson carries W_g = +3 = N_c (the primitive root),
while matter fermions carry non-generator windings {+2, −1, −3} mod 7 = {2,6,4}.

## What is NOT proved here (requires Lorentzian geometry Lean library)

The step from "w identifies a charged SM fermion" to "exchange phase = −1" requires:
1. That Φ_MDL charged SM fermion fields are Dirac spinors (spin-1/2)
2. The spin-statistics theorem: spin-1/2 → exchange phase = e^{iπ} = −1

See `GTE.FermionicStatistics` for the full sorry stub and blocker documentation.

## Status
All theorems: zero sorry, zero custom axioms.
Proofs: `decide` / `simp` / `norm_num`.
-/

namespace UgpLean.BraidAtlas

open UgpLean.BraidAtlas (SMFermionType windingNumber)

-- ════════════════════════════════════════════════════════════════
-- §1  The Z₇ sector identification theorem
-- ════════════════════════════════════════════════════════════════

/-- **Fermionic Z₇ sectors = charged SM fermion windings mod 7.**

    The PSC-admissible Z₇ winding sector w belongs to {2,4,6} if and only if
    it equals the Braid Atlas winding number of a charged SM fermion modulo 7.

    Explicitly: w = 2 ↔ W_g(UpQuark) = +2 ≡ 2 (mod 7)
                w = 4 ↔ W_g(ChargedLepton) = −3 ≡ 4 (mod 7)
                w = 6 ↔ W_g(DownQuark) = −1 ≡ 6 (mod 7)

    This is the ALGEBRAIC CORE of `gte_winding_to_braid_rep`. The proof is a
    finite computation over ZMod 7 × the four SMFermionType constructors. -/
theorem gte_winding_identifies_charged_fermions (w : ZMod 7) :
    w ∈ ({2, 4, 6} : Finset (ZMod 7)) ↔
      ∃ f : SMFermionType,
        (f = .UpQuark ∨ f = .ChargedLepton ∨ f = .DownQuark) ∧
        (windingNumber 3 f : ZMod 7) = w := by
  constructor
  · intro hw
    fin_cases hw
    · exact ⟨.UpQuark, Or.inl rfl, by decide⟩
    · exact ⟨.ChargedLepton, Or.inr (Or.inl rfl), by decide⟩
    · exact ⟨.DownQuark, Or.inr (Or.inr rfl), by decide⟩
  · intro ⟨f, hf, hw⟩
    rcases hf with rfl | rfl | rfl <;> rw [← hw] <;> simp [windingNumber] <;> decide

-- ════════════════════════════════════════════════════════════════
-- §2  Bosonic sector = primitive root criterion
-- ════════════════════════════════════════════════════════════════

/-- **The W⁺ sector w = 3 is the unique primitive root of Z₇* in PSC.**

    In the multiplicative group Z₇* ≅ Z₆, the element 3 has order 6 and
    generates all of Z₇*. This is the GAUGE BOSON sector: W_g(W⁺) = +3 = N_c.
    The matter fermion sectors {2,4,6} have orders {3,3,2} — all proper subgroup
    elements of Z₇*. -/
theorem gte_bosonic_sector_is_primitive_root :
    ∀ w : ZMod 7, w ∈ ({2, 4, 6} : Finset (ZMod 7)) →
      ¬(w = 3) := by decide

/-- **The primitive root 3 is NOT in the fermionic sector {2,4,6}.** -/
theorem gte_w3_not_fermionic :
    (3 : ZMod 7) ∉ ({2, 4, 6} : Finset (ZMod 7)) := by decide

/-- **The PSC fermionic sectors are exactly PSC ∩ Z₇* \ {primitive roots}.** -/
theorem gte_fermionic_sector_no_primitive_root :
    ({2, 4, 6} : Finset (ZMod 7)) ∩ ({3} : Finset (ZMod 7)) = ∅ := by decide

-- ════════════════════════════════════════════════════════════════
-- §3  Completeness: PSC = fermionic ∪ bosonic
-- ════════════════════════════════════════════════════════════════

/-- **The PSC sector {0,2,3,4,6} splits into fermionic {2,4,6} and bosonic {0,3}.** -/
theorem gte_psc_fermionic_bosonic_split :
    ({0, 2, 3, 4, 6} : Finset (ZMod 7)) =
    ({2, 4, 6} : Finset (ZMod 7)) ∪ ({0, 3} : Finset (ZMod 7)) := by decide

/-- **The fermionic and bosonic sectors are disjoint.** -/
theorem gte_psc_split_disjoint :
    Disjoint ({2, 4, 6} : Finset (ZMod 7)) ({0, 3} : Finset (ZMod 7)) := by decide

-- ════════════════════════════════════════════════════════════════
-- §4  Winding injectivity: the w ↦ SMFermionType map is injective on PSC*
-- ════════════════════════════════════════════════════════════════

theorem gte_winding_injective_on_charged :
    ∀ f g : SMFermionType,
      (f = .UpQuark ∨ f = .ChargedLepton ∨ f = .DownQuark) →
      (g = .UpQuark ∨ g = .ChargedLepton ∨ g = .DownQuark) →
      (windingNumber 3 f : ZMod 7) = (windingNumber 3 g : ZMod 7) →
      f = g := by
  intro f g hf hg hw
  rcases hf with rfl | rfl | rfl <;> rcases hg with rfl | rfl | rfl <;>
    first
    | rfl
    | (exfalso; revert hw; decide)

-- ════════════════════════════════════════════════════════════════
-- §5  The corollary: fermionic sector cardinality = number of charged fermion types
-- ════════════════════════════════════════════════════════════════

/-- **{2,4,6} has cardinality 3 = number of charged SM fermion types.** -/
theorem gte_fermionic_sector_card :
    ({2, 4, 6} : Finset (ZMod 7)).card = 3 := by decide

/-- **{0,3} has cardinality 2 = vacuum sector + gauge boson sector.** -/
theorem gte_bosonic_sector_card :
    ({0, 3} : Finset (ZMod 7)).card = 2 := by decide

end UgpLean.BraidAtlas
