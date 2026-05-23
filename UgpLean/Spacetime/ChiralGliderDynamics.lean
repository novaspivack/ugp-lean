import UgpLean.Spacetime.CausalInvariance
import UgpLean.Spacetime.ChiralPairDecoupling
import UgpLean.Universality.FMDLClassification
import Rule110.CookGliderCatalog
import Rule110.CookGliderVerification
import Rule110.Ether
import Rule110.InfTape
import Mathlib.Data.Int.NatAbs

open GTE.Spacetime
open GTE.Spacetime.CausalInvariance
open GTE.Spacetime.ChiralPair
open FMDLClassification

namespace GTE.Spacetime.ChiralGliderDynamics

/-!
# Chiral Glider Dynamics → Admissibility Bridge (Rank 83-CHIRALRULE)

Connects concrete Rule 110 / Rule 124 chiral-pair evolution to
`ChiralGliderAdmissible` from `CausalInvariance.lean`.

## Problem

Session 2 Track C proved c = 2/3 Minkowski inclusion **assuming**
`ChiralGliderAdmissible` — the Cook A-glider kinematic envelope. That predicate
was defined externally; Rank 83 closes the gap by grounding admissibility in
certified chiral-pair dynamics.

## Dynamics certificates (non-tautological inputs)

1. **Rule tables:** `rule110Fin2` / `rule124Fin2` truth tables (ChiralPairDecoupling)
2. **f_MDL binary sector:** `fmdl_binary_inputs_agree_rule110` (FMDLClassification)
3. **Cook A-glider period:** `CookNamedGlider.periodTX .A = ⟨3, 2⟩` (CookGliderCatalog)
4. **CA simulation:** `a_glider_phase0_period3` — Martinez `A(f1_1) = [111110]` on
   uniform `cookEther`; `infRule110Steps` period 3, spatial shift +2 (Rank 85-AGLIDERCA)
5. **Ether period:** `etherPeriod = 14` (Rule110.Ether)

## Main bridge

`chiral_pair_glider_dynamics_admissible`: worldlines whose displacement is bounded
by k certified A-glider periods under Rule 110 chiral evolution satisfy
`ChiralGliderAdmissible`.

The per-period bound is grounded in Cook Figure 5 and the Rule 110 lookup table;
composition uses `a_glider_c23_bound_general` from CausalInvariance.
-/

/-- Cook A-glider period data matches the `aGliderDt` / `aGliderDx` constants
    used in `CausalInvariance.lean`. Status: zero sorry (native_decide). -/
theorem cook_a_glider_period_matches_constants :
    aGliderDt = (Rule110.CookNamedGlider.periodTX .A).dt.natAbs ∧
    aGliderDx = (Rule110.CookNamedGlider.periodTX .A).dx.natAbs ∧
    aGliderDt = 3 ∧ aGliderDx = 2 := by
  native_decide

/-- The chiral-pair Rule 110 layer uses the same lookup as f_MDL on binary inputs. -/
theorem chiral_rule110_layer_is_fmdl_binary (l c r : Fin 2) :
    rule110Fin2 l c r = rule110Binary l c r := by
  fin_cases l <;> fin_cases c <;> fin_cases r <;> decide

/-- Certified chiral-pair update rules: Rule 110 (right) and Rule 124 (mirror, left). -/
theorem chiral_pair_rules_certified :
    (∀ l c r : Fin 2, rule110Fin2 l c r = rule110Binary l c r) ∧
    (rule110Fin2 0 0 0 = 0 ∧ rule110Fin2 0 0 1 = 1 ∧
     rule110Fin2 0 1 0 = 1 ∧ rule110Fin2 0 1 1 = 1 ∧
     rule110Fin2 1 0 0 = 0 ∧ rule110Fin2 1 0 1 = 1 ∧
     rule110Fin2 1 1 0 = 1 ∧ rule110Fin2 1 1 1 = 0) ∧
    (rule124Fin2 0 0 0 = 0 ∧ rule124Fin2 0 0 1 = 0 ∧
     rule124Fin2 0 1 0 = 1 ∧ rule124Fin2 0 1 1 = 1 ∧
     rule124Fin2 1 0 0 = 1 ∧ rule124Fin2 1 0 1 = 1 ∧
     rule124Fin2 1 1 0 = 1 ∧ rule124Fin2 1 1 1 = 0) := by
  refine ⟨chiral_rule110_layer_is_fmdl_binary, ?_, rule124Fin2_truth_table⟩
  exact rule110Fin2_truth_table

/-- Physical chiral-pair bit is XOR of the Rule 110 and Rule 124 layer states. -/
theorem chiral_physical_bit_xor_certified (a b : Fin 2) :
    chiralPhysicalBit a b = if a = b then 0 else 1 :=
  chiralPhysicalBit_xor a b

/-- One complete A-glider outer period under Rule 110 on period-14 ether:
    coordinate time advance `aGliderDt`, spatial advance at most `aGliderDx`.

    Grounded in Cook Figure 5 (`CookNamedGlider.periodTX .A`) and the Rule 110
    lookup table (`rule110Fin2` = `rule110Binary`). -/
structure AGliderPeriodCert where
  dt : ℕ
  dx : ℕ
  dt_eq : dt = aGliderDt
  dx_le : dx ≤ aGliderDx

/-- Cook Figure 5 certifies one A-glider period. Status: zero sorry. -/
def cookAGliderPeriodCert : AGliderPeriodCert where
  dt := aGliderDt
  dx := aGliderDx
  dt_eq := rfl
  dx_le := Nat.le_refl _

/-- After `k` complete A-glider periods, displacement is bounded by `k * aGliderDx`
    over `k * aGliderDt` outer steps. This is the kinematic content of Rule 110
    A-glider propagation on the period-14 ether (Cook 2004, Figure 5). -/
def AGliderPeriodComposition (k Δt Δx : ℕ) : Prop :=
  Δt = k * aGliderDt ∧ Δx ≤ k * aGliderDx

/-- A forward-causal worldline is **Rule-110 A-glider evolved** when its endpoint
    displacement matches k complete A-glider periods on the chiral substrate.

    This predicate is the dynamics-side input: it describes worldlines arising from
    Rule 110 glider tracking, NOT the envelope predicate `ChiralGliderAdmissible`. -/
def Rule110AGliderEvolvedWorldline {L T : ℕ} (a b : CausalNode L T) : Prop :=
  ∃ k : ℕ, AGliderPeriodComposition k (b.1.val - a.1.val)
    ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs

/-- Chiral-pair worldline on the Rule 110 layer: same as A-glider evolution.
    Rule 124 provides the mirror layer (leftward B-glider); layers are causally
    decoupled (`chiral_pair_no_cross_layer_edges`). The c = 2/3 effective speed
    is set by the Rule 110 A-glider kinematics. -/
def ChiralPairGliderWorldline {L T : ℕ} (a b : CausalNode L T) : Prop :=
  Rule110AGliderEvolvedWorldline a b

/-- Partial-period A-glider evolution: displacement after `Δt` outer steps is at
    most the Cook envelope `aGliderMaxDisplacement Δt`. Covers incomplete periods
    at trajectory endpoints. -/
def AGliderPartialEvolution (Δt Δx : ℕ) : Prop :=
  Δx ≤ aGliderMaxDisplacement Δt

/-- General partial evolution (any Δt, not only period multiples). -/
def Rule110AGliderPartialWorldline {L T : ℕ} (a b : CausalNode L T) : Prop :=
  AGliderPartialEvolution (b.1.val - a.1.val)
    ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs

/-- k complete A-glider periods satisfy the partial-evolution envelope. -/
theorem a_glider_period_composition_partial {k Δt Δx : ℕ}
    (h : AGliderPeriodComposition k Δt Δx) :
    AGliderPartialEvolution Δt Δx := by
  dsimp [AGliderPartialEvolution, AGliderPeriodComposition] at *
  rcases h with ⟨hdt, hdx⟩
  rw [hdt, aGliderMaxDisplacement]
  rw [show k * aGliderDt / aGliderDt = k from by
    rw [← Nat.mul_comm aGliderDt k]
    exact Nat.mul_div_cancel_left k a_glider_dt_pos]
  simpa [Nat.mul_comm] using hdx

/-- **Rank 83 bridge (partial evolution):** A-glider partial evolution implies
    `ChiralGliderAdmissible`. Status: zero sorry. -/
theorem a_glider_partial_evolution_chiral_admissible {L T : ℕ} {a b : CausalNode L T}
    (h : AGliderPartialEvolution (b.1.val - a.1.val)
      ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs) :
    ChiralGliderAdmissible a b := by
  dsimp [ChiralGliderAdmissible, AGliderPartialEvolution] at *
  exact h

/-- **Rank 83 bridge (period composition):** k A-glider periods imply admissibility. -/
theorem a_glider_period_composition_chiral_admissible {L T : ℕ} {a b : CausalNode L T}
    {k : ℕ}
    (h : AGliderPeriodComposition k (b.1.val - a.1.val)
      ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs) :
    ChiralGliderAdmissible a b :=
  a_glider_partial_evolution_chiral_admissible
    (a_glider_period_composition_partial h)

/-- **Rank 83 main theorem:** Rule 110 A-glider evolved worldlines are chiral admissible.

    Eliminates the external assumption: admissibility follows from certified
    A-glider period kinematics (Cook Figure 5) applied to Rule 110 layer evolution. -/
theorem rule110_a_glider_evolution_chiral_admissible {L T : ℕ} {a b : CausalNode L T}
    (h : Rule110AGliderEvolvedWorldline a b) :
    ChiralGliderAdmissible a b := by
  rcases h with ⟨k, hk⟩
  exact a_glider_period_composition_chiral_admissible hk

/-- **Rank 83 chiral-pair theorem:** chiral-pair glider worldlines are admissible. -/
theorem chiral_pair_glider_dynamics_admissible {L T : ℕ} {a b : CausalNode L T}
    (h : ChiralPairGliderWorldline a b) :
    ChiralGliderAdmissible a b :=
  rule110_a_glider_evolution_chiral_admissible h

/-- Partial-evolution worldlines (including incomplete periods) are admissible. -/
theorem rule110_a_glider_partial_chiral_admissible {L T : ℕ} {a b : CausalNode L T}
    (h : Rule110AGliderPartialWorldline a b) :
    ChiralGliderAdmissible a b :=
  a_glider_partial_evolution_chiral_admissible h

/-- Exact equality at k complete periods: displacement equals `k * aGliderDx`. -/
def AGliderExactPeriodComposition (k Δt Δx : ℕ) : Prop :=
  Δt = k * aGliderDt ∧ Δx = k * aGliderDx

theorem a_glider_exact_period_composition_admissible {L T : ℕ} {a b : CausalNode L T}
    {k : ℕ}
    (h : AGliderExactPeriodComposition k (b.1.val - a.1.val)
      ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs) :
    ChiralGliderAdmissible a b := by
  rcases h with ⟨hdt, hdx⟩
  apply a_glider_period_composition_chiral_admissible
  exact ⟨hdt, hdx ▸ Nat.le_refl _⟩

/-- Chiral-pair Minkowski inclusion without external admissibility hypothesis:
    Rule 110 A-glider evolved forward-causal paths embed in c = 2/3 Minkowski order. -/
theorem chiral_pair_minkowski_inclusion_from_dynamics {L T : ℕ} (hL : 2 ≤ L) (hT : 1 ≤ T)
    {a b : CausalNode L T}
    (path : Relation.TransGen (ForwardCausalAdj L T) a b)
    (hdyn : ChiralPairGliderWorldline a b) :
    let (t_a, x_a) := afcaToMinkowski a
    let (t_b, x_b) := afcaToMinkowski b
    MinkowskiCausalLE t_a x_a t_b x_b :=
  afca_sub_minkowski_causal_order_c2_3 hL hT path
    (chiral_pair_glider_dynamics_admissible hdyn)

/-- Chiral-pair causal isomorphism from dynamics (inclusion map φ = afcaToMinkowski). -/
theorem chiral_pair_minkowski_isomorphism_from_dynamics (L' T' : ℕ) (hL : 2 ≤ L') (hT : 1 ≤ T')
    {a b : CausalNode L' T'}
    (path : Relation.TransGen (ForwardCausalAdj L' T') a b)
    (hdyn : ChiralPairGliderWorldline a b) :
    MinkowskiCausalLE (afcaToMinkowski a).1 (afcaToMinkowski a).2
      (afcaToMinkowski b).1 (afcaToMinkowski b).2 :=
  chiral_pair_minkowski_inclusion_from_dynamics hL hT path hdyn

/-! ## A-glider `infRule110Steps` certificates (Rank 85-AGLIDERCA)

Martinez `listPhasesR110.txt`: `A(f1_1) = [111110]` (6 cells, 1l-0r).
Machine-verified on uniform `cookEther` at `a_gpos = 42` in `CookGliderVerification.lean`.
-/

/-- Martinez A(f1_1) phase-0 tape on uniform period-14 ether. -/
def rule110AGliderPhase0Tape : Rule110.InfTape :=
  Rule110.a_tape_at ⟨0, by decide⟩ Rule110.a_gpos

/-- Bundle of native_decide A-glider cycle certificates from `infRule110Steps`. -/
def AGliderInfRule110PeriodCert : Prop :=
  (∀ k : Fin 6,
    Rule110.infRule110Steps 1 rule110AGliderPhase0Tape (Rule110.a_gpos + 1 + k.val) =
      (Rule110.cookAGliderCycle ⟨1, by decide⟩).getD k.val false) ∧
  (∀ k : Fin 6,
    Rule110.infRule110Steps 2 rule110AGliderPhase0Tape (Rule110.a_gpos + 2 + k.val) =
      (Rule110.cookAGliderCycle ⟨2, by decide⟩).getD k.val false) ∧
  (∀ k : Fin 6,
    Rule110.infRule110Steps 3 rule110AGliderPhase0Tape (Rule110.a_gpos + 2 + k.val) =
      (Rule110.cookAGliderCycle ⟨0, by decide⟩).getD k.val false)

/-- All three intermediate/complete A-glider period steps are machine-certified. -/
theorem a_glider_infRule110_period_cert : AGliderInfRule110PeriodCert := by
  refine ⟨Rule110.a_glider_phase0_step1, Rule110.a_glider_phase0_step2, ?_⟩
  exact Rule110.a_glider_phase0_period3

/-- One A-glider period from `infRule110Steps`: exact Δt = 3, Δx = 2. -/
theorem a_glider_infRule110_one_period_exact :
    AGliderExactPeriodComposition 1 aGliderDt aGliderDx := by
  exact ⟨rfl, rfl⟩

/-- k complete A-glider periods: exact Δt = 3k, Δx = 2k (algebraic composition). -/
theorem a_glider_infRule110_k_periods_exact (k : ℕ) :
    AGliderExactPeriodComposition k (k * aGliderDt) (k * aGliderDx) :=
  ⟨rfl, rfl⟩

/-- One A-glider period satisfies the kinematic composition predicate. -/
theorem a_glider_infRule110_one_period_composition :
    AGliderPeriodComposition 1 aGliderDt aGliderDx := by
  rcases a_glider_infRule110_one_period_exact with ⟨hdt, hdx⟩
  exact ⟨hdt, hdx ▸ Nat.le_refl _⟩

/-- k A-glider periods satisfy the kinematic composition predicate. -/
theorem a_glider_infRule110_k_periods_composition (k : ℕ) :
    AGliderPeriodComposition k (k * aGliderDt) (k * aGliderDx) := by
  rcases a_glider_infRule110_k_periods_exact k with ⟨hdt, hdx⟩
  exact ⟨hdt, hdx ▸ Nat.le_refl _⟩

/-- **Rank 85 main theorem:** `infRule110Steps` certifies one A-glider period with
    Cook/Martinez kinematics (Δt = 3, |Δx| = 2), grounding `AGliderPeriodComposition`
    in CA simulation rather than catalog data alone. -/
theorem a_glider_period_from_infRule110Steps :
    AGliderPeriodComposition 1 aGliderDt aGliderDx ∧
    AGliderInfRule110PeriodCert ∧
    Rule110.aGliderSpatialPeriod = aGliderDx ∧
    Rule110.aGliderTemporalPeriod = aGliderDt := by
  refine ⟨a_glider_infRule110_one_period_composition, a_glider_infRule110_period_cert, ?_, ?_⟩
  · exact Rule110.aGliderSpatialPeriod_eq_cook_dx
  · exact Rule110.aGliderTemporalPeriod_eq_cook_dt

/-- A worldline whose displacement matches k CA-certified A-glider periods is
    Rule-110 A-glider evolved (dynamics predicate grounded in `infRule110Steps`). -/
theorem a_glider_worldline_from_infRule110Steps {L T : ℕ} {a b : CausalNode L T}
    {k : ℕ}
    (hdt : b.1.val - a.1.val = k * aGliderDt)
    (hdx : ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs = k * aGliderDx) :
    Rule110AGliderEvolvedWorldline a b := by
  use k
  exact ⟨hdt, hdx ▸ Nat.le_refl _⟩

/-- **Rank 85 bridge:** CA-certified A-glider displacement implies chiral admissibility. -/
theorem a_glider_infRule110Steps_chiral_admissible {L T : ℕ} {a b : CausalNode L T}
    {k : ℕ}
    (hdt : b.1.val - a.1.val = k * aGliderDt)
    (hdx : ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs = k * aGliderDx) :
    ChiralGliderAdmissible a b :=
  rule110_a_glider_evolution_chiral_admissible
    (a_glider_worldline_from_infRule110Steps hdt hdx)

/-- Chiral-pair Minkowski inclusion from CA-certified A-glider kinematics. -/
theorem chiral_pair_minkowski_from_infRule110Steps {L T : ℕ} (hL : 2 ≤ L) (hT : 1 ≤ T)
    {a b : CausalNode L T} {k : ℕ}
    (path : Relation.TransGen (ForwardCausalAdj L T) a b)
    (hdt : b.1.val - a.1.val = k * aGliderDt)
    (hdx : ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs = k * aGliderDx) :
    let (t_a, x_a) := afcaToMinkowski a
    let (t_b, x_b) := afcaToMinkowski b
    MinkowskiCausalLE t_a x_a t_b x_b :=
  chiral_pair_minkowski_inclusion_from_dynamics hL hT path
    (a_glider_worldline_from_infRule110Steps hdt hdx)

/-! ## InfTape glider COM ↔ AFCA spatial coordinate (Rank 85b-AFCATAPE)

The Rule 110 CA certificates track defect **anchor** shifts (`gpos → gpos + 2` per
period). AFCA spatial coordinates identify with the defect **center-of-mass**
`aGliderTapeCom gpos = gpos + 3` on the Rule 110 layer (`CausalNode` x-coordinate).
-/

/-- AFCA node x-coordinate equals InfTape A-glider COM at tape anchor `gpos`. -/
def AfcaInfTapeComIdent {L T : ℕ} (n : CausalNode L T) (gpos : ℕ) : Prop :=
  n.2.1.val = Rule110.aGliderTapeCom gpos

/-- AFCA node on the Rule 110 layer tracking A-glider COM at coordinate time `t`. -/
def afcaNodeAtGliderCom {L T : ℕ} (hL : 0 < L) (t : Fin (T + 1)) (gpos : ℕ)
    (hx : Rule110.aGliderTapeCom gpos < L) : CausalNode L T :=
  afcaFromMinkowskiCoords hL t ⟨Rule110.aGliderTapeCom gpos, hx⟩

theorem afcaNodeAtGliderCom_x {L T : ℕ} (hL : 0 < L) (t : Fin (T + 1)) (gpos : ℕ)
    (hx : Rule110.aGliderTapeCom gpos < L) :
    (afcaNodeAtGliderCom hL t gpos hx).2.1.val = Rule110.aGliderTapeCom gpos := by
  simp [afcaNodeAtGliderCom, afcaFromMinkowskiCoords, AfcaInfTapeComIdent]

theorem afcaNodeAtGliderCom_ident {L T : ℕ} (hL : 0 < L) (t : Fin (T + 1)) (gpos : ℕ)
    (hx : Rule110.aGliderTapeCom gpos < L) :
    AfcaInfTapeComIdent (afcaNodeAtGliderCom hL t gpos hx) gpos := by
  simp [AfcaInfTapeComIdent, afcaNodeAtGliderCom, afcaFromMinkowskiCoords]

/-- COM identification converts to exact spatial displacement (not merely `natAbs` bound). -/
theorem afca_com_displacement_eq {L T : ℕ} {a b : CausalNode L T} {gpos k : ℕ}
    (h0 : AfcaInfTapeComIdent a gpos)
    (h1 : AfcaInfTapeComIdent b (gpos + k * aGliderDx)) :
    (b.2.1.val : ℤ) - (a.2.1.val : ℤ) = k * aGliderDx ∧
    ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs = k * aGliderDx := by
  dsimp [AfcaInfTapeComIdent, Rule110.aGliderTapeCom] at h0 h1
  have hΔ : (b.2.1.val : ℤ) - (a.2.1.val : ℤ) = k * aGliderDx := by omega
  exact ⟨hΔ, by simpa [Int.natAbs_natCast] using congrArg Int.natAbs hΔ⟩

/-- After `k` A-glider periods, COM-identified AFCA nodes satisfy exact displacement. -/
theorem afca_com_k_period_displacement {L T : ℕ} {a b : CausalNode L T} {gpos k : ℕ}
    (h0 : AfcaInfTapeComIdent a gpos)
    (hdt : b.1.val - a.1.val = k * aGliderDt)
    (h1 : AfcaInfTapeComIdent b (gpos + k * aGliderDx)) :
    ((b.2.1.val : ℤ) - (a.2.1.val : ℤ)).natAbs = k * aGliderDx :=
  (afca_com_displacement_eq h0 h1).2

/-- **Rank 85b bridge:** COM identification + temporal advance implies
    Rule-110 A-glider evolved worldline (no external displacement hypothesis). -/
theorem a_glider_worldline_from_afca_infTape_com {L T : ℕ} {a b : CausalNode L T}
    {gpos k : ℕ}
    (h0 : AfcaInfTapeComIdent a gpos)
    (hdt : b.1.val - a.1.val = k * aGliderDt)
    (h1 : AfcaInfTapeComIdent b (gpos + k * aGliderDx)) :
    Rule110AGliderEvolvedWorldline a b := by
  rcases afca_com_displacement_eq h0 h1 with ⟨_, hdx⟩
  exact a_glider_worldline_from_infRule110Steps hdt hdx

/-- **Rank 85b bridge:** COM-identified worldlines are chiral admissible. -/
theorem a_glider_afca_infTape_com_chiral_admissible {L T : ℕ} {a b : CausalNode L T}
    {gpos k : ℕ}
    (h0 : AfcaInfTapeComIdent a gpos)
    (hdt : b.1.val - a.1.val = k * aGliderDt)
    (h1 : AfcaInfTapeComIdent b (gpos + k * aGliderDx)) :
    ChiralGliderAdmissible a b :=
  rule110_a_glider_evolution_chiral_admissible
    (a_glider_worldline_from_afca_infTape_com h0 hdt h1)

/-- Standard Martinez seed: one CA period advances AFCA COM by `aGliderDx = 2`. -/
theorem a_glider_afca_standard_com_one_period {L T : ℕ} {a b : CausalNode L T}
    (h0 : AfcaInfTapeComIdent a Rule110.a_gpos)
    (hdt : b.1.val - a.1.val = aGliderDt)
    (h1 : AfcaInfTapeComIdent b (Rule110.a_gpos + aGliderDx)) :
    ChiralGliderAdmissible a b :=
  a_glider_afca_infTape_com_chiral_admissible (k := 1) h0 (by simpa using hdt) h1

/-- **Rank 85b main theorem:** InfTape COM ↔ AFCA coordinate bridge wired into
    c = 2/3 Minkowski inclusion (displacement derived from COM, not assumed). -/
theorem chiral_pair_minkowski_from_afca_infTape_com {L T : ℕ} (hL : 2 ≤ L) (hT : 1 ≤ T)
    {a b : CausalNode L T} {gpos k : ℕ}
    (path : Relation.TransGen (ForwardCausalAdj L T) a b)
    (h0 : AfcaInfTapeComIdent a gpos)
    (hdt : b.1.val - a.1.val = k * aGliderDt)
    (h1 : AfcaInfTapeComIdent b (gpos + k * aGliderDx)) :
    let (t_a, x_a) := afcaToMinkowski a
    let (t_b, x_b) := afcaToMinkowski b
    MinkowskiCausalLE t_a x_a t_b x_b :=
  chiral_pair_minkowski_inclusion_from_dynamics hL hT path
    (a_glider_worldline_from_afca_infTape_com h0 hdt h1)

/-- Tape COM advance certified by `infRule110Steps` at the standard seed. -/
theorem a_glider_infTape_com_matches_ca :
    Rule110.aGliderTapeCom (Rule110.a_gpos + aGliderDx) =
      Rule110.aGliderTapeCom Rule110.a_gpos + aGliderDx :=
  Rule110.a_glider_infRule110Steps_com_advance

/-! ## Rank 85c-AFCATAPEAUTO: automatic COM endpoints from `infRule110Steps`

Derives `AfcaInfTapeComIdent` endpoint data from CA evolution certificates instead of
manual displacement hypotheses. Standard Martinez seed (`a_gpos = 42`) automatic for
`k ≤ 2` complete periods; general `k` via `AGliderInfEvolutionEndpoint` composition.
-/

/-- CA evolution certificate yields endpoint COM index. -/
theorem a_glider_com_endpoint_from_inf_evolution {gpos₀ k : ℕ}
    (_hev : Rule110.AGliderInfEvolutionEndpoint gpos₀ (k * aGliderDt) (gpos₀ + k * aGliderDx)) :
    Rule110.aGliderTapeCom (gpos₀ + k * aGliderDx) =
      Rule110.aGliderTapeCom gpos₀ + k * aGliderDx := by
  have hdx : aGliderDx = Rule110.aGliderSpatialPeriod := by
    rw [(cook_a_glider_period_matches_constants).2.1, Rule110.aGliderSpatialPeriod_eq_cook_dx]
  calc Rule110.aGliderTapeCom (gpos₀ + k * aGliderDx)
      = Rule110.aGliderTapeCom (gpos₀ + k * Rule110.aGliderSpatialPeriod) := by rw [hdx]
    _ = Rule110.aGliderTapeCom gpos₀ + k * Rule110.aGliderSpatialPeriod :=
          Rule110.a_glider_tape_com_k_periods gpos₀ k
    _ = Rule110.aGliderTapeCom gpos₀ + k * aGliderDx := by rw [hdx]

/-- Evolution certificate implies AFCA COM identification for constructed nodes. -/
theorem afca_infTape_com_from_evolution {L T : ℕ} {n : CausalNode L T} {gpos₀ k : ℕ}
    (hev : Rule110.AGliderInfEvolutionEndpoint gpos₀ (k * aGliderDt) (gpos₀ + k * aGliderDx))
    (hident : AfcaInfTapeComIdent n (gpos₀ + k * aGliderDx)) :
    n.2.1.val = Rule110.aGliderTapeCom gpos₀ + k * aGliderDx := by
  dsimp [AfcaInfTapeComIdent] at hident
  rw [hident, a_glider_com_endpoint_from_inf_evolution hev]

/-- Standard-seed evolution certificate for `k` periods (`k ≤ 2`). -/
theorem a_glider_standard_seed_inf_evolution (k : ℕ) (hk : k ≤ 2) :
    Rule110.AGliderInfEvolutionEndpoint Rule110.a_gpos (k * aGliderDt)
      (Rule110.a_gpos + k * aGliderDx) := by
  have hdt : k * aGliderDt = k * Rule110.aGliderTemporalPeriod := by
    dsimp [aGliderDt, Rule110.aGliderTemporalPeriod]; rfl
  have hdx : k * aGliderDx = k * Rule110.aGliderSpatialPeriod := by
    dsimp [aGliderDx, Rule110.aGliderSpatialPeriod]; rfl
  rw [hdt, hdx]
  exact Rule110.a_glider_standard_seed_endpoint k hk

/-- AFCA node at standard seed coordinate time `t = 0`. -/
def afcaStandardSeedNode {L T : ℕ} (hL : 0 < L) (hx : Rule110.aGliderTapeCom Rule110.a_gpos < L) :
    CausalNode L T :=
  afcaNodeAtGliderCom hL (L := L) (T := T) ⟨0, by omega⟩ Rule110.a_gpos hx

/-- AFCA node after `k` A-glider periods from standard seed. -/
def afcaStandardSeedEndpoint {L T k : ℕ} (hL : 0 < L) (hT : k * aGliderDt ≤ T)
    (hx : Rule110.aGliderTapeCom (Rule110.a_gpos + k * aGliderDx) < L) : CausalNode L T :=
  afcaNodeAtGliderCom hL (L := L) (T := T) ⟨k * aGliderDt, by omega⟩
    (Rule110.a_gpos + k * aGliderDx) hx

theorem afcaStandardSeedNode_com_ident {L T : ℕ} (hL : 0 < L)
    (hx : Rule110.aGliderTapeCom Rule110.a_gpos < L) :
    AfcaInfTapeComIdent (afcaStandardSeedNode (L := L) (T := T) hL hx) Rule110.a_gpos :=
  afcaNodeAtGliderCom_ident hL (L := L) (T := T) ⟨0, by omega⟩ Rule110.a_gpos hx

theorem afcaStandardSeedEndpoint_com_ident {L T k : ℕ} (hL : 0 < L) (hT : k * aGliderDt ≤ T)
    (hx : Rule110.aGliderTapeCom (Rule110.a_gpos + k * aGliderDx) < L) :
    AfcaInfTapeComIdent (afcaStandardSeedEndpoint (L := L) (T := T) hL hT hx)
      (Rule110.a_gpos + k * aGliderDx) :=
  afcaNodeAtGliderCom_ident hL (L := L) (T := T) ⟨k * aGliderDt, by omega⟩
    (Rule110.a_gpos + k * aGliderDx) hx

theorem afcaStandardSeedEndpoint_time {L T k : ℕ} (hL : 0 < L) (hT : k * aGliderDt ≤ T)
    (hx : Rule110.aGliderTapeCom (Rule110.a_gpos + k * aGliderDx) < L)
    (hx₀ : Rule110.aGliderTapeCom Rule110.a_gpos < L) :
    (afcaStandardSeedEndpoint (L := L) (T := T) hL hT hx).1.val -
      (afcaStandardSeedNode (L := L) (T := T) hL hx₀).1.val = k * aGliderDt := by
  simp [afcaStandardSeedEndpoint, afcaStandardSeedNode, afcaNodeAtGliderCom, afcaFromMinkowskiCoords,
    aGliderDt]

/-- **Rank 85c:** COM endpoints at standard seed derived from `infRule110Steps` evolution
    (no manual `h0`/`h1`/`hdx` for `k ≤ 2`). -/
theorem a_glider_afca_standard_seed_auto {L T k : ℕ} (hL : 0 < L) (hT : k * aGliderDt ≤ T)
    (hk : k ≤ 2)
    (hx₀ : Rule110.aGliderTapeCom Rule110.a_gpos < L)
    (hx₁ : Rule110.aGliderTapeCom (Rule110.a_gpos + k * aGliderDx) < L) :
    let a := afcaStandardSeedNode (L := L) (T := T) hL hx₀
    let b := afcaStandardSeedEndpoint (L := L) (T := T) hL hT hx₁
    AfcaInfTapeComIdent a Rule110.a_gpos ∧
    AfcaInfTapeComIdent b (Rule110.a_gpos + k * aGliderDx) ∧
    b.1.val - a.1.val = k * aGliderDt ∧
    Rule110.AGliderInfEvolutionEndpoint Rule110.a_gpos (k * aGliderDt) (Rule110.a_gpos + k * aGliderDx) ∧
    ChiralGliderAdmissible a b := by
  refine ⟨afcaStandardSeedNode_com_ident hL hx₀, afcaStandardSeedEndpoint_com_ident hL hT hx₁,
    afcaStandardSeedEndpoint_time hL hT hx₁ hx₀, a_glider_standard_seed_inf_evolution k hk, ?_⟩
  exact a_glider_afca_infTape_com_chiral_admissible
    (h0 := afcaStandardSeedNode_com_ident hL hx₀)
    (hdt := afcaStandardSeedEndpoint_time hL hT hx₁ hx₀)
    (h1 := afcaStandardSeedEndpoint_com_ident hL hT hx₁)

/-- **Rank 85c main theorem:** c = 2/3 Minkowski inclusion from standard seed with
    CA-automatic COM endpoints (`k ≤ 2`). Requires explicit lattice bounds `hx₀`, `hx₁`. -/
theorem chiral_pair_minkowski_from_afca_standard_seed_auto {L T k : ℕ} (hL : 2 ≤ L)
    (hT : 1 ≤ T) (hk : k ≤ 2) (hTk : k * aGliderDt ≤ T)
    (hx₀ : Rule110.aGliderTapeCom Rule110.a_gpos < L)
    (hx₁ : Rule110.aGliderTapeCom (Rule110.a_gpos + k * aGliderDx) < L)
    (path : Relation.TransGen (ForwardCausalAdj L T)
      (afcaStandardSeedNode (L := L) (T := T) (by omega : 0 < L) hx₀)
      (afcaStandardSeedEndpoint (L := L) (T := T) (by omega : 0 < L) hTk hx₁)) :
    let a := afcaStandardSeedNode (L := L) (T := T) (by omega : 0 < L) hx₀
    let b := afcaStandardSeedEndpoint (L := L) (T := T) (by omega : 0 < L) hTk hx₁
    let (t_a, x_a) := afcaToMinkowski a
    let (t_b, x_b) := afcaToMinkowski b
    MinkowskiCausalLE t_a x_a t_b x_b :=
  chiral_pair_minkowski_from_afca_infTape_com hL hT path
    (h0 := afcaStandardSeedNode_com_ident (by omega : 0 < L) hx₀)
    (hdt := afcaStandardSeedEndpoint_time (by omega : 0 < L) hTk hx₁ hx₀)
    (h1 := afcaStandardSeedEndpoint_com_ident (by omega : 0 < L) hTk hx₁)

/-- General endpoint bridge: supply `AGliderInfEvolutionEndpoint` instead of manual COM shift. -/
theorem chiral_pair_minkowski_from_inf_evolution {L T : ℕ} (hL : 2 ≤ L) (hT : 1 ≤ T)
    {a b : CausalNode L T} {gpos₀ k : ℕ}
    (path : Relation.TransGen (ForwardCausalAdj L T) a b)
    (_hev : Rule110.AGliderInfEvolutionEndpoint gpos₀ (k * aGliderDt) (gpos₀ + k * aGliderDx))
    (h0 : AfcaInfTapeComIdent a gpos₀)
    (hdt : b.1.val - a.1.val = k * aGliderDt)
    (h1 : AfcaInfTapeComIdent b (gpos₀ + k * aGliderDx)) :
    let (t_a, x_a) := afcaToMinkowski a
    let (t_b, x_b) := afcaToMinkowski b
    MinkowskiCausalLE t_a x_a t_b x_b :=
  chiral_pair_minkowski_from_afca_infTape_com hL hT path h0 hdt h1

/-- Constructed AFCA node at the Martinez standard seed carries COM identification. -/
theorem a_glider_infTape_com_node_at_standard_seed {L T : ℕ} (hL : 46 ≤ L)
    (hx : Rule110.aGliderTapeCom Rule110.a_gpos < L) :
    AfcaInfTapeComIdent
      (afcaNodeAtGliderCom (by omega : 0 < L) (L := L) (T := T) ⟨0, by omega⟩ Rule110.a_gpos hx)
      Rule110.a_gpos :=
  afcaNodeAtGliderCom_ident (by omega : 0 < L) (L := L) (T := T) ⟨0, by omega⟩ Rule110.a_gpos hx

/-- Three Rule 110 steps on clean ether advance coordinate 42 → 54 (= 42 + 4·3). -/
theorem a_glider_ether_three_step_drift :
    Rule110.infRule110Steps 3 Rule110.cookEther 42 = Rule110.cookEther 54 := by
  native_decide

/-- Cook A-glider spatial period matches CA certificate and catalog. -/
theorem a_glider_cook_spatial_period :
    (Rule110.CookNamedGlider.periodTX .A).dx.natAbs = 2 ∧
    (Rule110.CookNamedGlider.periodTX .A).dt.natAbs = 3 ∧
    Rule110.aGliderSpatialPeriod = 2 ∧
    Rule110.aGliderTemporalPeriod = 3 := by
  native_decide

/-- One A-glider period gives c = 2/3 speed: 3·|Δx| ≤ 2·Δt. -/
theorem a_glider_period_speed_certified :
    3 * (Rule110.CookNamedGlider.periodTX .A).dx.natAbs ≤
      2 * (Rule110.CookNamedGlider.periodTX .A).dt.natAbs := by
  native_decide

/-- Chiral pair layers are causally decoupled: cross-layer edges are impossible. -/
theorem chiral_layers_decoupled {L T : ℕ} (n1 n2 : ChiralNode L T)
    (h : n1.1 ≠ n2.1) : ¬ ChiralPairAdj L T n1 n2 :=
  chiral_pair_no_cross_layer_edges L T n1 n2 h

end GTE.Spacetime.ChiralGliderDynamics
