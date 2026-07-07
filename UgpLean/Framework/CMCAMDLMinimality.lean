import UgpLean.Framework.GTECategoryStructure
import UgpLean.Universality.MDLDerivabilityCriterion
import Mathlib.Data.Nat.Log

/-!
# UgpLean.Framework.CMCAMDLMinimality (CatAL conditional)

Lean certification that the **two-layer chiral AFCA (CMCA)** is the MDL-minimal
Level-1 discrete CA construction carrying all five GTE structural features.

## Six-channel MDL functional

`K_CA(c) = K_α + K_r + K_L + K_ρ_outer + K_τ + K_g`

Prefix-free `log₂+1` cost for cardinal channels; per-bit rule-table cost; MDL sharing
(inner = outer rule reuse = 0 extra bits); Z₂ mirror principle (+1 bit for R124 given R110).

## Certification status

| Component | Status |
|-----------|--------|
| `CAConstruction`, `K_CA`, four instances | CatAL — zero sorry, `decide` |
| `K_CA_all_features_lower_bound` | CatAL conditional — zero sorry |
| `cmca_is_mdl_minimal_with_all_five_features` | CatAL conditional — zero sorry |
| Physical-interpretation axioms | 1 axiom (CatAL physical certificate) |

## Axiom (physical interpretation — not a Lean gap)

`va_min_mirror_bit` — V–A + Turing universality forces the outer-rule-table channel
to carry one additional "mirror flag" bit (outerRuleBits ≥ 9) beyond the 8 bits needed
to specify Rule 110 alone, because Rule 124 is fully determined as the spatial mirror
of Rule 110 (`ChiralPairVA.rule124 l c r := rule110 r c l`) and therefore costs exactly
one extra bit to select, not a second independent 8-bit table.

### Note on the four channel-membership predicates

`ConstructionIsTuringUniversal`, `ConstructionHasZ7Orbit`, `ConstructionHasVAStructure`,
and the first conjunct of `ConstructionHasSRTimeDilation` are *definitions*
(`c.outerRuleBits ≥ 8`, `c.alphabetSize ≥ 7`, `c.numOuterLayers ≥ 2`,
`c.innerClockKind = .AsyncTauC`, `c.gatingBits ≥ 3` respectively) — the corresponding
channel bound is available directly from unfolding the hypothesis, with no axiom
required. A prior version of this module additionally declared five axioms
(`turing_universality_min_outer_bits`, `z7_orbit_min_alphabet`, `va_min_two_layers`,
`sr_min_async`, `sr_min_gating`) whose conclusions were syntactically identical to
their own hypotheses after unfolding — literal `P → P` tautologies contributing no
physical content beyond the definitions themselves. They have been removed;
`K_CA_all_features_lower_bound` now derives its four definitional bounds directly
from `hZ`, `hV`, and `hSR`, and depends on exactly one substantive axiom
(`va_min_mirror_bit`).
-/

namespace UgpLean.Framework.CMCAMDL

open UgpLean.Framework.GTECategory
open UgpLean.Universality.MDLDerivability

-- ─────────────────────────────────────────────────────────────────────────────
-- §1  CA construction record (six informational channels)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Inner clock structure: synchronous update vs asynchronous τ_c gating. -/
inductive InnerClock
  | Sync
  | AsyncTauC
  deriving DecidableEq, Repr

/-- Parametric Level-1 CA construction specification across six MDL channels. -/
structure CAConstruction where
  alphabetSize    : ℕ
  radius          : ℕ
  numOuterLayers  : ℕ
  outerRuleBits   : ℕ
  innerClockKind  : InnerClock
  gatingBits      : ℕ
  deriving DecidableEq, Repr

-- ─────────────────────────────────────────────────────────────────────────────
-- §2  K_CA description-length functional
-- ─────────────────────────────────────────────────────────────────────────────

/-- Bit cost of the inner-clock channel. -/
def innerClockBits : InnerClock → ℕ
  | .Sync     => 0
  | .AsyncTauC => 1

/-- Six-channel prefix-free MDL description length for a Level-1 CA construction. -/
def K_CA (c : CAConstruction) : ℕ :=
  primaryFieldBits c.alphabetSize
  + primaryFieldBits (max c.radius 1)
  + primaryFieldBits c.numOuterLayers
  + c.outerRuleBits
  + innerClockBits c.innerClockKind
  + c.gatingBits

-- ─────────────────────────────────────────────────────────────────────────────
-- §3  Four Level-1 construction instances
-- ─────────────────────────────────────────────────────────────────────────────

/-- Single-layer Rule 110, synchronous (baseline). -/
def cSingleR110 : CAConstruction := ⟨7, 1, 1, 8, .Sync, 0⟩

/-- Two-layer chiral (R110 + R124 mirror), synchronous. -/
def cTwoLayerChiral : CAConstruction := ⟨7, 1, 2, 9, .Sync, 0⟩

/-- Single-layer AFCA with asynchronous τ_c gating. -/
def cAFCA : CAConstruction := ⟨7, 1, 1, 8, .AsyncTauC, 3⟩

/-- Two-layer chiral AFCA (CMCA): all five Level-1 features at finite M. -/
def cCMCA : CAConstruction := ⟨7, 1, 2, 9, .AsyncTauC, 3⟩

theorem K_CA_singleR110 : K_CA cSingleR110 = 13 := by decide

theorem K_CA_twoLayerChiral : K_CA cTwoLayerChiral = 15 := by decide

theorem K_CA_AFCA : K_CA cAFCA = 17 := by decide

theorem K_CA_CMCA : K_CA cCMCA = 19 := by decide

/-- Strict MDL gap: CMCA exceeds every construction lacking at least one feature channel. -/
theorem K_CA_CMCA_gt_others :
    K_CA cSingleR110 < K_CA cCMCA ∧
    K_CA cTwoLayerChiral < K_CA cCMCA ∧
    K_CA cAFCA < K_CA cCMCA := by
  refine ⟨?_, ?_, ?_⟩ <;> decide

-- ─────────────────────────────────────────────────────────────────────────────
-- §4  Construction-level feature predicates
-- ─────────────────────────────────────────────────────────────────────────────

/-- Turing computational universality at the construction level. -/
def ConstructionIsTuringUniversal (c : CAConstruction) : Prop :=
  c.outerRuleBits ≥ 8

/-- Realizes the SM Z₇ generation orbit / f_MDL winding content. -/
def ConstructionHasZ7Orbit (c : CAConstruction) : Prop :=
  c.alphabetSize ≥ 7

/-- Carries discrete V–A chirality (two outer layers with mirror relation). -/
def ConstructionHasVAStructure (c : CAConstruction) : Prop :=
  c.numOuterLayers ≥ 2

/-- Dynamics-level SR time dilation via asynchronous τ_c gating. -/
def ConstructionHasSRTimeDilation (c : CAConstruction) : Prop :=
  c.innerClockKind = .AsyncTauC ∧ c.gatingBits ≥ 3

-- ─────────────────────────────────────────────────────────────────────────────
-- §5  Bridge from enumerated GTELevel1Object to CAConstruction
-- ─────────────────────────────────────────────────────────────────────────────

/-- Assign each Level-1 category object its canonical six-channel MDL specification. -/
def constructionOf : GTELevel1Object → CAConstruction
  | .SingleLayerR110     => cSingleR110
  | .TwoLayerChiral      => cTwoLayerChiral
  | .AFCA                => cAFCA
  | .TwoLayerChiralAFCA  => cCMCA
  | .PhiMDL              => cCMCA

-- ─────────────────────────────────────────────────────────────────────────────
-- §6  Physical-interpretation axiom (CatAL certificate)
-- ─────────────────────────────────────────────────────────────────────────────

/-- **CatAL (ChiralPairVA — Rule 124 as spatial mirror of Rule 110):** a Turing-universal
    outer rule table (≥ 8 bits) combined with a second, mirror-related outer layer
    (V–A structure, ≥ 2 layers) forces the outer-rule-table channel to ≥ 9 bits: the
    mirror layer is fully determined by the primary rule table up to a one-bit
    "mirror flag" (`ChiralPairVA.rule124 l c r := rule110 r c l`), rather than requiring
    a second independent 8-bit table. -/
axiom va_min_mirror_bit (c : CAConstruction)
    (hT : ConstructionIsTuringUniversal c)
    (hV : ConstructionHasVAStructure c) :
    c.outerRuleBits ≥ 9

-- ─────────────────────────────────────────────────────────────────────────────
-- §7  Main lower-bound theorem (CatAL conditional on one axiom)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Any Level-1 CA construction with all five feature channels costs at least 19 bits,
    saturating the CMCA specification exactly.

    Three of the four non-mirror channel bounds (`ha`, `hl`, `hi`/`hg`) follow directly
    from unfolding `ConstructionHasZ7Orbit`, `ConstructionHasVAStructure`, and
    `ConstructionHasSRTimeDilation` — no axiom is needed for them. Only the mirror-bit
    channel bound (`ho`) requires the substantive `va_min_mirror_bit` axiom. -/
theorem K_CA_all_features_lower_bound (c : CAConstruction)
    (hT : ConstructionIsTuringUniversal c)
    (hZ : ConstructionHasZ7Orbit c)
    (hV : ConstructionHasVAStructure c)
    (hSR : ConstructionHasSRTimeDilation c)
    (_h_r : c.radius ≥ 1) :
    K_CA c ≥ K_CA cCMCA := by
  have h19 : K_CA cCMCA = 19 := K_CA_CMCA
  have ho := va_min_mirror_bit c hT hV
  have ha : c.alphabetSize ≥ 7 := hZ
  have hl : c.numOuterLayers ≥ 2 := hV
  have hi : c.innerClockKind = .AsyncTauC := hSR.1
  have hg : c.gatingBits ≥ 3 := hSR.2
  have hge19 : K_CA c ≥ 19 := by
    unfold K_CA primaryFieldBits innerClockBits
    rw [hi]
    simp only [innerClockBits]
    have hla : Nat.log2 c.alphabetSize + 1 ≥ 3 := by
      have ha0 : c.alphabetSize ≠ 0 := by omega
      have hpow : 2 ^ 2 ≤ c.alphabetSize := by
        calc
          2 ^ 2 = 4 := by decide
          _ ≤ 7 := by decide
          _ ≤ c.alphabetSize := ha
      have := (Nat.le_log2 ha0).2 hpow
      omega
    have hll : Nat.log2 c.numOuterLayers + 1 ≥ 2 := by
      by_cases hl0 : c.numOuterLayers = 0
      · rw [hl0] at hl
        omega
      have hpow : 2 ^ 1 ≤ c.numOuterLayers := by omega
      have := (Nat.le_log2 hl0).2 hpow
      omega
    have hr : Nat.log2 (max c.radius 1) + 1 ≥ 1 := by
      have : Nat.log2 (max c.radius 1) ≥ 0 := Nat.zero_le _
      omega
    omega
  exact h19.symm ▸ hge19

-- ─────────────────────────────────────────────────────────────────────────────
-- §8  Master theorem — CMCA is MDL-minimal with all five features
-- ─────────────────────────────────────────────────────────────────────────────

/-- **CatAL conditional master bundle:** CMCA carries all five Level-1 features,
    achieves exactly 19 MDL bits, is the only finite enumerated object with all features
    (together with Φ_MDL), and saturates the construction-class lower bound. -/
theorem cmca_is_mdl_minimal_with_all_five_features :
    HasAllLevel1Features .TwoLayerChiralAFCA ∧
    K_CA (constructionOf .TwoLayerChiralAFCA) = 19 ∧
    (∀ obj, HasAllLevel1Features obj ↔
        obj = .PhiMDL ∨ obj = .TwoLayerChiralAFCA) ∧
    (∀ c : CAConstruction,
        ConstructionIsTuringUniversal c →
        ConstructionHasZ7Orbit c →
        ConstructionHasVAStructure c →
        ConstructionHasSRTimeDilation c →
        c.radius ≥ 1 →
        K_CA c ≥ 19) := by
  refine ⟨twoLayerChiralAfca_has_all_features, ?_, objects_with_all_features, ?_⟩
  · simp [constructionOf, K_CA_CMCA]
  · intro c hT hZ hV hSR hr
    have := K_CA_all_features_lower_bound c hT hZ hV hSR hr
    rwa [K_CA_CMCA] at this

end UgpLean.Framework.CMCAMDL
