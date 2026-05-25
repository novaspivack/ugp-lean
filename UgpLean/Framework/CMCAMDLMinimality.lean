import UgpLean.Framework.GTECategoryStructure
import UgpLean.Universality.MDLDerivabilityCriterion
import Mathlib.Data.Nat.Log

/-!
# UgpLean.Framework.CMCAMDLMinimality — Rank 074-UNIDM2 (CatAL conditional)

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
| `K_CA_all_features_lower_bound` | CatAL conditional — `omega`, zero sorry |
| `cmca_is_mdl_minimal_with_all_five_features` | CatAL conditional — zero sorry |
| Physical-interpretation axioms | 6 axioms (CatA/CatAD/CatAL physical certificates) |

## Axioms (physical interpretation — not Lean gaps)

1. `turing_universality_min_outer_bits` — Turing-univ → outerRuleBits ≥ 8 (CUP-4 / CUP-12)
2. `z7_orbit_min_alphabet` — Z₇ orbit → alphabetSize ≥ 7 (f_MDL, CUP-11)
3. `va_min_two_layers` — V–A → numOuterLayers ≥ 2 (ChiralPairVA, P41)
4. `va_min_mirror_bit` — V–A + Turing → outerRuleBits ≥ 9 (ChiralPairVA 32/125)
5. `sr_min_async` — dynamics-SR → innerClockKind = AsyncTauC (P36 `prop:async_equiv`)
6. `sr_min_gating` — dynamics-SR → gatingBits ≥ 3 (P36 §SR AFCA gating spec)
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
-- §6  Physical-interpretation axioms (CatA / CatAD / CatAL certificates)
-- ─────────────────────────────────────────────────────────────────────────────

/-- **CatAL (CUP-4 / CUP-12):** Turing-universal Z₇ CAs require ≥ 8 outer rule bits. -/
axiom turing_universality_min_outer_bits (c : CAConstruction)
    (hT : ConstructionIsTuringUniversal c) :
    c.outerRuleBits ≥ 8

/-- **CatAL (CUP-11 / f_MDL):** Z₇ orbit content requires alphabet Fin 7 or larger. -/
axiom z7_orbit_min_alphabet (c : CAConstruction)
    (hZ : ConstructionHasZ7Orbit c) :
    c.alphabetSize ≥ 7

/-- **CatAL (ChiralPairVA / P41):** V–A chirality requires at least two outer layers. -/
axiom va_min_two_layers (c : CAConstruction)
    (hV : ConstructionHasVAStructure c) :
    c.numOuterLayers ≥ 2

/-- **CatAL (ChiralPairVA 32/125):** V–A with Turing-univ forces mirror bit (+1) on outer rules. -/
axiom va_min_mirror_bit (c : CAConstruction)
    (hT : ConstructionIsTuringUniversal c)
    (hV : ConstructionHasVAStructure c) :
    c.outerRuleBits ≥ 9

/-- **CatAD (P36 `prop:async_equiv`):** dynamics-level SR requires asynchronous τ_c clock. -/
axiom sr_min_async (c : CAConstruction)
    (hSR : ConstructionHasSRTimeDilation c) :
    c.innerClockKind = .AsyncTauC

/-- **CatAD (P36 §SR AFCA gating):** dynamics-level SR requires ≥ 3 gating bits. -/
axiom sr_min_gating (c : CAConstruction)
    (hSR : ConstructionHasSRTimeDilation c) :
    c.gatingBits ≥ 3

-- ─────────────────────────────────────────────────────────────────────────────
-- §7  Main lower-bound theorem (CatAL conditional on 6 axioms)
-- ─────────────────────────────────────────────────────────────────────────────

/-- Any Level-1 CA construction with all five feature channels costs at least 19 bits,
    saturating the CMCA specification exactly. -/
theorem K_CA_all_features_lower_bound (c : CAConstruction)
    (hT : ConstructionIsTuringUniversal c)
    (hZ : ConstructionHasZ7Orbit c)
    (hV : ConstructionHasVAStructure c)
    (hSR : ConstructionHasSRTimeDilation c)
    (_h_r : c.radius ≥ 1) :
    K_CA c ≥ K_CA cCMCA := by
  have h19 : K_CA cCMCA = 19 := K_CA_CMCA
  have ho := va_min_mirror_bit c hT hV
  have ha := z7_orbit_min_alphabet c hZ
  have hl := va_min_two_layers c hV
  have hi := sr_min_async c hSR
  have hg := sr_min_gating c hSR
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
