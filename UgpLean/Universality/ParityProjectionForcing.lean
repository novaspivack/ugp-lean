import Mathlib
import UgpLean.Universality.TriangleLiftTheorem
import UgpLean.Universality.ParityProjectionBattery
import UgpLean.Polynomial.PolyExplorations

/-!
# Parity-projection forcing over the admissible reduction space

Certifies the φ-Forcing Scope Theorem additive and mod-2 recoding cores:
exhaustive `native_decide` censuses over all $777$ additive homomorphisms and
$16\\,807$ mod-2 recodings into $\\mathrm{GF}(7)$, with shadow-closure and
Rule-106 product-parity displaced-vacuum exclusion.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Universality.ParityProjectionForcing

open UgpLean.Universality.TriangleLiftTheorem
open UgpLean.Universality.ParityProjectionBattery
open UgpLean.Polynomial.PolyExplorations

/-- Unit conjugate coefficient vectors `g_t` for `t ∈ {1,2,3}`. -/
def unitConjugateCoeffs (t : ℕ) : Array (ZMod 7) :=
  match t with
  | 1 => polyPCoeffs
  | 2 => #[0, 0, 1, 1, 0, 0, 3, 5]
  | 3 => #[0, 0, 1, 1, 0, 0, 2, 3]
  | _ => polyPCoeffs

/-- Parity-factoring weighted forms `(α,β,γ) mod m`. -/
def isParityFactoringForm (α β γ m : ℕ) : Bool :=
  (α = 1 ∧ β = 1 ∧ γ = 1 ∧ m = 2) ∨
    (α = 2 ∧ β = 2 ∧ γ = 2 ∧ m = 4) ∨
    (α = 3 ∧ β = 3 ∧ γ = 3 ∧ m = 6)

private def additiveFormCount : ℕ := 777

/-- **parity_projection_additive_forcing** (CatAL): exhaustive additive homomorphism
    battery over all $777$ nonzero forms with $2 \\leq m \\leq 7$.  Status census
    $277/490/5/5$; exactly three shadow-closed FORCED survivors (parity-factoring
    forms) forcing $g_1=p$, $g_2$, $g_3$. -/
private def parity_projection_additive_forcing_proof :=
  And.intro additive_battery_totals <|
    And.intro additive_battery_mod_two <|
      And.intro additive_battery_mod_three <|
        And.intro additive_battery_mod_four <|
          And.intro additive_battery_mod_five <|
            And.intro additive_battery_mod_six <|
              And.intro additive_battery_mod_seven <|
                And.intro (show isParityFactoringForm 1 1 1 2 = true by native_decide) <|
                  And.intro (show isParityFactoringForm 2 2 2 4 = true by native_decide) <|
                    And.intro (show isParityFactoringForm 3 3 3 6 = true by native_decide) <|
                      And.intro (show unitConjugateCoeffs 1 = polyPCoeffs by native_decide) <|
                        And.intro
                          (show unitConjugateCoeffs 2 = #[0, 0, 1, 1, 0, 0, 3, 5] by native_decide) <|
                          And.intro
                            (show unitConjugateCoeffs 3 = #[0, 0, 1, 1, 0, 0, 2, 3] by native_decide) <|
                            And.intro
                              (show satisfiesOrbitVTConstraints (unitConjugateCoeffs 1) = true by
                                native_decide) <|
                              And.intro unit_conjugate_two_forced_scc unit_conjugate_three_forced_scc

def parity_projection_additive_forcing :=
  parity_projection_additive_forcing_proof

/-- **parity_projection_mod2_recoding_forcing** (CatAL): exhaustive mod-2 recoding
    census over $7^5 = 16\\,807$ assignments.  Status census
    $7392/8820/343/252$; twelve shadow-closed FORCED assignments split into six
    parity-factor survivors $t\\cdot\\varphi$ and six Rule-106 product-parity
    displaced-vacuum exclusions. -/
private def parity_projection_mod2_recoding_forcing_proof :=
  And.intro (show 7 ^ 5 = 16807 by native_decide) <|
    And.intro mod2_recoding_totals <|
      And.intro mod2_recoding_chunk_zero <|
        And.intro mod2_recoding_chunk_one <|
          And.intro mod2_recoding_chunk_two <|
            And.intro mod2_recoding_chunk_three <|
              And.intro mod2_recoding_chunk_four <|
                And.intro mod2_recoding_chunk_five mod2_recoding_chunk_six

def parity_projection_mod2_recoding_forcing :=
  parity_projection_mod2_recoding_forcing_proof

end UgpLean.Universality.ParityProjectionForcing
