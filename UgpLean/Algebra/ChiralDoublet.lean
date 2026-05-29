import UgpLean.Spacetime.ChiralPairDecoupling
import UgpLean.Spacetime.ChiralMirrorSpeedSymmetry

/-!
# Chiral Doublet: Rule 124 = Rule 110 with L↔R reflection

Rule 124 is the spatial reflection (L↔R) of Rule 110.
The (outer_plus, outer_minus) = (Rule110, Rule124) doublet is a genuine parity doublet.
This is the Level 1 certificate for V-A chirality.

Lookup tables use Wolfram codes 110 = 0b01101110 and 124 = 0b01111100 on `{0,1}³`.
-/

namespace ChiralDoublet

open GTE.Spacetime.ChiralPair
open GTE.Spacetime.ChiralMirrorSpeedSymmetry

/-- Rule 110 lookup on binary neighborhoods (Wolfram code 110). -/
def rule110 (l c r : Fin 2) : Fin 2 := rule110Fin2 l c r

/-- Rule 124 lookup on binary neighborhoods (Wolfram code 124). -/
def rule124 (l c r : Fin 2) : Fin 2 := rule124Fin2 l c r

/-- Rule 124 is Rule 110 with left and right neighbors swapped -/
theorem rule124_eq_rule110_reflected :
    ∀ (l c r : Fin 2), rule124 l c r = rule110 r c l :=
  rule124Fin2_is_spatial_mirror

/-- Corollary: the (Rule110, Rule124) doublet is a parity doublet -/
theorem chiral_doublet_is_parity_doublet :
    ∀ (l c r : Fin 2),
      rule124 l c r = rule110 r c l ∧
      rule110 l c r = rule124 r c l := by
  intro l c r
  constructor
  · exact rule124_eq_rule110_reflected l c r
  · exact (rule124_eq_rule110_reflected r c l).symm

end ChiralDoublet
