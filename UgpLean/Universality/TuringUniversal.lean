import UgpLean.Universality.UWCAembedsRule110

/-!
# UgpLean.Universality.TuringUniversal — UGP Turing Universality

The UGP substrate is Turing-universal via:
 1. UWCA simulates Rule 110 (proved in UWCAembedsRule110)
 2. Rule 110 is Turing-universal (Cook 2004, cited)

Reference: PRE Dynamics & Universality, Architecture of a Computable Universe
-/

namespace UgpLean.Universality

/-- The UGP substrate is Turing-universal. -/
theorem ugp_is_turing_universal : UGP_substrate_turing_universal :=
  ugp_turing_universal

end UgpLean.Universality
