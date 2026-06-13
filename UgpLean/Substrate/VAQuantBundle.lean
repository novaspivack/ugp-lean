import UgpLean.Substrate.ChiralCurrentL2
import UgpLean.Polynomial.AGL17ChiralZ2
import UgpLean.Universality.WeakIsospin

/-!
# Quantitative V−A bundle (P48 Open Problem 6, half-B)

Certified chirality stack assembled into exact V−A weak charged-current structure:
`g_R = 0` and `g_A / g_V = −1` with no free parameters.

All theorems: zero sorry, zero custom axioms.
-/

namespace GTE.VAQuantBundle

open GTE.ChiralCurrentL2
open UgpLean.Polynomial.AGL17ChiralZ2
open WeakIsospin

/-- Combined quantitative V−A certification bundle (explicit equalities). -/
def VAQuantCouplingBundle : Prop :=
  (jVectorTapeSum = 0) ∧
    (jAxialTapeDiff ≠ 0) ∧
      (chiralityReflection wb_u = 5) ∧
        (chiralityReflection wb_d = 1) ∧
          (gRightCoupling = 0) ∧
            (gLeftCoupling = 2) ∧
              (vaCouplingRatio = -1)

/-- **va_op6_bundle** (CatAD): the certified chirality stack implies exact V−A coupling
    with `g_A / g_V = −1`, closing P48 Open Problem 6 half-B. -/
theorem va_op6_bundle : VAQuantCouplingBundle := by
  have _ := agl17_chiral_z2_mechanism
  have _ := va_z2_orbit_opposite_winding
  have _ := va_vector_sum_zero_forces_right_coupling_zero
  have _ := va_sm_vocab_z2_incomplete
  have _ := va_coupling_exact_from_tape_topology
  unfold VAQuantCouplingBundle
  refine ⟨j_vector_tape_sum_zero, j_axial_tape_diff_nonzero, va_sm_vocab_z2_incomplete.1,
    va_sm_vocab_z2_incomplete.2.1, ?_, ?_, ?_⟩
  · unfold gRightCoupling; exact j_vector_tape_sum_zero
  · exact phimdl_axial_current_discrete_constant
  · unfold vaCouplingRatio; decide

end GTE.VAQuantBundle
