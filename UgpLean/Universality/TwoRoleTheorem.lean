import UgpLean.Universality.CUP3DUniqueness
import UgpLean.Universality.GUTStructure

/-!
# Two-Role Structural Theorem — Cogwheel vs GTE Cascade
-/

namespace GTE.Universality.TwoRoleTheorem

theorem cogwheel_equal_spacing_fails :
    GUTStructure.b_gen2 ≠ 2 * GUTStructure.b_gen1 ∧
    GUTStructure.b_gen3 ≠ 3 * GUTStructure.b_gen1 := by
  norm_num [GUTStructure.b_gen1, GUTStructure.b_gen2, GUTStructure.b_gen3]

theorem two_roles_non_redundant :
    type_of% GUTStructure.neff_not_monotone_in_tail ∧
    (GUTStructure.b_gen2 ≠ 2 * GUTStructure.b_gen1 ∧
      GUTStructure.b_gen3 ≠ 3 * GUTStructure.b_gen1) := by
  constructor
  · exact GUTStructure.neff_not_monotone_in_tail
  · exact cogwheel_equal_spacing_fails

/-- **two_role_structural_separation** ★ (CatAL skeleton / CatAD physical) -/
theorem two_role_structural_separation :
    type_of% CUP3D.fmdl_vacuum_is_unique_attractor ∧
    (type_of% GUTStructure.gen_orbit_step_lengths ∧
      type_of% GUTStructure.tail_length_strict_ordering) ∧
    (GUTStructure.b_gen1 = 73 ∧
      GUTStructure.b_gen2 = 42 ∧
      GUTStructure.b_gen3 = 275 ∧
      GUTStructure.b_sum = 390) ∧
    type_of% two_roles_non_redundant ∧
    type_of% GUTStructure.mass_quantitative_formula_requires_cascade ∧
    type_of% GUTStructure.mass_ordering_from_tail_length := by
  refine ⟨CUP3D.fmdl_vacuum_is_unique_attractor, ?_, ?_, ?_, ?_, ?_⟩
  · exact ⟨GUTStructure.gen_orbit_step_lengths, GUTStructure.tail_length_strict_ordering⟩
  · norm_num [GUTStructure.b_gen1, GUTStructure.b_gen2, GUTStructure.b_gen3, GUTStructure.b_sum]
  · exact two_roles_non_redundant
  · exact GUTStructure.mass_quantitative_formula_requires_cascade
  · exact GUTStructure.mass_ordering_from_tail_length

end GTE.Universality.TwoRoleTheorem
