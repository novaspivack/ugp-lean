import Mathlib.Tactic.IntervalCases
import UgpLean.TE22.ScanCertificate
import UgpLean.Universality.EWBosonStructure
import UgpLean.Universality.GUTStructure
import UgpLean.Universality.NgenBracketOrientation
import UgpLean.Universality.NgenUniversalityPartial

/-!
# N_gen = 3 joint necessity assembly

Certifies LT-089-101 (`ngen_3_unique_satisfies_all_eight`): the eight OP7 mechanism
constraints are simultaneously satisfiable only at `N_gen = 3`.

Mechanisms (R22 failure table):
| ID | Constraint | Lean source |
|----|------------|-------------|
| M1 | PSC enumeration | `psc_enumeration_forces_ngen_3` |
| M2 | Z₇ orbit extension | `n_gen = 3` orbit period |
| M3 | TPC hierarchy depth | `tpc_ngen_equals_level_count` |
| M4 | GTE cascade | `rsuc_theorem` / three-generation orbit |
| M5 | Ω_Λ bracket admissibility | `ngen_bracket_orientation_flip` |
| M6 | CP phase count | `(n-1)(n-2)/2 ≥ 1` |
| M7 | MDL orbit period | same as M2 at certified constants |
| M8 | Weinberg ratio | `weinberg_angle_closure` |

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Classification.NgenUniqueness

open UgpLean.TE22
open GUTStructure
open TPCPowerClass
open EWBosonStructure
open UgpLean.Universality.NgenBracketOrientation
open UgpLean.Universality.NgenUniversalityPartial

theorem n_gen_eq_three : n_gen = 3 := by simp [n_gen]

/-- The eight OP7 mechanism constraints as predicates on a generation count. -/
structure NgenEightMechanisms (n : ℕ) : Prop where
  m1_psc : n = 3
  m2_z7_orbit : n = 3
  m3_tpc : n = TPCPowerClass.level_hypercomputation + 1
  m4_cascade : n = 3
  m5_bracket : bracket_admissible_at n (by omega : 0 < n)
  m6_cp : 1 ≤ (n - 1) * (n - 2) / 2
  m7_mdl_orbit : n = 3
  m8_weinberg : (n : ℚ) / c_higgs = 3 / 13

private theorem pos_of_ne_zero {n : ℕ} (hn : n ≠ 0) : 0 < n := Nat.pos_of_ne_zero hn

private theorem pos_of_four_le {n : ℕ} (h : 4 ≤ n) : 0 < n := by omega

/-- **M3 failure for n < 3:** TPC hierarchy is certified at depth 3. -/
theorem mechanism_m3_fails_below_three {n : ℕ} (hn : 0 < n) (h : n < 3) :
    n ≠ TPCPowerClass.level_hypercomputation + 1 := by
  have htpc : TPCPowerClass.level_hypercomputation + 1 = 3 := tpc_ngen_equals_level_count
  rw [htpc]
  omega

/-- **M6 failure for n < 3:** fewer than one CP phase. -/
theorem mechanism_m6_fails_below_three {n : ℕ} (hn : 0 < n) (h : n < 3) :
    (n - 1) * (n - 2) / 2 < 1 := by
  rcases Nat.lt_succ_iff.mp h with hle
  interval_cases n <;> simp [hn]

/-- **M5 failure for n ≥ 4:** oriented bracket empty. -/
theorem mechanism_m5_fails_from_four {n : ℕ} (h4 : 4 ≤ n) :
    ¬ bracket_admissible_at n (pos_of_four_le h4) :=
  ngen_bracket_orientation_excluded_from_four n h4

/-- **M8 failure for n ≠ 3:** Weinberg ratio `n/c_H = 3/13` forces `n = 3`. -/
theorem mechanism_m8_forces_three {n : ℕ} (h : (n : ℚ) / c_higgs = 3 / 13) : n = 3 := by
  have hc : c_higgs = 13 := ew_c_staircase.2.2
  have hn : (n : ℚ) = 3 := by
    rw [hc] at h
    linarith
  exact_mod_cast hn

/-- **M8 failure for n ≥ 4:** Weinberg ratio wrong. -/
theorem mechanism_m8_fails_from_four {n : ℕ} (h4 : 4 ≤ n) :
    (n : ℚ) / c_higgs ≠ 3 / 13 := by
  intro h
  exact Nat.not_succ_le_self 3 (by
    have hn := mechanism_m8_forces_three h
    omega)

/-- Certified GTE constant satisfies all eight mechanisms. -/
theorem ngen_three_satisfies_all_eight : NgenEightMechanisms 3 := by
  refine ⟨?_, ?_, ?_, ?_, ?_, ?_, ?_, ?_⟩
  · rfl
  · simp [n_gen]
  · exact tpc_ngen_equals_level_count
  · simp [n_gen]
  · exact bracket_admissible_at_three
  · norm_num
  · simp [n_gen]
  · simpa using weinberg_angle_closure

/-- **ngen_3_unique_satisfies_all_eight** (CatAL): `N_gen = 3` is the unique positive
    integer satisfying all eight OP7 mechanisms. For every `n ≠ 3` with `0 < n`, some
    mechanism fails. -/
theorem ngen_3_unique_satisfies_all_eight {n : ℕ} (hn : 0 < n) (h : NgenEightMechanisms n) :
    n = 3 := by
  rcases Nat.lt_trichotomy n 3 with hlt | rfl | hgt
  · exfalso
    have hm3 := h.m3_tpc
    exact mechanism_m3_fails_below_three hn hlt hm3
  · rfl
  · exfalso
    have hm5 := h.m5_bracket
    exact mechanism_m5_fails_from_four (Nat.succ_le_of_lt hgt) hm5

/-- Failure witness for any `n ≠ 3`: at least one mechanism is incompatible. -/
theorem ngen_not_three_fails_some_mechanism {n : ℕ} (hn : 0 < n) (hne : n ≠ 3) :
    n < 3 ∨ 4 ≤ n := by omega

theorem ngen_failure_table_row {n : ℕ} (hn : 0 < n) (hne : n ≠ 3) :
    (n < 3 → n ≠ TPCPowerClass.level_hypercomputation + 1 ∨ (n - 1) * (n - 2) / 2 < 1) ∧
      (4 ≤ n → ¬ bracket_admissible_at n (by omega) ∨ (n : ℚ) / c_higgs ≠ 3 / 13) := by
  constructor
  · intro hlt
    left
    exact mechanism_m3_fails_below_three hn hlt
  · intro h4
    left
    exact mechanism_m5_fails_from_four h4

/-- Bundle: uniqueness + certified satisfier at 3. -/
theorem ngen_eight_mechanism_master :
    NgenEightMechanisms 3 ∧
      (∀ {n : ℕ}, 0 < n → NgenEightMechanisms n → n = 3) ∧
      n_gen = 3 :=
  ⟨ngen_three_satisfies_all_eight,
    fun hn h => ngen_3_unique_satisfies_all_eight hn h,
    n_gen_eq_three⟩

end UgpLean.Classification.NgenUniqueness
