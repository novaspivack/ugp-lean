#!/usr/bin/env python3
"""Clean deploy: W1BuildTest head/helpers + gap_v2 + Kantorovich tail + W1Test glued block."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
build = (ROOT / "UgpLean/ContinuumLimit/W1BuildTest.lean").read_text()
complete = (ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean.complete").read_text()
w1test = (ROOT / "UgpLean/ContinuumLimit/W1Test.lean").read_text()

head_end = build.index("set_option maxHeartbeats 800000 in")
head = build[:head_end]

delta_start = complete.index("private theorem exists_delta_neg_of_sum_zero")
gap_end = complete.index("private theorem exists_probExpectation_dist_gap")
gap_v2 = complete[delta_start:gap_end] + "\n"
gap_v2 = gap_v2.replace(
    """  have hpos : 0 < 2 * d0u * d1u / d01 :=
    div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (mul_pos h0u h1u)) h01
  nlinarith [e2, hz, hpos]""",
    """  have hpos : 0 < 2 * d0u * d1u / d01 :=
    div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (mul_pos h0u h1u)) h01
  by_cases hδup : 0 < δu
  · have hneg : δ0 * d0u + δ1 * d1u < 0 := by rw [hz]; exact mul_neg_of_pos_of_neg hpos hδup
    linarith [e2, hneg]
  · push_neg at hδup
    have hδun : δu < 0 := lt_of_le_of_ne hδup hu
    have hpos' : 0 < δ0 * d0u + δ1 * d1u := by rw [hz]; exact mul_neg_of_neg_of_pos hδun hpos
    linarith [e2, hpos']""",
)
gap_v2 = gap_v2.replace(
    """    · obtain ⟨u, hu, hut0ne, hutMne, hudne⟩ := hthird
      have hΔle : M.dist t0 tMinus ≤ M.dist t0 u + M.dist tMinus u := by""",
    """    · have hex := hthird
      obtain ⟨u, hu, hut0ne, hutMne, hudne⟩ := hex
      have hΔle : M.dist t0 tMinus ≤ M.dist t0 u + M.dist tMinus u := by""",
)
gap_v2 = gap_v2.replace(
    """      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) (hu' : t ≠ u) :
          δ t = 0 := by
        by_contra hδne
        exact not_exists.mp hthird ⟨t, ht, ht0', htM', hδne⟩""",
    """      have hvanish (v : ℕ) (hv : v ∈ M.vertices) :
            v = t0 ∨ v = tMinus ∨ v = u ∨ δ v = 0 := by
          by_contra hall
          push_neg at hall
          rcases hall with ⟨h0, hM, hu', hδ⟩
          exact hex ⟨v, hv, h0, hM, hδ⟩
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) (hu' : t ≠ u) :
          δ t = 0 := by
        rcases hvanish t ht with h | h | h | hδ
        · exact absurd h ht0'
        · exact absurd h htM'
        · exact absurd h hu'
        · exact hδ""",
)
gap_v2 = gap_v2.replace(
    """    · obtain ⟨u, hu, hutPne, hut0ne, hudne⟩ := hthird
      have hΔle : M.dist tPlus t0 ≤ M.dist tPlus u + M.dist t0 u := by""",
    """    · have hex := hthird
      obtain ⟨u, hu, hutPne, hut0ne, hudne⟩ := hex
      have hΔle : M.dist tPlus t0 ≤ M.dist tPlus u + M.dist t0 u := by""",
)
gap_v2 = gap_v2.replace(
    """      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) (hu' : t ≠ u) :
          δ t = 0 := by
        by_contra hδne
        exact not_exists.mp hthird ⟨t, ht, htP', ht0', hδne⟩""",
    """      have hvanish (v : ℕ) (hv : v ∈ M.vertices) :
            v = tPlus ∨ v = t0 ∨ v = u ∨ δ v = 0 := by
          by_contra hall
          push_neg at hall
          rcases hall with ⟨hP, h0, hu', hδ⟩
          exact hex ⟨v, hv, hP, h0, hδ⟩
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) (hu' : t ≠ u) :
          δ t = 0 := by
        rcases hvanish t ht with h | h | h | hδ
        · exact absurd h htP'
        · exact absurd h ht0'
        · exact absurd h hu'
        · exact hδ""",
)
for old_decomp, new_decomp in [
    (
        """        have hdecomp : M.vertices.sum δ =
            δ t0 + δ tMinus + δ u + (((M.vertices.erase t0).erase tMinus).erase u).sum δ := by
          rw [← Finset.sum_eq_add_sum_diff_singleton_of_mem ht0,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem htMinusInErase,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem
              (Finset.mem_erase.mpr ⟨hutMne, Finset.mem_erase.mpr ⟨hut0ne, hu⟩⟩)]""",
        """        have hdecomp : M.vertices.sum δ =
            δ t0 + δ tMinus + δ u + (((M.vertices.erase t0).erase tMinus).erase u).sum δ := by
          rw [← Finset.sum_eq_add_sum_diff_singleton_of_mem ht0, Finset.sdiff_singleton_eq_erase,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem htMinusInErase, Finset.sdiff_singleton_eq_erase,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem
              (Finset.mem_erase.mpr ⟨hutMne, Finset.mem_erase.mpr ⟨hut0ne, hu⟩⟩),
            Finset.sdiff_singleton_eq_erase]""",
    ),
    (
        """        have hdecomp : M.vertices.sum δ =
            δ tPlus + δ t0 + δ u + (((M.vertices.erase tPlus).erase t0).erase u).sum δ := by
          rw [← Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem
              (Finset.mem_erase.mpr ⟨hut0ne, Finset.mem_erase.mpr ⟨hutPne, hu⟩⟩)]""",
        """        have hdecomp : M.vertices.sum δ =
            δ tPlus + δ t0 + δ u + (((M.vertices.erase tPlus).erase t0).erase u).sum δ := by
          rw [← Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem, Finset.sdiff_singleton_eq_erase,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase, Finset.sdiff_singleton_eq_erase,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem
              (Finset.mem_erase.mpr ⟨hut0ne, Finset.mem_erase.mpr ⟨hutPne, hu⟩⟩),
            Finset.sdiff_singleton_eq_erase]""",
    ),
]:
    gap_v2 = gap_v2.replace(old_decomp, new_decomp)

gap_v2 = gap_v2.replace(
    """  have hpos : 0 < 2 * d0u * d1u / d01 := by
    apply div_pos (mul_pos (by norm_num) (mul_pos h0u h1u))
    exact h01
  nlinarith [e2, hz, hpos]""",
    """  have hpos : 0 < 2 * d0u * d1u / d01 :=
    div_pos (mul_pos (by norm_num : (0 : ℝ) < 2) (mul_pos h0u h1u)) h01
  by_cases hδup : 0 < δu
  · have hneg : δ0 * d0u + δ1 * d1u < 0 := by rw [hz]; exact mul_neg_of_pos_of_neg hpos hδup
    linarith [e2, hneg]
  · push_neg at hδup
    have hδun : δu < 0 := lt_of_le_of_ne hδup hu
    have hpos' : 0 < δ0 * d0u + δ1 * d1u := by rw [hz]; exact mul_neg_of_neg_of_pos hδun hpos
    linarith [e2, hpos']""",
)
gap_v2 = gap_v2.replace("exact hex ⟨", "exact hthird ⟨")
gap_v2 = gap_v2.replace(
    """    · have hex := hthird
      obtain ⟨u, hu, hut0ne, hutMne, hudne⟩ := hex""",
    """    · obtain ⟨u, hu, hut0ne, hutMne, hudne⟩ := hthird""",
)
gap_v2 = gap_v2.replace(
    """    · have hex := hthird
      obtain ⟨u, hu, hutPne, hut0ne, hudne⟩ := hex""",
    """    · obtain ⟨u, hu, hutPne, hut0ne, hudne⟩ := hthird""",
)
gap_v2 = gap_v2.replace(
    "M.dist_self t0, mul_zero, add_zero] at hdist0'",
    "M.dist_self t0, mul_zero, add_zero] at hdist0'",
)
gap_v2 = gap_v2.replace(
    "M.dist_self tMinus, mul_zero, add_zero] at hdistM'",
    "M.dist_self tMinus, mul_zero, add_zero] at hdistM'",
)
gap_v2 = gap_v2.replace(
    "M.dist_self u, mul_zero, add_zero] at hdistU'",
    "M.dist_self u, mul_zero, add_zero] at hdistU'",
)
gap_v2 = gap_v2.replace(
    "M.dist_self tPlus, mul_zero, add_zero] at hdistP'",
    "M.dist_self tPlus, mul_zero, add_zero] at hdistP'",
)
gap_v2 = gap_v2.replace(
    """          rw [← Finset.sum_eq_add_sum_diff_singleton_of_mem ht0, Finset.sdiff_singleton_eq_erase,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem htMinusInErase, Finset.sdiff_singleton_eq_erase,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem
              (Finset.mem_erase.mpr ⟨hutMne, Finset.mem_erase.mpr ⟨hut0ne, hu⟩⟩),
            Finset.sdiff_singleton_eq_erase]""",
    """          rw [← Finset.add_sum_erase (s := M.vertices) (f := δ) ht0,
            ← Finset.add_sum_erase (s := M.vertices.erase t0) (f := δ) htMinusInErase,
            ← Finset.add_sum_erase (s := (M.vertices.erase t0).erase tMinus) (f := δ)
              (Finset.mem_erase.mpr ⟨hutMne, Finset.mem_erase.mpr ⟨hut0ne, hu⟩⟩)]""",
)
gap_v2 = gap_v2.replace(
    """          rw [← Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem, Finset.sdiff_singleton_eq_erase,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase, Finset.sdiff_singleton_eq_erase,
            ← Finset.sum_eq_add_sum_diff_singleton_of_mem
              (Finset.mem_erase.mpr ⟨hut0ne, Finset.mem_erase.mpr ⟨hutPne, hu⟩⟩),
            Finset.sdiff_singleton_eq_erase]""",
    """          rw [← Finset.add_sum_erase (s := M.vertices) (f := δ) htPlusMem,
            ← Finset.add_sum_erase (s := M.vertices.erase tPlus) (f := δ) ht0InErase,
            ← Finset.add_sum_erase (s := (M.vertices.erase tPlus).erase t0) (f := δ)
              (Finset.mem_erase.mpr ⟨hut0ne, Finset.mem_erase.mpr ⟨hutPne, hu⟩⟩)]""",
)

head = head.replace("theorem probExpectation_dist_sub", "private theorem probExpectation_dist_sub", 1)

kant_start = build.index("private theorem exists_probExpectation_dist_gap")
glued_start = build.index("noncomputable def gluedCoupling")
kant = build[kant_start:glued_start]

glued_start_t = w1test.index("private theorem gluedCoupling_left_outside")
end_t = len(w1test)
glued_block = w1test[glued_start_t:end_t]

# Rename W1Test helper names to match W1BuildTest (only in cost_le hsplit)
glued_block = glued_block.replace("coupling_col_zero ", "coupling_col_zero_of_mass_zero ")

# Keep gluedCoupling def + nonneg from W1BuildTest; patch row/col/cost proofs
glued_def_start = build.index("noncomputable def gluedCoupling")
glued_is_start = build.index("theorem gluedCoupling_is_coupling")
glued_core = build[glued_def_start:glued_is_start]

# Patch row/col sum inner proofs
glued_core = glued_core.replace(
    """    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        have h₁ := Finset.mul_sum S (fun z => γ₂ w z) (γ₁ x w / ν.val w)
        calc
          S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) =
              S.sum (fun z => (γ₁ x w / ν.val w) * γ₂ w z) := by
            apply Finset.sum_congr rfl; intro z _; ring
          _ = (γ₁ x w / ν.val w) * S.sum (fun z => γ₂ w z) := h₁.symm
          _ = γ₁ x w := by rw [hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
    """    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        rw [show (fun z => γ₁ x w * γ₂ w z / ν.val w) = fun z => (γ₁ x w / ν.val w) * γ₂ w z
            from by ext z; ring, ← Finset.mul_sum, hγ₂.2.2.2.1 w hw]
        exact div_mul_cancel₀ (γ₁ x w) hν
      simp [hν, hinner]""",
)
glued_core = glued_core.replace(
    """    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'
      have hsum0 : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = 0 := by
        apply Finset.sum_eq_zero; intro x' _
        simp [hν, hcol x', zero_mul, mul_zero]
      simp [hν, hsum0]
    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by
        have h₁ := Finset.sum_mul S (fun x' => γ₁ x' w) (γ₂ w z / ν.val w)
        calc
          S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) =
              S.sum (fun x' => γ₁ x' w * (γ₂ w z / ν.val w)) := by
            apply Finset.sum_congr rfl; intro x' _; ring
          _ = S.sum (fun x' => γ₁ x' w) * (γ₂ w z / ν.val w) := h₁.symm
          _ = γ₂ w z := by rw [hγ₁.2.2.2.2 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]""",
    """    · have hrow0 : γ₂ w z = 0 := coupling_row_zero_of_mass_zero hγ₂ w hw hν z
      simp only [hν, ite_true, Finset.sum_const_zero, hrow0]
    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by
        rw [show (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = fun x' => γ₁ x' w * (γ₂ w z / ν.val w)
            from by ext x'; ring, ← Finset.sum_mul, hγ₁.2.2.2.2 w hw]
        exact mul_div_cancel₀ (γ₂ w z) hν
      simp only [hν, ite_false, hinner]""",
)
glued_core = glued_core.replace(
    """  classical
  unfold gluedCoupling
  trans S.sum fun w => γ₂ w z""",
    """  classical
  unfold gluedCoupling
  rw [Finset.sum_comm]
  trans S.sum fun w => γ₂ w z""",
)

# W1Test has better eq_zero, triangle, oric tail; keep W1BuildTest is_coupling (curried outside lemmas)
is_start_b = build.index("theorem gluedCoupling_is_coupling")
cost_start_b = build.index("theorem gluedCoupling_cost_le")
w1_eq_start_b = build.index("theorem W1_eq_zero_iff")
is_coupling_block = build[is_start_b:cost_start_b]
cost_block = build[cost_start_b:w1_eq_start_b]
cost_block = cost_block.replace(
    """    intro x z; unfold γ₃ gluedCoupling
    rw [← Finset.mul_sum M.vertices
      (fun w => if ν.val w = (0 : ℝ) then (0 : ℝ) else γ₁ x w * γ₂ w z / ν.val w) (M.dist x z)]""",
    """    intro x z; unfold γ₃ gluedCoupling; rw [Finset.mul_sum]""",
)
cost_block = cost_block.replace(
    """    · have hdiv : 0 ≤ γ₁ x w * γ₂ w z / ν.val w :=
        div_nonneg (mul_nonneg (hγ₁.1 x w) (hγ₂.1 w z))
          (lt_of_le_of_ne (ν.2.1 w (by simpa using hw)) (Ne.symm hν)).le
      simp only [hν, ite_false]
      calc""",
    """    · have hdiv : 0 ≤ γ₁ x w * γ₂ w z / ν.val w :=
        div_nonneg (mul_nonneg (hγ₁.1 x w) (hγ₂.1 w z))
          (lt_of_le_of_ne (ν.2.1 w (by simpa using hw)) (Ne.symm hν)).le
      calc""",
)
cost_block = cost_block.replace(
    """  have hsplit :
      M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = (0 : ℝ) then (0 : ℝ) else
                γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) =
        M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w =>
            if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := by""",
    """  have hsplit :
      (M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = (0 : ℝ) then (0 : ℝ) else
                γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z)) =
        (M.vertices.sum fun x =>
          (M.vertices.sum fun w => γ₁ x w * M.dist x w) +
          (M.vertices.sum fun w =>
            if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z)) := by""",
)
cost_block = cost_block.replace(
    """    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    congr 1; ext x
    rw [← Finset.sum_add_distrib, Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hν : ν.val w = (0 : ℝ)
    · have hγxw := coupling_col_zero_of_mass_zero hγ₁ w hw hν x
      simp only [hν, ite_true, zero_add, add_zero, hγxw, zero_mul, mul_zero, Finset.sum_const_zero]
    · simp only [hν, ite_false]
      have hν' : ν.val w ≠ 0 := Ne.symm hν
      have hcol : M.vertices.sum (fun z => γ₂ w z) = ν.val w := hγ₂.2.2.2.1 w hw
      calc
        M.vertices.sum fun z => γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) =
            γ₁ x w / ν.val w *
              M.vertices.sum fun z => γ₂ w z * (M.dist x w + M.dist w z) := by
          rw [Finset.mul_sum, mul_div_assoc, mul_assoc]
        _ = γ₁ x w / ν.val w * (M.vertices.sum fun z => γ₂ w z * M.dist x w +
              M.vertices.sum fun z => γ₂ w z * M.dist w z) := by
          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, mul_comm (M.dist x w)]
        _ = γ₁ x w * M.dist x w +
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := by
          rw [hcol, mul_div_cancel₀ _ hν']; ring""",
    """    apply Finset.sum_congr rfl
    intro x _
    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    conv_rhs => rw [← Finset.sum_add_distrib]
    apply Finset.sum_congr rfl
    intro w hw
    by_cases hνzero : ν.val w = 0
    · have hγxw := coupling_col_zero_of_mass_zero hγ₁ w hw hνzero x
      simp only [hνzero, ite_true, hγxw, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
    · have hν : ν.val w ≠ 0 := hνzero
      simp only [if_neg hν]
      have hcol : M.vertices.sum (fun z => γ₂ w z) = ν.val w := hγ₂.2.2.2.1 w hw
      calc
        M.vertices.sum (fun z => γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z)) =
            (γ₁ x w / ν.val w) * M.vertices.sum (fun z => γ₂ w z * (M.dist x w + M.dist w z)) := by
          rw [show (fun z => γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z)) =
                fun z => (γ₁ x w / ν.val w) * (γ₂ w z * (M.dist x w + M.dist w z)) from by ext z; ring,
            ← Finset.mul_sum]
        _ = γ₁ x w / ν.val w *
              (M.vertices.sum (fun z => γ₂ w z * M.dist x w) +
                M.vertices.sum (fun z => γ₂ w z * M.dist w z)) := by
          congr 1
          rw [show (fun z => γ₂ w z * (M.dist x w + M.dist w z)) =
                fun z => γ₂ w z * M.dist x w + γ₂ w z * M.dist w z from by ext z; ring,
              Finset.sum_add_distrib]
        _ = γ₁ x w * M.dist x w +
              γ₁ x w / ν.val w * M.vertices.sum (fun z => γ₂ w z * M.dist w z) := by
          rw [mul_add, ← Finset.sum_mul M.vertices (fun z => γ₂ w z) (M.dist x w), hcol,
            ← mul_assoc, div_mul_cancel₀ (γ₁ x w) hν]""",
)
cost_block = cost_block.replace(
    """    _ = M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w =>
            if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := hsplit""",
    """    _ = (M.vertices.sum fun x =>
          (M.vertices.sum fun w => γ₁ x w * M.dist x w) +
          (M.vertices.sum fun w =>
            if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z)) := hsplit""",
)
cost_block = cost_block.replace(
    """  have hbound :
      M.vertices.sum fun w =>
          if ν.val w = (0 : ℝ) then (0 : ℝ) else
            M.vertices.sum fun x => γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z ≤
        M.vertices.sum fun w => M.vertices.sum fun z => γ₂ w z * M.dist w z := by""",
    """  have hbound :
      (M.vertices.sum fun w =>
          if ν.val w = (0 : ℝ) then (0 : ℝ) else
            M.vertices.sum fun x => γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z) ≤
        (M.vertices.sum fun w => M.vertices.sum fun z => γ₂ w z * M.dist w z) := by""",
)
cost_block = cost_block.replace(
    """    refine Finset.sum_le_sum fun w hw => ?_
    split_ifs with hν
    · simp
    · rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_comm, mul_div_cancel₀ _ (Ne.symm hν)]""",
    """    refine Finset.sum_le_sum fun w hw => ?_
    split_ifs with hν
    · exact (Finset.sum_nonneg fun z _ => mul_nonneg (hγ₂.1 w z) (M.dist_nonneg w z))
    · have hν' : ν.val w ≠ 0 := hν
      apply le_of_eq
      rw [← Finset.sum_mul M.vertices (fun x => γ₁ x w / ν.val w)
            (M.vertices.sum (fun z => γ₂ w z * M.dist w z))]
      rw [show M.vertices.sum (fun x => γ₁ x w / ν.val w) =
            (M.vertices.sum (fun x => γ₁ x w)) / ν.val w from by rw [← Finset.sum_div],
          hγ₁.2.2.2.2 w hw, div_self hν', one_mul]""",
)
cost_block = cost_block.replace(
    """  calc
    M.vertices.sum fun x => M.vertices.sum fun z => M.dist x z * γ₃ x z ≤
        M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = (0 : ℝ) then (0 : ℝ) else
                γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => hterm x z
    _ = (M.vertices.sum fun x =>
          (M.vertices.sum fun w => γ₁ x w * M.dist x w) +
          (M.vertices.sum fun w =>
            if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z)) := hsplit""",
    """  calc
    (M.vertices.sum fun x => M.vertices.sum fun y => γ₃ x y * M.dist x y) ≤
        (M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = (0 : ℝ) then (0 : ℝ) else
                γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z)) := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => ?_
      rw [mul_comm (γ₃ x z)]
      exact hterm x z
    _ = (M.vertices.sum fun x =>
          (M.vertices.sum fun w => γ₁ x w * M.dist x w) +
          (M.vertices.sum fun w =>
            if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z)) := hsplit""",
)

cost_block = cost_block.replace(
    """    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      unfold couplingTransportCost
      rw [← Finset.sum_add_distrib]
      apply add_le_add le_rfl
      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
      exact hbound""",
    """    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      unfold couplingTransportCost
      have hle₂ :
          (M.vertices.sum fun x =>
              M.vertices.sum fun w =>
                if ν.val w = (0 : ℝ) then (0 : ℝ) else
                  γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z) ≤
            M.vertices.sum fun x => M.vertices.sum fun y => γ₂ x y * M.dist x y := by
        rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
        have hpull :
            ∀ w ∈ M.vertices,
              M.vertices.sum (fun x =>
                  if ν.val w = (0 : ℝ) then (0 : ℝ) else
                    γ₁ x w / ν.val w * M.vertices.sum (fun z => γ₂ w z * M.dist w z)) =
                if ν.val w = (0 : ℝ) then (0 : ℝ) else
                  M.vertices.sum (fun x =>
                    γ₁ x w / ν.val w * M.vertices.sum (fun z => γ₂ w z * M.dist w z)) := by
          intro w hw; by_cases hν : ν.val w = 0 <;> simp [hν]
        rw [Finset.sum_congr rfl hpull]
        exact hbound
      rw [Finset.sum_add_distrib]
      exact add_le_add le_rfl hle₂""",
)

tail_start_b = build.index("theorem W1_eq_zero_iff")
tail_block = build[tail_start_b:]

text = head + gap_v2 + kant + glued_core + is_coupling_block + cost_block + tail_block

while text.count('@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped"') > 1:
    text = text.replace(
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n'
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n',
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n',
        1,
    )

out = Path("/tmp/w1_final.lean")
out.write_text(text)
print(f"Wrote {len(text.splitlines())} lines to {out}")
