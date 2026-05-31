theorem gluedCoupling_cost_le (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling M.vertices μ ν γ₁)
    (hγ₂ : IsCoupling M.vertices ν ρ γ₂) :
    couplingTransportCost M (gluedCoupling M.vertices ν γ₁ γ₂) ≤
      couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
  classical
  set γ₃ := gluedCoupling M.vertices ν γ₁ γ₂
  unfold couplingTransportCost at *
  have hterm :
      ∀ x z,
        M.dist x z * γ₃ x z ≤
          M.vertices.sum fun w =>
            (if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z)) := by
    intro x z; unfold γ₃ gluedCoupling; rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    split_ifs with hν
    · simp
    · have hpos : 0 < ν.val w := lt_of_le_of_ne (ν.2.1 w (by simpa using hw)) (Ne.symm hν)
      have hdiv : 0 ≤ γ₁ x w * γ₂ w z / ν.val w :=
        div_nonneg (mul_nonneg (hγ₁.1 x w) (hγ₂.1 w z)) hpos.le
      calc
        M.dist x z * (γ₁ x w * γ₂ w z / ν.val w) =
            (γ₁ x w * γ₂ w z / ν.val w) * M.dist x z := by ring
        _ ≤ (γ₁ x w * γ₂ w z / ν.val w) * (M.dist x w + M.dist w z) :=
            mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv
  have hsplit :
      (M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              (if ν.val w = (0 : ℝ) then (0 : ℝ) else
                γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z))) =
        (M.vertices.sum fun x =>
          (M.vertices.sum fun w => γ₁ x w * M.dist x w) +
          (M.vertices.sum fun w =>
            (if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z))) := by
    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    congr 1; ext x
    rw [← Finset.sum_add_distrib, Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    congr 1; ext w hw
    by_cases hν : ν.val w = (0 : ℝ)
    · have hγxw := coupling_col_zero_of_mass_zero hγ₁ w hw hν x
      rw [if_pos hν, if_pos hν]
      simp [hγxw, zero_mul, mul_zero, Finset.sum_const_zero, add_zero]
    · rw [if_neg hν, if_neg hν]
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
          rw [hcol, mul_div_cancel₀ _ hν']; ring
  have hbound :
      (M.vertices.sum fun w =>
          (if ν.val w = (0 : ℝ) then (0 : ℝ) else
            M.vertices.sum fun x => γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z)) ≤
        M.vertices.sum fun w => M.vertices.sum fun z => γ₂ w z * M.dist w z := by
    refine Finset.sum_le_sum fun w hw => ?_
    split_ifs with hν
    · have hγw : ∀ z, γ₂ w z = 0 := fun z => coupling_row_zero_of_mass_zero hγ₂ w hw hν z
      simp [hν, hγw, zero_mul, Finset.sum_const_zero, le_rfl]
    · rw [Finset.sum_mul]
      rw [show (∑ x, γ₁ x w / ν.val w) = (∑ x, γ₁ x w) / ν.val w from
        (Finset.sum_div M.vertices (fun x => γ₁ x w) (ν.val w)).symm]
      rw [hγ₁.2.2.2.2 w hw, div_self (Ne.symm hν), one_mul]
  calc
    (M.vertices.sum fun x => M.vertices.sum fun z => γ₃ x z * M.dist x z) ≤
        (M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              (if ν.val w = (0 : ℝ) then (0 : ℝ) else
                γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z))) := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => ?_
      rw [show γ₃ x z * M.dist x z = M.dist x z * γ₃ x z from mul_comm _ _]
      exact hterm x z
    _ = M.vertices.sum fun x =>
          (M.vertices.sum fun w => γ₁ x w * M.dist x w) +
          (M.vertices.sum fun w =>
            (if ν.val w = (0 : ℝ) then (0 : ℝ) else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z)) := hsplit
    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      have hdecompCost :
          M.vertices.sum (fun x =>
              M.vertices.sum (fun w => γ₁ x w * M.dist x w) +
                M.vertices.sum (fun w =>
                  (if ν.val w = (0 : ℝ) then (0 : ℝ) else
                    γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z))) =
            couplingTransportCost M γ₁ +
              M.vertices.sum (fun x =>
                M.vertices.sum (fun w =>
                  (if ν.val w = (0 : ℝ) then (0 : ℝ) else
                    γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z))) := by
        simp_rw [← Finset.sum_add_distrib]
        unfold couplingTransportCost
        rfl
      rw [hdecompCost]
      exact add_le_add le_rfl (by
        rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
        exact hbound)
