#!/usr/bin/env python3
"""Build green WassersteinDistance.lean atomically."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
text = (ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean.staging").read_text()

start = text.index("set_option maxHeartbeats 800000 in")
end = text.index("private theorem W1_pos_of_vertex_ne")

NEW_BLOCK = """
private theorem exists_probExpectation_dist_gap (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) :
    ((∃ a ∈ M.vertices, 0 < probExpectation M μ (M.dist · a) - probExpectation M ν (M.dist · a)) ∨
      ∃ a ∈ M.vertices, 0 < probExpectation M ν (M.dist · a) - probExpectation M μ (M.dist · a)) := by
  obtain ⟨xPlus, hxPlus, xMinus, hxMinus, hPlus, hMinus⟩ := exists_mass_imbalance_pair M μ ν hne
  by_cases hμ : 0 < probExpectation M μ (M.dist · xPlus) - probExpectation M ν (M.dist · xPlus)
  · exact Or.inl ⟨xPlus, hxPlus, hμ⟩
  · push_neg at hμ
    by_cases hν : 0 < probExpectation M ν (M.dist · xPlus) - probExpectation M μ (M.dist · xPlus)
    · exact Or.inr ⟨xPlus, hxPlus, hν⟩
    · push_neg at hν
      by_cases hμM : 0 < probExpectation M μ (M.dist · xMinus) - probExpectation M ν (M.dist · xMinus)
      · exact Or.inl ⟨xMinus, hxMinus, hμM⟩
      · push_neg at hμM
        by_cases hνM : 0 < probExpectation M ν (M.dist · xMinus) - probExpectation M μ (M.dist · xMinus)
        · exact Or.inr ⟨xMinus, hxMinus, hνM⟩
        · push_neg at hνM
          have heqM : probExpectation M μ (M.dist · xMinus) = probExpectation M ν (M.dist · xMinus) := by linarith
          have hsumM : M.vertices.sum (fun t => (μ.val t - ν.val t) * M.dist t xMinus) = 0 := by
            rw [← probExpectation_dist_sub M μ ν xMinus, heqM, sub_self]
          have hnePM : xPlus ≠ xMinus := by intro heq'; subst heq'; linarith [hPlus, hMinus]
          have hdistPM : 0 < M.dist xPlus xMinus := dist_pos_of_ne M hnePM
          have hpos : 0 < (μ.val xPlus - ν.val xPlus) * M.dist xPlus xMinus :=
            mul_pos (sub_pos.mpr hPlus) hdistPM
          have hneg : (μ.val xMinus - ν.val xMinus) * M.dist xMinus xPlus < 0 :=
            mul_neg_of_neg_of_pos (sub_pos.mpr hMinus) (by rwa [M.dist_comm xMinus xPlus])
          have hxMinusInErase : xMinus ∈ M.vertices.erase xPlus :=
            Finset.mem_erase.mpr ⟨hnePM.symm, hxMinus⟩
          have hdecomp : M.vertices.sum (fun t => (μ.val t - ν.val t) * M.dist t xMinus) =
              (μ.val xPlus - ν.val xPlus) * M.dist xPlus xMinus +
                (μ.val xMinus - ν.val xMinus) * M.dist xMinus xMinus +
                ((M.vertices.erase xPlus).erase xMinus).sum (fun t => (μ.val t - ν.val t) * M.dist t xMinus) := by
            rw [← Finset.add_sum_erase (s := M.vertices) (f := fun t => (μ.val t - ν.val t) * M.dist t xMinus)
              hxPlus]
            rw [← Finset.add_sum_erase (s := M.vertices.erase xPlus)
              (f := fun t => (μ.val t - ν.val t) * M.dist t xMinus) hxMinusInErase]
            simp [M.dist_self, mul_zero, add_zero]
          linarith [hsumM, hdecomp, hpos, hneg]

private theorem probExpectation_dist_eq_all_imp_vertex_eq (M : FiniteMetricSpace)
    (μ ν : ProbDist M.vertices)
    (h : ∀ a ∈ M.vertices, probExpectation M μ (M.dist · a) = probExpectation M ν (M.dist · a)) :
    ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  intro x hx
  by_contra hne
  rcases exists_probExpectation_dist_gap M μ ν ⟨x, hx, hne⟩ with hμ | hν
  · rcases hμ with ⟨a, ha, hpos⟩
    have hz : probExpectation M μ (M.dist · a) - probExpectation M ν (M.dist · a) = 0 := by
      rw [h a ha, sub_self]
    linarith [hpos, hz]
  · rcases hν with ⟨a, ha, hpos⟩
    have hz : probExpectation M ν (M.dist · a) - probExpectation M μ (M.dist · a) = 0 := by
      rw [h a ha, sub_self]
    linarith [hpos, hz]

"""

text = text[:start] + NEW_BLOCK + text[end:]

OLD_START = text.find("theorem gluedCoupling_cost_le")
OLD_END = text.find("\n\ntheorem W1_eq_zero_iff")
NEW_COST = open(ROOT / "scripts/finalize_w1_staging.py").read().split('NEW_COST = """')[1].split('"""')[0]
text = text[:OLD_START] + NEW_COST + text[OLD_END:]

text = text.replace(
    "  · subst h; exact μ.2.2.1 y hy",
    "  · subst h; simp [μ.2.2.1 y hy]",
)
text = text.replace("theorem probExpectation_dist_sub", "private theorem probExpectation_dist_sub", 1)
text = text.replace(
    "      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy (Ne.symm hne)) (fun hne => absurd hx hne)]\n      simp\n    rw [hsumx",
    "      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun hne => absurd hx hne)]\n    rw [hsumx",
)
text = text.replace(
    "    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]\n    simp\n  have hnu",
    "    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]\n  have hnu",
)
text = text.replace(
    "        rw [hsum', Finset.sum_mul, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]",
    "        rw [hsum', ← Finset.mul_sum, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]",
)
text = text.replace(
    "      simp [hν, Finset.sum_eq_zero fun x' _ => by simp [hcol x']]",
    "      simp [hν, hcol, Finset.sum_const_zero]",
)
while text.count('@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped"') > 1:
    text = text.replace(
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n'
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n',
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n',
        1,
    )

tmp = Path("/tmp/w1_green_final.lean")
tmp.write_text(text)
print(f"Wrote {len(text.splitlines())} lines to {tmp}")
