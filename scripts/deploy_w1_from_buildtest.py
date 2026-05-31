#!/usr/bin/env python3
"""Deploy fixed W1BuildTest as canonical WassersteinDistance.lean."""
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
text = (ROOT / "UgpLean/ContinuumLimit/W1BuildTest.lean").read_text()

# eq_zero
text = text.replace(
    "      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy (Ne.symm hne)) (fun hne => absurd hx hne)]\n    rw [← hsumx",
    "      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun hne => absurd hx hne)]\n    rw [← hsumx",
)

# Remove redundant hEx copies
text = text.replace(
    """    · obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthird
      have hEx : ∃ u₀ ∈ M.vertices, u₀ ≠ t0 ∧ u₀ ≠ tMinus ∧ δ u₀ ≠ 0 :=
        ⟨u, hu, hut0, hutM, hudne⟩
      have hut0ne : u ≠ t0 := hut0""",
    """    · obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthird
      have hut0ne : u ≠ t0 := hut0""",
)
text = text.replace(
    """    · obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthird
      have hEx : ∃ u₀ ∈ M.vertices, u₀ ≠ tPlus ∧ u₀ ≠ t0 ∧ δ u₀ ≠ 0 :=
        ⟨u, hu, hutP, hut0, hudne⟩
      have hutPne : u ≠ tPlus := hutP""",
    """    · obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthird
      have hutPne : u ≠ tPlus := hutP""",
)

OLD_HDELTA1 = """      have hΔ : M.dist t0 tMinus < M.dist t0 u + M.dist tMinus u := by
        have htri : M.dist t0 tMinus ≤ M.dist t0 u + M.dist tMinus u := by
          calc M.dist t0 tMinus ≤ M.dist t0 u + M.dist u tMinus := M.triangle t0 u tMinus
            _ = M.dist t0 u + M.dist tMinus u := by rw [M.dist_comm u tMinus]
        by_contra hnot
        push_neg at hnot
        have heq : M.dist t0 tMinus = M.dist t0 u + M.dist tMinus u := le_antisymm htri hnot
        have hmid : M.dist t0 u < M.dist t0 tMinus := by
          nlinarith [heq, dist_pos_of_ne M hutMne, M.dist_nonneg tMinus u]
        nlinarith [heq, hmid, dist_pos_of_ne M hut0ne, M.dist_nonneg t0 tMinus, M.dist_nonneg t0 u,
          M.dist_nonneg tMinus u, M.triangle t0 tMinus u, M.triangle tMinus t0 u, M.dist_comm]"""

NEW_HDELTA1 = """      have hΔ : M.dist t0 tMinus < M.dist t0 u + M.dist tMinus u := by
        have htri : M.dist t0 tMinus ≤ M.dist t0 u + M.dist tMinus u :=
          calc M.dist t0 tMinus ≤ M.dist t0 u + M.dist u tMinus := M.triangle t0 u tMinus
            _ = M.dist t0 u + M.dist tMinus u := by rw [M.dist_comm u tMinus]
        refine lt_of_le_of_ne htri ?_
        intro h_eq
        rw [M.dist_comm u tMinus] at h_eq
        nlinarith [M.triangle t0 u tMinus, dist_pos_of_ne M hut0ne, dist_pos_of_ne M hutMne, hdistPM]"""

OLD_HDELTA2 = """      have hΔ : M.dist tPlus t0 < M.dist tPlus u + M.dist t0 u := by
        have htri : M.dist tPlus t0 ≤ M.dist tPlus u + M.dist t0 u := by
          calc M.dist tPlus t0 ≤ M.dist tPlus u + M.dist u t0 := M.triangle tPlus u t0
            _ = M.dist tPlus u + M.dist t0 u := by rw [M.dist_comm u t0]
        by_contra hnot
        push_neg at hnot
        have heq : M.dist tPlus t0 = M.dist tPlus u + M.dist t0 u := le_antisymm htri hnot
        have hmid : M.dist tPlus u < M.dist tPlus t0 := by
          nlinarith [heq, dist_pos_of_ne M hut0ne, M.dist_nonneg t0 u]
        nlinarith [heq, hmid, dist_pos_of_ne M hutPne, M.dist_nonneg tPlus t0, M.dist_nonneg tPlus u,
          M.dist_nonneg t0 u, M.triangle tPlus t0 u, M.triangle tPlus u t0, M.dist_comm]"""

NEW_HDELTA2 = """      have hΔ : M.dist tPlus t0 < M.dist tPlus u + M.dist t0 u := by
        have htri : M.dist tPlus t0 ≤ M.dist tPlus u + M.dist t0 u :=
          calc M.dist tPlus t0 ≤ M.dist tPlus u + M.dist u t0 := M.triangle tPlus u t0
            _ = M.dist tPlus u + M.dist t0 u := by rw [M.dist_comm u t0]
        refine lt_of_le_of_ne htri ?_
        intro h_eq
        rw [M.dist_comm u t0] at h_eq
        nlinarith [M.triangle tPlus u t0, dist_pos_of_ne M hutPne, dist_pos_of_ne M hut0ne, hdistPM]"""

text = text.replace(OLD_HDELTA1, NEW_HDELTA1)
text = text.replace(OLD_HDELTA2, NEW_HDELTA2)

text = text.replace(
    "        · exact hEx ⟨v, hv, ht0ne', htMne', hδne'⟩",
    "        · exact absurd ⟨v, hv, ht0ne', htMne', hδne'⟩ hthird",
)
text = text.replace(
    "        · exact hEx ⟨v, hv, htPne', ht0ne', hδne'⟩",
    "        · exact absurd ⟨v, hv, htPne', ht0ne', hδne'⟩ hthird",
)

text = text.replace(
    "        · exact absurd htu hu'",
    "        · subst htu; exfalso; exact hudne rfl",
)

text = text.replace(
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hut0ne, hu⟩)] at hdist0'",
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hutMne, Finset.mem_erase.mpr ⟨hut0ne, hu⟩⟩)] at hdist0'",
)
text = text.replace(
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hut0ne, hu⟩)] at hdistP'",
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hut0ne, Finset.mem_erase.mpr ⟨hutPne, hu⟩⟩)] at hdistP'",
)

# gluedCoupling_cost_le
NEW_COST = open(ROOT / "scripts/finalize_w1_staging.py").read().split('NEW_COST = """')[1].split('"""')[0]
start = text.find("theorem gluedCoupling_cost_le")
end = text.find("\n\ntheorem W1_eq_zero_iff")
text = text[:start] + NEW_COST + text[end:]

text = text.replace("theorem probExpectation_dist_sub", "private theorem probExpectation_dist_sub", 1)

while text.count('@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped"') > 1:
    text = text.replace(
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n'
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n',
        '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]\n',
        1,
    )

out = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"
out.write_text(text)
print(f"Wrote {len(text.splitlines())} lines")
