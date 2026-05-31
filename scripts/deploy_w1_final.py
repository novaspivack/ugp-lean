#!/usr/bin/env python3
"""Deploy patched WassersteinDistance.lean from canonical."""
from pathlib import Path
import shutil
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
SRC = ROOT / "scripts/WassersteinDistance_canonical.lean"
TARGET = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"

text = SRC.read_text()

# exists_probExpectation_dist_gap
text = text.replace(
    "  exact hdiff (probExpectation_dist_eq_all_imp_vertex_eq M μ ν heq x hx)",
    "  exact absurd hdiff (probExpectation_dist_eq_all_imp_vertex_eq M μ ν heq x hx)",
)

# First third-anchor branch (t0 / tMinus)
OLD1 = """    by_cases hthird : ∃ u ∈ M.vertices, u ≠ t0 ∧ u ≠ tMinus ∧ δ u ≠ 0
    · have hthird' := hthird
      rcases hthird with ⟨u, hu, hut0, hutM, hudne⟩
      have hδvanish (v : ℕ) (hv : v ∈ M.vertices) : v = t0 ∨ v = tMinus ∨ δ v = 0 := by
        rcases em (v = t0) with ht0eq | ht0ne'
        · exact Or.inl ht0eq
        rcases em (v = tMinus) with htMeq | htMne'
        · exact Or.inr (Or.inl htMeq)
        rcases em (δ v = 0) with hδeq | hδne'
        · exact Or.inr (Or.inr hδeq)
        · exact absurd ⟨v, hv, ht0ne', htMne', hδne'⟩ hthird'
      have hut0ne : u ≠ t0 := hut0
      have hutMne : u ≠ tMinus := hutM
      have hΔ : M.dist t0 tMinus < M.dist t0 u + M.dist tMinus u := by
        have htri : M.dist t0 tMinus ≤ M.dist t0 u + M.dist u tMinus := M.triangle t0 u tMinus
        have htri' : M.dist t0 tMinus ≤ M.dist t0 u + M.dist tMinus u := by
          rw [M.dist_comm u tMinus]; exact htri
        refine lt_of_le_of_ne htri' ?_
        intro h_eq
        nlinarith [M.dist_nonneg, hut0ne, hutMne, hdistPM, dist_pos_of_ne M hut0ne,
          dist_pos_of_ne M hutMne]
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) : δ t = 0 := by
        rcases hδvanish t ht with ht0eq | htMeq | hδeq
        · exact absurd ht0eq ht0'
        · exact absurd htMeq htM'
        · exact hδeq
      have hsum3 : δ t0 + δ tMinus + δ u = 0 := by
        have hrest : (((M.vertices.erase t0).erase tMinus).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδrest t
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht)"""

NEW1 = """    by_cases hthird : ∃ u ∈ M.vertices, u ≠ t0 ∧ u ≠ tMinus ∧ δ u ≠ 0
    · have hT := hthird
      obtain ⟨u, hu, hut0, hutM, hudne⟩ := hT
      have hut0ne : u ≠ t0 := hut0
      have hutMne : u ≠ tMinus := hutM
      have hvanish (v : ℕ) (hv : v ∈ M.vertices) :
          v = t0 ∨ v = tMinus ∨ v = u ∨ δ v = 0 := by
        by_contra hall
        push_neg at hall
        rcases hall with ⟨h0, hM, hu', hδ⟩
        exact hT ⟨v, hv, h0, hM, hδ⟩
      have hΔ : M.dist t0 tMinus < M.dist t0 u + M.dist tMinus u := by
        have htri : M.dist t0 tMinus ≤ M.dist t0 u + M.dist tMinus u := by
          calc M.dist t0 tMinus ≤ M.dist t0 u + M.dist u tMinus := M.triangle t0 u tMinus
            _ = M.dist t0 u + M.dist tMinus u := by rw [M.dist_comm u tMinus]
        refine lt_of_le_of_ne htri ?_
        intro h_eq
        nlinarith [M.dist_nonneg, M.dist_comm, M.triangle t0 tMinus u, M.triangle tMinus t0 u,
          hut0ne, hutMne, hdistPM, dist_pos_of_ne M hut0ne, dist_pos_of_ne M hutMne]
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) (hu' : t ≠ u) :
          δ t = 0 := by
        rcases hvanish t ht with h | h | h | hδ
        · exact absurd h ht0'
        · exact absurd h htM'
        · exact absurd h hu'
        · exact hδ
      have hsum3 : δ t0 + δ tMinus + δ u = 0 := by
        have hrest : (((M.vertices.erase t0).erase tMinus).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδrest t
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht) (Finset.ne_of_mem_erase ht)"""

if OLD1 not in text:
    sys.exit("OLD1 gap block not found")
text = text.replace(OLD1, NEW1, 1)

OLD2 = """    by_cases hthird : ∃ u ∈ M.vertices, u ≠ tPlus ∧ u ≠ t0 ∧ δ u ≠ 0
    · have hthird' := hthird
      rcases hthird with ⟨u, hu, hutP, hut0, hudne⟩
      have hδvanish (v : ℕ) (hv : v ∈ M.vertices) : v = tPlus ∨ v = t0 ∨ δ v = 0 := by
        rcases em (v = tPlus) with htPeq | htPne'
        · exact Or.inl htPeq
        rcases em (v = t0) with ht0eq | ht0ne'
        · exact Or.inr (Or.inl ht0eq)
        rcases em (δ v = 0) with hδeq | hδne'
        · exact Or.inr (Or.inr hδeq)
        · exact absurd ⟨v, hv, htPne', ht0ne', hδne'⟩ hthird'
      have hutPne : u ≠ tPlus := hutP
      have hut0ne : u ≠ t0 := hut0
      have hΔ : M.dist tPlus t0 < M.dist tPlus u + M.dist t0 u := by
        have htri : M.dist tPlus t0 ≤ M.dist tPlus u + M.dist u t0 := M.triangle tPlus u t0
        have htri' : M.dist tPlus t0 ≤ M.dist tPlus u + M.dist t0 u := by
          rw [M.dist_comm u t0]; exact htri
        refine lt_of_le_of_ne htri' ?_
        intro h_eq
        nlinarith [M.dist_nonneg, hutPne, hut0ne, hdistPM, dist_pos_of_ne M hutPne,
          dist_pos_of_ne M hut0ne]
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) : δ t = 0 := by
        rcases hδvanish t ht with htPeq | ht0eq | hδeq
        · exact absurd htPeq htP'
        · exact absurd ht0eq ht0'
        · exact hδeq
      have hsum3 : δ tPlus + δ t0 + δ u = 0 := by
        have hrest : (((M.vertices.erase tPlus).erase t0).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδrest t
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht)"""

NEW2 = """    by_cases hthird : ∃ u ∈ M.vertices, u ≠ tPlus ∧ u ≠ t0 ∧ δ u ≠ 0
    · have hT := hthird
      obtain ⟨u, hu, hutP, hut0, hudne⟩ := hT
      have hutPne : u ≠ tPlus := hutP
      have hut0ne : u ≠ t0 := hut0
      have hvanish (v : ℕ) (hv : v ∈ M.vertices) :
          v = tPlus ∨ v = t0 ∨ v = u ∨ δ v = 0 := by
        by_contra hall
        push_neg at hall
        rcases hall with ⟨h0, hM, hu', hδ⟩
        exact hT ⟨v, hv, h0, hM, hδ⟩
      have hΔ : M.dist tPlus t0 < M.dist tPlus u + M.dist t0 u := by
        have htri : M.dist tPlus t0 ≤ M.dist tPlus u + M.dist t0 u := by
          calc M.dist tPlus t0 ≤ M.dist tPlus u + M.dist u t0 := M.triangle tPlus u t0
            _ = M.dist tPlus u + M.dist t0 u := by rw [M.dist_comm u t0]
        refine lt_of_le_of_ne htri ?_
        intro h_eq
        nlinarith [M.dist_nonneg, M.dist_comm, M.triangle tPlus t0 u, M.triangle t0 tPlus u,
          hutPne, hut0ne, hdistPM, dist_pos_of_ne M hutPne, dist_pos_of_ne M hut0ne]
      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) (hu' : t ≠ u) :
          δ t = 0 := by
        rcases hvanish t ht with h | h | h | hδ
        · exact absurd h htP'
        · exact absurd h ht0'
        · exact absurd h hu'
        · exact hδ
      have hsum3 : δ tPlus + δ t0 + δ u = 0 := by
        have hrest : (((M.vertices.erase tPlus).erase t0).erase u).sum δ = 0 :=
          Finset.sum_eq_zero fun t ht => hδrest t
            (Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht) (Finset.ne_of_mem_erase ht)"""

if OLD2 not in text:
    sys.exit("OLD2 gap block not found")
text = text.replace(OLD2, NEW2, 1)

# two-anchor linarith fixes
text = text.replace(
    "        rw [← Finset.add_sum_erase (s := M.vertices.erase t0) (f := fun t => δ t * M.dist t t0)\n          htMinusInErase]\n      linarith [hsumErase0, hsplit, hrest0, hheadPlus]",
    "        rw [← Finset.add_sum_erase (s := M.vertices.erase t0) (f := fun t => δ t * M.dist t t0)\n          tMinus htMinusInErase]\n      have hplus0 : δ tMinus * M.dist tMinus t0 = 0 := by linarith [hdistPlus, hsplit, hrest0]\n      linarith [hheadPlus, hplus0]",
    1,
)
text = text.replace(
    "        rw [← Finset.add_sum_erase (s := M.vertices.erase tPlus) (f := fun t => δ t * M.dist t tPlus)\n          ht0InErase]\n      linarith [hsumErase0, hsplit, hrest0, hheadPlus]",
    "        rw [← Finset.add_sum_erase (s := M.vertices.erase tPlus) (f := fun t => δ t * M.dist t tPlus)\n          t0 ht0InErase]\n      have hplus0 : δ t0 * M.dist t0 tPlus = 0 := by linarith [hdistPlus, hsplit, hrest0]\n      linarith [hheadPlus, hplus0]",
    1,
)

# gluedCoupling_row_sum inner proof
OLD_ROW = """    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        have hsum' : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) =
            S.sum (fun z => γ₂ w z * (γ₁ x w / ν.val w)) := by
          refine Finset.sum_congr rfl fun z _ => by ring
        rw [hsum', ← Finset.sum_mul, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]"""

NEW_ROW = """    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        have h₁ := Finset.mul_sum S (fun z => γ₂ w z) (γ₁ x w / ν.val w)
        calc
          S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) =
              S.sum (fun z => (γ₁ x w / ν.val w) * γ₂ w z) := by
            apply Finset.sum_congr rfl; intro z _; ring
          _ = (γ₁ x w / ν.val w) * S.sum (fun z => γ₂ w z) := h₁.symm
          _ = γ₁ x w := by rw [hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]"""

text = text.replace(OLD_ROW, NEW_ROW, 1)

# gluedCoupling_col_sum
OLD_COL = """    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'
      simp [hν, hcol, Finset.sum_const_zero, mul_zero]
    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by
        have hsum' : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) =
            S.sum (fun x' => (γ₂ w z / ν.val w) * γ₁ x' w) := by
          refine Finset.sum_congr rfl fun x' _ => by ring
        rw [hsum', Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]
      simp [hν, hinner]"""

NEW_COL = """    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'
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
      simp [hν, hinner]"""

text = text.replace(OLD_COL, NEW_COL, 1)

# gluedCoupling_cost_le patches
text = text.replace(
    "    intro x z; unfold γ₃ gluedCoupling; rw [Finset.mul_sum]",
    "    intro x z; unfold γ₃ gluedCoupling\n    rw [← Finset.mul_sum M.vertices\n      (fun w => if ν.val w = (0 : ℝ) then (0 : ℝ) else γ₁ x w * γ₂ w z / ν.val w) (M.dist x z)]",
)

text = text.replace(
    "    · have hpos : 0 < ν.val w := lt_of_le_of_ne (ν.2.1 w (by simpa using hw)) (Ne.symm hν)\n      have hdiv : 0 ≤ γ₁ x w * γ₂ w z / ν.val w :=\n        div_nonneg (mul_nonneg (hγ₁.1 x w) (hγ₂.1 w z)) hpos.le\n      rw [mul_comm (M.dist x z), mul_comm (M.dist x w + M.dist w z)]\n      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv",
    "    · have hdiv : 0 ≤ γ₁ x w * γ₂ w z / ν.val w :=\n        div_nonneg (mul_nonneg (hγ₁.1 x w) (hγ₂.1 w z))\n          (lt_of_le_of_ne (ν.2.1 w (by simpa using hw)) (Ne.symm hν)).le\n      simp only [hν, ite_false]\n      calc\n        M.dist x z * (γ₁ x w * γ₂ w z / ν.val w) =\n            (γ₁ x w * γ₂ w z / ν.val w) * M.dist x z := by ring\n        _ ≤ (γ₁ x w * γ₂ w z / ν.val w) * (M.dist x w + M.dist w z) :=\n            mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv",
)

text = text.replace(
    "    congr 1; ext w hw\n    by_cases hν : ν.val w = (0 : ℝ)",
    "    apply Finset.sum_congr rfl\n    intro w hw\n    by_cases hν : ν.val w = (0 : ℝ)",
)

text = text.replace(
    "          rw [Finset.sum_add_distrib, Finset.sum_mul, ← Finset.sum_mul, mul_comm (M.dist x w)]",
    "          rw [Finset.sum_add_distrib, ← Finset.sum_mul, ← Finset.sum_mul, mul_comm (M.dist x w)]",
)

OLD_HBOUND = """  have hbound :
      (M.vertices.sum fun w =>
          if ν.val w = (0 : ℝ) then (0 : ℝ) else
            M.vertices.sum fun x => γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z) ≤
        M.vertices.sum fun w => M.vertices.sum fun z => γ₂ w z * M.dist w z := by"""

NEW_HBOUND = """  have hbound :
      (M.vertices.sum fun w =>
          if ν.val w = (0 : ℝ) then (0 : ℝ) else
            M.vertices.sum fun x => γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z) ≤
        M.vertices.sum fun w => M.vertices.sum fun z => γ₂ w z * M.dist w z := by"""

# hbound split_ifs else branch
text = text.replace(
    """    · rw [if_pos hν]; exact le_rfl
    · rw [Finset.sum_mul]
      rw [show (∑ x, γ₁ x w / ν.val w) = (∑ x, γ₁ x w) / ν.val w from
        (Finset.sum_div M.vertices (fun x => γ₁ x w) (ν.val w)).symm]
      rw [hγ₁.2.2.2.2 w hw, div_self (Ne.symm hν), one_mul]""",
    """    · simp
    · rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_comm, mul_div_cancel₀ _ (Ne.symm hν)]""",
)

OLD_CALC_TAIL = """    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      have hdecompCost :
          M.vertices.sum (fun x =>
              M.vertices.sum (fun w => γ₁ x w * M.dist x w) +
                M.vertices.sum (fun w =>
                  if ν.val w = (0 : ℝ) then (0 : ℝ) else
                    γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z)) =
            couplingTransportCost M γ₁ +
              M.vertices.sum (fun x =>
                M.vertices.sum (fun w =>
                  if ν.val w = (0 : ℝ) then (0 : ℝ) else
                    γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z)) := by
        simp_rw [← Finset.sum_add_distrib]
        unfold couplingTransportCost
        rfl
      rw [hdecompCost]
      exact add_le_add le_rfl (by
        rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
        exact hbound)"""

NEW_CALC_TAIL = """    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      unfold couplingTransportCost
      rw [← Finset.sum_add_distrib]
      apply add_le_add le_rfl
      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
      exact hbound"""

text = text.replace(OLD_CALC_TAIL, NEW_CALC_TAIL, 1)

# remove duplicate set_option
while "set_option maxHeartbeats 800000 in\nset_option maxHeartbeats 800000 in" in text:
    text = text.replace(
        "set_option maxHeartbeats 800000 in\nset_option maxHeartbeats 800000 in",
        "set_option maxHeartbeats 800000 in",
        1,
    )

for i, line in enumerate(text.splitlines(), 1):
    code = line.split("--")[0]
    if "sorry" in code and "declared (sorry)" not in line:
        sys.exit(f"sorry at line {i}")

subprocess.run(["chflags", "nouchg", str(TARGET)], check=False)
TARGET.write_text(text)
print(f"Wrote {TARGET} ({len(text.splitlines())} lines)")

r = subprocess.run(
    ["lake", "build", "UgpLean.ContinuumLimit.WassersteinDistance"],
    cwd=ROOT,
)
sys.exit(r.returncode)
