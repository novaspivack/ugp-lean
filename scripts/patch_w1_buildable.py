#!/usr/bin/env python3
"""Patch WassersteinDistance.lean to a building state."""
from pathlib import Path

TARGET = Path(__file__).resolve().parents[1] / "UgpLean/ContinuumLimit/WassersteinDistance.lean"
text = TARGET.read_text()

text = text.replace("push Not", "push_neg")

CTC_OLD = """  calc
    μ.val x = M.vertices.sum (γ x) := hγ.2.2.2.1 x hx
    _ = γ x x := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy hne) (fun hne => absurd hx hne)]
      simp
    _ = M.vertices.sum (fun z => γ z x) := by
      rw [Finset.sum_eq_single x]
      · simp
      · intro z hz hne; exact hoff z x hz hx hne
      · intro hne; exact absurd hx hne
    _ = ν.val x := hγ.2.2.2.2 x hx"""

CTC_NEW = """  have hdiag : γ x x = μ.val x := by
    have hsumx : M.vertices.sum (γ x) = μ.val x := hγ.2.2.2.1 x hx
    have hsplit : M.vertices.sum (γ x) = γ x x := by
      classical
      rw [← Finset.add_sum_erase (s := M.vertices) (f := γ x) hx, add_zero]
      apply Finset.sum_eq_zero
      intro b hb
      exact hoff x b hx (Finset.mem_of_mem_erase hb) (Finset.ne_of_mem_erase hb)
    linarith [hsplit, hsumx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    classical
    rw [← Finset.add_sum_erase (s := M.vertices) (f := fun z => γ z x) hx, add_zero]
    apply Finset.sum_eq_zero
    intro z hz
    exact hoff z x (Finset.mem_of_mem_erase hz) hx (Finset.ne_of_mem_erase hz)
  have hnu : ν.val x = γ x x := by rw [← hcol, hγ.2.2.2.2 x hx]
  linarith [hdiag, hnu]"""

if CTC_OLD in text:
    text = text.replace(CTC_OLD, CTC_NEW)

# gap: remove erroneous push_neg after obtain in positive hthird branches
text = text.replace(
    "    · obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthird\n      push_neg at hthird\n      have hut0ne",
    "    · obtain ⟨u, hu, hut0, hutM, hudne⟩ := hthird\n      have hut0ne",
)
text = text.replace(
    "    · obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthird\n      push_neg at hthird\n      have hutPne",
    "    · obtain ⟨u, hu, hutP, hut0, hudne⟩ := hthird\n      have hutPne",
)

text = text.replace(
    "      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) (hu' : t ≠ u) :\n"
    "          δ t = 0 := hthird t ht ht0' htM' hu'",
    "      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (ht0' : t ≠ t0) (htM' : t ≠ tMinus) :\n"
    "          δ t = 0 := by\n"
    "        by_contra hδne\n"
    "        exact absurd ⟨t, ht, ht0', htM', hδne⟩ hthird",
)
text = text.replace(
    "      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) (hu' : t ≠ u) :\n"
    "          δ t = 0 := hthird t ht htP' ht0' hu'",
    "      have hδrest (t : ℕ) (ht : t ∈ M.vertices) (htP' : t ≠ tPlus) (ht0' : t ≠ t0) :\n"
    "          δ t = 0 := by\n"
    "        by_contra hδne\n"
    "        exact absurd ⟨t, ht, htP', ht0', hδne⟩ hthird",
)

text = text.replace(
    "            ← Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hut0ne, hu⟩)]",
    "            ← Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hutMne,\n"
    "              Finset.mem_erase.mpr ⟨hut0ne, hu⟩⟩)]",
)

text = text.replace(
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hut0ne, hu⟩)] at hdist0'",
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hutMne,\n"
    "        Finset.mem_erase.mpr ⟨hut0ne, hu⟩⟩)] at hdist0'",
)

text = text.replace(
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hutMne, hu⟩)] at hdistM'",
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hutMne,\n"
    "        Finset.mem_erase.mpr ⟨hut0ne, hu⟩⟩)] at hdistM'",
)

text = text.replace(
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hut0ne, hu⟩)] at hdistP'",
    "      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem (Finset.mem_erase.mpr ⟨hut0ne,\n"
    "        Finset.mem_erase.mpr ⟨hutPne, hu⟩⟩)] at hdistP'",
)

TWO_ANCHOR_OLD = """      have hdistPlus := hdist0
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0] at hdistPlus
      simp only [M.dist_self, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htMinusInErase] at hdistPlus
      have hrest0 : ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) = 0 :=
        Finset.sum_eq_zero fun t ht => by
          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)
          simp [hδ0 t htVert (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht), zero_mul]
      have hsplit :
          (M.vertices.erase t0).sum (fun t => δ t * M.dist t t0) =
            δ tMinus * M.dist tMinus t0 +
              ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) := by
        rw [← Finset.add_sum_erase (M.vertices.erase t0) (fun t => δ t * M.dist t t0) tMinus htMinusInErase]
      linarith [hdistPlus, hsplit, hrest0, hheadPlus]"""

TWO_ANCHOR_NEW = """      have hdistPlus := hdist0
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0, M.dist_self t0, mul_zero, add_zero] at hdistPlus
      have hsumErase0 : (M.vertices.erase t0).sum (fun t => δ t * M.dist t t0) = 0 := by
        linarith [hdistPlus]
      have hrest0 : ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) = 0 :=
        Finset.sum_eq_zero fun t ht => by
          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)
          simp [hδ0 t htVert (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht), zero_mul]
      have hsplit :
          (M.vertices.erase t0).sum (fun t => δ t * M.dist t t0) =
            δ tMinus * M.dist tMinus t0 +
              ((M.vertices.erase t0).erase tMinus).sum (fun t => δ t * M.dist t t0) := by
        rw [← Finset.add_sum_erase (s := M.vertices.erase t0) (f := fun t => δ t * M.dist t t0)
          htMinusInErase]
      linarith [hsumErase0, hsplit, hrest0, hheadPlus]"""

if TWO_ANCHOR_OLD in text:
    text = text.replace(TWO_ANCHOR_OLD, TWO_ANCHOR_NEW)

TWO_ANCHOR2_OLD = """      have hdistPlus := hdistP
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem] at hdistPlus
      simp only [M.dist_self, mul_zero, add_zero, Finset.sdiff_singleton_eq_erase] at hdistPlus
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase] at hdistPlus
      have hrest0 : ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) = 0 :=
        Finset.sum_eq_zero fun t ht => by
          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)
          simp [hδ0 t htVert (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht), zero_mul]
      have hsplit :
          (M.vertices.erase tPlus).sum (fun t => δ t * M.dist t tPlus) =
            δ t0 * M.dist t0 tPlus +
              ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) := by
        rw [← Finset.add_sum_erase (M.vertices.erase tPlus) (fun t => δ t * M.dist t tPlus) t0 ht0InErase]
      linarith [hdistPlus, hsplit, hrest0, hheadPlus]"""

TWO_ANCHOR2_NEW = """      have hdistPlus := hdistP
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem htPlusMem, M.dist_self tPlus, mul_zero,
        add_zero] at hdistPlus
      rw [Finset.sum_eq_add_sum_diff_singleton_of_mem ht0InErase] at hdistPlus
      have hsumErase0 : (M.vertices.erase tPlus).sum (fun t => δ t * M.dist t tPlus) = 0 := by
        linarith [hdistPlus]
      have hrest0 : ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) = 0 :=
        Finset.sum_eq_zero fun t ht => by
          have htVert : t ∈ M.vertices := Finset.mem_of_mem_erase (Finset.mem_of_mem_erase ht)
          simp [hδ0 t htVert (Finset.ne_of_mem_erase (Finset.mem_of_mem_erase ht))
            (Finset.ne_of_mem_erase ht), zero_mul]
      have hsplit :
          (M.vertices.erase tPlus).sum (fun t => δ t * M.dist t tPlus) =
            δ t0 * M.dist t0 tPlus +
              ((M.vertices.erase tPlus).erase t0).sum (fun t => δ t * M.dist t tPlus) := by
        rw [← Finset.add_sum_erase (s := M.vertices.erase tPlus) (f := fun t => δ t * M.dist t tPlus)
          ht0InErase]
      linarith [hsumErase0, hsplit, hrest0, hheadPlus]"""

if TWO_ANCHOR2_OLD in text:
    text = text.replace(TWO_ANCHOR2_OLD, TWO_ANCHOR2_NEW)

text = text.replace("  · exact hγ.2.2.1 x hx w\n", "  · exact hγ.2.1 x hx w\n")
text = text.replace("  · exact hγ.2.1 w hw z\n", "  · exact hγ.2.2.1 z hz w\n")

text = text.replace(
    "private theorem gluedCoupling_left_outside (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)\n"
    "    (hγ₁ : ∀ x hx y, x ∉ S → γ₁ x y = 0) (x : ℕ) (hx : x ∉ S) (z : ℕ) :\n"
    "    gluedCoupling S ν γ₁ γ₂ x z = 0 := by\n"
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _; split_ifs <;> simp [hγ₁ x hx]",
    "private theorem gluedCoupling_left_outside (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)\n"
    "    (hγ₁ : ∀ x y, x ∉ S → γ₁ x y = 0) (x : ℕ) (hx : x ∉ S) (z : ℕ) :\n"
    "    gluedCoupling S ν γ₁ γ₂ x z = 0 := by\n"
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _;\n"
    "  by_cases hν : ν.val y = 0 <;> simp [hγ₁ x hx y, *]",
)

text = text.replace(
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _; split_ifs <;> simp [hγ₂ y hz]",
    "  unfold gluedCoupling; apply Finset.sum_eq_zero; intro y _;\n"
    "  by_cases hν : ν.val y = 0 <;> simp [hγ₂ y hz, *]",
)

text = text.replace(
    "    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by\n"
    "        rw [← Finset.mul_sum, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]\n"
    "      simp [hν, hinner]",
    "    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by\n"
    "        have hconst : ∀ z, γ₁ x w * γ₂ w z / ν.val w = (γ₁ x w / ν.val w) * γ₂ w z :=\n"
    "          fun z => by ring\n"
    "        rw [Finset.sum_congr rfl hconst, ← Finset.mul_sum, hγ₂.2.2.2.1 w hw,\n"
    "          mul_div_cancel₀ _ (Ne.symm hν)]\n"
    "      simp [hν, hinner]",
)

text = text.replace(
    "    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'\n"
    "      simp [hν, Finset.sum_eq_zero fun x' _ => by simp [hcol x']]",
    "    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'\n"
    "      simp [hν, hcol, Finset.sum_const_zero]",
)

text = text.replace(
    "    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by\n"
    "        rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]\n"
    "      simp [hν, hinner]",
    "    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by\n"
    "        have hconst : ∀ x', γ₁ x' w * γ₂ w z / ν.val w = (γ₂ w z / ν.val w) * γ₁ x' w :=\n"
    "          fun x' => by ring\n"
    "        rw [Finset.sum_congr rfl hconst, ← Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul,\n"
    "          mul_div_cancel₀ _ (Ne.symm hν)]\n"
    "      simp [hν, hinner]",
)

text = text.replace(
    "      rw [mul_comm (M.dist x z), mul_comm (M.dist x w + M.dist w z)]\n"
    "      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv",
    "      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv",
)

text = text.replace(
    "    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt (Ne.symm hdiff)",
    "    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff",
)

text = text.replace(
    "  · subst h; simp [μ.2.2.1 y hy]",
    "  · rw [if_pos h]; exact μ.2.2.1 y hy",
)

# remove duplicate productCoupling W1_pos if Kantorovich version exists later
parts = text.split("private theorem W1_pos_of_vertex_ne")
if len(parts) > 2:
    # keep header + first block up to next major section, skip first W1_pos, rejoin from second
    first = parts[0]
    rest = "private theorem W1_pos_of_vertex_ne".join(parts[1:])
    block1_end = rest.find("noncomputable def gluedCoupling")
    block2_start = rest.rfind("private theorem W1_pos_of_vertex_ne")
    if block1_end != -1 and block2_start != -1 and block2_start > block1_end:
        text = first + rest[block2_start:]

TARGET.write_text(text)
print(f"Patched {TARGET} ({text.count(chr(10)) + 1} lines)")
