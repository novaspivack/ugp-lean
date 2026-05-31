#!/usr/bin/env python3
"""Assemble zero-sorry WassersteinDistance.lean (product-coupling W1_pos path)."""
import subprocess
from pathlib import Path

ROOT = Path("/Users/nova/ugp-lean-exp")
TARGET = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"
INSERT_PATH = ROOT / "UgpLean/ContinuumLimit/_w1_extension_insert.lean"
CANON = ROOT / "scripts/WassersteinDistance_canonical.lean"

stash = subprocess.check_output(
    ["git", "show", "stash@{0}:UgpLean/ContinuumLimit/WassersteinDistance.lean"],
    cwd=ROOT, text=True,
).splitlines()

part_a = "\n".join(stash[260:331]) + "\n"

part_b = r'''
private theorem exists_mass_imbalance_neg (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (x : ℕ) (hgt : μ.val x > ν.val x) (hx : x ∈ M.vertices) :
    ∃ y ∈ M.vertices, μ.val y < ν.val y := by
  by_contra hall; push_neg at hall
  have hall' : ∀ t ∈ M.vertices, ν.val t ≤ μ.val t := fun t ht => hall t ht
  have hsum : M.vertices.sum (fun t => μ.val t - ν.val t) = 0 :=
    probDist_vertex_mass_balance M.vertices μ ν
  have hnonneg : ∀ t ∈ M.vertices, 0 ≤ μ.val t - ν.val t :=
    fun t ht => sub_nonneg.mpr (hall' t ht)
  have hpos : 0 < μ.val x - ν.val x := sub_pos.mpr hgt
  have hsumpos : 0 < M.vertices.sum (fun t => μ.val t - ν.val t) :=
    lt_of_lt_of_le hpos (Finset.single_le_sum hnonneg hx)
  linarith

private theorem exists_mass_imbalance_pos (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (x : ℕ) (hlt : μ.val x < ν.val x) (hx : x ∈ M.vertices) :
    ∃ y ∈ M.vertices, μ.val y > ν.val y := by
  by_contra hall; push_neg at hall
  have hall' : ∀ t ∈ M.vertices, μ.val t ≤ ν.val t := fun t ht => hall t ht
  have hsum : M.vertices.sum (fun t => ν.val t - μ.val t) = 0 := by
    simpa using probDist_vertex_mass_balance M.vertices ν μ
  have hnonneg : ∀ t ∈ M.vertices, 0 ≤ ν.val t - μ.val t :=
    fun t ht => sub_nonneg.mpr (hall' t ht)
  have hpos : 0 < ν.val x - μ.val x := sub_pos.mpr hlt
  have hsumpos : 0 < M.vertices.sum (fun t => ν.val t - μ.val t) :=
    lt_of_lt_of_le hpos (Finset.single_le_sum hnonneg hx)
  linarith

theorem exists_mass_imbalance_pair (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) :
    ∃ xPlus ∈ M.vertices, ∃ xMinus ∈ M.vertices,
      μ.val xPlus > ν.val xPlus ∧ μ.val xMinus < ν.val xMinus := by
  obtain ⟨x, hx, hdiff⟩ := hne
  by_cases hgt : μ.val x > ν.val x
  · obtain ⟨xMinus, hxMinus, hlt⟩ := exists_mass_imbalance_neg M μ ν x hgt hx
    exact ⟨x, hx, xMinus, hxMinus, hgt, hlt⟩
  · push_neg at hgt
    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff
    obtain ⟨xPlus, hxPlus, hgt'⟩ := exists_mass_imbalance_pos M μ ν x hlt hx
    exact ⟨xPlus, hxPlus, x, hx, hgt', hlt⟩

''' + "\n".join(stash[379:399]) + "\n"

part_c = r'''
private theorem couplingTransportCost_eq_zero_of_eq
    (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) (γ : ℕ → ℕ → ℝ)
    (hγ : IsCoupling M.vertices μ ν γ) (hc : couplingTransportCost M γ = 0) :
    ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  intro x hx
  have hrow_nonneg (a : ℕ) :
      0 ≤ M.vertices.sum (fun b => γ a b * M.dist a b) := by
    apply Finset.sum_nonneg; intro b _; exact mul_nonneg (hγ.1 a b) (M.dist_nonneg a b)
  have hrow_zero (a : ℕ) (ha : a ∈ M.vertices) :
      M.vertices.sum (fun b => γ a b * M.dist a b) = 0 := by
    unfold couplingTransportCost at hc
    have hle : M.vertices.sum (fun b => γ a b * M.dist a b) ≤ 0 := by
      have hle_total :
          M.vertices.sum (fun b => γ a b * M.dist a b) ≤
            M.vertices.sum (fun a' => M.vertices.sum (fun b => γ a' b * M.dist a' b)) :=
        Finset.single_le_sum (fun a' _ => hrow_nonneg a') ha
      linarith [hle_total, hc]
    exact le_antisymm hle (hrow_nonneg a)
  have hoff (a b : ℕ) (ha : a ∈ M.vertices) (hb : b ∈ M.vertices) (hne : a ≠ b) :
      γ a b = 0 := by
    have hnn : 0 ≤ γ a b * M.dist a b := mul_nonneg (hγ.1 a b) (M.dist_nonneg a b)
    have hzero : γ a b * M.dist a b = 0 :=
      (Finset.sum_eq_zero_iff_of_nonneg (fun c _ => mul_nonneg (hγ.1 a c) (M.dist_nonneg a c))).1
        (hrow_zero a ha) b hb
    exact (mul_eq_zero.mp hzero).resolve_right (ne_of_gt (dist_pos_of_ne M hne))
  have hdiag : γ x x = μ.val x := by
    have hsumx : γ x x = M.vertices.sum (γ x) := by
      rw [Finset.sum_eq_single x (fun y hy hne => hoff x y hx hy (Ne.symm hne)) (fun hne => absurd hx hne)]
      simp
    rw [hsumx, hγ.2.2.2.1 x hx]
  have hcol : M.vertices.sum (fun z => γ z x) = γ x x := by
    rw [Finset.sum_eq_single x (fun z hz hne => hoff z x hz hx hne) (fun hne => absurd hx hne)]
    simp
  have hnu : ν.val x = γ x x := by rw [← hcol, hγ.2.2.2.2 x hx]
  linarith [hdiag, hnu]

theorem couplingTransportCost_eq_zero_implies_vertex_eq (M : FiniteMetricSpace)
    (μ ν : ProbDist M.vertices) (γ : ℕ → ℕ → ℝ) (hγ : IsCoupling M.vertices μ ν γ)
    (hc : couplingTransportCost M γ = 0) :
    ∀ x ∈ M.vertices, μ.val x = ν.val x :=
  couplingTransportCost_eq_zero_of_eq M μ ν γ hγ hc

theorem couplingTransportCost_pos_of_vertex_ne (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) :
    0 < couplingTransportCost M (productCoupling M.vertices μ ν) := by
  obtain ⟨x, hx, hdiff⟩ := hne
  by_cases hgt : μ.val x > ν.val x
  · obtain ⟨y, hy, hlt⟩ := exists_mass_imbalance_neg M μ ν x hgt hx
    have hμpos : 0 < μ.val x := by linarith [μ.2.1 x hx, ν.2.1 x hx, hgt]
    have hνpos : 0 < ν.val y := by linarith [ν.2.1 y hy, μ.2.1 y hy, hlt]
    exact productCoupling_cost_pos M μ ν hx hy (by intro heq; subst heq; linarith) hμpos hνpos
  · push_neg at hgt
    have hlt : μ.val x < ν.val x := lt_of_le_of_ne hgt hdiff
    obtain ⟨y, hy, hgt'⟩ := exists_mass_imbalance_pos M μ ν x hlt hx
    have hμpos : 0 < μ.val y := by linarith [μ.2.1 y hy, ν.2.1 y hy, hgt']
    have hνpos : 0 < ν.val x := by linarith [ν.2.1 x hx, μ.2.1 x hx, hlt]
    exact productCoupling_cost_pos M μ ν hy hx (by intro heq; subst heq; linarith) hμpos hνpos

private theorem W1_pos_of_vertex_ne (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) : 0 < W1 M μ ν := by
  have hcost := couplingTransportCost_pos_of_vertex_ne M μ ν hne
  have hle := W1_le_couplingCost M μ ν (productCoupling M.vertices μ ν)
    (productCoupling_is_coupling M.vertices μ ν)
  exact hcost.trans_le hle

'''

canon = CANON.read_text()
g0 = canon.index("noncomputable def gluedCoupling")
g1 = canon.index("theorem W1_eq_zero_iff")
glued = canon[g0:g1]

INSERT_PATH.write_text(part_a + part_b + part_c + glued)

if __name__ == "__main__":
    subprocess.run(["python3", str(ROOT / "scripts/build_wasserstein_complete.py")], check=True, cwd=ROOT)
    text = TARGET.read_text()
    assert "delta_three" not in text, "gap machinery leaked"
    assert "sorry" not in text.replace("declared (sorry)", ""), "sorry in file"
    print(f"OK: {len(text.splitlines())} lines, no sorry/gap")
