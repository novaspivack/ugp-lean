#!/usr/bin/env python3
"""Write a complete, zero-sorry WassersteinDistance.lean atomically."""
from pathlib import Path
import subprocess
import sys

ROOT = Path(__file__).resolve().parents[1]
test_path = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance_test.lean"
test = test_path.read_text().splitlines()

i_w1pos = next(i for i, l in enumerate(test) if l.startswith("private theorem W1_pos_of_vertex_ne"))
i_glued = next(i for i, l in enumerate(test) if l.startswith("noncomputable def gluedCoupling"))
i_w1eq = next(i for i, l in enumerate(test) if l.startswith("theorem W1_eq_zero_iff"))
i_oll = next(i for i, l in enumerate(test) if l.startswith("noncomputable def OllivierRicci"))

clean_head = []
seen_deq = False
seen_arch = False
for line in test[:i_w1pos]:
    if line.strip() == "/-- Distances distinguish vertices: zero distance iff equal points. -/" and seen_deq:
        continue
    if line.strip().startswith("dist_eq_zero_iff :"):
        if seen_deq:
            continue
        seen_deq = True
    if line == "import Mathlib.Data.Real.Archimedean":
        if seen_arch:
            continue
        seen_arch = True
    clean_head.append(line)

# Fix exists_mass_imbalance_pair: sum over M.vertices, not Finset.univ; drop bad coercion
clean_head = [
    l.replace(
        "Finset.single_le_sum hnonneg (fun x _ => hnonneg x ‹x ∈ M.vertices›) (Finset.mem_univ x0)",
        "Finset.single_le_sum hnonneg hx0",
    ).replace(
        "Finset.single_le_sum hnonpos (fun x _ => hnonpos x ‹x ∈ M.vertices›) (Finset.mem_univ x0)",
        "Finset.single_le_sum hnonpos hx0",
    )
    for l in clean_head
]
clean_head = [
    l
    for l in clean_head
    if not l.strip().startswith("have hsum' : M.vertices.sum (fun x => ↑μ x - ↑ν x)")
    and not l.strip().startswith("simpa [ProbDist, Subtype] using hsum'")
]

exists_gap = """
private theorem W1_pos_of_vertex_ne (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices)
    (hne : ∃ x ∈ M.vertices, μ.val x ≠ ν.val x) : 0 < W1 M μ ν := by
  have hcost := couplingTransportCost_pos_of_vertex_ne M μ ν hne
  have hle := W1_le_couplingCost M μ ν (productCoupling M.vertices μ ν)
    (productCoupling_is_coupling M.vertices μ ν)
  exact hcost.trans_le hle
""".strip().splitlines()

glued_block = """
/-- Glued coupling of `γ₁ : μ ↝ ν` and `γ₂ : ν ↝ ρ` via disintegration at `ν`. -/
noncomputable def gluedCoupling (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ) (x z : ℕ) : ℝ :=
  S.sum fun y =>
    if ν.val y = 0 then 0 else γ₁ x y * γ₂ y z / ν.val y

private theorem gluedCoupling_nonneg (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : ∀ x y, 0 ≤ γ₁ x y) (hγ₂ : ∀ x y, 0 ≤ γ₂ x y) :
    ∀ x z, 0 ≤ gluedCoupling S ν γ₁ γ₂ x z := by
  intro x z
  unfold gluedCoupling
  apply Finset.sum_nonneg
  intro y hy
  split_ifs with h
  · simp
  · exact div_nonneg (mul_nonneg (hγ₁ x y) (hγ₂ y z)) (le_of_lt (lt_of_le_of_ne (ν.2.1 y hy) (Ne.symm h)))

private theorem gluedCoupling_left_outside (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : ∀ x y, x ∉ S → γ₁ x y = 0) (x : ℕ) (hx : x ∉ S) (z : ℕ) :
    gluedCoupling S ν γ₁ γ₂ x z = 0 := by
  unfold gluedCoupling
  apply Finset.sum_eq_zero
  intro y _
  split_ifs <;> simp [hγ₁ x _ hx]

private theorem gluedCoupling_right_outside (S : Finset ℕ) (ν : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₂ : ∀ w x, w ∉ S → γ₂ x w = 0) (z : ℕ) (hz : z ∉ S) (x : ℕ) :
    gluedCoupling S ν γ₁ γ₂ x z = 0 := by
  unfold gluedCoupling
  apply Finset.sum_eq_zero
  intro y _
  split_ifs <;> simp [hγ₂ z y hz]

private theorem coupling_col_zero_of_mass_zero {S : Finset ℕ} {μ ν : ProbDist S} {γ : ℕ → ℕ → ℝ}
    (hγ : IsCoupling S μ ν γ) (w : ℕ) (hw : w ∈ S) (hν : ν.val w = 0) :
    ∀ x, γ x w = 0 := by
  intro x
  have hcol := hγ.2.2.2.2 w hw; rw [hν] at hcol
  by_cases hx : x ∈ S
  · exact (Finset.sum_eq_zero_iff_of_nonneg (fun z _ => hγ.1 z w)).mp hcol x hx
  · exact hγ.2.1 x hx w

private theorem gluedCoupling_row_sum (S : Finset ℕ) (μ ν ρ : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : IsCoupling S μ ν γ₁) (hγ₂ : IsCoupling S ν ρ γ₂) (x : ℕ) (hx : x ∈ S) :
    S.sum (gluedCoupling S ν γ₁ γ₂ x) = μ.val x := by
  classical
  unfold gluedCoupling
  rw [Finset.sum_comm]
  trans S.sum fun w => γ₁ x w
  · apply Finset.sum_congr rfl
    intro w hw
    by_cases hν : ν.val w = 0
    · simp [hν, coupling_col_zero_of_mass_zero hγ₁ w hw hν x]
    · have hinner : S.sum (fun z => γ₁ x w * γ₂ w z / ν.val w) = γ₁ x w := by
        rw [← Finset.mul_sum, hγ₂.2.2.2.1 w hw, mul_div_cancel₀ _ (Ne.symm hν)]
      simpa [hν] using hinner
  · exact hγ₁.2.2.2.1 x hx

private theorem gluedCoupling_col_sum (S : Finset ℕ) (μ ν ρ : ProbDist S) (γ₁ γ₂ : ℕ → ℕ → ℝ)
    (hγ₁ : IsCoupling S μ ν γ₁) (hγ₂ : IsCoupling S ν ρ γ₂) (z : ℕ) (hz : z ∈ S) :
    S.sum (fun x => gluedCoupling S ν γ₁ γ₂ x z) = ρ.val z := by
  classical
  unfold gluedCoupling
  trans S.sum fun w => γ₂ w z
  · apply Finset.sum_congr rfl
    intro w hw
    by_cases hν : ν.val w = 0
    · have hcol : ∀ x', γ₁ x' w = 0 := fun x' => coupling_col_zero_of_mass_zero hγ₁ w hw hν x'
      simp [hν, Finset.sum_eq_zero fun x' _ => by simp [hcol x']]
    · have hinner : S.sum (fun x' => γ₁ x' w * γ₂ w z / ν.val w) = γ₂ w z := by
        rw [← Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_div_cancel₀ _ (Ne.symm hν)]
      simpa [hν] using hinner
  · exact hγ₂.2.2.2.2 z hz

theorem gluedCoupling_is_coupling (M : FiniteMetricSpace) (μ ν ρ : ProbDist M.vertices)
    (γ₁ γ₂ : ℕ → ℕ → ℝ) (hγ₁ : IsCoupling M.vertices μ ν γ₁)
    (hγ₂ : IsCoupling M.vertices ν ρ γ₂) :
    IsCoupling M.vertices μ ρ (gluedCoupling M.vertices ν γ₁ γ₂) := by
  refine ⟨gluedCoupling_nonneg M.vertices ν γ₁ γ₂ hγ₁.1 hγ₂.1, ?_, ?_, ?_, ?_⟩
  · intro x hx y; exact gluedCoupling_left_outside M.vertices ν γ₁ γ₂ (fun a ha b => hγ₁.2.1 ha b) x hx y
  · intro y hy x; exact gluedCoupling_right_outside M.vertices ν γ₁ γ₂ (fun w x hw => hγ₂.2.2.1 hw x) y hy x
  · intro x hx; exact gluedCoupling_row_sum M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂ x hx
  · intro y hy; exact gluedCoupling_col_sum M.vertices μ ν ρ γ₁ γ₂ hγ₁ hγ₂ y hy

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
            if ν.val w = (0 : ℝ) then (0 : ℝ) else γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) := by
    intro x z; unfold γ₃ gluedCoupling; rw [Finset.mul_sum]
    refine Finset.sum_le_sum fun w hw => ?_
    split_ifs with hν
    · simp
    · have hpos : 0 < ν.val w := lt_of_le_of_ne (ν.2.1 w (by simpa using hw)) (Ne.symm hν)
      have hdiv : 0 ≤ γ₁ x w * γ₂ w z / ν.val w :=
        div_nonneg (mul_nonneg (hγ₁.1 x w) (hγ₂.1 w z)) hpos.le
      exact mul_le_mul_of_nonneg_left (M.triangle x w z) hdiv
  have hsplit :
      M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = 0 then 0 else γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) =
        M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w =>
            if ν.val w = 0 then 0 else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := by
    rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    refine Finset.sum_congr rfl fun x _ => ?_
    rw [← Finset.sum_add_distrib, Finset.sum_comm (s := M.vertices) (t := M.vertices)]
    refine Finset.sum_congr rfl fun w hw => ?_
    by_cases hν : ν.val w = 0
    · have hγxw := coupling_col_zero_of_mass_zero hγ₁ w hw hν x
      simp [hν, hγxw, zero_mul, mul_zero, add_zero]
    · have hν' : ν.val w ≠ 0 := hν
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
      M.vertices.sum fun w =>
          if ν.val w = 0 then 0 else
            M.vertices.sum fun x => γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z ≤
        M.vertices.sum fun w => M.vertices.sum fun z => γ₂ w z * M.dist w z := by
    refine Finset.sum_le_sum fun w hw => ?_
    split_ifs with hν
    · simp
    · rw [Finset.sum_mul, hγ₁.2.2.2.2 w hw, one_mul, mul_comm, mul_div_cancel₀ _ (Ne.symm hν)]
  calc
    M.vertices.sum fun x => M.vertices.sum fun z => M.dist x z * γ₃ x z ≤
        M.vertices.sum fun x =>
          M.vertices.sum fun z =>
            M.vertices.sum fun w =>
              if ν.val w = (0 : ℝ) then (0 : ℝ) else γ₁ x w * γ₂ w z / ν.val w * (M.dist x w + M.dist w z) := by
      refine Finset.sum_le_sum fun x _ => Finset.sum_le_sum fun z _ => hterm x z
    _ = M.vertices.sum fun x => M.vertices.sum fun w => γ₁ x w * M.dist x w +
          M.vertices.sum fun w =>
            if ν.val w = 0 then 0 else
              γ₁ x w / ν.val w * M.vertices.sum fun z => γ₂ w z * M.dist w z := hsplit
    _ ≤ couplingTransportCost M γ₁ + couplingTransportCost M γ₂ := by
      unfold couplingTransportCost
      rw [← Finset.sum_add_distrib]
      apply add_le_add le_rfl
      rw [Finset.sum_comm (s := M.vertices) (t := M.vertices)]
      exact hbound
""".strip().splitlines()

w1_block = """
theorem W1_eq_zero_iff (M : FiniteMetricSpace) (μ ν : ProbDist M.vertices) :
    W1 M μ ν = 0 ↔ ∀ x ∈ M.vertices, μ.val x = ν.val x := by
  constructor
  · intro hW1
    by_contra hne
    push_neg at hne
    have hpos := W1_pos_of_vertex_ne M μ ν hne
    linarith [W1_nonneg M μ ν, hW1]
  · intro h
    have hμν : μ = ν := probDist_eq_of_vertex_weights_eq h
    subst hμν
    apply le_antisymm
    · have hle := W1_le_couplingCost M μ μ (diagonalCoupling M.vertices μ)
        (diagonalCoupling_is_coupling M.vertices μ)
      rw [diagonalCoupling_cost_zero M μ] at hle
      exact hle
    · exact W1_nonneg M μ μ

theorem W1_triangle (M : FiniteMetricSpace)
    (μ ν ρ : ProbDist M.vertices) :
    W1 M μ ρ ≤ W1 M μ ν + W1 M ν ρ := by
  rw [le_iff_forall_pos_lt_add]
  intro ε hε
  obtain ⟨c₁, hc₁mem, hc₁lt⟩ :=
    Real.lt_sInf_add_pos (couplingCostSet_nonempty M μ ν) (half_pos hε)
  obtain ⟨c₂, hc₂mem, hc₂lt⟩ :=
    Real.lt_sInf_add_pos (couplingCostSet_nonempty M ν ρ) (half_pos hε)
  obtain ⟨γ₁, hγ₁, hc₁eq⟩ := hc₁mem
  obtain ⟨γ₂, hγ₂, hc₂eq⟩ := hc₂mem
  have hglued := gluedCoupling_is_coupling M μ ν ρ γ₁ γ₂ hγ₁ hγ₂
  have hcost := gluedCoupling_cost_le M μ ν ρ γ₁ γ₂ hγ₁ hγ₂
  have hle := W1_le_couplingCost M μ ρ (gluedCoupling M.vertices ν γ₁ γ₂) hglued
  have hW1μν : W1 M μ ν ≤ c₁ := by
    unfold W1; apply csInf_le
    · refine ⟨0, ?_⟩; intro c hc; obtain ⟨γ', hγ', hc'⟩ := hc; rw [hc']; exact couplingTransportCost_nonneg M γ' hγ'.1
    · exact ⟨γ₁, hγ₁, hc₁eq⟩
  have hW1νρ : W1 M ν ρ ≤ c₂ := by
    unfold W1; apply csInf_le
    · refine ⟨0, ?_⟩; intro c hc; obtain ⟨γ', hγ', hc'⟩ := hc; rw [hc']; exact couplingTransportCost_nonneg M γ' hγ'.1
    · exact ⟨γ₂, hγ₂, hc₂eq⟩
  unfold W1 at hle hW1μν hW1νρ ⊢
  linarith [hle, hcost, hc₁lt, hc₂lt, hW1μν, hW1νρ]
""".strip().splitlines()

tail_fixed = []
for line in test[i_oll:]:
    if line.strip() == "axiom gorard_vacuum_oric_zero":
        tail_fixed.append(
            '@[deprecated "Use GorardVacuumW1Bridge.gorard_vacuum_oric_zero_scoped" (since := "2026-05-31")]'
        )
    tail_fixed.append(line)

out_lines = clean_head + [""] + exists_gap + [""] + glued_block + [""] + w1_block + [""] + tail_fixed
out = "\n".join(out_lines) + "\n"

if "hthirdEx" in out:
    print("REFUSING: bad block in output", file=sys.stderr)
    sys.exit(1)

if out.count("\nsorry") + (1 if out.rstrip().endswith("sorry") else 0) > 0:
    # allow "sorry" only in doc comments
    for i, line in enumerate(out.splitlines()):
        if "sorry" in line and not line.strip().startswith("-") and "declared (sorry)" not in line:
            if "sorry" in line.split("--")[0]:
                print(f"REFUSING: sorry at line {i+1}: {line}", file=sys.stderr)
                sys.exit(1)

final = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean"
staging = ROOT / "UgpLean/ContinuumLimit/WassersteinDistance.lean.staging"
staging.write_text(out)
staging.replace(final)
print(f"Wrote {len(out_lines)} lines to {final}")
