import UgpLean.Substrate.SechOverlapIntegralBounds_cosh

namespace UgpLean.Substrate.PhiMDLFluctuationSpectrum

open Real

lemma cosh_mono_Ici {x y : ℝ} (hx : 0 ≤ x) (hxy : x ≤ y) : cosh x ≤ cosh y := by
  exact cosh_strictMonoOn.monotoneOn (Set.mem_Ici.mpr hx)
    (Set.mem_Ici.mpr (hx.trans hxy)) hxy

lemma cosh_b20_ub : cosh ((1 : ℝ) / 500) ≤ (100000301 : ℝ) / 100000000 := by
  have exp_b20 : exp (((1 : ℝ) / 500)^2 / 2) ≤ (100000301 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100000301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1 : ℝ) / 500)).trans (le_trans exp_b20 (by norm_num))

lemma cosh_b40_ub : cosh ((1 : ℝ) / 250) ≤ (100000901 : ℝ) / 100000000 := by
  have exp_b40 : exp (((1 : ℝ) / 250)^2 / 2) ≤ (100000901 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100000901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1 : ℝ) / 250)).trans (le_trans exp_b40 (by norm_num))

lemma cosh_b55_ub : cosh ((11 : ℝ) / 2000) ≤ (100001601 : ℝ) / 100000000 := by
  have exp_b55 : exp (((11 : ℝ) / 2000)^2 / 2) ≤ (100001601 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((11 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((11 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100001601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((11 : ℝ) / 2000)).trans (le_trans exp_b55 (by norm_num))

lemma cosh_b75_ub : cosh ((3 : ℝ) / 400) ≤ (100002901 : ℝ) / 100000000 := by
  have exp_b75 : exp (((3 : ℝ) / 400)^2 / 2) ≤ (100002901 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((3 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100002901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 400)).trans (le_trans exp_b75 (by norm_num))

lemma cosh_b95_ub : cosh ((19 : ℝ) / 2000) ≤ (100004601 : ℝ) / 100000000 := by
  have exp_b95 : exp (((19 : ℝ) / 2000)^2 / 2) ≤ (100004601 : ℝ) / 100000000 := by
    have ht : ((19 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((19 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((19 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100004601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((19 : ℝ) / 2000)).trans (le_trans exp_b95 (by norm_num))

lemma cosh_b110_ub : cosh ((11 : ℝ) / 1000) ≤ (100006101 : ℝ) / 100000000 := by
  have exp_b110 : exp (((11 : ℝ) / 1000)^2 / 2) ≤ (100006101 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((11 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((11 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100006101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((11 : ℝ) / 1000)).trans (le_trans exp_b110 (by norm_num))

lemma cosh_b130_ub : cosh ((13 : ℝ) / 1000) ≤ (100008501 : ℝ) / 100000000 := by
  have exp_b130 : exp (((13 : ℝ) / 1000)^2 / 2) ≤ (100008501 : ℝ) / 100000000 := by
    have ht : ((13 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((13 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((13 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100008501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((13 : ℝ) / 1000)).trans (le_trans exp_b130 (by norm_num))

lemma cosh_b150_ub : cosh ((3 : ℝ) / 200) ≤ (100011301 : ℝ) / 100000000 := by
  have exp_b150 : exp (((3 : ℝ) / 200)^2 / 2) ≤ (100011301 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((3 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100011301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 200)).trans (le_trans exp_b150 (by norm_num))

lemma cosh_b165_ub : cosh ((33 : ℝ) / 2000) ≤ (100013701 : ℝ) / 100000000 := by
  have exp_b165 : exp (((33 : ℝ) / 2000)^2 / 2) ≤ (100013701 : ℝ) / 100000000 := by
    have ht : ((33 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((33 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((33 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100013701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((33 : ℝ) / 2000)).trans (le_trans exp_b165 (by norm_num))

lemma cosh_b185_ub : cosh ((37 : ℝ) / 2000) ≤ (100017201 : ℝ) / 100000000 := by
  have exp_b185 : exp (((37 : ℝ) / 2000)^2 / 2) ≤ (100017201 : ℝ) / 100000000 := by
    have ht : ((37 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((37 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((37 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100017201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((37 : ℝ) / 2000)).trans (le_trans exp_b185 (by norm_num))

lemma cosh_b200_ub : cosh ((1 : ℝ) / 50) ≤ (100020101 : ℝ) / 100000000 := by
  have exp_b200 : exp (((1 : ℝ) / 50)^2 / 2) ≤ (100020101 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100020101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1 : ℝ) / 50)).trans (le_trans exp_b200 (by norm_num))

lemma cosh_b220_ub : cosh ((11 : ℝ) / 500) ≤ (100024301 : ℝ) / 100000000 := by
  have exp_b220 : exp (((11 : ℝ) / 500)^2 / 2) ≤ (100024301 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((11 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((11 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100024301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((11 : ℝ) / 500)).trans (le_trans exp_b220 (by norm_num))

lemma cosh_b240_ub : cosh ((3 : ℝ) / 125) ≤ (100028901 : ℝ) / 100000000 := by
  have exp_b240 : exp (((3 : ℝ) / 125)^2 / 2) ≤ (100028901 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((3 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100028901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 125)).trans (le_trans exp_b240 (by norm_num))

lemma cosh_b255_ub : cosh ((51 : ℝ) / 2000) ≤ (100032601 : ℝ) / 100000000 := by
  have exp_b255 : exp (((51 : ℝ) / 2000)^2 / 2) ≤ (100032601 : ℝ) / 100000000 := by
    have ht : ((51 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((51 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((51 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100032601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((51 : ℝ) / 2000)).trans (le_trans exp_b255 (by norm_num))

lemma cosh_b275_ub : cosh ((11 : ℝ) / 400) ≤ (100037901 : ℝ) / 100000000 := by
  have exp_b275 : exp (((11 : ℝ) / 400)^2 / 2) ≤ (100037901 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((11 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((11 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100037901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((11 : ℝ) / 400)).trans (le_trans exp_b275 (by norm_num))

lemma cosh_b295_ub : cosh ((59 : ℝ) / 2000) ≤ (100043601 : ℝ) / 100000000 := by
  have exp_b295 : exp (((59 : ℝ) / 2000)^2 / 2) ≤ (100043601 : ℝ) / 100000000 := by
    have ht : ((59 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((59 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((59 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100043601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((59 : ℝ) / 2000)).trans (le_trans exp_b295 (by norm_num))

lemma cosh_b310_ub : cosh ((31 : ℝ) / 1000) ≤ (100048101 : ℝ) / 100000000 := by
  have exp_b310 : exp (((31 : ℝ) / 1000)^2 / 2) ≤ (100048101 : ℝ) / 100000000 := by
    have ht : ((31 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((31 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((31 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100048101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((31 : ℝ) / 1000)).trans (le_trans exp_b310 (by norm_num))

lemma cosh_b330_ub : cosh ((33 : ℝ) / 1000) ≤ (100054501 : ℝ) / 100000000 := by
  have exp_b330 : exp (((33 : ℝ) / 1000)^2 / 2) ≤ (100054501 : ℝ) / 100000000 := by
    have ht : ((33 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((33 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((33 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100054501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((33 : ℝ) / 1000)).trans (le_trans exp_b330 (by norm_num))

lemma cosh_b350_ub : cosh ((7 : ℝ) / 200) ≤ (100061301 : ℝ) / 100000000 := by
  have exp_b350 : exp (((7 : ℝ) / 200)^2 / 2) ≤ (100061301 : ℝ) / 100000000 := by
    have ht : ((7 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((7 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((7 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100061301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((7 : ℝ) / 200)).trans (le_trans exp_b350 (by norm_num))

lemma cosh_b365_ub : cosh ((73 : ℝ) / 2000) ≤ (100066701 : ℝ) / 100000000 := by
  have exp_b365 : exp (((73 : ℝ) / 2000)^2 / 2) ≤ (100066701 : ℝ) / 100000000 := by
    have ht : ((73 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((73 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((73 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100066701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((73 : ℝ) / 2000)).trans (le_trans exp_b365 (by norm_num))

lemma cosh_b385_ub : cosh ((77 : ℝ) / 2000) ≤ (100074201 : ℝ) / 100000000 := by
  have exp_b385 : exp (((77 : ℝ) / 2000)^2 / 2) ≤ (100074201 : ℝ) / 100000000 := by
    have ht : ((77 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((77 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((77 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100074201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((77 : ℝ) / 2000)).trans (le_trans exp_b385 (by norm_num))

lemma cosh_b400_ub : cosh ((1 : ℝ) / 25) ≤ (100080101 : ℝ) / 100000000 := by
  have exp_b400 : exp (((1 : ℝ) / 25)^2 / 2) ≤ (100080101 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100080101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1 : ℝ) / 25)).trans (le_trans exp_b400 (by norm_num))

lemma cosh_b420_ub : cosh ((21 : ℝ) / 500) ≤ (100088301 : ℝ) / 100000000 := by
  have exp_b420 : exp (((21 : ℝ) / 500)^2 / 2) ≤ (100088301 : ℝ) / 100000000 := by
    have ht : ((21 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((21 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((21 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100088301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((21 : ℝ) / 500)).trans (le_trans exp_b420 (by norm_num))

lemma cosh_b440_ub : cosh ((11 : ℝ) / 250) ≤ (100096901 : ℝ) / 100000000 := by
  have exp_b440 : exp (((11 : ℝ) / 250)^2 / 2) ≤ (100096901 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((11 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((11 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100096901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((11 : ℝ) / 250)).trans (le_trans exp_b440 (by norm_num))

lemma cosh_b455_ub : cosh ((91 : ℝ) / 2000) ≤ (100103601 : ℝ) / 100000000 := by
  have exp_b455 : exp (((91 : ℝ) / 2000)^2 / 2) ≤ (100103601 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((91 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((91 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100103601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((91 : ℝ) / 2000)).trans (le_trans exp_b455 (by norm_num))

lemma cosh_b475_ub : cosh ((19 : ℝ) / 400) ≤ (100112901 : ℝ) / 100000000 := by
  have exp_b475 : exp (((19 : ℝ) / 400)^2 / 2) ≤ (100112901 : ℝ) / 100000000 := by
    have ht : ((19 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((19 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((19 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100112901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((19 : ℝ) / 400)).trans (le_trans exp_b475 (by norm_num))

lemma cosh_b495_ub : cosh ((99 : ℝ) / 2000) ≤ (100122601 : ℝ) / 100000000 := by
  have exp_b495 : exp (((99 : ℝ) / 2000)^2 / 2) ≤ (100122601 : ℝ) / 100000000 := by
    have ht : ((99 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((99 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((99 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100122601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((99 : ℝ) / 2000)).trans (le_trans exp_b495 (by norm_num))

lemma cosh_b510_ub : cosh ((51 : ℝ) / 1000) ≤ (100130201 : ℝ) / 100000000 := by
  have exp_b510 : exp (((51 : ℝ) / 1000)^2 / 2) ≤ (100130201 : ℝ) / 100000000 := by
    have ht : ((51 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((51 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((51 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100130201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((51 : ℝ) / 1000)).trans (le_trans exp_b510 (by norm_num))

lemma cosh_b530_ub : cosh ((53 : ℝ) / 1000) ≤ (100140601 : ℝ) / 100000000 := by
  have exp_b530 : exp (((53 : ℝ) / 1000)^2 / 2) ≤ (100140601 : ℝ) / 100000000 := by
    have ht : ((53 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((53 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((53 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100140601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((53 : ℝ) / 1000)).trans (le_trans exp_b530 (by norm_num))

lemma cosh_b550_ub : cosh ((11 : ℝ) / 200) ≤ (100151401 : ℝ) / 100000000 := by
  have exp_b550 : exp (((11 : ℝ) / 200)^2 / 2) ≤ (100151401 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((11 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((11 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100151401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((11 : ℝ) / 200)).trans (le_trans exp_b550 (by norm_num))

lemma cosh_b565_ub : cosh ((113 : ℝ) / 2000) ≤ (100159801 : ℝ) / 100000000 := by
  have exp_b565 : exp (((113 : ℝ) / 2000)^2 / 2) ≤ (100159801 : ℝ) / 100000000 := by
    have ht : ((113 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((113 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((113 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100159801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((113 : ℝ) / 2000)).trans (le_trans exp_b565 (by norm_num))

lemma cosh_b585_ub : cosh ((117 : ℝ) / 2000) ≤ (100171301 : ℝ) / 100000000 := by
  have exp_b585 : exp (((117 : ℝ) / 2000)^2 / 2) ≤ (100171301 : ℝ) / 100000000 := by
    have ht : ((117 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((117 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((117 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100171301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((117 : ℝ) / 2000)).trans (le_trans exp_b585 (by norm_num))

lemma cosh_b600_ub : cosh ((3 : ℝ) / 50) ≤ (100180201 : ℝ) / 100000000 := by
  have exp_b600 : exp (((3 : ℝ) / 50)^2 / 2) ≤ (100180201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((3 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100180201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 50)).trans (le_trans exp_b600 (by norm_num))

lemma cosh_b620_ub : cosh ((31 : ℝ) / 500) ≤ (100192401 : ℝ) / 100000000 := by
  have exp_b620 : exp (((31 : ℝ) / 500)^2 / 2) ≤ (100192401 : ℝ) / 100000000 := by
    have ht : ((31 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((31 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((31 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100192401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((31 : ℝ) / 500)).trans (le_trans exp_b620 (by norm_num))

lemma cosh_b640_ub : cosh ((8 : ℝ) / 125) ≤ (100205101 : ℝ) / 100000000 := by
  have exp_b640 : exp (((8 : ℝ) / 125)^2 / 2) ≤ (100205101 : ℝ) / 100000000 := by
    have ht : ((8 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((8 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((8 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100205101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((8 : ℝ) / 125)).trans (le_trans exp_b640 (by norm_num))

lemma cosh_b655_ub : cosh ((131 : ℝ) / 2000) ≤ (100214801 : ℝ) / 100000000 := by
  have exp_b655 : exp (((131 : ℝ) / 2000)^2 / 2) ≤ (100214801 : ℝ) / 100000000 := by
    have ht : ((131 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((131 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((131 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100214801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((131 : ℝ) / 2000)).trans (le_trans exp_b655 (by norm_num))

lemma cosh_b675_ub : cosh ((27 : ℝ) / 400) ≤ (100228101 : ℝ) / 100000000 := by
  have exp_b675 : exp (((27 : ℝ) / 400)^2 / 2) ≤ (100228101 : ℝ) / 100000000 := by
    have ht : ((27 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((27 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((27 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100228101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((27 : ℝ) / 400)).trans (le_trans exp_b675 (by norm_num))

lemma cosh_b695_ub : cosh ((139 : ℝ) / 2000) ≤ (100241901 : ℝ) / 100000000 := by
  have exp_b695 : exp (((139 : ℝ) / 2000)^2 / 2) ≤ (100241901 : ℝ) / 100000000 := by
    have ht : ((139 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((139 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((139 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100241901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((139 : ℝ) / 2000)).trans (le_trans exp_b695 (by norm_num))

lemma cosh_b710_ub : cosh ((71 : ℝ) / 1000) ≤ (100252401 : ℝ) / 100000000 := by
  have exp_b710 : exp (((71 : ℝ) / 1000)^2 / 2) ≤ (100252401 : ℝ) / 100000000 := by
    have ht : ((71 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((71 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((71 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100252401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((71 : ℝ) / 1000)).trans (le_trans exp_b710 (by norm_num))

lemma cosh_b730_ub : cosh ((73 : ℝ) / 1000) ≤ (100266901 : ℝ) / 100000000 := by
  have exp_b730 : exp (((73 : ℝ) / 1000)^2 / 2) ≤ (100266901 : ℝ) / 100000000 := by
    have ht : ((73 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((73 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((73 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100266901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((73 : ℝ) / 1000)).trans (le_trans exp_b730 (by norm_num))

lemma cosh_b750_ub : cosh ((3 : ℝ) / 40) ≤ (100281701 : ℝ) / 100000000 := by
  have exp_b750 : exp (((3 : ℝ) / 40)^2 / 2) ≤ (100281701 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 40)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((3 : ℝ) / 40)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 40)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100281701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 40)).trans (le_trans exp_b750 (by norm_num))

lemma cosh_b765_ub : cosh ((153 : ℝ) / 2000) ≤ (100293101 : ℝ) / 100000000 := by
  have exp_b765 : exp (((153 : ℝ) / 2000)^2 / 2) ≤ (100293101 : ℝ) / 100000000 := by
    have ht : ((153 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((153 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((153 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100293101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((153 : ℝ) / 2000)).trans (le_trans exp_b765 (by norm_num))

lemma cosh_b785_ub : cosh ((157 : ℝ) / 2000) ≤ (100308601 : ℝ) / 100000000 := by
  have exp_b785 : exp (((157 : ℝ) / 2000)^2 / 2) ≤ (100308601 : ℝ) / 100000000 := by
    have ht : ((157 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((157 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((157 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100308601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((157 : ℝ) / 2000)).trans (le_trans exp_b785 (by norm_num))

lemma cosh_b800_ub : cosh ((2 : ℝ) / 25) ≤ (100320601 : ℝ) / 100000000 := by
  have exp_b800 : exp (((2 : ℝ) / 25)^2 / 2) ≤ (100320601 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100320601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 25)).trans (le_trans exp_b800 (by norm_num))

lemma cosh_b820_ub : cosh ((41 : ℝ) / 500) ≤ (100336801 : ℝ) / 100000000 := by
  have exp_b820 : exp (((41 : ℝ) / 500)^2 / 2) ≤ (100336801 : ℝ) / 100000000 := by
    have ht : ((41 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((41 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((41 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100336801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((41 : ℝ) / 500)).trans (le_trans exp_b820 (by norm_num))

lemma cosh_b840_ub : cosh ((21 : ℝ) / 250) ≤ (100353501 : ℝ) / 100000000 := by
  have exp_b840 : exp (((21 : ℝ) / 250)^2 / 2) ≤ (100353501 : ℝ) / 100000000 := by
    have ht : ((21 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((21 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((21 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100353501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((21 : ℝ) / 250)).trans (le_trans exp_b840 (by norm_num))

lemma cosh_b855_ub : cosh ((171 : ℝ) / 2000) ≤ (100366201 : ℝ) / 100000000 := by
  have exp_b855 : exp (((171 : ℝ) / 2000)^2 / 2) ≤ (100366201 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((171 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((171 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100366201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((171 : ℝ) / 2000)).trans (le_trans exp_b855 (by norm_num))

lemma cosh_b875_ub : cosh ((7 : ℝ) / 80) ≤ (100383601 : ℝ) / 100000000 := by
  have exp_b875 : exp (((7 : ℝ) / 80)^2 / 2) ≤ (100383601 : ℝ) / 100000000 := by
    have ht : ((7 : ℝ) / 80)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((7 : ℝ) / 80)^2 / 2) ^ m / (Nat.factorial m)) +
          (((7 : ℝ) / 80)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100383601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((7 : ℝ) / 80)).trans (le_trans exp_b875 (by norm_num))

lemma cosh_b895_ub : cosh ((179 : ℝ) / 2000) ≤ (100401401 : ℝ) / 100000000 := by
  have exp_b895 : exp (((179 : ℝ) / 2000)^2 / 2) ≤ (100401401 : ℝ) / 100000000 := by
    have ht : ((179 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((179 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((179 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100401401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((179 : ℝ) / 2000)).trans (le_trans exp_b895 (by norm_num))

lemma cosh_b910_ub : cosh ((91 : ℝ) / 1000) ≤ (100415001 : ℝ) / 100000000 := by
  have exp_b910 : exp (((91 : ℝ) / 1000)^2 / 2) ≤ (100415001 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((91 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((91 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100415001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((91 : ℝ) / 1000)).trans (le_trans exp_b910 (by norm_num))

lemma cosh_b930_ub : cosh ((93 : ℝ) / 1000) ≤ (100433401 : ℝ) / 100000000 := by
  have exp_b930 : exp (((93 : ℝ) / 1000)^2 / 2) ≤ (100433401 : ℝ) / 100000000 := by
    have ht : ((93 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((93 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((93 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100433401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((93 : ℝ) / 1000)).trans (le_trans exp_b930 (by norm_num))

lemma cosh_b950_ub : cosh ((19 : ℝ) / 200) ≤ (100452301 : ℝ) / 100000000 := by
  have exp_b950 : exp (((19 : ℝ) / 200)^2 / 2) ≤ (100452301 : ℝ) / 100000000 := by
    have ht : ((19 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((19 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((19 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100452301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((19 : ℝ) / 200)).trans (le_trans exp_b950 (by norm_num))

lemma cosh_b965_ub : cosh ((193 : ℝ) / 2000) ≤ (100466701 : ℝ) / 100000000 := by
  have exp_b965 : exp (((193 : ℝ) / 2000)^2 / 2) ≤ (100466701 : ℝ) / 100000000 := by
    have ht : ((193 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((193 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((193 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100466701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((193 : ℝ) / 2000)).trans (le_trans exp_b965 (by norm_num))

lemma cosh_b985_ub : cosh ((197 : ℝ) / 2000) ≤ (100486301 : ℝ) / 100000000 := by
  have exp_b985 : exp (((197 : ℝ) / 2000)^2 / 2) ≤ (100486301 : ℝ) / 100000000 := by
    have ht : ((197 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((197 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((197 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100486301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((197 : ℝ) / 2000)).trans (le_trans exp_b985 (by norm_num))

lemma cosh_b1000_ub : cosh ((1 : ℝ) / 10) ≤ (100501301 : ℝ) / 100000000 := by
  have exp_b1000 : exp (((1 : ℝ) / 10)^2 / 2) ≤ (100501301 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 10)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1 : ℝ) / 10)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1 : ℝ) / 10)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100501301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1 : ℝ) / 10)).trans (le_trans exp_b1000 (by norm_num))

lemma cosh_b1020_ub : cosh ((51 : ℝ) / 500) ≤ (100521601 : ℝ) / 100000000 := by
  have exp_b1020 : exp (((51 : ℝ) / 500)^2 / 2) ≤ (100521601 : ℝ) / 100000000 := by
    have ht : ((51 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((51 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((51 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100521601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((51 : ℝ) / 500)).trans (le_trans exp_b1020 (by norm_num))

lemma cosh_b1040_ub : cosh ((13 : ℝ) / 125) ≤ (100542301 : ℝ) / 100000000 := by
  have exp_b1040 : exp (((13 : ℝ) / 125)^2 / 2) ≤ (100542301 : ℝ) / 100000000 := by
    have ht : ((13 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((13 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((13 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100542301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((13 : ℝ) / 125)).trans (le_trans exp_b1040 (by norm_num))

lemma cosh_b1055_ub : cosh ((211 : ℝ) / 2000) ≤ (100558101 : ℝ) / 100000000 := by
  have exp_b1055 : exp (((211 : ℝ) / 2000)^2 / 2) ≤ (100558101 : ℝ) / 100000000 := by
    have ht : ((211 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((211 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((211 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100558101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((211 : ℝ) / 2000)).trans (le_trans exp_b1055 (by norm_num))

lemma cosh_b1075_ub : cosh ((43 : ℝ) / 400) ≤ (100579501 : ℝ) / 100000000 := by
  have exp_b1075 : exp (((43 : ℝ) / 400)^2 / 2) ≤ (100579501 : ℝ) / 100000000 := by
    have ht : ((43 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((43 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((43 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100579501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((43 : ℝ) / 400)).trans (le_trans exp_b1075 (by norm_num))

lemma cosh_b1095_ub : cosh ((219 : ℝ) / 2000) ≤ (100601401 : ℝ) / 100000000 := by
  have exp_b1095 : exp (((219 : ℝ) / 2000)^2 / 2) ≤ (100601401 : ℝ) / 100000000 := by
    have ht : ((219 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((219 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((219 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100601401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((219 : ℝ) / 2000)).trans (le_trans exp_b1095 (by norm_num))

lemma cosh_b1110_ub : cosh ((111 : ℝ) / 1000) ≤ (100618001 : ℝ) / 100000000 := by
  have exp_b1110 : exp (((111 : ℝ) / 1000)^2 / 2) ≤ (100618001 : ℝ) / 100000000 := by
    have ht : ((111 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((111 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((111 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100618001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((111 : ℝ) / 1000)).trans (le_trans exp_b1110 (by norm_num))

lemma cosh_b1130_ub : cosh ((113 : ℝ) / 1000) ≤ (100640501 : ℝ) / 100000000 := by
  have exp_b1130 : exp (((113 : ℝ) / 1000)^2 / 2) ≤ (100640501 : ℝ) / 100000000 := by
    have ht : ((113 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((113 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((113 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100640501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((113 : ℝ) / 1000)).trans (le_trans exp_b1130 (by norm_num))

lemma cosh_b1150_ub : cosh ((23 : ℝ) / 200) ≤ (100663501 : ℝ) / 100000000 := by
  have exp_b1150 : exp (((23 : ℝ) / 200)^2 / 2) ≤ (100663501 : ℝ) / 100000000 := by
    have ht : ((23 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((23 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((23 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100663501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((23 : ℝ) / 200)).trans (le_trans exp_b1150 (by norm_num))

lemma cosh_b1165_ub : cosh ((233 : ℝ) / 2000) ≤ (100681001 : ℝ) / 100000000 := by
  have exp_b1165 : exp (((233 : ℝ) / 2000)^2 / 2) ≤ (100681001 : ℝ) / 100000000 := by
    have ht : ((233 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((233 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((233 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100681001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((233 : ℝ) / 2000)).trans (le_trans exp_b1165 (by norm_num))

lemma cosh_b1185_ub : cosh ((237 : ℝ) / 2000) ≤ (100704601 : ℝ) / 100000000 := by
  have exp_b1185 : exp (((237 : ℝ) / 2000)^2 / 2) ≤ (100704601 : ℝ) / 100000000 := by
    have ht : ((237 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((237 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((237 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100704601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((237 : ℝ) / 2000)).trans (le_trans exp_b1185 (by norm_num))

lemma cosh_b1200_ub : cosh ((3 : ℝ) / 25) ≤ (100722601 : ℝ) / 100000000 := by
  have exp_b1200 : exp (((3 : ℝ) / 25)^2 / 2) ≤ (100722601 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((3 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100722601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 25)).trans (le_trans exp_b1200 (by norm_num))

lemma cosh_b1220_ub : cosh ((61 : ℝ) / 500) ≤ (100747001 : ℝ) / 100000000 := by
  have exp_b1220 : exp (((61 : ℝ) / 500)^2 / 2) ≤ (100747001 : ℝ) / 100000000 := by
    have ht : ((61 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((61 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((61 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100747001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((61 : ℝ) / 500)).trans (le_trans exp_b1220 (by norm_num))

lemma cosh_b1240_ub : cosh ((31 : ℝ) / 250) ≤ (100771801 : ℝ) / 100000000 := by
  have exp_b1240 : exp (((31 : ℝ) / 250)^2 / 2) ≤ (100771801 : ℝ) / 100000000 := by
    have ht : ((31 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((31 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((31 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100771801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((31 : ℝ) / 250)).trans (le_trans exp_b1240 (by norm_num))

lemma cosh_b1255_ub : cosh ((251 : ℝ) / 2000) ≤ (100790701 : ℝ) / 100000000 := by
  have exp_b1255 : exp (((251 : ℝ) / 2000)^2 / 2) ≤ (100790701 : ℝ) / 100000000 := by
    have ht : ((251 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((251 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((251 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100790701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((251 : ℝ) / 2000)).trans (le_trans exp_b1255 (by norm_num))

lemma cosh_b1275_ub : cosh ((51 : ℝ) / 400) ≤ (100816201 : ℝ) / 100000000 := by
  have exp_b1275 : exp (((51 : ℝ) / 400)^2 / 2) ≤ (100816201 : ℝ) / 100000000 := by
    have ht : ((51 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((51 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((51 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100816201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((51 : ℝ) / 400)).trans (le_trans exp_b1275 (by norm_num))

lemma cosh_b1295_ub : cosh ((259 : ℝ) / 2000) ≤ (100842101 : ℝ) / 100000000 := by
  have exp_b1295 : exp (((259 : ℝ) / 2000)^2 / 2) ≤ (100842101 : ℝ) / 100000000 := by
    have ht : ((259 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((259 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((259 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100842101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((259 : ℝ) / 2000)).trans (le_trans exp_b1295 (by norm_num))

lemma cosh_b1310_ub : cosh ((131 : ℝ) / 1000) ≤ (100861801 : ℝ) / 100000000 := by
  have exp_b1310 : exp (((131 : ℝ) / 1000)^2 / 2) ≤ (100861801 : ℝ) / 100000000 := by
    have ht : ((131 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((131 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((131 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100861801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((131 : ℝ) / 1000)).trans (le_trans exp_b1310 (by norm_num))

lemma cosh_b1330_ub : cosh ((133 : ℝ) / 1000) ≤ (100888401 : ℝ) / 100000000 := by
  have exp_b1330 : exp (((133 : ℝ) / 1000)^2 / 2) ≤ (100888401 : ℝ) / 100000000 := by
    have ht : ((133 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((133 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((133 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100888401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((133 : ℝ) / 1000)).trans (le_trans exp_b1330 (by norm_num))

lemma cosh_b1350_ub : cosh ((27 : ℝ) / 200) ≤ (100915501 : ℝ) / 100000000 := by
  have exp_b1350 : exp (((27 : ℝ) / 200)^2 / 2) ≤ (100915501 : ℝ) / 100000000 := by
    have ht : ((27 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((27 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((27 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100915501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((27 : ℝ) / 200)).trans (le_trans exp_b1350 (by norm_num))

lemma cosh_b1365_ub : cosh ((273 : ℝ) / 2000) ≤ (100936001 : ℝ) / 100000000 := by
  have exp_b1365 : exp (((273 : ℝ) / 2000)^2 / 2) ≤ (100936001 : ℝ) / 100000000 := by
    have ht : ((273 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((273 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((273 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100936001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((273 : ℝ) / 2000)).trans (le_trans exp_b1365 (by norm_num))

lemma cosh_b1385_ub : cosh ((277 : ℝ) / 2000) ≤ (100963801 : ℝ) / 100000000 := by
  have exp_b1385 : exp (((277 : ℝ) / 2000)^2 / 2) ≤ (100963801 : ℝ) / 100000000 := by
    have ht : ((277 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((277 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((277 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100963801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((277 : ℝ) / 2000)).trans (le_trans exp_b1385 (by norm_num))

lemma cosh_b1400_ub : cosh ((7 : ℝ) / 50) ≤ (100984901 : ℝ) / 100000000 := by
  have exp_b1400 : exp (((7 : ℝ) / 50)^2 / 2) ≤ (100984901 : ℝ) / 100000000 := by
    have ht : ((7 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((7 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((7 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100984901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((7 : ℝ) / 50)).trans (le_trans exp_b1400 (by norm_num))

lemma cosh_b1420_ub : cosh ((71 : ℝ) / 500) ≤ (101013301 : ℝ) / 100000000 := by
  have exp_b1420 : exp (((71 : ℝ) / 500)^2 / 2) ≤ (101013301 : ℝ) / 100000000 := by
    have ht : ((71 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((71 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((71 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101013301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((71 : ℝ) / 500)).trans (le_trans exp_b1420 (by norm_num))

lemma cosh_b1440_ub : cosh ((18 : ℝ) / 125) ≤ (101042201 : ℝ) / 100000000 := by
  have exp_b1440 : exp (((18 : ℝ) / 125)^2 / 2) ≤ (101042201 : ℝ) / 100000000 := by
    have ht : ((18 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((18 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((18 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101042201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((18 : ℝ) / 125)).trans (le_trans exp_b1440 (by norm_num))

lemma cosh_b1455_ub : cosh ((291 : ℝ) / 2000) ≤ (101064201 : ℝ) / 100000000 := by
  have exp_b1455 : exp (((291 : ℝ) / 2000)^2 / 2) ≤ (101064201 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((291 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((291 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101064201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((291 : ℝ) / 2000)).trans (le_trans exp_b1455 (by norm_num))

lemma cosh_b1475_ub : cosh ((59 : ℝ) / 400) ≤ (101093801 : ℝ) / 100000000 := by
  have exp_b1475 : exp (((59 : ℝ) / 400)^2 / 2) ≤ (101093801 : ℝ) / 100000000 := by
    have ht : ((59 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((59 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((59 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101093801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((59 : ℝ) / 400)).trans (le_trans exp_b1475 (by norm_num))

lemma cosh_b1495_ub : cosh ((299 : ℝ) / 2000) ≤ (101123801 : ℝ) / 100000000 := by
  have exp_b1495 : exp (((299 : ℝ) / 2000)^2 / 2) ≤ (101123801 : ℝ) / 100000000 := by
    have ht : ((299 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((299 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((299 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101123801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((299 : ℝ) / 2000)).trans (le_trans exp_b1495 (by norm_num))

lemma cosh_b1510_ub : cosh ((151 : ℝ) / 1000) ≤ (101146601 : ℝ) / 100000000 := by
  have exp_b1510 : exp (((151 : ℝ) / 1000)^2 / 2) ≤ (101146601 : ℝ) / 100000000 := by
    have ht : ((151 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((151 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((151 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101146601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((151 : ℝ) / 1000)).trans (le_trans exp_b1510 (by norm_num))

lemma cosh_b1530_ub : cosh ((153 : ℝ) / 1000) ≤ (101177401 : ℝ) / 100000000 := by
  have exp_b1530 : exp (((153 : ℝ) / 1000)^2 / 2) ≤ (101177401 : ℝ) / 100000000 := by
    have ht : ((153 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((153 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((153 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101177401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((153 : ℝ) / 1000)).trans (le_trans exp_b1530 (by norm_num))

lemma cosh_b1550_ub : cosh ((31 : ℝ) / 200) ≤ (101208501 : ℝ) / 100000000 := by
  have exp_b1550 : exp (((31 : ℝ) / 200)^2 / 2) ≤ (101208501 : ℝ) / 100000000 := by
    have ht : ((31 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((31 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((31 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101208501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((31 : ℝ) / 200)).trans (le_trans exp_b1550 (by norm_num))

lemma cosh_b1565_ub : cosh ((313 : ℝ) / 2000) ≤ (101232201 : ℝ) / 100000000 := by
  have exp_b1565 : exp (((313 : ℝ) / 2000)^2 / 2) ≤ (101232201 : ℝ) / 100000000 := by
    have ht : ((313 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((313 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((313 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101232201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((313 : ℝ) / 2000)).trans (le_trans exp_b1565 (by norm_num))

lemma cosh_b1585_ub : cosh ((317 : ℝ) / 2000) ≤ (101264101 : ℝ) / 100000000 := by
  have exp_b1585 : exp (((317 : ℝ) / 2000)^2 / 2) ≤ (101264101 : ℝ) / 100000000 := by
    have ht : ((317 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((317 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((317 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101264101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((317 : ℝ) / 2000)).trans (le_trans exp_b1585 (by norm_num))

lemma cosh_b1600_ub : cosh ((4 : ℝ) / 25) ≤ (101288301 : ℝ) / 100000000 := by
  have exp_b1600 : exp (((4 : ℝ) / 25)^2 / 2) ≤ (101288301 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((4 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101288301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 25)).trans (le_trans exp_b1600 (by norm_num))

lemma cosh_b1620_ub : cosh ((81 : ℝ) / 500) ≤ (101320901 : ℝ) / 100000000 := by
  have exp_b1620 : exp (((81 : ℝ) / 500)^2 / 2) ≤ (101320901 : ℝ) / 100000000 := by
    have ht : ((81 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((81 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((81 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101320901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((81 : ℝ) / 500)).trans (le_trans exp_b1620 (by norm_num))

lemma cosh_b1640_ub : cosh ((41 : ℝ) / 250) ≤ (101353901 : ℝ) / 100000000 := by
  have exp_b1640 : exp (((41 : ℝ) / 250)^2 / 2) ≤ (101353901 : ℝ) / 100000000 := by
    have ht : ((41 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((41 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((41 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101353901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((41 : ℝ) / 250)).trans (le_trans exp_b1640 (by norm_num))

lemma cosh_b1655_ub : cosh ((331 : ℝ) / 2000) ≤ (101379001 : ℝ) / 100000000 := by
  have exp_b1655 : exp (((331 : ℝ) / 2000)^2 / 2) ≤ (101379001 : ℝ) / 100000000 := by
    have ht : ((331 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((331 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((331 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101379001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((331 : ℝ) / 2000)).trans (le_trans exp_b1655 (by norm_num))

lemma cosh_b1675_ub : cosh ((67 : ℝ) / 400) ≤ (101412701 : ℝ) / 100000000 := by
  have exp_b1675 : exp (((67 : ℝ) / 400)^2 / 2) ≤ (101412701 : ℝ) / 100000000 := by
    have ht : ((67 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((67 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((67 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101412701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((67 : ℝ) / 400)).trans (le_trans exp_b1675 (by norm_num))

lemma cosh_b1695_ub : cosh ((339 : ℝ) / 2000) ≤ (101446901 : ℝ) / 100000000 := by
  have exp_b1695 : exp (((339 : ℝ) / 2000)^2 / 2) ≤ (101446901 : ℝ) / 100000000 := by
    have ht : ((339 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((339 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((339 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101446901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((339 : ℝ) / 2000)).trans (le_trans exp_b1695 (by norm_num))

lemma cosh_b1710_ub : cosh ((171 : ℝ) / 1000) ≤ (101472801 : ℝ) / 100000000 := by
  have exp_b1710 : exp (((171 : ℝ) / 1000)^2 / 2) ≤ (101472801 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((171 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((171 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101472801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((171 : ℝ) / 1000)).trans (le_trans exp_b1710 (by norm_num))

lemma cosh_b1730_ub : cosh ((173 : ℝ) / 1000) ≤ (101507801 : ℝ) / 100000000 := by
  have exp_b1730 : exp (((173 : ℝ) / 1000)^2 / 2) ≤ (101507801 : ℝ) / 100000000 := by
    have ht : ((173 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((173 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((173 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101507801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((173 : ℝ) / 1000)).trans (le_trans exp_b1730 (by norm_num))

lemma cosh_b1750_ub : cosh ((7 : ℝ) / 40) ≤ (101543101 : ℝ) / 100000000 := by
  have exp_b1750 : exp (((7 : ℝ) / 40)^2 / 2) ≤ (101543101 : ℝ) / 100000000 := by
    have ht : ((7 : ℝ) / 40)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((7 : ℝ) / 40)^2 / 2) ^ m / (Nat.factorial m)) +
          (((7 : ℝ) / 40)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101543101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((7 : ℝ) / 40)).trans (le_trans exp_b1750 (by norm_num))

lemma cosh_b1765_ub : cosh ((353 : ℝ) / 2000) ≤ (101569901 : ℝ) / 100000000 := by
  have exp_b1765 : exp (((353 : ℝ) / 2000)^2 / 2) ≤ (101569901 : ℝ) / 100000000 := by
    have ht : ((353 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((353 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((353 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101569901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((353 : ℝ) / 2000)).trans (le_trans exp_b1765 (by norm_num))

lemma cosh_b1785_ub : cosh ((357 : ℝ) / 2000) ≤ (101605901 : ℝ) / 100000000 := by
  have exp_b1785 : exp (((357 : ℝ) / 2000)^2 / 2) ≤ (101605901 : ℝ) / 100000000 := by
    have ht : ((357 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((357 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((357 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101605901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((357 : ℝ) / 2000)).trans (le_trans exp_b1785 (by norm_num))

lemma cosh_b1800_ub : cosh ((9 : ℝ) / 50) ≤ (101633201 : ℝ) / 100000000 := by
  have exp_b1800 : exp (((9 : ℝ) / 50)^2 / 2) ≤ (101633201 : ℝ) / 100000000 := by
    have ht : ((9 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((9 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((9 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101633201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((9 : ℝ) / 50)).trans (le_trans exp_b1800 (by norm_num))

lemma cosh_b1820_ub : cosh ((91 : ℝ) / 500) ≤ (101670001 : ℝ) / 100000000 := by
  have exp_b1820 : exp (((91 : ℝ) / 500)^2 / 2) ≤ (101670001 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((91 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((91 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101670001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((91 : ℝ) / 500)).trans (le_trans exp_b1820 (by norm_num))

lemma cosh_b1840_ub : cosh ((23 : ℝ) / 125) ≤ (101707301 : ℝ) / 100000000 := by
  have exp_b1840 : exp (((23 : ℝ) / 125)^2 / 2) ≤ (101707301 : ℝ) / 100000000 := by
    have ht : ((23 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((23 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((23 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101707301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((23 : ℝ) / 125)).trans (le_trans exp_b1840 (by norm_num))

lemma cosh_b1855_ub : cosh ((371 : ℝ) / 2000) ≤ (101735401 : ℝ) / 100000000 := by
  have exp_b1855 : exp (((371 : ℝ) / 2000)^2 / 2) ≤ (101735401 : ℝ) / 100000000 := by
    have ht : ((371 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((371 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((371 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101735401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((371 : ℝ) / 2000)).trans (le_trans exp_b1855 (by norm_num))

lemma cosh_b1875_ub : cosh ((3 : ℝ) / 16) ≤ (101773401 : ℝ) / 100000000 := by
  have exp_b1875 : exp (((3 : ℝ) / 16)^2 / 2) ≤ (101773401 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 16)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((3 : ℝ) / 16)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 16)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101773401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 16)).trans (le_trans exp_b1875 (by norm_num))

lemma cosh_b1895_ub : cosh ((379 : ℝ) / 2000) ≤ (101811801 : ℝ) / 100000000 := by
  have exp_b1895 : exp (((379 : ℝ) / 2000)^2 / 2) ≤ (101811801 : ℝ) / 100000000 := by
    have ht : ((379 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((379 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((379 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101811801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((379 : ℝ) / 2000)).trans (le_trans exp_b1895 (by norm_num))

lemma cosh_b1910_ub : cosh ((191 : ℝ) / 1000) ≤ (101840801 : ℝ) / 100000000 := by
  have exp_b1910 : exp (((191 : ℝ) / 1000)^2 / 2) ≤ (101840801 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((191 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((191 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101840801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((191 : ℝ) / 1000)).trans (le_trans exp_b1910 (by norm_num))

lemma cosh_b1930_ub : cosh ((193 : ℝ) / 1000) ≤ (101880001 : ℝ) / 100000000 := by
  have exp_b1930 : exp (((193 : ℝ) / 1000)^2 / 2) ≤ (101880001 : ℝ) / 100000000 := by
    have ht : ((193 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((193 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((193 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101880001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((193 : ℝ) / 1000)).trans (le_trans exp_b1930 (by norm_num))

lemma cosh_b1950_ub : cosh ((39 : ℝ) / 200) ≤ (101919501 : ℝ) / 100000000 := by
  have exp_b1950 : exp (((39 : ℝ) / 200)^2 / 2) ≤ (101919501 : ℝ) / 100000000 := by
    have ht : ((39 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((39 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((39 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101919501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((39 : ℝ) / 200)).trans (le_trans exp_b1950 (by norm_num))

lemma cosh_b1965_ub : cosh ((393 : ℝ) / 2000) ≤ (101949401 : ℝ) / 100000000 := by
  have exp_b1965 : exp (((393 : ℝ) / 2000)^2 / 2) ≤ (101949401 : ℝ) / 100000000 := by
    have ht : ((393 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((393 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((393 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101949401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((393 : ℝ) / 2000)).trans (le_trans exp_b1965 (by norm_num))

lemma cosh_b1985_ub : cosh ((397 : ℝ) / 2000) ≤ (101989701 : ℝ) / 100000000 := by
  have exp_b1985 : exp (((397 : ℝ) / 2000)^2 / 2) ≤ (101989701 : ℝ) / 100000000 := by
    have ht : ((397 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((397 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((397 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101989701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((397 : ℝ) / 2000)).trans (le_trans exp_b1985 (by norm_num))

lemma cosh_b2000_ub : cosh ((1 : ℝ) / 5) ≤ (102020201 : ℝ) / 100000000 := by
  have exp_b2000 : exp (((1 : ℝ) / 5)^2 / 2) ≤ (102020201 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 5)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1 : ℝ) / 5)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1 : ℝ) / 5)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102020201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1 : ℝ) / 5)).trans (le_trans exp_b2000 (by norm_num))

lemma cosh_b2020_ub : cosh ((101 : ℝ) / 500) ≤ (102061201 : ℝ) / 100000000 := by
  have exp_b2020 : exp (((101 : ℝ) / 500)^2 / 2) ≤ (102061201 : ℝ) / 100000000 := by
    have ht : ((101 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((101 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((101 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102061201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((101 : ℝ) / 500)).trans (le_trans exp_b2020 (by norm_num))

lemma cosh_b2040_ub : cosh ((51 : ℝ) / 250) ≤ (102102601 : ℝ) / 100000000 := by
  have exp_b2040 : exp (((51 : ℝ) / 250)^2 / 2) ≤ (102102601 : ℝ) / 100000000 := by
    have ht : ((51 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((51 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((51 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102102601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((51 : ℝ) / 250)).trans (le_trans exp_b2040 (by norm_num))

lemma cosh_b2055_ub : cosh ((411 : ℝ) / 2000) ≤ (102134001 : ℝ) / 100000000 := by
  have exp_b2055 : exp (((411 : ℝ) / 2000)^2 / 2) ≤ (102134001 : ℝ) / 100000000 := by
    have ht : ((411 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((411 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((411 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102134001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((411 : ℝ) / 2000)).trans (le_trans exp_b2055 (by norm_num))

lemma cosh_b2075_ub : cosh ((83 : ℝ) / 400) ≤ (102176201 : ℝ) / 100000000 := by
  have exp_b2075 : exp (((83 : ℝ) / 400)^2 / 2) ≤ (102176201 : ℝ) / 100000000 := by
    have ht : ((83 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((83 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((83 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102176201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((83 : ℝ) / 400)).trans (le_trans exp_b2075 (by norm_num))

lemma cosh_b2095_ub : cosh ((419 : ℝ) / 2000) ≤ (102218801 : ℝ) / 100000000 := by
  have exp_b2095 : exp (((419 : ℝ) / 2000)^2 / 2) ≤ (102218801 : ℝ) / 100000000 := by
    have ht : ((419 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((419 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((419 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102218801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((419 : ℝ) / 2000)).trans (le_trans exp_b2095 (by norm_num))

lemma cosh_b2110_ub : cosh ((211 : ℝ) / 1000) ≤ (102251101 : ℝ) / 100000000 := by
  have exp_b2110 : exp (((211 : ℝ) / 1000)^2 / 2) ≤ (102251101 : ℝ) / 100000000 := by
    have ht : ((211 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((211 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((211 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102251101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((211 : ℝ) / 1000)).trans (le_trans exp_b2110 (by norm_num))

lemma cosh_b2130_ub : cosh ((213 : ℝ) / 1000) ≤ (102294401 : ℝ) / 100000000 := by
  have exp_b2130 : exp (((213 : ℝ) / 1000)^2 / 2) ≤ (102294401 : ℝ) / 100000000 := by
    have ht : ((213 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((213 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((213 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102294401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((213 : ℝ) / 1000)).trans (le_trans exp_b2130 (by norm_num))

lemma cosh_b2150_ub : cosh ((43 : ℝ) / 200) ≤ (102338201 : ℝ) / 100000000 := by
  have exp_b2150 : exp (((43 : ℝ) / 200)^2 / 2) ≤ (102338201 : ℝ) / 100000000 := by
    have ht : ((43 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((43 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((43 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102338201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((43 : ℝ) / 200)).trans (le_trans exp_b2150 (by norm_num))

lemma cosh_b2165_ub : cosh ((433 : ℝ) / 2000) ≤ (102371301 : ℝ) / 100000000 := by
  have exp_b2165 : exp (((433 : ℝ) / 2000)^2 / 2) ≤ (102371301 : ℝ) / 100000000 := by
    have ht : ((433 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((433 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((433 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102371301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((433 : ℝ) / 2000)).trans (le_trans exp_b2165 (by norm_num))

lemma cosh_b2185_ub : cosh ((437 : ℝ) / 2000) ≤ (102415901 : ℝ) / 100000000 := by
  have exp_b2185 : exp (((437 : ℝ) / 2000)^2 / 2) ≤ (102415901 : ℝ) / 100000000 := by
    have ht : ((437 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((437 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((437 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102415901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((437 : ℝ) / 2000)).trans (le_trans exp_b2185 (by norm_num))

lemma cosh_b2200_ub : cosh ((11 : ℝ) / 50) ≤ (102449601 : ℝ) / 100000000 := by
  have exp_b2200 : exp (((11 : ℝ) / 50)^2 / 2) ≤ (102449601 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((11 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((11 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102449601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((11 : ℝ) / 50)).trans (le_trans exp_b2200 (by norm_num))

lemma cosh_b2220_ub : cosh ((111 : ℝ) / 500) ≤ (102494901 : ℝ) / 100000000 := by
  have exp_b2220 : exp (((111 : ℝ) / 500)^2 / 2) ≤ (102494901 : ℝ) / 100000000 := by
    have ht : ((111 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((111 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((111 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102494901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((111 : ℝ) / 500)).trans (le_trans exp_b2220 (by norm_num))

lemma cosh_b2240_ub : cosh ((28 : ℝ) / 125) ≤ (102540601 : ℝ) / 100000000 := by
  have exp_b2240 : exp (((28 : ℝ) / 125)^2 / 2) ≤ (102540601 : ℝ) / 100000000 := by
    have ht : ((28 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((28 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((28 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102540601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((28 : ℝ) / 125)).trans (le_trans exp_b2240 (by norm_num))

lemma cosh_b2255_ub : cosh ((451 : ℝ) / 2000) ≤ (102575201 : ℝ) / 100000000 := by
  have exp_b2255 : exp (((451 : ℝ) / 2000)^2 / 2) ≤ (102575201 : ℝ) / 100000000 := by
    have ht : ((451 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((451 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((451 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102575201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((451 : ℝ) / 2000)).trans (le_trans exp_b2255 (by norm_num))

lemma cosh_b2275_ub : cosh ((91 : ℝ) / 400) ≤ (102621601 : ℝ) / 100000000 := by
  have exp_b2275 : exp (((91 : ℝ) / 400)^2 / 2) ≤ (102621601 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((91 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((91 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102621601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((91 : ℝ) / 400)).trans (le_trans exp_b2275 (by norm_num))

lemma cosh_b2295_ub : cosh ((459 : ℝ) / 2000) ≤ (102668501 : ℝ) / 100000000 := by
  have exp_b2295 : exp (((459 : ℝ) / 2000)^2 / 2) ≤ (102668501 : ℝ) / 100000000 := by
    have ht : ((459 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((459 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((459 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102668501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((459 : ℝ) / 2000)).trans (le_trans exp_b2295 (by norm_num))

lemma cosh_b2310_ub : cosh ((231 : ℝ) / 1000) ≤ (102704001 : ℝ) / 100000000 := by
  have exp_b2310 : exp (((231 : ℝ) / 1000)^2 / 2) ≤ (102704001 : ℝ) / 100000000 := by
    have ht : ((231 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((231 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((231 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102704001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((231 : ℝ) / 1000)).trans (le_trans exp_b2310 (by norm_num))

lemma cosh_b2330_ub : cosh ((233 : ℝ) / 1000) ≤ (102751701 : ℝ) / 100000000 := by
  have exp_b2330 : exp (((233 : ℝ) / 1000)^2 / 2) ≤ (102751701 : ℝ) / 100000000 := by
    have ht : ((233 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((233 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((233 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102751701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((233 : ℝ) / 1000)).trans (le_trans exp_b2330 (by norm_num))

lemma cosh_b2350_ub : cosh ((47 : ℝ) / 200) ≤ (102799801 : ℝ) / 100000000 := by
  have exp_b2350 : exp (((47 : ℝ) / 200)^2 / 2) ≤ (102799801 : ℝ) / 100000000 := by
    have ht : ((47 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((47 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((47 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102799801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((47 : ℝ) / 200)).trans (le_trans exp_b2350 (by norm_num))

lemma cosh_b2365_ub : cosh ((473 : ℝ) / 2000) ≤ (102836101 : ℝ) / 100000000 := by
  have exp_b2365 : exp (((473 : ℝ) / 2000)^2 / 2) ≤ (102836101 : ℝ) / 100000000 := by
    have ht : ((473 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((473 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((473 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102836101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((473 : ℝ) / 2000)).trans (le_trans exp_b2365 (by norm_num))

lemma cosh_b2385_ub : cosh ((477 : ℝ) / 2000) ≤ (102885001 : ℝ) / 100000000 := by
  have exp_b2385 : exp (((477 : ℝ) / 2000)^2 / 2) ≤ (102885001 : ℝ) / 100000000 := by
    have ht : ((477 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((477 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((477 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102885001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((477 : ℝ) / 2000)).trans (le_trans exp_b2385 (by norm_num))

lemma cosh_b2400_ub : cosh ((6 : ℝ) / 25) ≤ (102921901 : ℝ) / 100000000 := by
  have exp_b2400 : exp (((6 : ℝ) / 25)^2 / 2) ≤ (102921901 : ℝ) / 100000000 := by
    have ht : ((6 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((6 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((6 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102921901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((6 : ℝ) / 25)).trans (le_trans exp_b2400 (by norm_num))

lemma cosh_b2420_ub : cosh ((121 : ℝ) / 500) ≤ (102971501 : ℝ) / 100000000 := by
  have exp_b2420 : exp (((121 : ℝ) / 500)^2 / 2) ≤ (102971501 : ℝ) / 100000000 := by
    have ht : ((121 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((121 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((121 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102971501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((121 : ℝ) / 500)).trans (le_trans exp_b2420 (by norm_num))

lemma cosh_b2440_ub : cosh ((61 : ℝ) / 250) ≤ (103021601 : ℝ) / 100000000 := by
  have exp_b2440 : exp (((61 : ℝ) / 250)^2 / 2) ≤ (103021601 : ℝ) / 100000000 := by
    have ht : ((61 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((61 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((61 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103021601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((61 : ℝ) / 250)).trans (le_trans exp_b2440 (by norm_num))

lemma cosh_b2455_ub : cosh ((491 : ℝ) / 2000) ≤ (103059401 : ℝ) / 100000000 := by
  have exp_b2455 : exp (((491 : ℝ) / 2000)^2 / 2) ≤ (103059401 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((491 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((491 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103059401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((491 : ℝ) / 2000)).trans (le_trans exp_b2455 (by norm_num))

lemma cosh_b2475_ub : cosh ((99 : ℝ) / 400) ≤ (103110201 : ℝ) / 100000000 := by
  have exp_b2475 : exp (((99 : ℝ) / 400)^2 / 2) ≤ (103110201 : ℝ) / 100000000 := by
    have ht : ((99 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((99 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((99 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103110201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((99 : ℝ) / 400)).trans (le_trans exp_b2475 (by norm_num))

lemma cosh_b2495_ub : cosh ((499 : ℝ) / 2000) ≤ (103161501 : ℝ) / 100000000 := by
  have exp_b2495 : exp (((499 : ℝ) / 2000)^2 / 2) ≤ (103161501 : ℝ) / 100000000 := by
    have ht : ((499 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((499 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((499 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103161501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((499 : ℝ) / 2000)).trans (le_trans exp_b2495 (by norm_num))

lemma cosh_b2510_ub : cosh ((251 : ℝ) / 1000) ≤ (103200201 : ℝ) / 100000000 := by
  have exp_b2510 : exp (((251 : ℝ) / 1000)^2 / 2) ≤ (103200201 : ℝ) / 100000000 := by
    have ht : ((251 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((251 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((251 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103200201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((251 : ℝ) / 1000)).trans (le_trans exp_b2510 (by norm_num))

lemma cosh_b2530_ub : cosh ((253 : ℝ) / 1000) ≤ (103252301 : ℝ) / 100000000 := by
  have exp_b2530 : exp (((253 : ℝ) / 1000)^2 / 2) ≤ (103252301 : ℝ) / 100000000 := by
    have ht : ((253 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((253 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((253 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103252301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((253 : ℝ) / 1000)).trans (le_trans exp_b2530 (by norm_num))

lemma cosh_b2550_ub : cosh ((51 : ℝ) / 200) ≤ (103304701 : ℝ) / 100000000 := by
  have exp_b2550 : exp (((51 : ℝ) / 200)^2 / 2) ≤ (103304701 : ℝ) / 100000000 := by
    have ht : ((51 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((51 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((51 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103304701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((51 : ℝ) / 200)).trans (le_trans exp_b2550 (by norm_num))

lemma cosh_b2565_ub : cosh ((513 : ℝ) / 2000) ≤ (103344401 : ℝ) / 100000000 := by
  have exp_b2565 : exp (((513 : ℝ) / 2000)^2 / 2) ≤ (103344401 : ℝ) / 100000000 := by
    have ht : ((513 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((513 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((513 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103344401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((513 : ℝ) / 2000)).trans (le_trans exp_b2565 (by norm_num))

lemma cosh_b2585_ub : cosh ((517 : ℝ) / 2000) ≤ (103397601 : ℝ) / 100000000 := by
  have exp_b2585 : exp (((517 : ℝ) / 2000)^2 / 2) ≤ (103397601 : ℝ) / 100000000 := by
    have ht : ((517 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((517 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((517 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103397601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((517 : ℝ) / 2000)).trans (le_trans exp_b2585 (by norm_num))

lemma cosh_b2600_ub : cosh ((13 : ℝ) / 50) ≤ (103437801 : ℝ) / 100000000 := by
  have exp_b2600 : exp (((13 : ℝ) / 50)^2 / 2) ≤ (103437801 : ℝ) / 100000000 := by
    have ht : ((13 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((13 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((13 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103437801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((13 : ℝ) / 50)).trans (le_trans exp_b2600 (by norm_num))

lemma cosh_b2620_ub : cosh ((131 : ℝ) / 500) ≤ (103491801 : ℝ) / 100000000 := by
  have exp_b2620 : exp (((131 : ℝ) / 500)^2 / 2) ≤ (103491801 : ℝ) / 100000000 := by
    have ht : ((131 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((131 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((131 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103491801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((131 : ℝ) / 500)).trans (le_trans exp_b2620 (by norm_num))

lemma cosh_b2640_ub : cosh ((33 : ℝ) / 125) ≤ (103546301 : ℝ) / 100000000 := by
  have exp_b2640 : exp (((33 : ℝ) / 125)^2 / 2) ≤ (103546301 : ℝ) / 100000000 := by
    have ht : ((33 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((33 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((33 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103546301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((33 : ℝ) / 125)).trans (le_trans exp_b2640 (by norm_num))

lemma cosh_b2655_ub : cosh ((531 : ℝ) / 2000) ≤ (103587401 : ℝ) / 100000000 := by
  have exp_b2655 : exp (((531 : ℝ) / 2000)^2 / 2) ≤ (103587401 : ℝ) / 100000000 := by
    have ht : ((531 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((531 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((531 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103587401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((531 : ℝ) / 2000)).trans (le_trans exp_b2655 (by norm_num))

lemma cosh_b2675_ub : cosh ((107 : ℝ) / 400) ≤ (103642601 : ℝ) / 100000000 := by
  have exp_b2675 : exp (((107 : ℝ) / 400)^2 / 2) ≤ (103642601 : ℝ) / 100000000 := by
    have ht : ((107 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((107 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((107 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103642601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((107 : ℝ) / 400)).trans (le_trans exp_b2675 (by norm_num))

lemma cosh_b2695_ub : cosh ((539 : ℝ) / 2000) ≤ (103698301 : ℝ) / 100000000 := by
  have exp_b2695 : exp (((539 : ℝ) / 2000)^2 / 2) ≤ (103698301 : ℝ) / 100000000 := by
    have ht : ((539 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((539 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((539 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103698301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((539 : ℝ) / 2000)).trans (le_trans exp_b2695 (by norm_num))

lemma cosh_b2710_ub : cosh ((271 : ℝ) / 1000) ≤ (103740401 : ℝ) / 100000000 := by
  have exp_b2710 : exp (((271 : ℝ) / 1000)^2 / 2) ≤ (103740401 : ℝ) / 100000000 := by
    have ht : ((271 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((271 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((271 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103740401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((271 : ℝ) / 1000)).trans (le_trans exp_b2710 (by norm_num))

lemma cosh_b2730_ub : cosh ((273 : ℝ) / 1000) ≤ (103796801 : ℝ) / 100000000 := by
  have exp_b2730 : exp (((273 : ℝ) / 1000)^2 / 2) ≤ (103796801 : ℝ) / 100000000 := by
    have ht : ((273 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((273 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((273 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103796801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((273 : ℝ) / 1000)).trans (le_trans exp_b2730 (by norm_num))

lemma cosh_b2750_ub : cosh ((11 : ℝ) / 40) ≤ (103853701 : ℝ) / 100000000 := by
  have exp_b2750 : exp (((11 : ℝ) / 40)^2 / 2) ≤ (103853701 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 40)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((11 : ℝ) / 40)^2 / 2) ^ m / (Nat.factorial m)) +
          (((11 : ℝ) / 40)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103853701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((11 : ℝ) / 40)).trans (le_trans exp_b2750 (by norm_num))

lemma cosh_b2765_ub : cosh ((553 : ℝ) / 2000) ≤ (103896701 : ℝ) / 100000000 := by
  have exp_b2765 : exp (((553 : ℝ) / 2000)^2 / 2) ≤ (103896701 : ℝ) / 100000000 := by
    have ht : ((553 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((553 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((553 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103896701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((553 : ℝ) / 2000)).trans (le_trans exp_b2765 (by norm_num))

lemma cosh_b2785_ub : cosh ((557 : ℝ) / 2000) ≤ (103954301 : ℝ) / 100000000 := by
  have exp_b2785 : exp (((557 : ℝ) / 2000)^2 / 2) ≤ (103954301 : ℝ) / 100000000 := by
    have ht : ((557 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((557 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((557 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103954301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((557 : ℝ) / 2000)).trans (le_trans exp_b2785 (by norm_num))

lemma cosh_b2800_ub : cosh ((7 : ℝ) / 25) ≤ (103997901 : ℝ) / 100000000 := by
  have exp_b2800 : exp (((7 : ℝ) / 25)^2 / 2) ≤ (103997901 : ℝ) / 100000000 := by
    have ht : ((7 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((7 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((7 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103997901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((7 : ℝ) / 25)).trans (le_trans exp_b2800 (by norm_num))

lemma cosh_b2820_ub : cosh ((141 : ℝ) / 500) ≤ (104056401 : ℝ) / 100000000 := by
  have exp_b2820 : exp (((141 : ℝ) / 500)^2 / 2) ≤ (104056401 : ℝ) / 100000000 := by
    have ht : ((141 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((141 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((141 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104056401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((141 : ℝ) / 500)).trans (le_trans exp_b2820 (by norm_num))

lemma cosh_b2840_ub : cosh ((71 : ℝ) / 250) ≤ (104115301 : ℝ) / 100000000 := by
  have exp_b2840 : exp (((71 : ℝ) / 250)^2 / 2) ≤ (104115301 : ℝ) / 100000000 := by
    have ht : ((71 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((71 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((71 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104115301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((71 : ℝ) / 250)).trans (le_trans exp_b2840 (by norm_num))

lemma cosh_b2855_ub : cosh ((571 : ℝ) / 2000) ≤ (104159801 : ℝ) / 100000000 := by
  have exp_b2855 : exp (((571 : ℝ) / 2000)^2 / 2) ≤ (104159801 : ℝ) / 100000000 := by
    have ht : ((571 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((571 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((571 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104159801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((571 : ℝ) / 2000)).trans (le_trans exp_b2855 (by norm_num))

lemma cosh_b2875_ub : cosh ((23 : ℝ) / 80) ≤ (104219501 : ℝ) / 100000000 := by
  have exp_b2875 : exp (((23 : ℝ) / 80)^2 / 2) ≤ (104219501 : ℝ) / 100000000 := by
    have ht : ((23 : ℝ) / 80)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((23 : ℝ) / 80)^2 / 2) ^ m / (Nat.factorial m)) +
          (((23 : ℝ) / 80)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104219501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((23 : ℝ) / 80)).trans (le_trans exp_b2875 (by norm_num))

lemma cosh_b2895_ub : cosh ((579 : ℝ) / 2000) ≤ (104279601 : ℝ) / 100000000 := by
  have exp_b2895 : exp (((579 : ℝ) / 2000)^2 / 2) ≤ (104279601 : ℝ) / 100000000 := by
    have ht : ((579 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((579 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((579 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104279601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((579 : ℝ) / 2000)).trans (le_trans exp_b2895 (by norm_num))

lemma cosh_b2910_ub : cosh ((291 : ℝ) / 1000) ≤ (104325001 : ℝ) / 100000000 := by
  have exp_b2910 : exp (((291 : ℝ) / 1000)^2 / 2) ≤ (104325001 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((291 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((291 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104325001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((291 : ℝ) / 1000)).trans (le_trans exp_b2910 (by norm_num))

lemma cosh_b2930_ub : cosh ((293 : ℝ) / 1000) ≤ (104386001 : ℝ) / 100000000 := by
  have exp_b2930 : exp (((293 : ℝ) / 1000)^2 / 2) ≤ (104386001 : ℝ) / 100000000 := by
    have ht : ((293 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((293 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((293 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104386001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((293 : ℝ) / 1000)).trans (le_trans exp_b2930 (by norm_num))

lemma cosh_b2950_ub : cosh ((59 : ℝ) / 200) ≤ (104447401 : ℝ) / 100000000 := by
  have exp_b2950 : exp (((59 : ℝ) / 200)^2 / 2) ≤ (104447401 : ℝ) / 100000000 := by
    have ht : ((59 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((59 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((59 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104447401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((59 : ℝ) / 200)).trans (le_trans exp_b2950 (by norm_num))

lemma cosh_b2965_ub : cosh ((593 : ℝ) / 2000) ≤ (104493701 : ℝ) / 100000000 := by
  have exp_b2965 : exp (((593 : ℝ) / 2000)^2 / 2) ≤ (104493701 : ℝ) / 100000000 := by
    have ht : ((593 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((593 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((593 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104493701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((593 : ℝ) / 2000)).trans (le_trans exp_b2965 (by norm_num))

lemma cosh_b2985_ub : cosh ((597 : ℝ) / 2000) ≤ (104555901 : ℝ) / 100000000 := by
  have exp_b2985 : exp (((597 : ℝ) / 2000)^2 / 2) ≤ (104555901 : ℝ) / 100000000 := by
    have ht : ((597 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((597 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((597 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104555901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((597 : ℝ) / 2000)).trans (le_trans exp_b2985 (by norm_num))

lemma cosh_b3000_ub : cosh ((3 : ℝ) / 10) ≤ (104602801 : ℝ) / 100000000 := by
  have exp_b3000 : exp (((3 : ℝ) / 10)^2 / 2) ≤ (104602801 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 10)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((3 : ℝ) / 10)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 10)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104602801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 10)).trans (le_trans exp_b3000 (by norm_num))

lemma cosh_b3020_ub : cosh ((151 : ℝ) / 500) ≤ (104665801 : ℝ) / 100000000 := by
  have exp_b3020 : exp (((151 : ℝ) / 500)^2 / 2) ≤ (104665801 : ℝ) / 100000000 := by
    have ht : ((151 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((151 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((151 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104665801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((151 : ℝ) / 500)).trans (le_trans exp_b3020 (by norm_num))

lemma cosh_b3040_ub : cosh ((38 : ℝ) / 125) ≤ (104729301 : ℝ) / 100000000 := by
  have exp_b3040 : exp (((38 : ℝ) / 125)^2 / 2) ≤ (104729301 : ℝ) / 100000000 := by
    have ht : ((38 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((38 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((38 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104729301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((38 : ℝ) / 125)).trans (le_trans exp_b3040 (by norm_num))

lemma cosh_b3055_ub : cosh ((611 : ℝ) / 2000) ≤ (104777201 : ℝ) / 100000000 := by
  have exp_b3055 : exp (((611 : ℝ) / 2000)^2 / 2) ≤ (104777201 : ℝ) / 100000000 := by
    have ht : ((611 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((611 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((611 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104777201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((611 : ℝ) / 2000)).trans (le_trans exp_b3055 (by norm_num))

lemma cosh_b3075_ub : cosh ((123 : ℝ) / 400) ≤ (104841401 : ℝ) / 100000000 := by
  have exp_b3075 : exp (((123 : ℝ) / 400)^2 / 2) ≤ (104841401 : ℝ) / 100000000 := by
    have ht : ((123 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((123 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((123 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104841401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((123 : ℝ) / 400)).trans (le_trans exp_b3075 (by norm_num))

lemma cosh_b3095_ub : cosh ((619 : ℝ) / 2000) ≤ (104906101 : ℝ) / 100000000 := by
  have exp_b3095 : exp (((619 : ℝ) / 2000)^2 / 2) ≤ (104906101 : ℝ) / 100000000 := by
    have ht : ((619 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((619 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((619 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104906101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((619 : ℝ) / 2000)).trans (le_trans exp_b3095 (by norm_num))

lemma cosh_b3110_ub : cosh ((311 : ℝ) / 1000) ≤ (104954901 : ℝ) / 100000000 := by
  have exp_b3110 : exp (((311 : ℝ) / 1000)^2 / 2) ≤ (104954901 : ℝ) / 100000000 := by
    have ht : ((311 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((311 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((311 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104954901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((311 : ℝ) / 1000)).trans (le_trans exp_b3110 (by norm_num))

lemma cosh_b3130_ub : cosh ((313 : ℝ) / 1000) ≤ (105020501 : ℝ) / 100000000 := by
  have exp_b3130 : exp (((313 : ℝ) / 1000)^2 / 2) ≤ (105020501 : ℝ) / 100000000 := by
    have ht : ((313 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((313 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((313 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105020501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((313 : ℝ) / 1000)).trans (le_trans exp_b3130 (by norm_num))

lemma cosh_b3150_ub : cosh ((63 : ℝ) / 200) ≤ (105086401 : ℝ) / 100000000 := by
  have exp_b3150 : exp (((63 : ℝ) / 200)^2 / 2) ≤ (105086401 : ℝ) / 100000000 := by
    have ht : ((63 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((63 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((63 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105086401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((63 : ℝ) / 200)).trans (le_trans exp_b3150 (by norm_num))

lemma cosh_b3165_ub : cosh ((633 : ℝ) / 2000) ≤ (105136201 : ℝ) / 100000000 := by
  have exp_b3165 : exp (((633 : ℝ) / 2000)^2 / 2) ≤ (105136201 : ℝ) / 100000000 := by
    have ht : ((633 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((633 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((633 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105136201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((633 : ℝ) / 2000)).trans (le_trans exp_b3165 (by norm_num))

lemma cosh_b3185_ub : cosh ((637 : ℝ) / 2000) ≤ (105203001 : ℝ) / 100000000 := by
  have exp_b3185 : exp (((637 : ℝ) / 2000)^2 / 2) ≤ (105203001 : ℝ) / 100000000 := by
    have ht : ((637 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((637 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((637 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105203001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((637 : ℝ) / 2000)).trans (le_trans exp_b3185 (by norm_num))

lemma cosh_b3200_ub : cosh ((8 : ℝ) / 25) ≤ (105253401 : ℝ) / 100000000 := by
  have exp_b3200 : exp (((8 : ℝ) / 25)^2 / 2) ≤ (105253401 : ℝ) / 100000000 := by
    have ht : ((8 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((8 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((8 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105253401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((8 : ℝ) / 25)).trans (le_trans exp_b3200 (by norm_num))

lemma cosh_b3220_ub : cosh ((161 : ℝ) / 500) ≤ (105321001 : ℝ) / 100000000 := by
  have exp_b3220 : exp (((161 : ℝ) / 500)^2 / 2) ≤ (105321001 : ℝ) / 100000000 := by
    have ht : ((161 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((161 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((161 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105321001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((161 : ℝ) / 500)).trans (le_trans exp_b3220 (by norm_num))

lemma cosh_b3240_ub : cosh ((81 : ℝ) / 250) ≤ (105389001 : ℝ) / 100000000 := by
  have exp_b3240 : exp (((81 : ℝ) / 250)^2 / 2) ≤ (105389001 : ℝ) / 100000000 := by
    have ht : ((81 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((81 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((81 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105389001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((81 : ℝ) / 250)).trans (le_trans exp_b3240 (by norm_num))

lemma cosh_b3255_ub : cosh ((651 : ℝ) / 2000) ≤ (105440401 : ℝ) / 100000000 := by
  have exp_b3255 : exp (((651 : ℝ) / 2000)^2 / 2) ≤ (105440401 : ℝ) / 100000000 := by
    have ht : ((651 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((651 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((651 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105440401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((651 : ℝ) / 2000)).trans (le_trans exp_b3255 (by norm_num))

lemma cosh_b3275_ub : cosh ((131 : ℝ) / 400) ≤ (105509301 : ℝ) / 100000000 := by
  have exp_b3275 : exp (((131 : ℝ) / 400)^2 / 2) ≤ (105509301 : ℝ) / 100000000 := by
    have ht : ((131 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((131 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((131 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105509301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((131 : ℝ) / 400)).trans (le_trans exp_b3275 (by norm_num))

lemma cosh_b3295_ub : cosh ((659 : ℝ) / 2000) ≤ (105578601 : ℝ) / 100000000 := by
  have exp_b3295 : exp (((659 : ℝ) / 2000)^2 / 2) ≤ (105578601 : ℝ) / 100000000 := by
    have ht : ((659 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((659 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((659 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105578601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((659 : ℝ) / 2000)).trans (le_trans exp_b3295 (by norm_num))

lemma cosh_b3310_ub : cosh ((331 : ℝ) / 1000) ≤ (105630901 : ℝ) / 100000000 := by
  have exp_b3310 : exp (((331 : ℝ) / 1000)^2 / 2) ≤ (105630901 : ℝ) / 100000000 := by
    have ht : ((331 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((331 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((331 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105630901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((331 : ℝ) / 1000)).trans (le_trans exp_b3310 (by norm_num))

lemma cosh_b3330_ub : cosh ((333 : ℝ) / 1000) ≤ (105701101 : ℝ) / 100000000 := by
  have exp_b3330 : exp (((333 : ℝ) / 1000)^2 / 2) ≤ (105701101 : ℝ) / 100000000 := by
    have ht : ((333 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((333 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((333 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105701101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((333 : ℝ) / 1000)).trans (le_trans exp_b3330 (by norm_num))

lemma cosh_b3350_ub : cosh ((67 : ℝ) / 200) ≤ (105771701 : ℝ) / 100000000 := by
  have exp_b3350 : exp (((67 : ℝ) / 200)^2 / 2) ≤ (105771701 : ℝ) / 100000000 := by
    have ht : ((67 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((67 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((67 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105771701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((67 : ℝ) / 200)).trans (le_trans exp_b3350 (by norm_num))

lemma cosh_b3365_ub : cosh ((673 : ℝ) / 2000) ≤ (105825001 : ℝ) / 100000000 := by
  have exp_b3365 : exp (((673 : ℝ) / 2000)^2 / 2) ≤ (105825001 : ℝ) / 100000000 := by
    have ht : ((673 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((673 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((673 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105825001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((673 : ℝ) / 2000)).trans (le_trans exp_b3365 (by norm_num))

lemma cosh_b3385_ub : cosh ((677 : ℝ) / 2000) ≤ (105896501 : ℝ) / 100000000 := by
  have exp_b3385 : exp (((677 : ℝ) / 2000)^2 / 2) ≤ (105896501 : ℝ) / 100000000 := by
    have ht : ((677 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((677 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((677 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105896501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((677 : ℝ) / 2000)).trans (le_trans exp_b3385 (by norm_num))

lemma cosh_b3400_ub : cosh ((17 : ℝ) / 50) ≤ (105950401 : ℝ) / 100000000 := by
  have exp_b3400 : exp (((17 : ℝ) / 50)^2 / 2) ≤ (105950401 : ℝ) / 100000000 := by
    have ht : ((17 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((17 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((17 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105950401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((17 : ℝ) / 50)).trans (le_trans exp_b3400 (by norm_num))

lemma cosh_b3420_ub : cosh ((171 : ℝ) / 500) ≤ (106022601 : ℝ) / 100000000 := by
  have exp_b3420 : exp (((171 : ℝ) / 500)^2 / 2) ≤ (106022601 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((171 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((171 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106022601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((171 : ℝ) / 500)).trans (le_trans exp_b3420 (by norm_num))

lemma cosh_b3440_ub : cosh ((43 : ℝ) / 125) ≤ (106095401 : ℝ) / 100000000 := by
  have exp_b3440 : exp (((43 : ℝ) / 125)^2 / 2) ≤ (106095401 : ℝ) / 100000000 := by
    have ht : ((43 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((43 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((43 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106095401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((43 : ℝ) / 125)).trans (le_trans exp_b3440 (by norm_num))

lemma cosh_b3455_ub : cosh ((691 : ℝ) / 2000) ≤ (106150301 : ℝ) / 100000000 := by
  have exp_b3455 : exp (((691 : ℝ) / 2000)^2 / 2) ≤ (106150301 : ℝ) / 100000000 := by
    have ht : ((691 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((691 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((691 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106150301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((691 : ℝ) / 2000)).trans (le_trans exp_b3455 (by norm_num))

lemma cosh_b3475_ub : cosh ((139 : ℝ) / 400) ≤ (106223901 : ℝ) / 100000000 := by
  have exp_b3475 : exp (((139 : ℝ) / 400)^2 / 2) ≤ (106223901 : ℝ) / 100000000 := by
    have ht : ((139 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((139 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((139 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106223901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((139 : ℝ) / 400)).trans (le_trans exp_b3475 (by norm_num))

lemma cosh_b3495_ub : cosh ((699 : ℝ) / 2000) ≤ (106297901 : ℝ) / 100000000 := by
  have exp_b3495 : exp (((699 : ℝ) / 2000)^2 / 2) ≤ (106297901 : ℝ) / 100000000 := by
    have ht : ((699 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((699 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((699 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106297901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((699 : ℝ) / 2000)).trans (le_trans exp_b3495 (by norm_num))

lemma cosh_b3510_ub : cosh ((351 : ℝ) / 1000) ≤ (106353801 : ℝ) / 100000000 := by
  have exp_b3510 : exp (((351 : ℝ) / 1000)^2 / 2) ≤ (106353801 : ℝ) / 100000000 := by
    have ht : ((351 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((351 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((351 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106353801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((351 : ℝ) / 1000)).trans (le_trans exp_b3510 (by norm_num))

lemma cosh_b3530_ub : cosh ((353 : ℝ) / 1000) ≤ (106428701 : ℝ) / 100000000 := by
  have exp_b3530 : exp (((353 : ℝ) / 1000)^2 / 2) ≤ (106428701 : ℝ) / 100000000 := by
    have ht : ((353 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((353 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((353 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106428701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((353 : ℝ) / 1000)).trans (le_trans exp_b3530 (by norm_num))

lemma cosh_b3550_ub : cosh ((71 : ℝ) / 200) ≤ (106504101 : ℝ) / 100000000 := by
  have exp_b3550 : exp (((71 : ℝ) / 200)^2 / 2) ≤ (106504101 : ℝ) / 100000000 := by
    have ht : ((71 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((71 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((71 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106504101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((71 : ℝ) / 200)).trans (le_trans exp_b3550 (by norm_num))

lemma cosh_b3565_ub : cosh ((713 : ℝ) / 2000) ≤ (106560901 : ℝ) / 100000000 := by
  have exp_b3565 : exp (((713 : ℝ) / 2000)^2 / 2) ≤ (106560901 : ℝ) / 100000000 := by
    have ht : ((713 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((713 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((713 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106560901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((713 : ℝ) / 2000)).trans (le_trans exp_b3565 (by norm_num))

lemma cosh_b3585_ub : cosh ((717 : ℝ) / 2000) ≤ (106637101 : ℝ) / 100000000 := by
  have exp_b3585 : exp (((717 : ℝ) / 2000)^2 / 2) ≤ (106637101 : ℝ) / 100000000 := by
    have ht : ((717 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((717 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((717 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106637101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((717 : ℝ) / 2000)).trans (le_trans exp_b3585 (by norm_num))

lemma cosh_b3600_ub : cosh ((9 : ℝ) / 25) ≤ (106694601 : ℝ) / 100000000 := by
  have exp_b3600 : exp (((9 : ℝ) / 25)^2 / 2) ≤ (106694601 : ℝ) / 100000000 := by
    have ht : ((9 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((9 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((9 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106694601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((9 : ℝ) / 25)).trans (le_trans exp_b3600 (by norm_num))

lemma cosh_b3620_ub : cosh ((181 : ℝ) / 500) ≤ (106771701 : ℝ) / 100000000 := by
  have exp_b3620 : exp (((181 : ℝ) / 500)^2 / 2) ≤ (106771701 : ℝ) / 100000000 := by
    have ht : ((181 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((181 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((181 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106771701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((181 : ℝ) / 500)).trans (le_trans exp_b3620 (by norm_num))

lemma cosh_b3640_ub : cosh ((91 : ℝ) / 250) ≤ (106849201 : ℝ) / 100000000 := by
  have exp_b3640 : exp (((91 : ℝ) / 250)^2 / 2) ≤ (106849201 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((91 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((91 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106849201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((91 : ℝ) / 250)).trans (le_trans exp_b3640 (by norm_num))

lemma cosh_b3655_ub : cosh ((731 : ℝ) / 2000) ≤ (106907701 : ℝ) / 100000000 := by
  have exp_b3655 : exp (((731 : ℝ) / 2000)^2 / 2) ≤ (106907701 : ℝ) / 100000000 := by
    have ht : ((731 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((731 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((731 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106907701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((731 : ℝ) / 2000)).trans (le_trans exp_b3655 (by norm_num))

lemma cosh_b3675_ub : cosh ((147 : ℝ) / 400) ≤ (106986101 : ℝ) / 100000000 := by
  have exp_b3675 : exp (((147 : ℝ) / 400)^2 / 2) ≤ (106986101 : ℝ) / 100000000 := by
    have ht : ((147 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((147 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((147 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106986101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((147 : ℝ) / 400)).trans (le_trans exp_b3675 (by norm_num))

lemma cosh_b3695_ub : cosh ((739 : ℝ) / 2000) ≤ (107065001 : ℝ) / 100000000 := by
  have exp_b3695 : exp (((739 : ℝ) / 2000)^2 / 2) ≤ (107065001 : ℝ) / 100000000 := by
    have ht : ((739 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((739 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((739 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107065001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((739 : ℝ) / 2000)).trans (le_trans exp_b3695 (by norm_num))

lemma cosh_b3710_ub : cosh ((371 : ℝ) / 1000) ≤ (107124401 : ℝ) / 100000000 := by
  have exp_b3710 : exp (((371 : ℝ) / 1000)^2 / 2) ≤ (107124401 : ℝ) / 100000000 := by
    have ht : ((371 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((371 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((371 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107124401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((371 : ℝ) / 1000)).trans (le_trans exp_b3710 (by norm_num))

lemma cosh_b3730_ub : cosh ((373 : ℝ) / 1000) ≤ (107204201 : ℝ) / 100000000 := by
  have exp_b3730 : exp (((373 : ℝ) / 1000)^2 / 2) ≤ (107204201 : ℝ) / 100000000 := by
    have ht : ((373 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((373 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((373 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107204201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((373 : ℝ) / 1000)).trans (le_trans exp_b3730 (by norm_num))

lemma cosh_b3750_ub : cosh ((3 : ℝ) / 8) ≤ (107284401 : ℝ) / 100000000 := by
  have exp_b3750 : exp (((3 : ℝ) / 8)^2 / 2) ≤ (107284401 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 8)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((3 : ℝ) / 8)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 8)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107284401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 8)).trans (le_trans exp_b3750 (by norm_num))

lemma cosh_b3765_ub : cosh ((753 : ℝ) / 2000) ≤ (107344901 : ℝ) / 100000000 := by
  have exp_b3765 : exp (((753 : ℝ) / 2000)^2 / 2) ≤ (107344901 : ℝ) / 100000000 := by
    have ht : ((753 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((753 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((753 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107344901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((753 : ℝ) / 2000)).trans (le_trans exp_b3765 (by norm_num))

lemma cosh_b3785_ub : cosh ((757 : ℝ) / 2000) ≤ (107426001 : ℝ) / 100000000 := by
  have exp_b3785 : exp (((757 : ℝ) / 2000)^2 / 2) ≤ (107426001 : ℝ) / 100000000 := by
    have ht : ((757 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((757 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((757 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107426001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((757 : ℝ) / 2000)).trans (le_trans exp_b3785 (by norm_num))

lemma cosh_b3800_ub : cosh ((19 : ℝ) / 50) ≤ (107487101 : ℝ) / 100000000 := by
  have exp_b3800 : exp (((19 : ℝ) / 50)^2 / 2) ≤ (107487101 : ℝ) / 100000000 := by
    have ht : ((19 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((19 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((19 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107487101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((19 : ℝ) / 50)).trans (le_trans exp_b3800 (by norm_num))

lemma cosh_b3820_ub : cosh ((191 : ℝ) / 500) ≤ (107569001 : ℝ) / 100000000 := by
  have exp_b3820 : exp (((191 : ℝ) / 500)^2 / 2) ≤ (107569001 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((191 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((191 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107569001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((191 : ℝ) / 500)).trans (le_trans exp_b3820 (by norm_num))

lemma cosh_b3840_ub : cosh ((48 : ℝ) / 125) ≤ (107651401 : ℝ) / 100000000 := by
  have exp_b3840 : exp (((48 : ℝ) / 125)^2 / 2) ≤ (107651401 : ℝ) / 100000000 := by
    have ht : ((48 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((48 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((48 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107651401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((48 : ℝ) / 125)).trans (le_trans exp_b3840 (by norm_num))

lemma cosh_b3855_ub : cosh ((771 : ℝ) / 2000) ≤ (107713601 : ℝ) / 100000000 := by
  have exp_b3855 : exp (((771 : ℝ) / 2000)^2 / 2) ≤ (107713601 : ℝ) / 100000000 := by
    have ht : ((771 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((771 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((771 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107713601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((771 : ℝ) / 2000)).trans (le_trans exp_b3855 (by norm_num))

lemma cosh_b3875_ub : cosh ((31 : ℝ) / 80) ≤ (107796901 : ℝ) / 100000000 := by
  have exp_b3875 : exp (((31 : ℝ) / 80)^2 / 2) ≤ (107796901 : ℝ) / 100000000 := by
    have ht : ((31 : ℝ) / 80)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((31 : ℝ) / 80)^2 / 2) ^ m / (Nat.factorial m)) +
          (((31 : ℝ) / 80)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107796901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((31 : ℝ) / 80)).trans (le_trans exp_b3875 (by norm_num))

lemma cosh_b3895_ub : cosh ((779 : ℝ) / 2000) ≤ (107880701 : ℝ) / 100000000 := by
  have exp_b3895 : exp (((779 : ℝ) / 2000)^2 / 2) ≤ (107880701 : ℝ) / 100000000 := by
    have ht : ((779 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((779 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((779 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107880701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((779 : ℝ) / 2000)).trans (le_trans exp_b3895 (by norm_num))

lemma cosh_b3910_ub : cosh ((391 : ℝ) / 1000) ≤ (107943801 : ℝ) / 100000000 := by
  have exp_b3910 : exp (((391 : ℝ) / 1000)^2 / 2) ≤ (107943801 : ℝ) / 100000000 := by
    have ht : ((391 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((391 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((391 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107943801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((391 : ℝ) / 1000)).trans (le_trans exp_b3910 (by norm_num))

lemma cosh_b3930_ub : cosh ((393 : ℝ) / 1000) ≤ (108028501 : ℝ) / 100000000 := by
  have exp_b3930 : exp (((393 : ℝ) / 1000)^2 / 2) ≤ (108028501 : ℝ) / 100000000 := by
    have ht : ((393 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((393 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((393 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108028501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((393 : ℝ) / 1000)).trans (le_trans exp_b3930 (by norm_num))

lemma cosh_b3950_ub : cosh ((79 : ℝ) / 200) ≤ (108113701 : ℝ) / 100000000 := by
  have exp_b3950 : exp (((79 : ℝ) / 200)^2 / 2) ≤ (108113701 : ℝ) / 100000000 := by
    have ht : ((79 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((79 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((79 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108113701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((79 : ℝ) / 200)).trans (le_trans exp_b3950 (by norm_num))

lemma cosh_b3965_ub : cosh ((793 : ℝ) / 2000) ≤ (108177901 : ℝ) / 100000000 := by
  have exp_b3965 : exp (((793 : ℝ) / 2000)^2 / 2) ≤ (108177901 : ℝ) / 100000000 := by
    have ht : ((793 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((793 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((793 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108177901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((793 : ℝ) / 2000)).trans (le_trans exp_b3965 (by norm_num))

lemma cosh_b3985_ub : cosh ((797 : ℝ) / 2000) ≤ (108263901 : ℝ) / 100000000 := by
  have exp_b3985 : exp (((797 : ℝ) / 2000)^2 / 2) ≤ (108263901 : ℝ) / 100000000 := by
    have ht : ((797 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((797 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((797 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108263901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((797 : ℝ) / 2000)).trans (le_trans exp_b3985 (by norm_num))

lemma cosh_b4000_ub : cosh ((2 : ℝ) / 5) ≤ (108328801 : ℝ) / 100000000 := by
  have exp_b4000 : exp (((2 : ℝ) / 5)^2 / 2) ≤ (108328801 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 5)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2 : ℝ) / 5)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 5)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108328801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 5)).trans (le_trans exp_b4000 (by norm_num))

lemma cosh_b4020_ub : cosh ((201 : ℝ) / 500) ≤ (108415701 : ℝ) / 100000000 := by
  have exp_b4020 : exp (((201 : ℝ) / 500)^2 / 2) ≤ (108415701 : ℝ) / 100000000 := by
    have ht : ((201 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((201 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((201 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108415701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((201 : ℝ) / 500)).trans (le_trans exp_b4020 (by norm_num))

lemma cosh_b4040_ub : cosh ((101 : ℝ) / 250) ≤ (108503101 : ℝ) / 100000000 := by
  have exp_b4040 : exp (((101 : ℝ) / 250)^2 / 2) ≤ (108503101 : ℝ) / 100000000 := by
    have ht : ((101 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((101 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((101 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108503101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((101 : ℝ) / 250)).trans (le_trans exp_b4040 (by norm_num))

lemma cosh_b4055_ub : cosh ((811 : ℝ) / 2000) ≤ (108569001 : ℝ) / 100000000 := by
  have exp_b4055 : exp (((811 : ℝ) / 2000)^2 / 2) ≤ (108569001 : ℝ) / 100000000 := by
    have ht : ((811 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((811 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((811 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108569001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((811 : ℝ) / 2000)).trans (le_trans exp_b4055 (by norm_num))

lemma cosh_b4075_ub : cosh ((163 : ℝ) / 400) ≤ (108657301 : ℝ) / 100000000 := by
  have exp_b4075 : exp (((163 : ℝ) / 400)^2 / 2) ≤ (108657301 : ℝ) / 100000000 := by
    have ht : ((163 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((163 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((163 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108657301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((163 : ℝ) / 400)).trans (le_trans exp_b4075 (by norm_num))

lemma cosh_b4095_ub : cosh ((819 : ℝ) / 2000) ≤ (108746101 : ℝ) / 100000000 := by
  have exp_b4095 : exp (((819 : ℝ) / 2000)^2 / 2) ≤ (108746101 : ℝ) / 100000000 := by
    have ht : ((819 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((819 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((819 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108746101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((819 : ℝ) / 2000)).trans (le_trans exp_b4095 (by norm_num))

lemma cosh_b4110_ub : cosh ((411 : ℝ) / 1000) ≤ (108813001 : ℝ) / 100000000 := by
  have exp_b4110 : exp (((411 : ℝ) / 1000)^2 / 2) ≤ (108813001 : ℝ) / 100000000 := by
    have ht : ((411 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((411 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((411 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108813001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((411 : ℝ) / 1000)).trans (le_trans exp_b4110 (by norm_num))

lemma cosh_b4130_ub : cosh ((413 : ℝ) / 1000) ≤ (108902701 : ℝ) / 100000000 := by
  have exp_b4130 : exp (((413 : ℝ) / 1000)^2 / 2) ≤ (108902701 : ℝ) / 100000000 := by
    have ht : ((413 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((413 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((413 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108902701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((413 : ℝ) / 1000)).trans (le_trans exp_b4130 (by norm_num))

lemma cosh_b4150_ub : cosh ((83 : ℝ) / 200) ≤ (108992901 : ℝ) / 100000000 := by
  have exp_b4150 : exp (((83 : ℝ) / 200)^2 / 2) ≤ (108992901 : ℝ) / 100000000 := by
    have ht : ((83 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((83 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((83 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108992901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((83 : ℝ) / 200)).trans (le_trans exp_b4150 (by norm_num))

lemma cosh_b4165_ub : cosh ((833 : ℝ) / 2000) ≤ (109060901 : ℝ) / 100000000 := by
  have exp_b4165 : exp (((833 : ℝ) / 2000)^2 / 2) ≤ (109060901 : ℝ) / 100000000 := by
    have ht : ((833 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((833 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((833 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109060901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((833 : ℝ) / 2000)).trans (le_trans exp_b4165 (by norm_num))

lemma cosh_b4185_ub : cosh ((837 : ℝ) / 2000) ≤ (109152001 : ℝ) / 100000000 := by
  have exp_b4185 : exp (((837 : ℝ) / 2000)^2 / 2) ≤ (109152001 : ℝ) / 100000000 := by
    have ht : ((837 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((837 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((837 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109152001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((837 : ℝ) / 2000)).trans (le_trans exp_b4185 (by norm_num))

lemma cosh_b4200_ub : cosh ((21 : ℝ) / 50) ≤ (109220701 : ℝ) / 100000000 := by
  have exp_b4200 : exp (((21 : ℝ) / 50)^2 / 2) ≤ (109220701 : ℝ) / 100000000 := by
    have ht : ((21 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((21 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((21 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109220701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((21 : ℝ) / 50)).trans (le_trans exp_b4200 (by norm_num))

lemma cosh_b4220_ub : cosh ((211 : ℝ) / 500) ≤ (109312701 : ℝ) / 100000000 := by
  have exp_b4220 : exp (((211 : ℝ) / 500)^2 / 2) ≤ (109312701 : ℝ) / 100000000 := by
    have ht : ((211 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((211 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((211 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109312701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((211 : ℝ) / 500)).trans (le_trans exp_b4220 (by norm_num))

lemma cosh_b4240_ub : cosh ((53 : ℝ) / 125) ≤ (109405201 : ℝ) / 100000000 := by
  have exp_b4240 : exp (((53 : ℝ) / 125)^2 / 2) ≤ (109405201 : ℝ) / 100000000 := by
    have ht : ((53 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((53 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((53 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109405201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((53 : ℝ) / 125)).trans (le_trans exp_b4240 (by norm_num))

lemma cosh_b4255_ub : cosh ((851 : ℝ) / 2000) ≤ (109475001 : ℝ) / 100000000 := by
  have exp_b4255 : exp (((851 : ℝ) / 2000)^2 / 2) ≤ (109475001 : ℝ) / 100000000 := by
    have ht : ((851 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((851 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((851 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109475001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((851 : ℝ) / 2000)).trans (le_trans exp_b4255 (by norm_num))

lemma cosh_b4275_ub : cosh ((171 : ℝ) / 400) ≤ (109568401 : ℝ) / 100000000 := by
  have exp_b4275 : exp (((171 : ℝ) / 400)^2 / 2) ≤ (109568401 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((171 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((171 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109568401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((171 : ℝ) / 400)).trans (le_trans exp_b4275 (by norm_num))

lemma cosh_b4295_ub : cosh ((859 : ℝ) / 2000) ≤ (109662301 : ℝ) / 100000000 := by
  have exp_b4295 : exp (((859 : ℝ) / 2000)^2 / 2) ≤ (109662301 : ℝ) / 100000000 := by
    have ht : ((859 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((859 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((859 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109662301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((859 : ℝ) / 2000)).trans (le_trans exp_b4295 (by norm_num))

lemma cosh_b4310_ub : cosh ((431 : ℝ) / 1000) ≤ (109733101 : ℝ) / 100000000 := by
  have exp_b4310 : exp (((431 : ℝ) / 1000)^2 / 2) ≤ (109733101 : ℝ) / 100000000 := by
    have ht : ((431 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((431 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((431 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109733101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((431 : ℝ) / 1000)).trans (le_trans exp_b4310 (by norm_num))

lemma cosh_b4330_ub : cosh ((433 : ℝ) / 1000) ≤ (109828001 : ℝ) / 100000000 := by
  have exp_b4330 : exp (((433 : ℝ) / 1000)^2 / 2) ≤ (109828001 : ℝ) / 100000000 := by
    have ht : ((433 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((433 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((433 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109828001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((433 : ℝ) / 1000)).trans (le_trans exp_b4330 (by norm_num))

lemma cosh_b4350_ub : cosh ((87 : ℝ) / 200) ≤ (109923301 : ℝ) / 100000000 := by
  have exp_b4350 : exp (((87 : ℝ) / 200)^2 / 2) ≤ (109923301 : ℝ) / 100000000 := by
    have ht : ((87 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((87 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((87 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109923301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((87 : ℝ) / 200)).trans (le_trans exp_b4350 (by norm_num))

lemma cosh_b4365_ub : cosh ((873 : ℝ) / 2000) ≤ (109995201 : ℝ) / 100000000 := by
  have exp_b4365 : exp (((873 : ℝ) / 2000)^2 / 2) ≤ (109995201 : ℝ) / 100000000 := by
    have ht : ((873 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((873 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((873 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109995201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((873 : ℝ) / 2000)).trans (le_trans exp_b4365 (by norm_num))

lemma cosh_b4385_ub : cosh ((877 : ℝ) / 2000) ≤ (110091501 : ℝ) / 100000000 := by
  have exp_b4385 : exp (((877 : ℝ) / 2000)^2 / 2) ≤ (110091501 : ℝ) / 100000000 := by
    have ht : ((877 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((877 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((877 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110091501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((877 : ℝ) / 2000)).trans (le_trans exp_b4385 (by norm_num))

lemma cosh_b4400_ub : cosh ((11 : ℝ) / 25) ≤ (110164101 : ℝ) / 100000000 := by
  have exp_b4400 : exp (((11 : ℝ) / 25)^2 / 2) ≤ (110164101 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((11 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((11 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110164101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((11 : ℝ) / 25)).trans (le_trans exp_b4400 (by norm_num))

lemma cosh_b4420_ub : cosh ((221 : ℝ) / 500) ≤ (110261301 : ℝ) / 100000000 := by
  have exp_b4420 : exp (((221 : ℝ) / 500)^2 / 2) ≤ (110261301 : ℝ) / 100000000 := by
    have ht : ((221 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((221 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((221 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110261301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((221 : ℝ) / 500)).trans (le_trans exp_b4420 (by norm_num))

lemma cosh_b4440_ub : cosh ((111 : ℝ) / 250) ≤ (110359001 : ℝ) / 100000000 := by
  have exp_b4440 : exp (((111 : ℝ) / 250)^2 / 2) ≤ (110359001 : ℝ) / 100000000 := by
    have ht : ((111 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((111 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((111 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110359001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((111 : ℝ) / 250)).trans (le_trans exp_b4440 (by norm_num))

lemma cosh_b4455_ub : cosh ((891 : ℝ) / 2000) ≤ (110432601 : ℝ) / 100000000 := by
  have exp_b4455 : exp (((891 : ℝ) / 2000)^2 / 2) ≤ (110432601 : ℝ) / 100000000 := by
    have ht : ((891 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((891 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((891 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110432601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((891 : ℝ) / 2000)).trans (le_trans exp_b4455 (by norm_num))

lemma cosh_b4475_ub : cosh ((179 : ℝ) / 400) ≤ (110531301 : ℝ) / 100000000 := by
  have exp_b4475 : exp (((179 : ℝ) / 400)^2 / 2) ≤ (110531301 : ℝ) / 100000000 := by
    have ht : ((179 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((179 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((179 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110531301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((179 : ℝ) / 400)).trans (le_trans exp_b4475 (by norm_num))

lemma cosh_b4495_ub : cosh ((899 : ℝ) / 2000) ≤ (110630501 : ℝ) / 100000000 := by
  have exp_b4495 : exp (((899 : ℝ) / 2000)^2 / 2) ≤ (110630501 : ℝ) / 100000000 := by
    have ht : ((899 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((899 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((899 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110630501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((899 : ℝ) / 2000)).trans (le_trans exp_b4495 (by norm_num))

lemma cosh_b4510_ub : cosh ((451 : ℝ) / 1000) ≤ (110705201 : ℝ) / 100000000 := by
  have exp_b4510 : exp (((451 : ℝ) / 1000)^2 / 2) ≤ (110705201 : ℝ) / 100000000 := by
    have ht : ((451 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((451 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((451 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110705201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((451 : ℝ) / 1000)).trans (le_trans exp_b4510 (by norm_num))

lemma cosh_b4530_ub : cosh ((453 : ℝ) / 1000) ≤ (110805401 : ℝ) / 100000000 := by
  have exp_b4530 : exp (((453 : ℝ) / 1000)^2 / 2) ≤ (110805401 : ℝ) / 100000000 := by
    have ht : ((453 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((453 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((453 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110805401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((453 : ℝ) / 1000)).trans (le_trans exp_b4530 (by norm_num))

lemma cosh_b4550_ub : cosh ((91 : ℝ) / 200) ≤ (110906001 : ℝ) / 100000000 := by
  have exp_b4550 : exp (((91 : ℝ) / 200)^2 / 2) ≤ (110906001 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((91 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((91 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110906001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((91 : ℝ) / 200)).trans (le_trans exp_b4550 (by norm_num))

lemma cosh_b4565_ub : cosh ((913 : ℝ) / 2000) ≤ (110981901 : ℝ) / 100000000 := by
  have exp_b4565 : exp (((913 : ℝ) / 2000)^2 / 2) ≤ (110981901 : ℝ) / 100000000 := by
    have ht : ((913 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((913 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((913 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110981901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((913 : ℝ) / 2000)).trans (le_trans exp_b4565 (by norm_num))

lemma cosh_b4585_ub : cosh ((917 : ℝ) / 2000) ≤ (111083501 : ℝ) / 100000000 := by
  have exp_b4585 : exp (((917 : ℝ) / 2000)^2 / 2) ≤ (111083501 : ℝ) / 100000000 := by
    have ht : ((917 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((917 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((917 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (111083501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((917 : ℝ) / 2000)).trans (le_trans exp_b4585 (by norm_num))

lemma cosh_b4600_ub : cosh ((23 : ℝ) / 50) ≤ (111160001 : ℝ) / 100000000 := by
  have exp_b4600 : exp (((23 : ℝ) / 50)^2 / 2) ≤ (111160001 : ℝ) / 100000000 := by
    have ht : ((23 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((23 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((23 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (111160001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((23 : ℝ) / 50)).trans (le_trans exp_b4600 (by norm_num))

lemma cosh_b4620_ub : cosh ((231 : ℝ) / 500) ≤ (111262501 : ℝ) / 100000000 := by
  have exp_b4620 : exp (((231 : ℝ) / 500)^2 / 2) ≤ (111262501 : ℝ) / 100000000 := by
    have ht : ((231 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((231 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((231 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (111262501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((231 : ℝ) / 500)).trans (le_trans exp_b4620 (by norm_num))

lemma cosh_b4640_ub : cosh ((58 : ℝ) / 125) ≤ (111365601 : ℝ) / 100000000 := by
  have exp_b4640 : exp (((58 : ℝ) / 125)^2 / 2) ≤ (111365601 : ℝ) / 100000000 := by
    have ht : ((58 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((58 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((58 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (111365601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((58 : ℝ) / 125)).trans (le_trans exp_b4640 (by norm_num))

lemma cosh_b4655_ub : cosh ((931 : ℝ) / 2000) ≤ (111443301 : ℝ) / 100000000 := by
  have exp_b4655 : exp (((931 : ℝ) / 2000)^2 / 2) ≤ (111443301 : ℝ) / 100000000 := by
    have ht : ((931 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((931 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((931 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (111443301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((931 : ℝ) / 2000)).trans (le_trans exp_b4655 (by norm_num))

lemma cosh_b4675_ub : cosh ((187 : ℝ) / 400) ≤ (111547301 : ℝ) / 100000000 := by
  have exp_b4675 : exp (((187 : ℝ) / 400)^2 / 2) ≤ (111547301 : ℝ) / 100000000 := by
    have ht : ((187 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((187 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((187 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (111547301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((187 : ℝ) / 400)).trans (le_trans exp_b4675 (by norm_num))

lemma cosh_b4695_ub : cosh ((939 : ℝ) / 2000) ≤ (111651901 : ℝ) / 100000000 := by
  have exp_b4695 : exp (((939 : ℝ) / 2000)^2 / 2) ≤ (111651901 : ℝ) / 100000000 := by
    have ht : ((939 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((939 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((939 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (111651901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((939 : ℝ) / 2000)).trans (le_trans exp_b4695 (by norm_num))

lemma cosh_b4710_ub : cosh ((471 : ℝ) / 1000) ≤ (111730701 : ℝ) / 100000000 := by
  have exp_b4710 : exp (((471 : ℝ) / 1000)^2 / 2) ≤ (111730701 : ℝ) / 100000000 := by
    have ht : ((471 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((471 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((471 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (111730701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((471 : ℝ) / 1000)).trans (le_trans exp_b4710 (by norm_num))

lemma cosh_b4730_ub : cosh ((473 : ℝ) / 1000) ≤ (111836201 : ℝ) / 100000000 := by
  have exp_b4730 : exp (((473 : ℝ) / 1000)^2 / 2) ≤ (111836201 : ℝ) / 100000000 := by
    have ht : ((473 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((473 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((473 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (111836201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((473 : ℝ) / 1000)).trans (le_trans exp_b4730 (by norm_num))

lemma cosh_b4750_ub : cosh ((19 : ℝ) / 40) ≤ (111942301 : ℝ) / 100000000 := by
  have exp_b4750 : exp (((19 : ℝ) / 40)^2 / 2) ≤ (111942301 : ℝ) / 100000000 := by
    have ht : ((19 : ℝ) / 40)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((19 : ℝ) / 40)^2 / 2) ^ m / (Nat.factorial m)) +
          (((19 : ℝ) / 40)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (111942301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((19 : ℝ) / 40)).trans (le_trans exp_b4750 (by norm_num))

lemma cosh_b4765_ub : cosh ((953 : ℝ) / 2000) ≤ (112022201 : ℝ) / 100000000 := by
  have exp_b4765 : exp (((953 : ℝ) / 2000)^2 / 2) ≤ (112022201 : ℝ) / 100000000 := by
    have ht : ((953 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((953 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((953 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (112022201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((953 : ℝ) / 2000)).trans (le_trans exp_b4765 (by norm_num))

lemma cosh_b4785_ub : cosh ((957 : ℝ) / 2000) ≤ (112129201 : ℝ) / 100000000 := by
  have exp_b4785 : exp (((957 : ℝ) / 2000)^2 / 2) ≤ (112129201 : ℝ) / 100000000 := by
    have ht : ((957 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((957 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((957 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (112129201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((957 : ℝ) / 2000)).trans (le_trans exp_b4785 (by norm_num))

lemma cosh_b4800_ub : cosh ((12 : ℝ) / 25) ≤ (112209801 : ℝ) / 100000000 := by
  have exp_b4800 : exp (((12 : ℝ) / 25)^2 / 2) ≤ (112209801 : ℝ) / 100000000 := by
    have ht : ((12 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((12 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((12 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (112209801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((12 : ℝ) / 25)).trans (le_trans exp_b4800 (by norm_num))

lemma cosh_b4820_ub : cosh ((241 : ℝ) / 500) ≤ (112317801 : ℝ) / 100000000 := by
  have exp_b4820 : exp (((241 : ℝ) / 500)^2 / 2) ≤ (112317801 : ℝ) / 100000000 := by
    have ht : ((241 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((241 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((241 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (112317801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((241 : ℝ) / 500)).trans (le_trans exp_b4820 (by norm_num))

lemma cosh_b4840_ub : cosh ((121 : ℝ) / 250) ≤ (112426401 : ℝ) / 100000000 := by
  have exp_b4840 : exp (((121 : ℝ) / 250)^2 / 2) ≤ (112426401 : ℝ) / 100000000 := by
    have ht : ((121 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((121 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((121 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (112426401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((121 : ℝ) / 250)).trans (le_trans exp_b4840 (by norm_num))

lemma cosh_b4855_ub : cosh ((971 : ℝ) / 2000) ≤ (112508201 : ℝ) / 100000000 := by
  have exp_b4855 : exp (((971 : ℝ) / 2000)^2 / 2) ≤ (112508201 : ℝ) / 100000000 := by
    have ht : ((971 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((971 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((971 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (112508201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((971 : ℝ) / 2000)).trans (le_trans exp_b4855 (by norm_num))

lemma cosh_b4875_ub : cosh ((39 : ℝ) / 80) ≤ (112617701 : ℝ) / 100000000 := by
  have exp_b4875 : exp (((39 : ℝ) / 80)^2 / 2) ≤ (112617701 : ℝ) / 100000000 := by
    have ht : ((39 : ℝ) / 80)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((39 : ℝ) / 80)^2 / 2) ^ m / (Nat.factorial m)) +
          (((39 : ℝ) / 80)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (112617701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((39 : ℝ) / 80)).trans (le_trans exp_b4875 (by norm_num))

lemma cosh_b4895_ub : cosh ((979 : ℝ) / 2000) ≤ (112727801 : ℝ) / 100000000 := by
  have exp_b4895 : exp (((979 : ℝ) / 2000)^2 / 2) ≤ (112727801 : ℝ) / 100000000 := by
    have ht : ((979 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((979 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((979 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (112727801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((979 : ℝ) / 2000)).trans (le_trans exp_b4895 (by norm_num))

lemma cosh_b4910_ub : cosh ((491 : ℝ) / 1000) ≤ (112810701 : ℝ) / 100000000 := by
  have exp_b4910 : exp (((491 : ℝ) / 1000)^2 / 2) ≤ (112810701 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((491 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((491 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (112810701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((491 : ℝ) / 1000)).trans (le_trans exp_b4910 (by norm_num))

lemma cosh_b4930_ub : cosh ((493 : ℝ) / 1000) ≤ (112921801 : ℝ) / 100000000 := by
  have exp_b4930 : exp (((493 : ℝ) / 1000)^2 / 2) ≤ (112921801 : ℝ) / 100000000 := by
    have ht : ((493 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((493 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((493 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (112921801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((493 : ℝ) / 1000)).trans (le_trans exp_b4930 (by norm_num))

lemma cosh_b4950_ub : cosh ((99 : ℝ) / 200) ≤ (113033401 : ℝ) / 100000000 := by
  have exp_b4950 : exp (((99 : ℝ) / 200)^2 / 2) ≤ (113033401 : ℝ) / 100000000 := by
    have ht : ((99 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((99 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((99 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (113033401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((99 : ℝ) / 200)).trans (le_trans exp_b4950 (by norm_num))

lemma cosh_b4965_ub : cosh ((993 : ℝ) / 2000) ≤ (113117501 : ℝ) / 100000000 := by
  have exp_b4965 : exp (((993 : ℝ) / 2000)^2 / 2) ≤ (113117501 : ℝ) / 100000000 := by
    have ht : ((993 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((993 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((993 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (113117501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((993 : ℝ) / 2000)).trans (le_trans exp_b4965 (by norm_num))

lemma cosh_b4985_ub : cosh ((997 : ℝ) / 2000) ≤ (113230101 : ℝ) / 100000000 := by
  have exp_b4985 : exp (((997 : ℝ) / 2000)^2 / 2) ≤ (113230101 : ℝ) / 100000000 := by
    have ht : ((997 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((997 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((997 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (113230101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((997 : ℝ) / 2000)).trans (le_trans exp_b4985 (by norm_num))

lemma cosh_b5000_ub : cosh ((1 : ℝ) / 2) ≤ (113314901 : ℝ) / 100000000 := by
  have exp_b5000 : exp (((1 : ℝ) / 2)^2 / 2) ≤ (113314901 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 2)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1 : ℝ) / 2)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1 : ℝ) / 2)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (113314901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1 : ℝ) / 2)).trans (le_trans exp_b5000 (by norm_num))

lemma cosh_b5020_ub : cosh ((251 : ℝ) / 500) ≤ (113428501 : ℝ) / 100000000 := by
  have exp_b5020 : exp (((251 : ℝ) / 500)^2 / 2) ≤ (113428501 : ℝ) / 100000000 := by
    have ht : ((251 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((251 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((251 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (113428501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((251 : ℝ) / 500)).trans (le_trans exp_b5020 (by norm_num))

lemma cosh_b5040_ub : cosh ((63 : ℝ) / 125) ≤ (113542701 : ℝ) / 100000000 := by
  have exp_b5040 : exp (((63 : ℝ) / 125)^2 / 2) ≤ (113542701 : ℝ) / 100000000 := by
    have ht : ((63 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((63 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((63 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (113542701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((63 : ℝ) / 125)).trans (le_trans exp_b5040 (by norm_num))

lemma cosh_b5055_ub : cosh ((1011 : ℝ) / 2000) ≤ (113628701 : ℝ) / 100000000 := by
  have exp_b5055 : exp (((1011 : ℝ) / 2000)^2 / 2) ≤ (113628701 : ℝ) / 100000000 := by
    have ht : ((1011 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1011 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1011 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (113628701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1011 : ℝ) / 2000)).trans (le_trans exp_b5055 (by norm_num))

lemma cosh_b5075_ub : cosh ((203 : ℝ) / 400) ≤ (113743801 : ℝ) / 100000000 := by
  have exp_b5075 : exp (((203 : ℝ) / 400)^2 / 2) ≤ (113743801 : ℝ) / 100000000 := by
    have ht : ((203 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((203 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((203 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (113743801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((203 : ℝ) / 400)).trans (le_trans exp_b5075 (by norm_num))

lemma cosh_b5095_ub : cosh ((1019 : ℝ) / 2000) ≤ (113859601 : ℝ) / 100000000 := by
  have exp_b5095 : exp (((1019 : ℝ) / 2000)^2 / 2) ≤ (113859601 : ℝ) / 100000000 := by
    have ht : ((1019 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1019 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1019 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (113859601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1019 : ℝ) / 2000)).trans (le_trans exp_b5095 (by norm_num))

lemma cosh_b5110_ub : cosh ((511 : ℝ) / 1000) ≤ (113946701 : ℝ) / 100000000 := by
  have exp_b5110 : exp (((511 : ℝ) / 1000)^2 / 2) ≤ (113946701 : ℝ) / 100000000 := by
    have ht : ((511 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((511 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((511 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (113946701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((511 : ℝ) / 1000)).trans (le_trans exp_b5110 (by norm_num))

lemma cosh_b5130_ub : cosh ((513 : ℝ) / 1000) ≤ (114063501 : ℝ) / 100000000 := by
  have exp_b5130 : exp (((513 : ℝ) / 1000)^2 / 2) ≤ (114063501 : ℝ) / 100000000 := by
    have ht : ((513 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((513 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((513 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (114063501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((513 : ℝ) / 1000)).trans (le_trans exp_b5130 (by norm_num))

lemma cosh_b5150_ub : cosh ((103 : ℝ) / 200) ≤ (114180801 : ℝ) / 100000000 := by
  have exp_b5150 : exp (((103 : ℝ) / 200)^2 / 2) ≤ (114180801 : ℝ) / 100000000 := by
    have ht : ((103 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((103 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((103 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (114180801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((103 : ℝ) / 200)).trans (le_trans exp_b5150 (by norm_num))

lemma cosh_b5165_ub : cosh ((1033 : ℝ) / 2000) ≤ (114269201 : ℝ) / 100000000 := by
  have exp_b5165 : exp (((1033 : ℝ) / 2000)^2 / 2) ≤ (114269201 : ℝ) / 100000000 := by
    have ht : ((1033 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1033 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1033 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (114269201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1033 : ℝ) / 2000)).trans (le_trans exp_b5165 (by norm_num))

lemma cosh_b5185_ub : cosh ((1037 : ℝ) / 2000) ≤ (114387501 : ℝ) / 100000000 := by
  have exp_b5185 : exp (((1037 : ℝ) / 2000)^2 / 2) ≤ (114387501 : ℝ) / 100000000 := by
    have ht : ((1037 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1037 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1037 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (114387501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1037 : ℝ) / 2000)).trans (le_trans exp_b5185 (by norm_num))

lemma cosh_b5200_ub : cosh ((13 : ℝ) / 25) ≤ (114476601 : ℝ) / 100000000 := by
  have exp_b5200 : exp (((13 : ℝ) / 25)^2 / 2) ≤ (114476601 : ℝ) / 100000000 := by
    have ht : ((13 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((13 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((13 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (114476601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((13 : ℝ) / 25)).trans (le_trans exp_b5200 (by norm_num))

lemma cosh_b5220_ub : cosh ((261 : ℝ) / 500) ≤ (114596001 : ℝ) / 100000000 := by
  have exp_b5220 : exp (((261 : ℝ) / 500)^2 / 2) ≤ (114596001 : ℝ) / 100000000 := by
    have ht : ((261 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((261 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((261 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (114596001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((261 : ℝ) / 500)).trans (le_trans exp_b5220 (by norm_num))

lemma cosh_b5240_ub : cosh ((131 : ℝ) / 250) ≤ (114715901 : ℝ) / 100000000 := by
  have exp_b5240 : exp (((131 : ℝ) / 250)^2 / 2) ≤ (114715901 : ℝ) / 100000000 := by
    have ht : ((131 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((131 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((131 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (114715901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((131 : ℝ) / 250)).trans (le_trans exp_b5240 (by norm_num))

lemma cosh_b5255_ub : cosh ((1051 : ℝ) / 2000) ≤ (114806201 : ℝ) / 100000000 := by
  have exp_b5255 : exp (((1051 : ℝ) / 2000)^2 / 2) ≤ (114806201 : ℝ) / 100000000 := by
    have ht : ((1051 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1051 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1051 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (114806201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1051 : ℝ) / 2000)).trans (le_trans exp_b5255 (by norm_num))

lemma cosh_b5275_ub : cosh ((211 : ℝ) / 400) ≤ (114927201 : ℝ) / 100000000 := by
  have exp_b5275 : exp (((211 : ℝ) / 400)^2 / 2) ≤ (114927201 : ℝ) / 100000000 := by
    have ht : ((211 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((211 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((211 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (114927201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((211 : ℝ) / 400)).trans (le_trans exp_b5275 (by norm_num))

lemma cosh_b5295_ub : cosh ((1059 : ℝ) / 2000) ≤ (115048701 : ℝ) / 100000000 := by
  have exp_b5295 : exp (((1059 : ℝ) / 2000)^2 / 2) ≤ (115048701 : ℝ) / 100000000 := by
    have ht : ((1059 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1059 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1059 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (115048701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1059 : ℝ) / 2000)).trans (le_trans exp_b5295 (by norm_num))

lemma cosh_b5310_ub : cosh ((531 : ℝ) / 1000) ≤ (115140301 : ℝ) / 100000000 := by
  have exp_b5310 : exp (((531 : ℝ) / 1000)^2 / 2) ≤ (115140301 : ℝ) / 100000000 := by
    have ht : ((531 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((531 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((531 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (115140301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((531 : ℝ) / 1000)).trans (le_trans exp_b5310 (by norm_num))

lemma cosh_b5330_ub : cosh ((533 : ℝ) / 1000) ≤ (115262801 : ℝ) / 100000000 := by
  have exp_b5330 : exp (((533 : ℝ) / 1000)^2 / 2) ≤ (115262801 : ℝ) / 100000000 := by
    have ht : ((533 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((533 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((533 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (115262801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((533 : ℝ) / 1000)).trans (le_trans exp_b5330 (by norm_num))

lemma cosh_b5350_ub : cosh ((107 : ℝ) / 200) ≤ (115386001 : ℝ) / 100000000 := by
  have exp_b5350 : exp (((107 : ℝ) / 200)^2 / 2) ≤ (115386001 : ℝ) / 100000000 := by
    have ht : ((107 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((107 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((107 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (115386001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((107 : ℝ) / 200)).trans (le_trans exp_b5350 (by norm_num))

lemma cosh_b5365_ub : cosh ((1073 : ℝ) / 2000) ≤ (115478801 : ℝ) / 100000000 := by
  have exp_b5365 : exp (((1073 : ℝ) / 2000)^2 / 2) ≤ (115478801 : ℝ) / 100000000 := by
    have ht : ((1073 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1073 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1073 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (115478801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1073 : ℝ) / 2000)).trans (le_trans exp_b5365 (by norm_num))

lemma cosh_b5385_ub : cosh ((1077 : ℝ) / 2000) ≤ (115603001 : ℝ) / 100000000 := by
  have exp_b5385 : exp (((1077 : ℝ) / 2000)^2 / 2) ≤ (115603001 : ℝ) / 100000000 := by
    have ht : ((1077 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1077 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1077 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (115603001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1077 : ℝ) / 2000)).trans (le_trans exp_b5385 (by norm_num))

lemma cosh_b5400_ub : cosh ((27 : ℝ) / 50) ≤ (115696501 : ℝ) / 100000000 := by
  have exp_b5400 : exp (((27 : ℝ) / 50)^2 / 2) ≤ (115696501 : ℝ) / 100000000 := by
    have ht : ((27 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((27 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((27 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (115696501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((27 : ℝ) / 50)).trans (le_trans exp_b5400 (by norm_num))

lemma cosh_b5420_ub : cosh ((271 : ℝ) / 500) ≤ (115821801 : ℝ) / 100000000 := by
  have exp_b5420 : exp (((271 : ℝ) / 500)^2 / 2) ≤ (115821801 : ℝ) / 100000000 := by
    have ht : ((271 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((271 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((271 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (115821801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((271 : ℝ) / 500)).trans (le_trans exp_b5420 (by norm_num))

lemma cosh_b5440_ub : cosh ((68 : ℝ) / 125) ≤ (115947601 : ℝ) / 100000000 := by
  have exp_b5440 : exp (((68 : ℝ) / 125)^2 / 2) ≤ (115947601 : ℝ) / 100000000 := by
    have ht : ((68 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((68 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((68 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (115947601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((68 : ℝ) / 125)).trans (le_trans exp_b5440 (by norm_num))

lemma cosh_b5455_ub : cosh ((1091 : ℝ) / 2000) ≤ (116042401 : ℝ) / 100000000 := by
  have exp_b5455 : exp (((1091 : ℝ) / 2000)^2 / 2) ≤ (116042401 : ℝ) / 100000000 := by
    have ht : ((1091 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1091 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1091 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (116042401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1091 : ℝ) / 2000)).trans (le_trans exp_b5455 (by norm_num))

lemma cosh_b5475_ub : cosh ((219 : ℝ) / 400) ≤ (116169301 : ℝ) / 100000000 := by
  have exp_b5475 : exp (((219 : ℝ) / 400)^2 / 2) ≤ (116169301 : ℝ) / 100000000 := by
    have ht : ((219 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((219 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((219 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (116169301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((219 : ℝ) / 400)).trans (le_trans exp_b5475 (by norm_num))

lemma cosh_b5495_ub : cosh ((1099 : ℝ) / 2000) ≤ (116296801 : ℝ) / 100000000 := by
  have exp_b5495 : exp (((1099 : ℝ) / 2000)^2 / 2) ≤ (116296801 : ℝ) / 100000000 := by
    have ht : ((1099 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1099 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1099 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (116296801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1099 : ℝ) / 2000)).trans (le_trans exp_b5495 (by norm_num))

lemma cosh_b5510_ub : cosh ((551 : ℝ) / 1000) ≤ (116392901 : ℝ) / 100000000 := by
  have exp_b5510 : exp (((551 : ℝ) / 1000)^2 / 2) ≤ (116392901 : ℝ) / 100000000 := by
    have ht : ((551 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((551 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((551 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (116392901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((551 : ℝ) / 1000)).trans (le_trans exp_b5510 (by norm_num))

lemma cosh_b5530_ub : cosh ((553 : ℝ) / 1000) ≤ (116521401 : ℝ) / 100000000 := by
  have exp_b5530 : exp (((553 : ℝ) / 1000)^2 / 2) ≤ (116521401 : ℝ) / 100000000 := by
    have ht : ((553 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((553 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((553 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (116521401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((553 : ℝ) / 1000)).trans (le_trans exp_b5530 (by norm_num))

lemma cosh_b5550_ub : cosh ((111 : ℝ) / 200) ≤ (116650601 : ℝ) / 100000000 := by
  have exp_b5550 : exp (((111 : ℝ) / 200)^2 / 2) ≤ (116650601 : ℝ) / 100000000 := by
    have ht : ((111 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((111 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((111 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (116650601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((111 : ℝ) / 200)).trans (le_trans exp_b5550 (by norm_num))

lemma cosh_b5565_ub : cosh ((1113 : ℝ) / 2000) ≤ (116747901 : ℝ) / 100000000 := by
  have exp_b5565 : exp (((1113 : ℝ) / 2000)^2 / 2) ≤ (116747901 : ℝ) / 100000000 := by
    have ht : ((1113 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1113 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1113 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (116747901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1113 : ℝ) / 2000)).trans (le_trans exp_b5565 (by norm_num))

lemma cosh_b5585_ub : cosh ((1117 : ℝ) / 2000) ≤ (116878101 : ℝ) / 100000000 := by
  have exp_b5585 : exp (((1117 : ℝ) / 2000)^2 / 2) ≤ (116878101 : ℝ) / 100000000 := by
    have ht : ((1117 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1117 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1117 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (116878101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1117 : ℝ) / 2000)).trans (le_trans exp_b5585 (by norm_num))

lemma cosh_b5600_ub : cosh ((14 : ℝ) / 25) ≤ (116976201 : ℝ) / 100000000 := by
  have exp_b5600 : exp (((14 : ℝ) / 25)^2 / 2) ≤ (116976201 : ℝ) / 100000000 := by
    have ht : ((14 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((14 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((14 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (116976201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((14 : ℝ) / 25)).trans (le_trans exp_b5600 (by norm_num))

lemma cosh_b5620_ub : cosh ((281 : ℝ) / 500) ≤ (117107501 : ℝ) / 100000000 := by
  have exp_b5620 : exp (((281 : ℝ) / 500)^2 / 2) ≤ (117107501 : ℝ) / 100000000 := by
    have ht : ((281 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((281 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((281 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (117107501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((281 : ℝ) / 500)).trans (le_trans exp_b5620 (by norm_num))

lemma cosh_b5640_ub : cosh ((141 : ℝ) / 250) ≤ (117239501 : ℝ) / 100000000 := by
  have exp_b5640 : exp (((141 : ℝ) / 250)^2 / 2) ≤ (117239501 : ℝ) / 100000000 := by
    have ht : ((141 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((141 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((141 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (117239501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((141 : ℝ) / 250)).trans (le_trans exp_b5640 (by norm_num))

lemma cosh_b5655_ub : cosh ((1131 : ℝ) / 2000) ≤ (117338801 : ℝ) / 100000000 := by
  have exp_b5655 : exp (((1131 : ℝ) / 2000)^2 / 2) ≤ (117338801 : ℝ) / 100000000 := by
    have ht : ((1131 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1131 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1131 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (117338801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1131 : ℝ) / 2000)).trans (le_trans exp_b5655 (by norm_num))

lemma cosh_b5675_ub : cosh ((227 : ℝ) / 400) ≤ (117471901 : ℝ) / 100000000 := by
  have exp_b5675 : exp (((227 : ℝ) / 400)^2 / 2) ≤ (117471901 : ℝ) / 100000000 := by
    have ht : ((227 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((227 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((227 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (117471901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((227 : ℝ) / 400)).trans (le_trans exp_b5675 (by norm_num))

lemma cosh_b5695_ub : cosh ((1139 : ℝ) / 2000) ≤ (117605501 : ℝ) / 100000000 := by
  have exp_b5695 : exp (((1139 : ℝ) / 2000)^2 / 2) ≤ (117605501 : ℝ) / 100000000 := by
    have ht : ((1139 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1139 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1139 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (117605501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1139 : ℝ) / 2000)).trans (le_trans exp_b5695 (by norm_num))

lemma cosh_b5710_ub : cosh ((571 : ℝ) / 1000) ≤ (117706101 : ℝ) / 100000000 := by
  have exp_b5710 : exp (((571 : ℝ) / 1000)^2 / 2) ≤ (117706101 : ℝ) / 100000000 := by
    have ht : ((571 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((571 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((571 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (117706101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((571 : ℝ) / 1000)).trans (le_trans exp_b5710 (by norm_num))

lemma cosh_b5730_ub : cosh ((573 : ℝ) / 1000) ≤ (117840901 : ℝ) / 100000000 := by
  have exp_b5730 : exp (((573 : ℝ) / 1000)^2 / 2) ≤ (117840901 : ℝ) / 100000000 := by
    have ht : ((573 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((573 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((573 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (117840901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((573 : ℝ) / 1000)).trans (le_trans exp_b5730 (by norm_num))

lemma cosh_b5750_ub : cosh ((23 : ℝ) / 40) ≤ (117976201 : ℝ) / 100000000 := by
  have exp_b5750 : exp (((23 : ℝ) / 40)^2 / 2) ≤ (117976201 : ℝ) / 100000000 := by
    have ht : ((23 : ℝ) / 40)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((23 : ℝ) / 40)^2 / 2) ^ m / (Nat.factorial m)) +
          (((23 : ℝ) / 40)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (117976201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((23 : ℝ) / 40)).trans (le_trans exp_b5750 (by norm_num))

lemma cosh_b5765_ub : cosh ((1153 : ℝ) / 2000) ≤ (118078201 : ℝ) / 100000000 := by
  have exp_b5765 : exp (((1153 : ℝ) / 2000)^2 / 2) ≤ (118078201 : ℝ) / 100000000 := by
    have ht : ((1153 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1153 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1153 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (118078201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1153 : ℝ) / 2000)).trans (le_trans exp_b5765 (by norm_num))

lemma cosh_b5785_ub : cosh ((1157 : ℝ) / 2000) ≤ (118214601 : ℝ) / 100000000 := by
  have exp_b5785 : exp (((1157 : ℝ) / 2000)^2 / 2) ≤ (118214601 : ℝ) / 100000000 := by
    have ht : ((1157 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1157 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1157 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (118214601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1157 : ℝ) / 2000)).trans (le_trans exp_b5785 (by norm_num))

lemma cosh_b5800_ub : cosh ((29 : ℝ) / 50) ≤ (118317401 : ℝ) / 100000000 := by
  have exp_b5800 : exp (((29 : ℝ) / 50)^2 / 2) ≤ (118317401 : ℝ) / 100000000 := by
    have ht : ((29 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((29 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((29 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (118317401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((29 : ℝ) / 50)).trans (le_trans exp_b5800 (by norm_num))

lemma cosh_b5820_ub : cosh ((291 : ℝ) / 500) ≤ (118454901 : ℝ) / 100000000 := by
  have exp_b5820 : exp (((291 : ℝ) / 500)^2 / 2) ≤ (118454901 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((291 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((291 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (118454901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((291 : ℝ) / 500)).trans (le_trans exp_b5820 (by norm_num))

lemma cosh_b5840_ub : cosh ((73 : ℝ) / 125) ≤ (118593101 : ℝ) / 100000000 := by
  have exp_b5840 : exp (((73 : ℝ) / 125)^2 / 2) ≤ (118593101 : ℝ) / 100000000 := by
    have ht : ((73 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((73 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((73 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (118593101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((73 : ℝ) / 125)).trans (le_trans exp_b5840 (by norm_num))

lemma cosh_b5855_ub : cosh ((1171 : ℝ) / 2000) ≤ (118697201 : ℝ) / 100000000 := by
  have exp_b5855 : exp (((1171 : ℝ) / 2000)^2 / 2) ≤ (118697201 : ℝ) / 100000000 := by
    have ht : ((1171 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1171 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1171 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (118697201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1171 : ℝ) / 2000)).trans (le_trans exp_b5855 (by norm_num))

lemma cosh_b5875_ub : cosh ((47 : ℝ) / 80) ≤ (118836501 : ℝ) / 100000000 := by
  have exp_b5875 : exp (((47 : ℝ) / 80)^2 / 2) ≤ (118836501 : ℝ) / 100000000 := by
    have ht : ((47 : ℝ) / 80)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((47 : ℝ) / 80)^2 / 2) ^ m / (Nat.factorial m)) +
          (((47 : ℝ) / 80)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (118836501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((47 : ℝ) / 80)).trans (le_trans exp_b5875 (by norm_num))

lemma cosh_b5895_ub : cosh ((1179 : ℝ) / 2000) ≤ (118976501 : ℝ) / 100000000 := by
  have exp_b5895 : exp (((1179 : ℝ) / 2000)^2 / 2) ≤ (118976501 : ℝ) / 100000000 := by
    have ht : ((1179 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1179 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1179 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (118976501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1179 : ℝ) / 2000)).trans (le_trans exp_b5895 (by norm_num))

lemma cosh_b5910_ub : cosh ((591 : ℝ) / 1000) ≤ (119081901 : ℝ) / 100000000 := by
  have exp_b5910 : exp (((591 : ℝ) / 1000)^2 / 2) ≤ (119081901 : ℝ) / 100000000 := by
    have ht : ((591 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((591 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((591 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (119081901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((591 : ℝ) / 1000)).trans (le_trans exp_b5910 (by norm_num))

lemma cosh_b5930_ub : cosh ((593 : ℝ) / 1000) ≤ (119222901 : ℝ) / 100000000 := by
  have exp_b5930 : exp (((593 : ℝ) / 1000)^2 / 2) ≤ (119222901 : ℝ) / 100000000 := by
    have ht : ((593 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((593 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((593 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (119222901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((593 : ℝ) / 1000)).trans (le_trans exp_b5930 (by norm_num))

lemma cosh_b5950_ub : cosh ((119 : ℝ) / 200) ≤ (119364701 : ℝ) / 100000000 := by
  have exp_b5950 : exp (((119 : ℝ) / 200)^2 / 2) ≤ (119364701 : ℝ) / 100000000 := by
    have ht : ((119 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((119 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((119 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (119364701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((119 : ℝ) / 200)).trans (le_trans exp_b5950 (by norm_num))

lemma cosh_b5965_ub : cosh ((1193 : ℝ) / 2000) ≤ (119471401 : ℝ) / 100000000 := by
  have exp_b5965 : exp (((1193 : ℝ) / 2000)^2 / 2) ≤ (119471401 : ℝ) / 100000000 := by
    have ht : ((1193 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1193 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1193 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (119471401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1193 : ℝ) / 2000)).trans (le_trans exp_b5965 (by norm_num))

lemma cosh_b5985_ub : cosh ((1197 : ℝ) / 2000) ≤ (119614201 : ℝ) / 100000000 := by
  have exp_b5985 : exp (((1197 : ℝ) / 2000)^2 / 2) ≤ (119614201 : ℝ) / 100000000 := by
    have ht : ((1197 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1197 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1197 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (119614201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1197 : ℝ) / 2000)).trans (le_trans exp_b5985 (by norm_num))

lemma cosh_b6000_ub : cosh ((3 : ℝ) / 5) ≤ (119721801 : ℝ) / 100000000 := by
  have exp_b6000 : exp (((3 : ℝ) / 5)^2 / 2) ≤ (119721801 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 5)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((3 : ℝ) / 5)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 5)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (119721801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 5)).trans (le_trans exp_b6000 (by norm_num))

lemma cosh_b6020_ub : cosh ((301 : ℝ) / 500) ≤ (119865801 : ℝ) / 100000000 := by
  have exp_b6020 : exp (((301 : ℝ) / 500)^2 / 2) ≤ (119865801 : ℝ) / 100000000 := by
    have ht : ((301 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((301 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((301 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (119865801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((301 : ℝ) / 500)).trans (le_trans exp_b6020 (by norm_num))

lemma cosh_b6040_ub : cosh ((151 : ℝ) / 250) ≤ (120010401 : ℝ) / 100000000 := by
  have exp_b6040 : exp (((151 : ℝ) / 250)^2 / 2) ≤ (120010401 : ℝ) / 100000000 := by
    have ht : ((151 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((151 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((151 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (120010401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((151 : ℝ) / 250)).trans (le_trans exp_b6040 (by norm_num))

lemma cosh_b6055_ub : cosh ((1211 : ℝ) / 2000) ≤ (120119301 : ℝ) / 100000000 := by
  have exp_b6055 : exp (((1211 : ℝ) / 2000)^2 / 2) ≤ (120119301 : ℝ) / 100000000 := by
    have ht : ((1211 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1211 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1211 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (120119301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1211 : ℝ) / 2000)).trans (le_trans exp_b6055 (by norm_num))

lemma cosh_b6075_ub : cosh ((243 : ℝ) / 400) ≤ (120265101 : ℝ) / 100000000 := by
  have exp_b6075 : exp (((243 : ℝ) / 400)^2 / 2) ≤ (120265101 : ℝ) / 100000000 := by
    have ht : ((243 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((243 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((243 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (120265101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((243 : ℝ) / 400)).trans (le_trans exp_b6075 (by norm_num))

lemma cosh_b6095_ub : cosh ((1219 : ℝ) / 2000) ≤ (120411601 : ℝ) / 100000000 := by
  have exp_b6095 : exp (((1219 : ℝ) / 2000)^2 / 2) ≤ (120411601 : ℝ) / 100000000 := by
    have ht : ((1219 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1219 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1219 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (120411601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1219 : ℝ) / 2000)).trans (le_trans exp_b6095 (by norm_num))

lemma cosh_b6110_ub : cosh ((611 : ℝ) / 1000) ≤ (120521901 : ℝ) / 100000000 := by
  have exp_b6110 : exp (((611 : ℝ) / 1000)^2 / 2) ≤ (120521901 : ℝ) / 100000000 := by
    have ht : ((611 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((611 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((611 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (120521901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((611 : ℝ) / 1000)).trans (le_trans exp_b6110 (by norm_num))

lemma cosh_b6130_ub : cosh ((613 : ℝ) / 1000) ≤ (120669501 : ℝ) / 100000000 := by
  have exp_b6130 : exp (((613 : ℝ) / 1000)^2 / 2) ≤ (120669501 : ℝ) / 100000000 := by
    have ht : ((613 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((613 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((613 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (120669501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((613 : ℝ) / 1000)).trans (le_trans exp_b6130 (by norm_num))

lemma cosh_b6150_ub : cosh ((123 : ℝ) / 200) ≤ (120817701 : ℝ) / 100000000 := by
  have exp_b6150 : exp (((123 : ℝ) / 200)^2 / 2) ≤ (120817701 : ℝ) / 100000000 := by
    have ht : ((123 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((123 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((123 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (120817701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((123 : ℝ) / 200)).trans (le_trans exp_b6150 (by norm_num))

lemma cosh_b6165_ub : cosh ((1233 : ℝ) / 2000) ≤ (120929401 : ℝ) / 100000000 := by
  have exp_b6165 : exp (((1233 : ℝ) / 2000)^2 / 2) ≤ (120929401 : ℝ) / 100000000 := by
    have ht : ((1233 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1233 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1233 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (120929401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1233 : ℝ) / 2000)).trans (le_trans exp_b6165 (by norm_num))

lemma cosh_b6185_ub : cosh ((1237 : ℝ) / 2000) ≤ (121078801 : ℝ) / 100000000 := by
  have exp_b6185 : exp (((1237 : ℝ) / 2000)^2 / 2) ≤ (121078801 : ℝ) / 100000000 := by
    have ht : ((1237 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1237 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1237 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (121078801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1237 : ℝ) / 2000)).trans (le_trans exp_b6185 (by norm_num))

lemma cosh_b6200_ub : cosh ((31 : ℝ) / 50) ≤ (121191301 : ℝ) / 100000000 := by
  have exp_b6200 : exp (((31 : ℝ) / 50)^2 / 2) ≤ (121191301 : ℝ) / 100000000 := by
    have ht : ((31 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((31 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((31 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (121191301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((31 : ℝ) / 50)).trans (le_trans exp_b6200 (by norm_num))

lemma cosh_b6220_ub : cosh ((311 : ℝ) / 500) ≤ (121342001 : ℝ) / 100000000 := by
  have exp_b6220 : exp (((311 : ℝ) / 500)^2 / 2) ≤ (121342001 : ℝ) / 100000000 := by
    have ht : ((311 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((311 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((311 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (121342001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((311 : ℝ) / 500)).trans (le_trans exp_b6220 (by norm_num))

lemma cosh_b6240_ub : cosh ((78 : ℝ) / 125) ≤ (121493201 : ℝ) / 100000000 := by
  have exp_b6240 : exp (((78 : ℝ) / 125)^2 / 2) ≤ (121493201 : ℝ) / 100000000 := by
    have ht : ((78 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((78 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((78 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (121493201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((78 : ℝ) / 125)).trans (le_trans exp_b6240 (by norm_num))

lemma cosh_b6255_ub : cosh ((1251 : ℝ) / 2000) ≤ (121607101 : ℝ) / 100000000 := by
  have exp_b6255 : exp (((1251 : ℝ) / 2000)^2 / 2) ≤ (121607101 : ℝ) / 100000000 := by
    have ht : ((1251 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1251 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1251 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (121607101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1251 : ℝ) / 2000)).trans (le_trans exp_b6255 (by norm_num))

lemma cosh_b6275_ub : cosh ((251 : ℝ) / 400) ≤ (121759601 : ℝ) / 100000000 := by
  have exp_b6275 : exp (((251 : ℝ) / 400)^2 / 2) ≤ (121759601 : ℝ) / 100000000 := by
    have ht : ((251 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((251 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((251 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (121759601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((251 : ℝ) / 400)).trans (le_trans exp_b6275 (by norm_num))

lemma cosh_b6295_ub : cosh ((1259 : ℝ) / 2000) ≤ (121912801 : ℝ) / 100000000 := by
  have exp_b6295 : exp (((1259 : ℝ) / 2000)^2 / 2) ≤ (121912801 : ℝ) / 100000000 := by
    have ht : ((1259 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1259 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1259 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (121912801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1259 : ℝ) / 2000)).trans (le_trans exp_b6295 (by norm_num))

lemma cosh_b6310_ub : cosh ((631 : ℝ) / 1000) ≤ (122028101 : ℝ) / 100000000 := by
  have exp_b6310 : exp (((631 : ℝ) / 1000)^2 / 2) ≤ (122028101 : ℝ) / 100000000 := by
    have ht : ((631 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((631 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((631 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (122028101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((631 : ℝ) / 1000)).trans (le_trans exp_b6310 (by norm_num))

lemma cosh_b6330_ub : cosh ((633 : ℝ) / 1000) ≤ (122182401 : ℝ) / 100000000 := by
  have exp_b6330 : exp (((633 : ℝ) / 1000)^2 / 2) ≤ (122182401 : ℝ) / 100000000 := by
    have ht : ((633 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((633 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((633 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (122182401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((633 : ℝ) / 1000)).trans (le_trans exp_b6330 (by norm_num))

lemma cosh_b6350_ub : cosh ((127 : ℝ) / 200) ≤ (122337401 : ℝ) / 100000000 := by
  have exp_b6350 : exp (((127 : ℝ) / 200)^2 / 2) ≤ (122337401 : ℝ) / 100000000 := by
    have ht : ((127 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((127 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((127 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (122337401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((127 : ℝ) / 200)).trans (le_trans exp_b6350 (by norm_num))

lemma cosh_b6365_ub : cosh ((1273 : ℝ) / 2000) ≤ (122454201 : ℝ) / 100000000 := by
  have exp_b6365 : exp (((1273 : ℝ) / 2000)^2 / 2) ≤ (122454201 : ℝ) / 100000000 := by
    have ht : ((1273 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1273 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1273 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (122454201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1273 : ℝ) / 2000)).trans (le_trans exp_b6365 (by norm_num))

lemma cosh_b6385_ub : cosh ((1277 : ℝ) / 2000) ≤ (122610401 : ℝ) / 100000000 := by
  have exp_b6385 : exp (((1277 : ℝ) / 2000)^2 / 2) ≤ (122610401 : ℝ) / 100000000 := by
    have ht : ((1277 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1277 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1277 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (122610401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1277 : ℝ) / 2000)).trans (le_trans exp_b6385 (by norm_num))

lemma cosh_b6400_ub : cosh ((16 : ℝ) / 25) ≤ (122728001 : ℝ) / 100000000 := by
  have exp_b6400 : exp (((16 : ℝ) / 25)^2 / 2) ≤ (122728001 : ℝ) / 100000000 := by
    have ht : ((16 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((16 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((16 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (122728001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((16 : ℝ) / 25)).trans (le_trans exp_b6400 (by norm_num))

lemma cosh_b6420_ub : cosh ((321 : ℝ) / 500) ≤ (122885401 : ℝ) / 100000000 := by
  have exp_b6420 : exp (((321 : ℝ) / 500)^2 / 2) ≤ (122885401 : ℝ) / 100000000 := by
    have ht : ((321 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((321 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((321 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (122885401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((321 : ℝ) / 500)).trans (le_trans exp_b6420 (by norm_num))

lemma cosh_b6440_ub : cosh ((161 : ℝ) / 250) ≤ (123043601 : ℝ) / 100000000 := by
  have exp_b6440 : exp (((161 : ℝ) / 250)^2 / 2) ≤ (123043601 : ℝ) / 100000000 := by
    have ht : ((161 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((161 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((161 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (123043601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((161 : ℝ) / 250)).trans (le_trans exp_b6440 (by norm_num))

lemma cosh_b6455_ub : cosh ((1291 : ℝ) / 2000) ≤ (123162601 : ℝ) / 100000000 := by
  have exp_b6455 : exp (((1291 : ℝ) / 2000)^2 / 2) ≤ (123162601 : ℝ) / 100000000 := by
    have ht : ((1291 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1291 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1291 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (123162601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1291 : ℝ) / 2000)).trans (le_trans exp_b6455 (by norm_num))

lemma cosh_b6475_ub : cosh ((259 : ℝ) / 400) ≤ (123322001 : ℝ) / 100000000 := by
  have exp_b6475 : exp (((259 : ℝ) / 400)^2 / 2) ≤ (123322001 : ℝ) / 100000000 := by
    have ht : ((259 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((259 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((259 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (123322001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((259 : ℝ) / 400)).trans (le_trans exp_b6475 (by norm_num))

lemma cosh_b6495_ub : cosh ((1299 : ℝ) / 2000) ≤ (123482001 : ℝ) / 100000000 := by
  have exp_b6495 : exp (((1299 : ℝ) / 2000)^2 / 2) ≤ (123482001 : ℝ) / 100000000 := by
    have ht : ((1299 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1299 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1299 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (123482001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1299 : ℝ) / 2000)).trans (le_trans exp_b6495 (by norm_num))

lemma cosh_b6510_ub : cosh ((651 : ℝ) / 1000) ≤ (123602501 : ℝ) / 100000000 := by
  have exp_b6510 : exp (((651 : ℝ) / 1000)^2 / 2) ≤ (123602501 : ℝ) / 100000000 := by
    have ht : ((651 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((651 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((651 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (123602501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((651 : ℝ) / 1000)).trans (le_trans exp_b6510 (by norm_num))

lemma cosh_b6530_ub : cosh ((653 : ℝ) / 1000) ≤ (123763801 : ℝ) / 100000000 := by
  have exp_b6530 : exp (((653 : ℝ) / 1000)^2 / 2) ≤ (123763801 : ℝ) / 100000000 := by
    have ht : ((653 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((653 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((653 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (123763801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((653 : ℝ) / 1000)).trans (le_trans exp_b6530 (by norm_num))

lemma cosh_b6550_ub : cosh ((131 : ℝ) / 200) ≤ (123925801 : ℝ) / 100000000 := by
  have exp_b6550 : exp (((131 : ℝ) / 200)^2 / 2) ≤ (123925801 : ℝ) / 100000000 := by
    have ht : ((131 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((131 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((131 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (123925801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((131 : ℝ) / 200)).trans (le_trans exp_b6550 (by norm_num))

lemma cosh_b6565_ub : cosh ((1313 : ℝ) / 2000) ≤ (124047801 : ℝ) / 100000000 := by
  have exp_b6565 : exp (((1313 : ℝ) / 2000)^2 / 2) ≤ (124047801 : ℝ) / 100000000 := by
    have ht : ((1313 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1313 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1313 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (124047801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1313 : ℝ) / 2000)).trans (le_trans exp_b6565 (by norm_num))

lemma cosh_b6585_ub : cosh ((1317 : ℝ) / 2000) ≤ (124211001 : ℝ) / 100000000 := by
  have exp_b6585 : exp (((1317 : ℝ) / 2000)^2 / 2) ≤ (124211001 : ℝ) / 100000000 := by
    have ht : ((1317 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1317 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1317 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (124211001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1317 : ℝ) / 2000)).trans (le_trans exp_b6585 (by norm_num))

lemma cosh_b6600_ub : cosh ((33 : ℝ) / 50) ≤ (124333901 : ℝ) / 100000000 := by
  have exp_b6600 : exp (((33 : ℝ) / 50)^2 / 2) ≤ (124333901 : ℝ) / 100000000 := by
    have ht : ((33 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((33 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((33 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (124333901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((33 : ℝ) / 50)).trans (le_trans exp_b6600 (by norm_num))

lemma cosh_b6620_ub : cosh ((331 : ℝ) / 500) ≤ (124498401 : ℝ) / 100000000 := by
  have exp_b6620 : exp (((331 : ℝ) / 500)^2 / 2) ≤ (124498401 : ℝ) / 100000000 := by
    have ht : ((331 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((331 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((331 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (124498401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((331 : ℝ) / 500)).trans (le_trans exp_b6620 (by norm_num))

lemma cosh_b6640_ub : cosh ((83 : ℝ) / 125) ≤ (124663601 : ℝ) / 100000000 := by
  have exp_b6640 : exp (((83 : ℝ) / 125)^2 / 2) ≤ (124663601 : ℝ) / 100000000 := by
    have ht : ((83 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((83 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((83 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (124663601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((83 : ℝ) / 125)).trans (le_trans exp_b6640 (by norm_num))

lemma cosh_b6655_ub : cosh ((1331 : ℝ) / 2000) ≤ (124787901 : ℝ) / 100000000 := by
  have exp_b6655 : exp (((1331 : ℝ) / 2000)^2 / 2) ≤ (124787901 : ℝ) / 100000000 := by
    have ht : ((1331 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1331 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1331 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (124787901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1331 : ℝ) / 2000)).trans (le_trans exp_b6655 (by norm_num))

lemma cosh_b6675_ub : cosh ((267 : ℝ) / 400) ≤ (124954401 : ℝ) / 100000000 := by
  have exp_b6675 : exp (((267 : ℝ) / 400)^2 / 2) ≤ (124954401 : ℝ) / 100000000 := by
    have ht : ((267 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((267 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((267 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (124954401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((267 : ℝ) / 400)).trans (le_trans exp_b6675 (by norm_num))

lemma cosh_b6695_ub : cosh ((1339 : ℝ) / 2000) ≤ (125121601 : ℝ) / 100000000 := by
  have exp_b6695 : exp (((1339 : ℝ) / 2000)^2 / 2) ≤ (125121601 : ℝ) / 100000000 := by
    have ht : ((1339 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1339 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1339 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (125121601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1339 : ℝ) / 2000)).trans (le_trans exp_b6695 (by norm_num))

lemma cosh_b6710_ub : cosh ((671 : ℝ) / 1000) ≤ (125247401 : ℝ) / 100000000 := by
  have exp_b6710 : exp (((671 : ℝ) / 1000)^2 / 2) ≤ (125247401 : ℝ) / 100000000 := by
    have ht : ((671 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((671 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((671 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (125247401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((671 : ℝ) / 1000)).trans (le_trans exp_b6710 (by norm_num))

lemma cosh_b6730_ub : cosh ((673 : ℝ) / 1000) ≤ (125415901 : ℝ) / 100000000 := by
  have exp_b6730 : exp (((673 : ℝ) / 1000)^2 / 2) ≤ (125415901 : ℝ) / 100000000 := by
    have ht : ((673 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((673 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((673 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (125415901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((673 : ℝ) / 1000)).trans (le_trans exp_b6730 (by norm_num))

lemma cosh_b6750_ub : cosh ((27 : ℝ) / 40) ≤ (125585001 : ℝ) / 100000000 := by
  have exp_b6750 : exp (((27 : ℝ) / 40)^2 / 2) ≤ (125585001 : ℝ) / 100000000 := by
    have ht : ((27 : ℝ) / 40)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((27 : ℝ) / 40)^2 / 2) ^ m / (Nat.factorial m)) +
          (((27 : ℝ) / 40)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (125585001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((27 : ℝ) / 40)).trans (le_trans exp_b6750 (by norm_num))

lemma cosh_b6765_ub : cosh ((1353 : ℝ) / 2000) ≤ (125712401 : ℝ) / 100000000 := by
  have exp_b6765 : exp (((1353 : ℝ) / 2000)^2 / 2) ≤ (125712401 : ℝ) / 100000000 := by
    have ht : ((1353 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1353 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1353 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (125712401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1353 : ℝ) / 2000)).trans (le_trans exp_b6765 (by norm_num))

lemma cosh_b6785_ub : cosh ((1357 : ℝ) / 2000) ≤ (125882801 : ℝ) / 100000000 := by
  have exp_b6785 : exp (((1357 : ℝ) / 2000)^2 / 2) ≤ (125882801 : ℝ) / 100000000 := by
    have ht : ((1357 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1357 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1357 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (125882801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1357 : ℝ) / 2000)).trans (le_trans exp_b6785 (by norm_num))

lemma cosh_b6800_ub : cosh ((17 : ℝ) / 25) ≤ (126011201 : ℝ) / 100000000 := by
  have exp_b6800 : exp (((17 : ℝ) / 25)^2 / 2) ≤ (126011201 : ℝ) / 100000000 := by
    have ht : ((17 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((17 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((17 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (126011201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((17 : ℝ) / 25)).trans (le_trans exp_b6800 (by norm_num))

lemma cosh_b6820_ub : cosh ((341 : ℝ) / 500) ≤ (126182901 : ℝ) / 100000000 := by
  have exp_b6820 : exp (((341 : ℝ) / 500)^2 / 2) ≤ (126182901 : ℝ) / 100000000 := by
    have ht : ((341 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((341 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((341 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (126182901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((341 : ℝ) / 500)).trans (le_trans exp_b6820 (by norm_num))

lemma cosh_b6840_ub : cosh ((171 : ℝ) / 250) ≤ (126355401 : ℝ) / 100000000 := by
  have exp_b6840 : exp (((171 : ℝ) / 250)^2 / 2) ≤ (126355401 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((171 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((171 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (126355401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((171 : ℝ) / 250)).trans (le_trans exp_b6840 (by norm_num))

lemma cosh_b6855_ub : cosh ((1371 : ℝ) / 2000) ≤ (126485301 : ℝ) / 100000000 := by
  have exp_b6855 : exp (((1371 : ℝ) / 2000)^2 / 2) ≤ (126485301 : ℝ) / 100000000 := by
    have ht : ((1371 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1371 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1371 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (126485301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1371 : ℝ) / 2000)).trans (le_trans exp_b6855 (by norm_num))

lemma cosh_b6875_ub : cosh ((11 : ℝ) / 16) ≤ (126659001 : ℝ) / 100000000 := by
  have exp_b6875 : exp (((11 : ℝ) / 16)^2 / 2) ≤ (126659001 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 16)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((11 : ℝ) / 16)^2 / 2) ^ m / (Nat.factorial m)) +
          (((11 : ℝ) / 16)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (126659001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((11 : ℝ) / 16)).trans (le_trans exp_b6875 (by norm_num))

lemma cosh_b6895_ub : cosh ((1379 : ℝ) / 2000) ≤ (126833601 : ℝ) / 100000000 := by
  have exp_b6895 : exp (((1379 : ℝ) / 2000)^2 / 2) ≤ (126833601 : ℝ) / 100000000 := by
    have ht : ((1379 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1379 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1379 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (126833601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1379 : ℝ) / 2000)).trans (le_trans exp_b6895 (by norm_num))

lemma cosh_b6910_ub : cosh ((691 : ℝ) / 1000) ≤ (126965001 : ℝ) / 100000000 := by
  have exp_b6910 : exp (((691 : ℝ) / 1000)^2 / 2) ≤ (126965001 : ℝ) / 100000000 := by
    have ht : ((691 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((691 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((691 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (126965001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((691 : ℝ) / 1000)).trans (le_trans exp_b6910 (by norm_num))

lemma cosh_b6930_ub : cosh ((693 : ℝ) / 1000) ≤ (127140801 : ℝ) / 100000000 := by
  have exp_b6930 : exp (((693 : ℝ) / 1000)^2 / 2) ≤ (127140801 : ℝ) / 100000000 := by
    have ht : ((693 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((693 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((693 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (127140801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((693 : ℝ) / 1000)).trans (le_trans exp_b6930 (by norm_num))

lemma cosh_b6950_ub : cosh ((139 : ℝ) / 200) ≤ (127317401 : ℝ) / 100000000 := by
  have exp_b6950 : exp (((139 : ℝ) / 200)^2 / 2) ≤ (127317401 : ℝ) / 100000000 := by
    have ht : ((139 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((139 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((139 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (127317401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((139 : ℝ) / 200)).trans (le_trans exp_b6950 (by norm_num))

lemma cosh_b6965_ub : cosh ((1393 : ℝ) / 2000) ≤ (127450301 : ℝ) / 100000000 := by
  have exp_b6965 : exp (((1393 : ℝ) / 2000)^2 / 2) ≤ (127450301 : ℝ) / 100000000 := by
    have ht : ((1393 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1393 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1393 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (127450301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1393 : ℝ) / 2000)).trans (le_trans exp_b6965 (by norm_num))

lemma cosh_b6985_ub : cosh ((1397 : ℝ) / 2000) ≤ (127628201 : ℝ) / 100000000 := by
  have exp_b6985 : exp (((1397 : ℝ) / 2000)^2 / 2) ≤ (127628201 : ℝ) / 100000000 := by
    have ht : ((1397 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1397 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1397 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (127628201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1397 : ℝ) / 2000)).trans (le_trans exp_b6985 (by norm_num))

lemma cosh_b7000_ub : cosh ((7 : ℝ) / 10) ≤ (127762201 : ℝ) / 100000000 := by
  have exp_b7000 : exp (((7 : ℝ) / 10)^2 / 2) ≤ (127762201 : ℝ) / 100000000 := by
    have ht : ((7 : ℝ) / 10)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((7 : ℝ) / 10)^2 / 2) ^ m / (Nat.factorial m)) +
          (((7 : ℝ) / 10)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (127762201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((7 : ℝ) / 10)).trans (le_trans exp_b7000 (by norm_num))

lemma cosh_b7020_ub : cosh ((351 : ℝ) / 500) ≤ (127941401 : ℝ) / 100000000 := by
  have exp_b7020 : exp (((351 : ℝ) / 500)^2 / 2) ≤ (127941401 : ℝ) / 100000000 := by
    have ht : ((351 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((351 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((351 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (127941401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((351 : ℝ) / 500)).trans (le_trans exp_b7020 (by norm_num))

lemma cosh_b7040_ub : cosh ((88 : ℝ) / 125) ≤ (128121401 : ℝ) / 100000000 := by
  have exp_b7040 : exp (((88 : ℝ) / 125)^2 / 2) ≤ (128121401 : ℝ) / 100000000 := by
    have ht : ((88 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((88 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((88 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (128121401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((88 : ℝ) / 125)).trans (le_trans exp_b7040 (by norm_num))

lemma cosh_b7055_ub : cosh ((1411 : ℝ) / 2000) ≤ (128257001 : ℝ) / 100000000 := by
  have exp_b7055 : exp (((1411 : ℝ) / 2000)^2 / 2) ≤ (128257001 : ℝ) / 100000000 := by
    have ht : ((1411 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1411 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1411 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (128257001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1411 : ℝ) / 2000)).trans (le_trans exp_b7055 (by norm_num))

lemma cosh_b7075_ub : cosh ((283 : ℝ) / 400) ≤ (128438301 : ℝ) / 100000000 := by
  have exp_b7075 : exp (((283 : ℝ) / 400)^2 / 2) ≤ (128438301 : ℝ) / 100000000 := by
    have ht : ((283 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((283 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((283 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (128438301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((283 : ℝ) / 400)).trans (le_trans exp_b7075 (by norm_num))

lemma cosh_b7095_ub : cosh ((1419 : ℝ) / 2000) ≤ (128620401 : ℝ) / 100000000 := by
  have exp_b7095 : exp (((1419 : ℝ) / 2000)^2 / 2) ≤ (128620401 : ℝ) / 100000000 := by
    have ht : ((1419 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1419 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1419 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (128620401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1419 : ℝ) / 2000)).trans (le_trans exp_b7095 (by norm_num))

lemma cosh_b7110_ub : cosh ((711 : ℝ) / 1000) ≤ (128757501 : ℝ) / 100000000 := by
  have exp_b7110 : exp (((711 : ℝ) / 1000)^2 / 2) ≤ (128757501 : ℝ) / 100000000 := by
    have ht : ((711 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((711 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((711 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (128757501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((711 : ℝ) / 1000)).trans (le_trans exp_b7110 (by norm_num))

lemma cosh_b7130_ub : cosh ((713 : ℝ) / 1000) ≤ (128941001 : ℝ) / 100000000 := by
  have exp_b7130 : exp (((713 : ℝ) / 1000)^2 / 2) ≤ (128941001 : ℝ) / 100000000 := by
    have ht : ((713 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((713 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((713 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (128941001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((713 : ℝ) / 1000)).trans (le_trans exp_b7130 (by norm_num))

lemma cosh_b7150_ub : cosh ((143 : ℝ) / 200) ≤ (129125301 : ℝ) / 100000000 := by
  have exp_b7150 : exp (((143 : ℝ) / 200)^2 / 2) ≤ (129125301 : ℝ) / 100000000 := by
    have ht : ((143 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((143 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((143 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (129125301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((143 : ℝ) / 200)).trans (le_trans exp_b7150 (by norm_num))

lemma cosh_b7165_ub : cosh ((1433 : ℝ) / 2000) ≤ (129264001 : ℝ) / 100000000 := by
  have exp_b7165 : exp (((1433 : ℝ) / 2000)^2 / 2) ≤ (129264001 : ℝ) / 100000000 := by
    have ht : ((1433 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1433 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1433 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (129264001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1433 : ℝ) / 2000)).trans (le_trans exp_b7165 (by norm_num))

lemma cosh_b7185_ub : cosh ((1437 : ℝ) / 2000) ≤ (129449601 : ℝ) / 100000000 := by
  have exp_b7185 : exp (((1437 : ℝ) / 2000)^2 / 2) ≤ (129449601 : ℝ) / 100000000 := by
    have ht : ((1437 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1437 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1437 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (129449601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1437 : ℝ) / 2000)).trans (le_trans exp_b7185 (by norm_num))

lemma cosh_b7200_ub : cosh ((18 : ℝ) / 25) ≤ (129589301 : ℝ) / 100000000 := by
  have exp_b7200 : exp (((18 : ℝ) / 25)^2 / 2) ≤ (129589301 : ℝ) / 100000000 := by
    have ht : ((18 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((18 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((18 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (129589301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((18 : ℝ) / 25)).trans (le_trans exp_b7200 (by norm_num))

lemma cosh_b7220_ub : cosh ((361 : ℝ) / 500) ≤ (129776301 : ℝ) / 100000000 := by
  have exp_b7220 : exp (((361 : ℝ) / 500)^2 / 2) ≤ (129776301 : ℝ) / 100000000 := by
    have ht : ((361 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((361 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((361 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (129776301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((361 : ℝ) / 500)).trans (le_trans exp_b7220 (by norm_num))

lemma cosh_b7240_ub : cosh ((181 : ℝ) / 250) ≤ (129964101 : ℝ) / 100000000 := by
  have exp_b7240 : exp (((181 : ℝ) / 250)^2 / 2) ≤ (129964101 : ℝ) / 100000000 := by
    have ht : ((181 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((181 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((181 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (129964101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((181 : ℝ) / 250)).trans (le_trans exp_b7240 (by norm_num))

lemma cosh_b7255_ub : cosh ((1451 : ℝ) / 2000) ≤ (130105501 : ℝ) / 100000000 := by
  have exp_b7255 : exp (((1451 : ℝ) / 2000)^2 / 2) ≤ (130105501 : ℝ) / 100000000 := by
    have ht : ((1451 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1451 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1451 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (130105501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1451 : ℝ) / 2000)).trans (le_trans exp_b7255 (by norm_num))

lemma cosh_b7275_ub : cosh ((291 : ℝ) / 400) ≤ (130294701 : ℝ) / 100000000 := by
  have exp_b7275 : exp (((291 : ℝ) / 400)^2 / 2) ≤ (130294701 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((291 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((291 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (130294701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((291 : ℝ) / 400)).trans (le_trans exp_b7275 (by norm_num))

lemma cosh_b7295_ub : cosh ((1459 : ℝ) / 2000) ≤ (130484701 : ℝ) / 100000000 := by
  have exp_b7295 : exp (((1459 : ℝ) / 2000)^2 / 2) ≤ (130484701 : ℝ) / 100000000 := by
    have ht : ((1459 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1459 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1459 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (130484701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1459 : ℝ) / 2000)).trans (le_trans exp_b7295 (by norm_num))

lemma cosh_b7310_ub : cosh ((731 : ℝ) / 1000) ≤ (130627701 : ℝ) / 100000000 := by
  have exp_b7310 : exp (((731 : ℝ) / 1000)^2 / 2) ≤ (130627701 : ℝ) / 100000000 := by
    have ht : ((731 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((731 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((731 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (130627701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((731 : ℝ) / 1000)).trans (le_trans exp_b7310 (by norm_num))

lemma cosh_b7330_ub : cosh ((733 : ℝ) / 1000) ≤ (130819001 : ℝ) / 100000000 := by
  have exp_b7330 : exp (((733 : ℝ) / 1000)^2 / 2) ≤ (130819001 : ℝ) / 100000000 := by
    have ht : ((733 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((733 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((733 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (130819001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((733 : ℝ) / 1000)).trans (le_trans exp_b7330 (by norm_num))

lemma cosh_b7350_ub : cosh ((147 : ℝ) / 200) ≤ (131011201 : ℝ) / 100000000 := by
  have exp_b7350 : exp (((147 : ℝ) / 200)^2 / 2) ≤ (131011201 : ℝ) / 100000000 := by
    have ht : ((147 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((147 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((147 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (131011201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((147 : ℝ) / 200)).trans (le_trans exp_b7350 (by norm_num))

lemma cosh_b7365_ub : cosh ((1473 : ℝ) / 2000) ≤ (131155901 : ℝ) / 100000000 := by
  have exp_b7365 : exp (((1473 : ℝ) / 2000)^2 / 2) ≤ (131155901 : ℝ) / 100000000 := by
    have ht : ((1473 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1473 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1473 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (131155901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1473 : ℝ) / 2000)).trans (le_trans exp_b7365 (by norm_num))

lemma cosh_b7385_ub : cosh ((1477 : ℝ) / 2000) ≤ (131349501 : ℝ) / 100000000 := by
  have exp_b7385 : exp (((1477 : ℝ) / 2000)^2 / 2) ≤ (131349501 : ℝ) / 100000000 := by
    have ht : ((1477 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1477 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1477 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (131349501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1477 : ℝ) / 2000)).trans (le_trans exp_b7385 (by norm_num))

lemma cosh_b7400_ub : cosh ((37 : ℝ) / 50) ≤ (131495201 : ℝ) / 100000000 := by
  have exp_b7400 : exp (((37 : ℝ) / 50)^2 / 2) ≤ (131495201 : ℝ) / 100000000 := by
    have ht : ((37 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((37 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((37 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (131495201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((37 : ℝ) / 50)).trans (le_trans exp_b7400 (by norm_num))

lemma cosh_b7420_ub : cosh ((371 : ℝ) / 500) ≤ (131690201 : ℝ) / 100000000 := by
  have exp_b7420 : exp (((371 : ℝ) / 500)^2 / 2) ≤ (131690201 : ℝ) / 100000000 := by
    have ht : ((371 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((371 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((371 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (131690201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((371 : ℝ) / 500)).trans (le_trans exp_b7420 (by norm_num))

lemma cosh_b7440_ub : cosh ((93 : ℝ) / 125) ≤ (131886101 : ℝ) / 100000000 := by
  have exp_b7440 : exp (((93 : ℝ) / 125)^2 / 2) ≤ (131886101 : ℝ) / 100000000 := by
    have ht : ((93 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((93 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((93 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (131886101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((93 : ℝ) / 125)).trans (le_trans exp_b7440 (by norm_num))

lemma cosh_b7455_ub : cosh ((1491 : ℝ) / 2000) ≤ (132033501 : ℝ) / 100000000 := by
  have exp_b7455 : exp (((1491 : ℝ) / 2000)^2 / 2) ≤ (132033501 : ℝ) / 100000000 := by
    have ht : ((1491 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1491 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1491 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (132033501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1491 : ℝ) / 2000)).trans (le_trans exp_b7455 (by norm_num))

lemma cosh_b7475_ub : cosh ((299 : ℝ) / 400) ≤ (132230801 : ℝ) / 100000000 := by
  have exp_b7475 : exp (((299 : ℝ) / 400)^2 / 2) ≤ (132230801 : ℝ) / 100000000 := by
    have ht : ((299 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((299 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((299 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (132230801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((299 : ℝ) / 400)).trans (le_trans exp_b7475 (by norm_num))

lemma cosh_b7495_ub : cosh ((1499 : ℝ) / 2000) ≤ (132428901 : ℝ) / 100000000 := by
  have exp_b7495 : exp (((1499 : ℝ) / 2000)^2 / 2) ≤ (132428901 : ℝ) / 100000000 := by
    have ht : ((1499 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1499 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1499 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (132428901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1499 : ℝ) / 2000)).trans (le_trans exp_b7495 (by norm_num))

lemma cosh_b7510_ub : cosh ((751 : ℝ) / 1000) ≤ (132578001 : ℝ) / 100000000 := by
  have exp_b7510 : exp (((751 : ℝ) / 1000)^2 / 2) ≤ (132578001 : ℝ) / 100000000 := by
    have ht : ((751 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((751 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((751 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (132578001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((751 : ℝ) / 1000)).trans (le_trans exp_b7510 (by norm_num))

lemma cosh_b7530_ub : cosh ((753 : ℝ) / 1000) ≤ (132777501 : ℝ) / 100000000 := by
  have exp_b7530 : exp (((753 : ℝ) / 1000)^2 / 2) ≤ (132777501 : ℝ) / 100000000 := by
    have ht : ((753 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((753 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((753 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (132777501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((753 : ℝ) / 1000)).trans (le_trans exp_b7530 (by norm_num))

lemma cosh_b7550_ub : cosh ((151 : ℝ) / 200) ≤ (132977901 : ℝ) / 100000000 := by
  have exp_b7550 : exp (((151 : ℝ) / 200)^2 / 2) ≤ (132977901 : ℝ) / 100000000 := by
    have ht : ((151 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((151 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((151 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (132977901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((151 : ℝ) / 200)).trans (le_trans exp_b7550 (by norm_num))

lemma cosh_b7565_ub : cosh ((1513 : ℝ) / 2000) ≤ (133128701 : ℝ) / 100000000 := by
  have exp_b7565 : exp (((1513 : ℝ) / 2000)^2 / 2) ≤ (133128701 : ℝ) / 100000000 := by
    have ht : ((1513 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1513 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1513 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (133128701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1513 : ℝ) / 2000)).trans (le_trans exp_b7565 (by norm_num))

lemma cosh_b7585_ub : cosh ((1517 : ℝ) / 2000) ≤ (133330601 : ℝ) / 100000000 := by
  have exp_b7585 : exp (((1517 : ℝ) / 2000)^2 / 2) ≤ (133330601 : ℝ) / 100000000 := by
    have ht : ((1517 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1517 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1517 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (133330601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1517 : ℝ) / 2000)).trans (le_trans exp_b7585 (by norm_num))

lemma cosh_b7600_ub : cosh ((19 : ℝ) / 25) ≤ (133482501 : ℝ) / 100000000 := by
  have exp_b7600 : exp (((19 : ℝ) / 25)^2 / 2) ≤ (133482501 : ℝ) / 100000000 := by
    have ht : ((19 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((19 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((19 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (133482501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((19 : ℝ) / 25)).trans (le_trans exp_b7600 (by norm_num))

lemma cosh_b7620_ub : cosh ((381 : ℝ) / 500) ≤ (133685801 : ℝ) / 100000000 := by
  have exp_b7620 : exp (((381 : ℝ) / 500)^2 / 2) ≤ (133685801 : ℝ) / 100000000 := by
    have ht : ((381 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((381 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((381 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (133685801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((381 : ℝ) / 500)).trans (le_trans exp_b7620 (by norm_num))

lemma cosh_b7640_ub : cosh ((191 : ℝ) / 250) ≤ (133890001 : ℝ) / 100000000 := by
  have exp_b7640 : exp (((191 : ℝ) / 250)^2 / 2) ≤ (133890001 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((191 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((191 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (133890001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((191 : ℝ) / 250)).trans (le_trans exp_b7640 (by norm_num))

lemma cosh_b7655_ub : cosh ((1531 : ℝ) / 2000) ≤ (134043701 : ℝ) / 100000000 := by
  have exp_b7655 : exp (((1531 : ℝ) / 2000)^2 / 2) ≤ (134043701 : ℝ) / 100000000 := by
    have ht : ((1531 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1531 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1531 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (134043701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1531 : ℝ) / 2000)).trans (le_trans exp_b7655 (by norm_num))

lemma cosh_b7675_ub : cosh ((307 : ℝ) / 400) ≤ (134249301 : ℝ) / 100000000 := by
  have exp_b7675 : exp (((307 : ℝ) / 400)^2 / 2) ≤ (134249301 : ℝ) / 100000000 := by
    have ht : ((307 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((307 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((307 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (134249301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((307 : ℝ) / 400)).trans (le_trans exp_b7675 (by norm_num))

lemma cosh_b7695_ub : cosh ((1539 : ℝ) / 2000) ≤ (134455801 : ℝ) / 100000000 := by
  have exp_b7695 : exp (((1539 : ℝ) / 2000)^2 / 2) ≤ (134455801 : ℝ) / 100000000 := by
    have ht : ((1539 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1539 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1539 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (134455801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1539 : ℝ) / 2000)).trans (le_trans exp_b7695 (by norm_num))

lemma cosh_b7710_ub : cosh ((771 : ℝ) / 1000) ≤ (134611301 : ℝ) / 100000000 := by
  have exp_b7710 : exp (((771 : ℝ) / 1000)^2 / 2) ≤ (134611301 : ℝ) / 100000000 := by
    have ht : ((771 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((771 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((771 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (134611301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((771 : ℝ) / 1000)).trans (le_trans exp_b7710 (by norm_num))

lemma cosh_b7730_ub : cosh ((773 : ℝ) / 1000) ≤ (134819301 : ℝ) / 100000000 := by
  have exp_b7730 : exp (((773 : ℝ) / 1000)^2 / 2) ≤ (134819301 : ℝ) / 100000000 := by
    have ht : ((773 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((773 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((773 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (134819301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((773 : ℝ) / 1000)).trans (le_trans exp_b7730 (by norm_num))

lemma cosh_b7750_ub : cosh ((31 : ℝ) / 40) ≤ (135028101 : ℝ) / 100000000 := by
  have exp_b7750 : exp (((31 : ℝ) / 40)^2 / 2) ≤ (135028101 : ℝ) / 100000000 := by
    have ht : ((31 : ℝ) / 40)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((31 : ℝ) / 40)^2 / 2) ^ m / (Nat.factorial m)) +
          (((31 : ℝ) / 40)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (135028101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((31 : ℝ) / 40)).trans (le_trans exp_b7750 (by norm_num))

lemma cosh_b7765_ub : cosh ((1553 : ℝ) / 2000) ≤ (135185301 : ℝ) / 100000000 := by
  have exp_b7765 : exp (((1553 : ℝ) / 2000)^2 / 2) ≤ (135185301 : ℝ) / 100000000 := by
    have ht : ((1553 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1553 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1553 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (135185301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1553 : ℝ) / 2000)).trans (le_trans exp_b7765 (by norm_num))

lemma cosh_b7785_ub : cosh ((1557 : ℝ) / 2000) ≤ (135395701 : ℝ) / 100000000 := by
  have exp_b7785 : exp (((1557 : ℝ) / 2000)^2 / 2) ≤ (135395701 : ℝ) / 100000000 := by
    have ht : ((1557 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1557 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1557 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (135395701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1557 : ℝ) / 2000)).trans (le_trans exp_b7785 (by norm_num))

lemma cosh_b7800_ub : cosh ((39 : ℝ) / 50) ≤ (135554101 : ℝ) / 100000000 := by
  have exp_b7800 : exp (((39 : ℝ) / 50)^2 / 2) ≤ (135554101 : ℝ) / 100000000 := by
    have ht : ((39 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((39 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((39 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (135554101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((39 : ℝ) / 50)).trans (le_trans exp_b7800 (by norm_num))

lemma cosh_b7820_ub : cosh ((391 : ℝ) / 500) ≤ (135766001 : ℝ) / 100000000 := by
  have exp_b7820 : exp (((391 : ℝ) / 500)^2 / 2) ≤ (135766001 : ℝ) / 100000000 := by
    have ht : ((391 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((391 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((391 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (135766001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((391 : ℝ) / 500)).trans (le_trans exp_b7820 (by norm_num))

lemma cosh_b7840_ub : cosh ((98 : ℝ) / 125) ≤ (135978701 : ℝ) / 100000000 := by
  have exp_b7840 : exp (((98 : ℝ) / 125)^2 / 2) ≤ (135978701 : ℝ) / 100000000 := by
    have ht : ((98 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((98 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((98 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (135978701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((98 : ℝ) / 125)).trans (le_trans exp_b7840 (by norm_num))

lemma cosh_b7855_ub : cosh ((1571 : ℝ) / 2000) ≤ (136138901 : ℝ) / 100000000 := by
  have exp_b7855 : exp (((1571 : ℝ) / 2000)^2 / 2) ≤ (136138901 : ℝ) / 100000000 := by
    have ht : ((1571 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1571 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1571 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (136138901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1571 : ℝ) / 2000)).trans (le_trans exp_b7855 (by norm_num))

lemma cosh_b7875_ub : cosh ((63 : ℝ) / 80) ≤ (136353201 : ℝ) / 100000000 := by
  have exp_b7875 : exp (((63 : ℝ) / 80)^2 / 2) ≤ (136353201 : ℝ) / 100000000 := by
    have ht : ((63 : ℝ) / 80)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((63 : ℝ) / 80)^2 / 2) ^ m / (Nat.factorial m)) +
          (((63 : ℝ) / 80)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (136353201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((63 : ℝ) / 80)).trans (le_trans exp_b7875 (by norm_num))

lemma cosh_b7895_ub : cosh ((1579 : ℝ) / 2000) ≤ (136568401 : ℝ) / 100000000 := by
  have exp_b7895 : exp (((1579 : ℝ) / 2000)^2 / 2) ≤ (136568401 : ℝ) / 100000000 := by
    have ht : ((1579 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1579 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1579 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (136568401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1579 : ℝ) / 2000)).trans (le_trans exp_b7895 (by norm_num))

lemma cosh_b7910_ub : cosh ((791 : ℝ) / 1000) ≤ (136730401 : ℝ) / 100000000 := by
  have exp_b7910 : exp (((791 : ℝ) / 1000)^2 / 2) ≤ (136730401 : ℝ) / 100000000 := by
    have ht : ((791 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((791 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((791 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (136730401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((791 : ℝ) / 1000)).trans (le_trans exp_b7910 (by norm_num))

lemma cosh_b7930_ub : cosh ((793 : ℝ) / 1000) ≤ (136947101 : ℝ) / 100000000 := by
  have exp_b7930 : exp (((793 : ℝ) / 1000)^2 / 2) ≤ (136947101 : ℝ) / 100000000 := by
    have ht : ((793 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((793 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((793 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (136947101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((793 : ℝ) / 1000)).trans (le_trans exp_b7930 (by norm_num))

lemma cosh_b7950_ub : cosh ((159 : ℝ) / 200) ≤ (137164801 : ℝ) / 100000000 := by
  have exp_b7950 : exp (((159 : ℝ) / 200)^2 / 2) ≤ (137164801 : ℝ) / 100000000 := by
    have ht : ((159 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((159 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((159 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (137164801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((159 : ℝ) / 200)).trans (le_trans exp_b7950 (by norm_num))

lemma cosh_b7965_ub : cosh ((1593 : ℝ) / 2000) ≤ (137328601 : ℝ) / 100000000 := by
  have exp_b7965 : exp (((1593 : ℝ) / 2000)^2 / 2) ≤ (137328601 : ℝ) / 100000000 := by
    have ht : ((1593 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1593 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1593 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (137328601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1593 : ℝ) / 2000)).trans (le_trans exp_b7965 (by norm_num))

lemma cosh_b7985_ub : cosh ((1597 : ℝ) / 2000) ≤ (137547801 : ℝ) / 100000000 := by
  have exp_b7985 : exp (((1597 : ℝ) / 2000)^2 / 2) ≤ (137547801 : ℝ) / 100000000 := by
    have ht : ((1597 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1597 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1597 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (137547801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1597 : ℝ) / 2000)).trans (le_trans exp_b7985 (by norm_num))

lemma cosh_b8000_ub : cosh ((4 : ℝ) / 5) ≤ (137712801 : ℝ) / 100000000 := by
  have exp_b8000 : exp (((4 : ℝ) / 5)^2 / 2) ≤ (137712801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 5)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((4 : ℝ) / 5)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 5)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (137712801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 5)).trans (le_trans exp_b8000 (by norm_num))

lemma cosh_b8020_ub : cosh ((401 : ℝ) / 500) ≤ (137933601 : ℝ) / 100000000 := by
  have exp_b8020 : exp (((401 : ℝ) / 500)^2 / 2) ≤ (137933601 : ℝ) / 100000000 := by
    have ht : ((401 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((401 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((401 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (137933601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((401 : ℝ) / 500)).trans (le_trans exp_b8020 (by norm_num))

lemma cosh_b8040_ub : cosh ((201 : ℝ) / 250) ≤ (138155301 : ℝ) / 100000000 := by
  have exp_b8040 : exp (((201 : ℝ) / 250)^2 / 2) ≤ (138155301 : ℝ) / 100000000 := by
    have ht : ((201 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((201 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((201 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (138155301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((201 : ℝ) / 250)).trans (le_trans exp_b8040 (by norm_num))

lemma cosh_b8055_ub : cosh ((1611 : ℝ) / 2000) ≤ (138322201 : ℝ) / 100000000 := by
  have exp_b8055 : exp (((1611 : ℝ) / 2000)^2 / 2) ≤ (138322201 : ℝ) / 100000000 := by
    have ht : ((1611 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1611 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1611 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (138322201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1611 : ℝ) / 2000)).trans (le_trans exp_b8055 (by norm_num))

lemma cosh_b8075_ub : cosh ((323 : ℝ) / 400) ≤ (138545501 : ℝ) / 100000000 := by
  have exp_b8075 : exp (((323 : ℝ) / 400)^2 / 2) ≤ (138545501 : ℝ) / 100000000 := by
    have ht : ((323 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((323 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((323 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (138545501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((323 : ℝ) / 400)).trans (le_trans exp_b8075 (by norm_num))

lemma cosh_b8095_ub : cosh ((1619 : ℝ) / 2000) ≤ (138769701 : ℝ) / 100000000 := by
  have exp_b8095 : exp (((1619 : ℝ) / 2000)^2 / 2) ≤ (138769701 : ℝ) / 100000000 := by
    have ht : ((1619 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1619 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1619 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (138769701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1619 : ℝ) / 2000)).trans (le_trans exp_b8095 (by norm_num))

lemma cosh_b8110_ub : cosh ((811 : ℝ) / 1000) ≤ (138938501 : ℝ) / 100000000 := by
  have exp_b8110 : exp (((811 : ℝ) / 1000)^2 / 2) ≤ (138938501 : ℝ) / 100000000 := by
    have ht : ((811 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((811 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((811 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (138938501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((811 : ℝ) / 1000)).trans (le_trans exp_b8110 (by norm_num))

lemma cosh_b8130_ub : cosh ((813 : ℝ) / 1000) ≤ (139164301 : ℝ) / 100000000 := by
  have exp_b8130 : exp (((813 : ℝ) / 1000)^2 / 2) ≤ (139164301 : ℝ) / 100000000 := by
    have ht : ((813 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((813 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((813 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (139164301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((813 : ℝ) / 1000)).trans (le_trans exp_b8130 (by norm_num))

lemma cosh_b8150_ub : cosh ((163 : ℝ) / 200) ≤ (139391001 : ℝ) / 100000000 := by
  have exp_b8150 : exp (((163 : ℝ) / 200)^2 / 2) ≤ (139391001 : ℝ) / 100000000 := by
    have ht : ((163 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((163 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((163 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (139391001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((163 : ℝ) / 200)).trans (le_trans exp_b8150 (by norm_num))

lemma cosh_b8165_ub : cosh ((1633 : ℝ) / 2000) ≤ (139561701 : ℝ) / 100000000 := by
  have exp_b8165 : exp (((1633 : ℝ) / 2000)^2 / 2) ≤ (139561701 : ℝ) / 100000000 := by
    have ht : ((1633 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1633 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1633 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (139561701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1633 : ℝ) / 2000)).trans (le_trans exp_b8165 (by norm_num))

lemma cosh_b8185_ub : cosh ((1637 : ℝ) / 2000) ≤ (139790101 : ℝ) / 100000000 := by
  have exp_b8185 : exp (((1637 : ℝ) / 2000)^2 / 2) ≤ (139790101 : ℝ) / 100000000 := by
    have ht : ((1637 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1637 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1637 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (139790101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1637 : ℝ) / 2000)).trans (le_trans exp_b8185 (by norm_num))

lemma cosh_b8200_ub : cosh ((41 : ℝ) / 50) ≤ (139961901 : ℝ) / 100000000 := by
  have exp_b8200 : exp (((41 : ℝ) / 50)^2 / 2) ≤ (139961901 : ℝ) / 100000000 := by
    have ht : ((41 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((41 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((41 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (139961901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((41 : ℝ) / 50)).trans (le_trans exp_b8200 (by norm_num))

lemma cosh_b8220_ub : cosh ((411 : ℝ) / 500) ≤ (140191901 : ℝ) / 100000000 := by
  have exp_b8220 : exp (((411 : ℝ) / 500)^2 / 2) ≤ (140191901 : ℝ) / 100000000 := by
    have ht : ((411 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((411 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((411 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (140191901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((411 : ℝ) / 500)).trans (le_trans exp_b8220 (by norm_num))

lemma cosh_b8240_ub : cosh ((103 : ℝ) / 125) ≤ (140422901 : ℝ) / 100000000 := by
  have exp_b8240 : exp (((103 : ℝ) / 125)^2 / 2) ≤ (140422901 : ℝ) / 100000000 := by
    have ht : ((103 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((103 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((103 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (140422901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((103 : ℝ) / 125)).trans (le_trans exp_b8240 (by norm_num))

lemma cosh_b8255_ub : cosh ((1651 : ℝ) / 2000) ≤ (140596701 : ℝ) / 100000000 := by
  have exp_b8255 : exp (((1651 : ℝ) / 2000)^2 / 2) ≤ (140596701 : ℝ) / 100000000 := by
    have ht : ((1651 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1651 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1651 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (140596701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1651 : ℝ) / 2000)).trans (le_trans exp_b8255 (by norm_num))

lemma cosh_b8275_ub : cosh ((331 : ℝ) / 400) ≤ (140829301 : ℝ) / 100000000 := by
  have exp_b8275 : exp (((331 : ℝ) / 400)^2 / 2) ≤ (140829301 : ℝ) / 100000000 := by
    have ht : ((331 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((331 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((331 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (140829301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((331 : ℝ) / 400)).trans (le_trans exp_b8275 (by norm_num))

lemma cosh_b8295_ub : cosh ((1659 : ℝ) / 2000) ≤ (141062901 : ℝ) / 100000000 := by
  have exp_b8295 : exp (((1659 : ℝ) / 2000)^2 / 2) ≤ (141062901 : ℝ) / 100000000 := by
    have ht : ((1659 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1659 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1659 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (141062901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1659 : ℝ) / 2000)).trans (le_trans exp_b8295 (by norm_num))

lemma cosh_b8310_ub : cosh ((831 : ℝ) / 1000) ≤ (141238701 : ℝ) / 100000000 := by
  have exp_b8310 : exp (((831 : ℝ) / 1000)^2 / 2) ≤ (141238701 : ℝ) / 100000000 := by
    have ht : ((831 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((831 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((831 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (141238701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((831 : ℝ) / 1000)).trans (le_trans exp_b8310 (by norm_num))

lemma cosh_b8330_ub : cosh ((833 : ℝ) / 1000) ≤ (141473901 : ℝ) / 100000000 := by
  have exp_b8330 : exp (((833 : ℝ) / 1000)^2 / 2) ≤ (141473901 : ℝ) / 100000000 := by
    have ht : ((833 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((833 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((833 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (141473901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((833 : ℝ) / 1000)).trans (le_trans exp_b8330 (by norm_num))

lemma cosh_b8350_ub : cosh ((167 : ℝ) / 200) ≤ (141710001 : ℝ) / 100000000 := by
  have exp_b8350 : exp (((167 : ℝ) / 200)^2 / 2) ≤ (141710001 : ℝ) / 100000000 := by
    have ht : ((167 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((167 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((167 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (141710001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((167 : ℝ) / 200)).trans (le_trans exp_b8350 (by norm_num))

lemma cosh_b8365_ub : cosh ((1673 : ℝ) / 2000) ≤ (141887801 : ℝ) / 100000000 := by
  have exp_b8365 : exp (((1673 : ℝ) / 2000)^2 / 2) ≤ (141887801 : ℝ) / 100000000 := by
    have ht : ((1673 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1673 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1673 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (141887801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1673 : ℝ) / 2000)).trans (le_trans exp_b8365 (by norm_num))

lemma cosh_b8385_ub : cosh ((1677 : ℝ) / 2000) ≤ (142125701 : ℝ) / 100000000 := by
  have exp_b8385 : exp (((1677 : ℝ) / 2000)^2 / 2) ≤ (142125701 : ℝ) / 100000000 := by
    have ht : ((1677 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1677 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1677 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (142125701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1677 : ℝ) / 2000)).trans (le_trans exp_b8385 (by norm_num))

lemma cosh_b8400_ub : cosh ((21 : ℝ) / 25) ≤ (142304701 : ℝ) / 100000000 := by
  have exp_b8400 : exp (((21 : ℝ) / 25)^2 / 2) ≤ (142304701 : ℝ) / 100000000 := by
    have ht : ((21 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((21 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((21 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (142304701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((21 : ℝ) / 25)).trans (le_trans exp_b8400 (by norm_num))

lemma cosh_b8420_ub : cosh ((421 : ℝ) / 500) ≤ (142544301 : ℝ) / 100000000 := by
  have exp_b8420 : exp (((421 : ℝ) / 500)^2 / 2) ≤ (142544301 : ℝ) / 100000000 := by
    have ht : ((421 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((421 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((421 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (142544301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((421 : ℝ) / 500)).trans (le_trans exp_b8420 (by norm_num))

lemma cosh_b8440_ub : cosh ((211 : ℝ) / 250) ≤ (142784801 : ℝ) / 100000000 := by
  have exp_b8440 : exp (((211 : ℝ) / 250)^2 / 2) ≤ (142784801 : ℝ) / 100000000 := by
    have ht : ((211 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((211 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((211 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (142784801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((211 : ℝ) / 250)).trans (le_trans exp_b8440 (by norm_num))

lemma cosh_b8455_ub : cosh ((1691 : ℝ) / 2000) ≤ (142965801 : ℝ) / 100000000 := by
  have exp_b8455 : exp (((1691 : ℝ) / 2000)^2 / 2) ≤ (142965801 : ℝ) / 100000000 := by
    have ht : ((1691 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1691 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1691 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (142965801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1691 : ℝ) / 2000)).trans (le_trans exp_b8455 (by norm_num))

lemma cosh_b8475_ub : cosh ((339 : ℝ) / 400) ≤ (143208101 : ℝ) / 100000000 := by
  have exp_b8475 : exp (((339 : ℝ) / 400)^2 / 2) ≤ (143208101 : ℝ) / 100000000 := by
    have ht : ((339 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((339 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((339 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (143208101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((339 : ℝ) / 400)).trans (le_trans exp_b8475 (by norm_num))

lemma cosh_b8495_ub : cosh ((1699 : ℝ) / 2000) ≤ (143451301 : ℝ) / 100000000 := by
  have exp_b8495 : exp (((1699 : ℝ) / 2000)^2 / 2) ≤ (143451301 : ℝ) / 100000000 := by
    have ht : ((1699 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1699 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1699 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (143451301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1699 : ℝ) / 2000)).trans (le_trans exp_b8495 (by norm_num))

lemma cosh_b8510_ub : cosh ((851 : ℝ) / 1000) ≤ (143634401 : ℝ) / 100000000 := by
  have exp_b8510 : exp (((851 : ℝ) / 1000)^2 / 2) ≤ (143634401 : ℝ) / 100000000 := by
    have ht : ((851 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((851 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((851 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (143634401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((851 : ℝ) / 1000)).trans (le_trans exp_b8510 (by norm_num))

lemma cosh_b8530_ub : cosh ((853 : ℝ) / 1000) ≤ (143879301 : ℝ) / 100000000 := by
  have exp_b8530 : exp (((853 : ℝ) / 1000)^2 / 2) ≤ (143879301 : ℝ) / 100000000 := by
    have ht : ((853 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((853 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((853 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (143879301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((853 : ℝ) / 1000)).trans (le_trans exp_b8530 (by norm_num))

lemma cosh_b8550_ub : cosh ((171 : ℝ) / 200) ≤ (144125301 : ℝ) / 100000000 := by
  have exp_b8550 : exp (((171 : ℝ) / 200)^2 / 2) ≤ (144125301 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((171 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((171 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (144125301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((171 : ℝ) / 200)).trans (le_trans exp_b8550 (by norm_num))

lemma cosh_b8565_ub : cosh ((1713 : ℝ) / 2000) ≤ (144310401 : ℝ) / 100000000 := by
  have exp_b8565 : exp (((1713 : ℝ) / 2000)^2 / 2) ≤ (144310401 : ℝ) / 100000000 := by
    have ht : ((1713 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1713 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1713 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (144310401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1713 : ℝ) / 2000)).trans (le_trans exp_b8565 (by norm_num))

lemma cosh_b8585_ub : cosh ((1717 : ℝ) / 2000) ≤ (144558101 : ℝ) / 100000000 := by
  have exp_b8585 : exp (((1717 : ℝ) / 2000)^2 / 2) ≤ (144558101 : ℝ) / 100000000 := by
    have ht : ((1717 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1717 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1717 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (144558101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1717 : ℝ) / 2000)).trans (le_trans exp_b8585 (by norm_num))

lemma cosh_b8600_ub : cosh ((43 : ℝ) / 50) ≤ (144744601 : ℝ) / 100000000 := by
  have exp_b8600 : exp (((43 : ℝ) / 50)^2 / 2) ≤ (144744601 : ℝ) / 100000000 := by
    have ht : ((43 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((43 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((43 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (144744601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((43 : ℝ) / 50)).trans (le_trans exp_b8600 (by norm_num))

lemma cosh_b8620_ub : cosh ((431 : ℝ) / 500) ≤ (144994001 : ℝ) / 100000000 := by
  have exp_b8620 : exp (((431 : ℝ) / 500)^2 / 2) ≤ (144994001 : ℝ) / 100000000 := by
    have ht : ((431 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((431 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((431 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (144994001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((431 : ℝ) / 500)).trans (le_trans exp_b8620 (by norm_num))

lemma cosh_b8640_ub : cosh ((108 : ℝ) / 125) ≤ (145244501 : ℝ) / 100000000 := by
  have exp_b8640 : exp (((108 : ℝ) / 125)^2 / 2) ≤ (145244501 : ℝ) / 100000000 := by
    have ht : ((108 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((108 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((108 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (145244501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((108 : ℝ) / 125)).trans (le_trans exp_b8640 (by norm_num))

lemma cosh_b8655_ub : cosh ((1731 : ℝ) / 2000) ≤ (145433001 : ℝ) / 100000000 := by
  have exp_b8655 : exp (((1731 : ℝ) / 2000)^2 / 2) ≤ (145433001 : ℝ) / 100000000 := by
    have ht : ((1731 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1731 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1731 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (145433001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1731 : ℝ) / 2000)).trans (le_trans exp_b8655 (by norm_num))

lemma cosh_b8675_ub : cosh ((347 : ℝ) / 400) ≤ (145685301 : ℝ) / 100000000 := by
  have exp_b8675 : exp (((347 : ℝ) / 400)^2 / 2) ≤ (145685301 : ℝ) / 100000000 := by
    have ht : ((347 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((347 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((347 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (145685301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((347 : ℝ) / 400)).trans (le_trans exp_b8675 (by norm_num))

lemma cosh_b8695_ub : cosh ((1739 : ℝ) / 2000) ≤ (145938601 : ℝ) / 100000000 := by
  have exp_b8695 : exp (((1739 : ℝ) / 2000)^2 / 2) ≤ (145938601 : ℝ) / 100000000 := by
    have ht : ((1739 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1739 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1739 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (145938601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1739 : ℝ) / 2000)).trans (le_trans exp_b8695 (by norm_num))

lemma cosh_b8710_ub : cosh ((871 : ℝ) / 1000) ≤ (146129201 : ℝ) / 100000000 := by
  have exp_b8710 : exp (((871 : ℝ) / 1000)^2 / 2) ≤ (146129201 : ℝ) / 100000000 := by
    have ht : ((871 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((871 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((871 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (146129201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((871 : ℝ) / 1000)).trans (le_trans exp_b8710 (by norm_num))

lemma cosh_b8730_ub : cosh ((873 : ℝ) / 1000) ≤ (146384301 : ℝ) / 100000000 := by
  have exp_b8730 : exp (((873 : ℝ) / 1000)^2 / 2) ≤ (146384301 : ℝ) / 100000000 := by
    have ht : ((873 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((873 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((873 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (146384301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((873 : ℝ) / 1000)).trans (le_trans exp_b8730 (by norm_num))

lemma cosh_b8750_ub : cosh ((7 : ℝ) / 8) ≤ (146640401 : ℝ) / 100000000 := by
  have exp_b8750 : exp (((7 : ℝ) / 8)^2 / 2) ≤ (146640401 : ℝ) / 100000000 := by
    have ht : ((7 : ℝ) / 8)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((7 : ℝ) / 8)^2 / 2) ^ m / (Nat.factorial m)) +
          (((7 : ℝ) / 8)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (146640401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((7 : ℝ) / 8)).trans (le_trans exp_b8750 (by norm_num))

lemma cosh_b8765_ub : cosh ((1753 : ℝ) / 2000) ≤ (146833101 : ℝ) / 100000000 := by
  have exp_b8765 : exp (((1753 : ℝ) / 2000)^2 / 2) ≤ (146833101 : ℝ) / 100000000 := by
    have ht : ((1753 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1753 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1753 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (146833101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1753 : ℝ) / 2000)).trans (le_trans exp_b8765 (by norm_num))

lemma cosh_b8785_ub : cosh ((1757 : ℝ) / 2000) ≤ (147091001 : ℝ) / 100000000 := by
  have exp_b8785 : exp (((1757 : ℝ) / 2000)^2 / 2) ≤ (147091001 : ℝ) / 100000000 := by
    have ht : ((1757 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1757 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1757 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (147091001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1757 : ℝ) / 2000)).trans (le_trans exp_b8785 (by norm_num))

lemma cosh_b8800_ub : cosh ((22 : ℝ) / 25) ≤ (147285201 : ℝ) / 100000000 := by
  have exp_b8800 : exp (((22 : ℝ) / 25)^2 / 2) ≤ (147285201 : ℝ) / 100000000 := by
    have ht : ((22 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((22 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((22 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (147285201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((22 : ℝ) / 25)).trans (le_trans exp_b8800 (by norm_num))

lemma cosh_b8820_ub : cosh ((441 : ℝ) / 500) ≤ (147544901 : ℝ) / 100000000 := by
  have exp_b8820 : exp (((441 : ℝ) / 500)^2 / 2) ≤ (147544901 : ℝ) / 100000000 := by
    have ht : ((441 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((441 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((441 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (147544901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((441 : ℝ) / 500)).trans (le_trans exp_b8820 (by norm_num))

lemma cosh_b8840_ub : cosh ((221 : ℝ) / 250) ≤ (147805701 : ℝ) / 100000000 := by
  have exp_b8840 : exp (((221 : ℝ) / 250)^2 / 2) ≤ (147805701 : ℝ) / 100000000 := by
    have ht : ((221 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((221 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((221 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (147805701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((221 : ℝ) / 250)).trans (le_trans exp_b8840 (by norm_num))

lemma cosh_b8855_ub : cosh ((1771 : ℝ) / 2000) ≤ (148002001 : ℝ) / 100000000 := by
  have exp_b8855 : exp (((1771 : ℝ) / 2000)^2 / 2) ≤ (148002001 : ℝ) / 100000000 := by
    have ht : ((1771 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1771 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1771 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (148002001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1771 : ℝ) / 2000)).trans (le_trans exp_b8855 (by norm_num))

lemma cosh_b8875_ub : cosh ((71 : ℝ) / 80) ≤ (148264601 : ℝ) / 100000000 := by
  have exp_b8875 : exp (((71 : ℝ) / 80)^2 / 2) ≤ (148264601 : ℝ) / 100000000 := by
    have ht : ((71 : ℝ) / 80)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((71 : ℝ) / 80)^2 / 2) ^ m / (Nat.factorial m)) +
          (((71 : ℝ) / 80)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (148264601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((71 : ℝ) / 80)).trans (le_trans exp_b8875 (by norm_num))

lemma cosh_b8895_ub : cosh ((1779 : ℝ) / 2000) ≤ (148528301 : ℝ) / 100000000 := by
  have exp_b8895 : exp (((1779 : ℝ) / 2000)^2 / 2) ≤ (148528301 : ℝ) / 100000000 := by
    have ht : ((1779 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1779 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1779 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (148528301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1779 : ℝ) / 2000)).trans (le_trans exp_b8895 (by norm_num))

lemma cosh_b8910_ub : cosh ((891 : ℝ) / 1000) ≤ (148726801 : ℝ) / 100000000 := by
  have exp_b8910 : exp (((891 : ℝ) / 1000)^2 / 2) ≤ (148726801 : ℝ) / 100000000 := by
    have ht : ((891 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((891 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((891 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (148726801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((891 : ℝ) / 1000)).trans (le_trans exp_b8910 (by norm_num))

lemma cosh_b8930_ub : cosh ((893 : ℝ) / 1000) ≤ (148992401 : ℝ) / 100000000 := by
  have exp_b8930 : exp (((893 : ℝ) / 1000)^2 / 2) ≤ (148992401 : ℝ) / 100000000 := by
    have ht : ((893 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((893 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((893 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (148992401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((893 : ℝ) / 1000)).trans (le_trans exp_b8930 (by norm_num))

lemma cosh_b8950_ub : cosh ((179 : ℝ) / 200) ≤ (149259001 : ℝ) / 100000000 := by
  have exp_b8950 : exp (((179 : ℝ) / 200)^2 / 2) ≤ (149259001 : ℝ) / 100000000 := by
    have ht : ((179 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((179 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((179 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (149259001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((179 : ℝ) / 200)).trans (le_trans exp_b8950 (by norm_num))

lemma cosh_b8965_ub : cosh ((1793 : ℝ) / 2000) ≤ (149459701 : ℝ) / 100000000 := by
  have exp_b8965 : exp (((1793 : ℝ) / 2000)^2 / 2) ≤ (149459701 : ℝ) / 100000000 := by
    have ht : ((1793 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1793 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1793 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (149459701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1793 : ℝ) / 2000)).trans (le_trans exp_b8965 (by norm_num))

lemma cosh_b8985_ub : cosh ((1797 : ℝ) / 2000) ≤ (149728201 : ℝ) / 100000000 := by
  have exp_b8985 : exp (((1797 : ℝ) / 2000)^2 / 2) ≤ (149728201 : ℝ) / 100000000 := by
    have ht : ((1797 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1797 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1797 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (149728201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1797 : ℝ) / 2000)).trans (le_trans exp_b8985 (by norm_num))

lemma cosh_b9000_ub : cosh ((9 : ℝ) / 10) ≤ (149930301 : ℝ) / 100000000 := by
  have exp_b9000 : exp (((9 : ℝ) / 10)^2 / 2) ≤ (149930301 : ℝ) / 100000000 := by
    have ht : ((9 : ℝ) / 10)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((9 : ℝ) / 10)^2 / 2) ^ m / (Nat.factorial m)) +
          (((9 : ℝ) / 10)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (149930301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((9 : ℝ) / 10)).trans (le_trans exp_b9000 (by norm_num))

lemma cosh_b9020_ub : cosh ((451 : ℝ) / 500) ≤ (150200701 : ℝ) / 100000000 := by
  have exp_b9020 : exp (((451 : ℝ) / 500)^2 / 2) ≤ (150200701 : ℝ) / 100000000 := by
    have ht : ((451 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((451 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((451 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (150200701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((451 : ℝ) / 500)).trans (le_trans exp_b9020 (by norm_num))

lemma cosh_b9040_ub : cosh ((113 : ℝ) / 125) ≤ (150472201 : ℝ) / 100000000 := by
  have exp_b9040 : exp (((113 : ℝ) / 125)^2 / 2) ≤ (150472201 : ℝ) / 100000000 := by
    have ht : ((113 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((113 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((113 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (150472201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((113 : ℝ) / 125)).trans (le_trans exp_b9040 (by norm_num))

lemma cosh_b9055_ub : cosh ((1811 : ℝ) / 2000) ≤ (150676601 : ℝ) / 100000000 := by
  have exp_b9055 : exp (((1811 : ℝ) / 2000)^2 / 2) ≤ (150676601 : ℝ) / 100000000 := by
    have ht : ((1811 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1811 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1811 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (150676601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1811 : ℝ) / 2000)).trans (le_trans exp_b9055 (by norm_num))

lemma cosh_b9075_ub : cosh ((363 : ℝ) / 400) ≤ (150950001 : ℝ) / 100000000 := by
  have exp_b9075 : exp (((363 : ℝ) / 400)^2 / 2) ≤ (150950001 : ℝ) / 100000000 := by
    have ht : ((363 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((363 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((363 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (150950001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((363 : ℝ) / 400)).trans (le_trans exp_b9075 (by norm_num))

lemma cosh_b9095_ub : cosh ((1819 : ℝ) / 2000) ≤ (151224501 : ℝ) / 100000000 := by
  have exp_b9095 : exp (((1819 : ℝ) / 2000)^2 / 2) ≤ (151224501 : ℝ) / 100000000 := by
    have ht : ((1819 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1819 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1819 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (151224501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1819 : ℝ) / 2000)).trans (le_trans exp_b9095 (by norm_num))

lemma cosh_b9110_ub : cosh ((911 : ℝ) / 1000) ≤ (151431101 : ℝ) / 100000000 := by
  have exp_b9110 : exp (((911 : ℝ) / 1000)^2 / 2) ≤ (151431101 : ℝ) / 100000000 := by
    have ht : ((911 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((911 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((911 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (151431101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((911 : ℝ) / 1000)).trans (le_trans exp_b9110 (by norm_num))

lemma cosh_b9130_ub : cosh ((913 : ℝ) / 1000) ≤ (151707601 : ℝ) / 100000000 := by
  have exp_b9130 : exp (((913 : ℝ) / 1000)^2 / 2) ≤ (151707601 : ℝ) / 100000000 := by
    have ht : ((913 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((913 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((913 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (151707601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((913 : ℝ) / 1000)).trans (le_trans exp_b9130 (by norm_num))

lemma cosh_b9150_ub : cosh ((183 : ℝ) / 200) ≤ (151985201 : ℝ) / 100000000 := by
  have exp_b9150 : exp (((183 : ℝ) / 200)^2 / 2) ≤ (151985201 : ℝ) / 100000000 := by
    have ht : ((183 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((183 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((183 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (151985201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((183 : ℝ) / 200)).trans (le_trans exp_b9150 (by norm_num))

lemma cosh_b9165_ub : cosh ((1833 : ℝ) / 2000) ≤ (152194101 : ℝ) / 100000000 := by
  have exp_b9165 : exp (((1833 : ℝ) / 2000)^2 / 2) ≤ (152194101 : ℝ) / 100000000 := by
    have ht : ((1833 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1833 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1833 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (152194101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1833 : ℝ) / 2000)).trans (le_trans exp_b9165 (by norm_num))

lemma cosh_b9185_ub : cosh ((1837 : ℝ) / 2000) ≤ (152473601 : ℝ) / 100000000 := by
  have exp_b9185 : exp (((1837 : ℝ) / 2000)^2 / 2) ≤ (152473601 : ℝ) / 100000000 := by
    have ht : ((1837 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1837 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1837 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (152473601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1837 : ℝ) / 2000)).trans (le_trans exp_b9185 (by norm_num))

lemma cosh_b9200_ub : cosh ((23 : ℝ) / 25) ≤ (152684001 : ℝ) / 100000000 := by
  have exp_b9200 : exp (((23 : ℝ) / 25)^2 / 2) ≤ (152684001 : ℝ) / 100000000 := by
    have ht : ((23 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((23 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((23 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (152684001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((23 : ℝ) / 25)).trans (le_trans exp_b9200 (by norm_num))

lemma cosh_b9220_ub : cosh ((461 : ℝ) / 500) ≤ (152965501 : ℝ) / 100000000 := by
  have exp_b9220 : exp (((461 : ℝ) / 500)^2 / 2) ≤ (152965501 : ℝ) / 100000000 := by
    have ht : ((461 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((461 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((461 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (152965501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((461 : ℝ) / 500)).trans (le_trans exp_b9220 (by norm_num))

lemma cosh_b9240_ub : cosh ((231 : ℝ) / 250) ≤ (153248201 : ℝ) / 100000000 := by
  have exp_b9240 : exp (((231 : ℝ) / 250)^2 / 2) ≤ (153248201 : ℝ) / 100000000 := by
    have ht : ((231 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((231 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((231 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (153248201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((231 : ℝ) / 250)).trans (le_trans exp_b9240 (by norm_num))

lemma cosh_b9255_ub : cosh ((1851 : ℝ) / 2000) ≤ (153460901 : ℝ) / 100000000 := by
  have exp_b9255 : exp (((1851 : ℝ) / 2000)^2 / 2) ≤ (153460901 : ℝ) / 100000000 := by
    have ht : ((1851 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1851 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1851 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (153460901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1851 : ℝ) / 2000)).trans (le_trans exp_b9255 (by norm_num))

lemma cosh_b9275_ub : cosh ((371 : ℝ) / 400) ≤ (153745501 : ℝ) / 100000000 := by
  have exp_b9275 : exp (((371 : ℝ) / 400)^2 / 2) ≤ (153745501 : ℝ) / 100000000 := by
    have ht : ((371 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((371 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((371 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (153745501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((371 : ℝ) / 400)).trans (le_trans exp_b9275 (by norm_num))

lemma cosh_b9295_ub : cosh ((1859 : ℝ) / 2000) ≤ (154031301 : ℝ) / 100000000 := by
  have exp_b9295 : exp (((1859 : ℝ) / 2000)^2 / 2) ≤ (154031301 : ℝ) / 100000000 := by
    have ht : ((1859 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1859 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1859 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (154031301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1859 : ℝ) / 2000)).trans (le_trans exp_b9295 (by norm_num))

lemma cosh_b9310_ub : cosh ((931 : ℝ) / 1000) ≤ (154246401 : ℝ) / 100000000 := by
  have exp_b9310 : exp (((931 : ℝ) / 1000)^2 / 2) ≤ (154246401 : ℝ) / 100000000 := by
    have ht : ((931 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((931 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((931 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (154246401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((931 : ℝ) / 1000)).trans (le_trans exp_b9310 (by norm_num))

lemma cosh_b9330_ub : cosh ((933 : ℝ) / 1000) ≤ (154534101 : ℝ) / 100000000 := by
  have exp_b9330 : exp (((933 : ℝ) / 1000)^2 / 2) ≤ (154534101 : ℝ) / 100000000 := by
    have ht : ((933 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((933 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((933 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (154534101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((933 : ℝ) / 1000)).trans (le_trans exp_b9330 (by norm_num))

lemma cosh_b9350_ub : cosh ((187 : ℝ) / 200) ≤ (154823101 : ℝ) / 100000000 := by
  have exp_b9350 : exp (((187 : ℝ) / 200)^2 / 2) ≤ (154823101 : ℝ) / 100000000 := by
    have ht : ((187 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((187 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((187 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (154823101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((187 : ℝ) / 200)).trans (le_trans exp_b9350 (by norm_num))

lemma cosh_b9365_ub : cosh ((1873 : ℝ) / 2000) ≤ (155040501 : ℝ) / 100000000 := by
  have exp_b9365 : exp (((1873 : ℝ) / 2000)^2 / 2) ≤ (155040501 : ℝ) / 100000000 := by
    have ht : ((1873 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1873 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1873 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (155040501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1873 : ℝ) / 2000)).trans (le_trans exp_b9365 (by norm_num))

lemma cosh_b9385_ub : cosh ((1877 : ℝ) / 2000) ≤ (155331501 : ℝ) / 100000000 := by
  have exp_b9385 : exp (((1877 : ℝ) / 2000)^2 / 2) ≤ (155331501 : ℝ) / 100000000 := by
    have ht : ((1877 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1877 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1877 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (155331501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1877 : ℝ) / 2000)).trans (le_trans exp_b9385 (by norm_num))

lemma cosh_b9400_ub : cosh ((47 : ℝ) / 50) ≤ (155550501 : ℝ) / 100000000 := by
  have exp_b9400 : exp (((47 : ℝ) / 50)^2 / 2) ≤ (155550501 : ℝ) / 100000000 := by
    have ht : ((47 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((47 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((47 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (155550501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((47 : ℝ) / 50)).trans (le_trans exp_b9400 (by norm_num))

lemma cosh_b9420_ub : cosh ((471 : ℝ) / 500) ≤ (155843501 : ℝ) / 100000000 := by
  have exp_b9420 : exp (((471 : ℝ) / 500)^2 / 2) ≤ (155843501 : ℝ) / 100000000 := by
    have ht : ((471 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((471 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((471 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (155843501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((471 : ℝ) / 500)).trans (le_trans exp_b9420 (by norm_num))

lemma cosh_b9440_ub : cosh ((118 : ℝ) / 125) ≤ (156137701 : ℝ) / 100000000 := by
  have exp_b9440 : exp (((118 : ℝ) / 125)^2 / 2) ≤ (156137701 : ℝ) / 100000000 := by
    have ht : ((118 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((118 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((118 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (156137701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((118 : ℝ) / 125)).trans (le_trans exp_b9440 (by norm_num))

lemma cosh_b9455_ub : cosh ((1891 : ℝ) / 2000) ≤ (156359201 : ℝ) / 100000000 := by
  have exp_b9455 : exp (((1891 : ℝ) / 2000)^2 / 2) ≤ (156359201 : ℝ) / 100000000 := by
    have ht : ((1891 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1891 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1891 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (156359201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1891 : ℝ) / 2000)).trans (le_trans exp_b9455 (by norm_num))

lemma cosh_b9475_ub : cosh ((379 : ℝ) / 400) ≤ (156655401 : ℝ) / 100000000 := by
  have exp_b9475 : exp (((379 : ℝ) / 400)^2 / 2) ≤ (156655401 : ℝ) / 100000000 := by
    have ht : ((379 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((379 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((379 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (156655401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((379 : ℝ) / 400)).trans (le_trans exp_b9475 (by norm_num))

lemma cosh_b9495_ub : cosh ((1899 : ℝ) / 2000) ≤ (156952901 : ℝ) / 100000000 := by
  have exp_b9495 : exp (((1899 : ℝ) / 2000)^2 / 2) ≤ (156952901 : ℝ) / 100000000 := by
    have ht : ((1899 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1899 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1899 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (156952901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1899 : ℝ) / 2000)).trans (le_trans exp_b9495 (by norm_num))

lemma cosh_b9510_ub : cosh ((951 : ℝ) / 1000) ≤ (157176801 : ℝ) / 100000000 := by
  have exp_b9510 : exp (((951 : ℝ) / 1000)^2 / 2) ≤ (157176801 : ℝ) / 100000000 := by
    have ht : ((951 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((951 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((951 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (157176801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((951 : ℝ) / 1000)).trans (le_trans exp_b9510 (by norm_num))

lemma cosh_b9530_ub : cosh ((953 : ℝ) / 1000) ≤ (157476301 : ℝ) / 100000000 := by
  have exp_b9530 : exp (((953 : ℝ) / 1000)^2 / 2) ≤ (157476301 : ℝ) / 100000000 := by
    have ht : ((953 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((953 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((953 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (157476301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((953 : ℝ) / 1000)).trans (le_trans exp_b9530 (by norm_num))

lemma cosh_b9550_ub : cosh ((191 : ℝ) / 200) ≤ (157777101 : ℝ) / 100000000 := by
  have exp_b9550 : exp (((191 : ℝ) / 200)^2 / 2) ≤ (157777101 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((191 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((191 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (157777101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((191 : ℝ) / 200)).trans (le_trans exp_b9550 (by norm_num))

lemma cosh_b9565_ub : cosh ((1913 : ℝ) / 2000) ≤ (158003401 : ℝ) / 100000000 := by
  have exp_b9565 : exp (((1913 : ℝ) / 2000)^2 / 2) ≤ (158003401 : ℝ) / 100000000 := by
    have ht : ((1913 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1913 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1913 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (158003401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1913 : ℝ) / 2000)).trans (le_trans exp_b9565 (by norm_num))

lemma cosh_b9585_ub : cosh ((1917 : ℝ) / 2000) ≤ (158306301 : ℝ) / 100000000 := by
  have exp_b9585 : exp (((1917 : ℝ) / 2000)^2 / 2) ≤ (158306301 : ℝ) / 100000000 := by
    have ht : ((1917 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1917 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1917 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (158306301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1917 : ℝ) / 2000)).trans (le_trans exp_b9585 (by norm_num))

lemma cosh_b9600_ub : cosh ((24 : ℝ) / 25) ≤ (158534201 : ℝ) / 100000000 := by
  have exp_b9600 : exp (((24 : ℝ) / 25)^2 / 2) ≤ (158534201 : ℝ) / 100000000 := by
    have ht : ((24 : ℝ) / 25)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((24 : ℝ) / 25)^2 / 2) ^ m / (Nat.factorial m)) +
          (((24 : ℝ) / 25)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (158534201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((24 : ℝ) / 25)).trans (le_trans exp_b9600 (by norm_num))

lemma cosh_b9620_ub : cosh ((481 : ℝ) / 500) ≤ (158839201 : ℝ) / 100000000 := by
  have exp_b9620 : exp (((481 : ℝ) / 500)^2 / 2) ≤ (158839201 : ℝ) / 100000000 := by
    have ht : ((481 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((481 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((481 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (158839201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((481 : ℝ) / 500)).trans (le_trans exp_b9620 (by norm_num))

lemma cosh_b9640_ub : cosh ((241 : ℝ) / 250) ≤ (159145401 : ℝ) / 100000000 := by
  have exp_b9640 : exp (((241 : ℝ) / 250)^2 / 2) ≤ (159145401 : ℝ) / 100000000 := by
    have ht : ((241 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((241 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((241 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (159145401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((241 : ℝ) / 250)).trans (le_trans exp_b9640 (by norm_num))

lemma cosh_b9655_ub : cosh ((1931 : ℝ) / 2000) ≤ (159375901 : ℝ) / 100000000 := by
  have exp_b9655 : exp (((1931 : ℝ) / 2000)^2 / 2) ≤ (159375901 : ℝ) / 100000000 := by
    have ht : ((1931 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1931 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1931 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (159375901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1931 : ℝ) / 2000)).trans (le_trans exp_b9655 (by norm_num))

lemma cosh_b9675_ub : cosh ((387 : ℝ) / 400) ≤ (159684301 : ℝ) / 100000000 := by
  have exp_b9675 : exp (((387 : ℝ) / 400)^2 / 2) ≤ (159684301 : ℝ) / 100000000 := by
    have ht : ((387 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((387 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((387 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (159684301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((387 : ℝ) / 400)).trans (le_trans exp_b9675 (by norm_num))

lemma cosh_b9695_ub : cosh ((1939 : ℝ) / 2000) ≤ (159993901 : ℝ) / 100000000 := by
  have exp_b9695 : exp (((1939 : ℝ) / 2000)^2 / 2) ≤ (159993901 : ℝ) / 100000000 := by
    have ht : ((1939 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1939 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1939 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (159993901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1939 : ℝ) / 2000)).trans (le_trans exp_b9695 (by norm_num))

lemma cosh_b9710_ub : cosh ((971 : ℝ) / 1000) ≤ (160226901 : ℝ) / 100000000 := by
  have exp_b9710 : exp (((971 : ℝ) / 1000)^2 / 2) ≤ (160226901 : ℝ) / 100000000 := by
    have ht : ((971 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((971 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((971 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (160226901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((971 : ℝ) / 1000)).trans (le_trans exp_b9710 (by norm_num))

lemma cosh_b9730_ub : cosh ((973 : ℝ) / 1000) ≤ (160538701 : ℝ) / 100000000 := by
  have exp_b9730 : exp (((973 : ℝ) / 1000)^2 / 2) ≤ (160538701 : ℝ) / 100000000 := by
    have ht : ((973 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((973 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((973 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (160538701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((973 : ℝ) / 1000)).trans (le_trans exp_b9730 (by norm_num))

lemma cosh_b9750_ub : cosh ((39 : ℝ) / 40) ≤ (160851701 : ℝ) / 100000000 := by
  have exp_b9750 : exp (((39 : ℝ) / 40)^2 / 2) ≤ (160851701 : ℝ) / 100000000 := by
    have ht : ((39 : ℝ) / 40)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((39 : ℝ) / 40)^2 / 2) ^ m / (Nat.factorial m)) +
          (((39 : ℝ) / 40)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (160851701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((39 : ℝ) / 40)).trans (le_trans exp_b9750 (by norm_num))

lemma cosh_b9765_ub : cosh ((1953 : ℝ) / 2000) ≤ (161087301 : ℝ) / 100000000 := by
  have exp_b9765 : exp (((1953 : ℝ) / 2000)^2 / 2) ≤ (161087301 : ℝ) / 100000000 := by
    have ht : ((1953 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1953 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1953 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (161087301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1953 : ℝ) / 2000)).trans (le_trans exp_b9765 (by norm_num))

lemma cosh_b9785_ub : cosh ((1957 : ℝ) / 2000) ≤ (161402601 : ℝ) / 100000000 := by
  have exp_b9785 : exp (((1957 : ℝ) / 2000)^2 / 2) ≤ (161402601 : ℝ) / 100000000 := by
    have ht : ((1957 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1957 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1957 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (161402601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1957 : ℝ) / 2000)).trans (le_trans exp_b9785 (by norm_num))

lemma cosh_b9800_ub : cosh ((49 : ℝ) / 50) ≤ (161639801 : ℝ) / 100000000 := by
  have exp_b9800 : exp (((49 : ℝ) / 50)^2 / 2) ≤ (161639801 : ℝ) / 100000000 := by
    have ht : ((49 : ℝ) / 50)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((49 : ℝ) / 50)^2 / 2) ^ m / (Nat.factorial m)) +
          (((49 : ℝ) / 50)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (161639801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((49 : ℝ) / 50)).trans (le_trans exp_b9800 (by norm_num))

lemma cosh_b9820_ub : cosh ((491 : ℝ) / 500) ≤ (161957301 : ℝ) / 100000000 := by
  have exp_b9820 : exp (((491 : ℝ) / 500)^2 / 2) ≤ (161957301 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((491 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((491 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (161957301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((491 : ℝ) / 500)).trans (le_trans exp_b9820 (by norm_num))

lemma cosh_b9840_ub : cosh ((123 : ℝ) / 125) ≤ (162276001 : ℝ) / 100000000 := by
  have exp_b9840 : exp (((123 : ℝ) / 125)^2 / 2) ≤ (162276001 : ℝ) / 100000000 := by
    have ht : ((123 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((123 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((123 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (162276001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((123 : ℝ) / 125)).trans (le_trans exp_b9840 (by norm_num))

lemma cosh_b9855_ub : cosh ((1971 : ℝ) / 2000) ≤ (162515901 : ℝ) / 100000000 := by
  have exp_b9855 : exp (((1971 : ℝ) / 2000)^2 / 2) ≤ (162515901 : ℝ) / 100000000 := by
    have ht : ((1971 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1971 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1971 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (162515901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1971 : ℝ) / 2000)).trans (le_trans exp_b9855 (by norm_num))

lemma cosh_b9875_ub : cosh ((79 : ℝ) / 80) ≤ (162836801 : ℝ) / 100000000 := by
  have exp_b9875 : exp (((79 : ℝ) / 80)^2 / 2) ≤ (162836801 : ℝ) / 100000000 := by
    have ht : ((79 : ℝ) / 80)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((79 : ℝ) / 80)^2 / 2) ^ m / (Nat.factorial m)) +
          (((79 : ℝ) / 80)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (162836801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((79 : ℝ) / 80)).trans (le_trans exp_b9875 (by norm_num))

lemma cosh_b9895_ub : cosh ((1979 : ℝ) / 2000) ≤ (163159101 : ℝ) / 100000000 := by
  have exp_b9895 : exp (((1979 : ℝ) / 2000)^2 / 2) ≤ (163159101 : ℝ) / 100000000 := by
    have ht : ((1979 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1979 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1979 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (163159101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1979 : ℝ) / 2000)).trans (le_trans exp_b9895 (by norm_num))

lemma cosh_b9910_ub : cosh ((991 : ℝ) / 1000) ≤ (163401601 : ℝ) / 100000000 := by
  have exp_b9910 : exp (((991 : ℝ) / 1000)^2 / 2) ≤ (163401601 : ℝ) / 100000000 := by
    have ht : ((991 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((991 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((991 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (163401601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((991 : ℝ) / 1000)).trans (le_trans exp_b9910 (by norm_num))

lemma cosh_b9930_ub : cosh ((993 : ℝ) / 1000) ≤ (163726101 : ℝ) / 100000000 := by
  have exp_b9930 : exp (((993 : ℝ) / 1000)^2 / 2) ≤ (163726101 : ℝ) / 100000000 := by
    have ht : ((993 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((993 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((993 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (163726101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((993 : ℝ) / 1000)).trans (le_trans exp_b9930 (by norm_num))

lemma cosh_b9950_ub : cosh ((199 : ℝ) / 200) ≤ (164051901 : ℝ) / 100000000 := by
  have exp_b9950 : exp (((199 : ℝ) / 200)^2 / 2) ≤ (164051901 : ℝ) / 100000000 := by
    have ht : ((199 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((199 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((199 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (164051901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((199 : ℝ) / 200)).trans (le_trans exp_b9950 (by norm_num))

lemma cosh_b9965_ub : cosh ((1993 : ℝ) / 2000) ≤ (164297101 : ℝ) / 100000000 := by
  have exp_b9965 : exp (((1993 : ℝ) / 2000)^2 / 2) ≤ (164297101 : ℝ) / 100000000 := by
    have ht : ((1993 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1993 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1993 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (164297101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1993 : ℝ) / 2000)).trans (le_trans exp_b9965 (by norm_num))

lemma cosh_b9985_ub : cosh ((1997 : ℝ) / 2000) ≤ (164625201 : ℝ) / 100000000 := by
  have exp_b9985 : exp (((1997 : ℝ) / 2000)^2 / 2) ≤ (164625201 : ℝ) / 100000000 := by
    have ht : ((1997 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1997 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1997 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (164625201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1997 : ℝ) / 2000)).trans (le_trans exp_b9985 (by norm_num))

lemma cosh_b10000_ub : cosh ((1 : ℝ) / 1) ≤ (164872201 : ℝ) / 100000000 := by
  have exp_b10000 : exp (((1 : ℝ) / 1)^2 / 2) ≤ (164872201 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1 : ℝ) / 1)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (164872201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1 : ℝ) / 1)).trans (le_trans exp_b10000 (by norm_num))

lemma cosh_b10095_ub : cosh ((2019 : ℝ) / 2000) ≤ (166453401 : ℝ) / 100000000 := by
  have exp_b10095 : exp (((2019 : ℝ) / 2000)^2 / 2) ≤ (166453401 : ℝ) / 100000000 := by
    have ht : ((2019 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2019 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2019 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (166453401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2019 : ℝ) / 2000)).trans (le_trans exp_b10095 (by norm_num))

lemma cosh_b10185_ub : cosh ((2037 : ℝ) / 2000) ≤ (167979401 : ℝ) / 100000000 := by
  have exp_b10185 : exp (((2037 : ℝ) / 2000)^2 / 2) ≤ (167979401 : ℝ) / 100000000 := by
    have ht : ((2037 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2037 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2037 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (167979401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2037 : ℝ) / 2000)).trans (le_trans exp_b10185 (by norm_num))

lemma cosh_b10275_ub : cosh ((411 : ℝ) / 400) ≤ (169533201 : ℝ) / 100000000 := by
  have exp_b10275 : exp (((411 : ℝ) / 400)^2 / 2) ≤ (169533201 : ℝ) / 100000000 := by
    have ht : ((411 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((411 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((411 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (169533201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((411 : ℝ) / 400)).trans (le_trans exp_b10275 (by norm_num))

lemma cosh_b10365_ub : cosh ((2073 : ℝ) / 2000) ≤ (171115101 : ℝ) / 100000000 := by
  have exp_b10365 : exp (((2073 : ℝ) / 2000)^2 / 2) ≤ (171115101 : ℝ) / 100000000 := by
    have ht : ((2073 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2073 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2073 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (171115101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2073 : ℝ) / 2000)).trans (le_trans exp_b10365 (by norm_num))

lemma cosh_b10455_ub : cosh ((2091 : ℝ) / 2000) ≤ (172725801 : ℝ) / 100000000 := by
  have exp_b10455 : exp (((2091 : ℝ) / 2000)^2 / 2) ≤ (172725801 : ℝ) / 100000000 := by
    have ht : ((2091 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2091 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2091 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (172725801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2091 : ℝ) / 2000)).trans (le_trans exp_b10455 (by norm_num))

lemma cosh_b10550_ub : cosh ((211 : ℝ) / 200) ≤ (174457801 : ℝ) / 100000000 := by
  have exp_b10550 : exp (((211 : ℝ) / 200)^2 / 2) ≤ (174457801 : ℝ) / 100000000 := by
    have ht : ((211 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((211 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((211 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (174457801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((211 : ℝ) / 200)).trans (le_trans exp_b10550 (by norm_num))

lemma cosh_b10640_ub : cosh ((133 : ℝ) / 125) ≤ (176129301 : ℝ) / 100000000 := by
  have exp_b10640 : exp (((133 : ℝ) / 125)^2 / 2) ≤ (176129301 : ℝ) / 100000000 := by
    have ht : ((133 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((133 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((133 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (176129301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((133 : ℝ) / 125)).trans (le_trans exp_b10640 (by norm_num))

lemma cosh_b10730_ub : cosh ((1073 : ℝ) / 1000) ≤ (177831201 : ℝ) / 100000000 := by
  have exp_b10730 : exp (((1073 : ℝ) / 1000)^2 / 2) ≤ (177831201 : ℝ) / 100000000 := by
    have ht : ((1073 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1073 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1073 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (177831201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1073 : ℝ) / 1000)).trans (le_trans exp_b10730 (by norm_num))

lemma cosh_b10820_ub : cosh ((541 : ℝ) / 500) ≤ (179564101 : ℝ) / 100000000 := by
  have exp_b10820 : exp (((541 : ℝ) / 500)^2 / 2) ≤ (179564101 : ℝ) / 100000000 := by
    have ht : ((541 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((541 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((541 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (179564101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((541 : ℝ) / 500)).trans (le_trans exp_b10820 (by norm_num))

lemma cosh_b10910_ub : cosh ((1091 : ℝ) / 1000) ≤ (181328601 : ℝ) / 100000000 := by
  have exp_b10910 : exp (((1091 : ℝ) / 1000)^2 / 2) ≤ (181328601 : ℝ) / 100000000 := by
    have ht : ((1091 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1091 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1091 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (181328601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1091 : ℝ) / 1000)).trans (le_trans exp_b10910 (by norm_num))

lemma cosh_b11000_ub : cosh ((11 : ℝ) / 10) ≤ (183125301 : ℝ) / 100000000 := by
  have exp_b11000 : exp (((11 : ℝ) / 10)^2 / 2) ≤ (183125301 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 10)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((11 : ℝ) / 10)^2 / 2) ^ m / (Nat.factorial m)) +
          (((11 : ℝ) / 10)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (183125301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((11 : ℝ) / 10)).trans (le_trans exp_b11000 (by norm_num))

lemma cosh_b11095_ub : cosh ((2219 : ℝ) / 2000) ≤ (185057301 : ℝ) / 100000000 := by
  have exp_b11095 : exp (((2219 : ℝ) / 2000)^2 / 2) ≤ (185057301 : ℝ) / 100000000 := by
    have ht : ((2219 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2219 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2219 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (185057301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2219 : ℝ) / 2000)).trans (le_trans exp_b11095 (by norm_num))

lemma cosh_b11185_ub : cosh ((2237 : ℝ) / 2000) ≤ (186922001 : ℝ) / 100000000 := by
  have exp_b11185 : exp (((2237 : ℝ) / 2000)^2 / 2) ≤ (186922001 : ℝ) / 100000000 := by
    have ht : ((2237 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2237 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2237 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (186922001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2237 : ℝ) / 2000)).trans (le_trans exp_b11185 (by norm_num))

lemma cosh_b11275_ub : cosh ((451 : ℝ) / 400) ≤ (188820801 : ℝ) / 100000000 := by
  have exp_b11275 : exp (((451 : ℝ) / 400)^2 / 2) ≤ (188820801 : ℝ) / 100000000 := by
    have ht : ((451 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((451 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((451 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (188820801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((451 : ℝ) / 400)).trans (le_trans exp_b11275 (by norm_num))

lemma cosh_b11365_ub : cosh ((2273 : ℝ) / 2000) ≤ (190754401 : ℝ) / 100000000 := by
  have exp_b11365 : exp (((2273 : ℝ) / 2000)^2 / 2) ≤ (190754401 : ℝ) / 100000000 := by
    have ht : ((2273 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2273 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2273 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (190754401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2273 : ℝ) / 2000)).trans (le_trans exp_b11365 (by norm_num))

lemma cosh_b11455_ub : cosh ((2291 : ℝ) / 2000) ≤ (192723301 : ℝ) / 100000000 := by
  have exp_b11455 : exp (((2291 : ℝ) / 2000)^2 / 2) ≤ (192723301 : ℝ) / 100000000 := by
    have ht : ((2291 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2291 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2291 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (192723301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2291 : ℝ) / 2000)).trans (le_trans exp_b11455 (by norm_num))

lemma cosh_b11550_ub : cosh ((231 : ℝ) / 200) ≤ (194840801 : ℝ) / 100000000 := by
  have exp_b11550 : exp (((231 : ℝ) / 200)^2 / 2) ≤ (194840801 : ℝ) / 100000000 := by
    have ht : ((231 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((231 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((231 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (194840801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((231 : ℝ) / 200)).trans (le_trans exp_b11550 (by norm_num))

lemma cosh_b11640_ub : cosh ((291 : ℝ) / 250) ≤ (196884701 : ℝ) / 100000000 := by
  have exp_b11640 : exp (((291 : ℝ) / 250)^2 / 2) ≤ (196884701 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((291 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((291 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (196884701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((291 : ℝ) / 250)).trans (le_trans exp_b11640 (by norm_num))

lemma cosh_b11730_ub : cosh ((1173 : ℝ) / 1000) ≤ (198966201 : ℝ) / 100000000 := by
  have exp_b11730 : exp (((1173 : ℝ) / 1000)^2 / 2) ≤ (198966201 : ℝ) / 100000000 := by
    have ht : ((1173 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1173 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1173 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (198966201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1173 : ℝ) / 1000)).trans (le_trans exp_b11730 (by norm_num))

lemma cosh_b11820_ub : cosh ((591 : ℝ) / 500) ≤ (201086001 : ℝ) / 100000000 := by
  have exp_b11820 : exp (((591 : ℝ) / 500)^2 / 2) ≤ (201086001 : ℝ) / 100000000 := by
    have ht : ((591 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((591 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((591 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (201086001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((591 : ℝ) / 500)).trans (le_trans exp_b11820 (by norm_num))

lemma cosh_b11910_ub : cosh ((1191 : ℝ) / 1000) ≤ (203244801 : ℝ) / 100000000 := by
  have exp_b11910 : exp (((1191 : ℝ) / 1000)^2 / 2) ≤ (203244801 : ℝ) / 100000000 := by
    have ht : ((1191 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1191 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1191 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (203244801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1191 : ℝ) / 1000)).trans (le_trans exp_b11910 (by norm_num))

lemma cosh_b12000_ub : cosh ((6 : ℝ) / 5) ≤ (205443401 : ℝ) / 100000000 := by
  have exp_b12000 : exp (((6 : ℝ) / 5)^2 / 2) ≤ (205443401 : ℝ) / 100000000 := by
    have ht : ((6 : ℝ) / 5)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((6 : ℝ) / 5)^2 / 2) ^ m / (Nat.factorial m)) +
          (((6 : ℝ) / 5)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (205443401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((6 : ℝ) / 5)).trans (le_trans exp_b12000 (by norm_num))

lemma cosh_b12095_ub : cosh ((2419 : ℝ) / 2000) ≤ (207808201 : ℝ) / 100000000 := by
  have exp_b12095 : exp (((2419 : ℝ) / 2000)^2 / 2) ≤ (207808201 : ℝ) / 100000000 := by
    have ht : ((2419 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2419 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2419 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (207808201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2419 : ℝ) / 2000)).trans (le_trans exp_b12095 (by norm_num))

lemma cosh_b12185_ub : cosh ((2437 : ℝ) / 2000) ≤ (210091201 : ℝ) / 100000000 := by
  have exp_b12185 : exp (((2437 : ℝ) / 2000)^2 / 2) ≤ (210091201 : ℝ) / 100000000 := by
    have ht : ((2437 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2437 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2437 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (210091201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2437 : ℝ) / 2000)).trans (le_trans exp_b12185 (by norm_num))

lemma cosh_b12275_ub : cosh ((491 : ℝ) / 400) ≤ (212416401 : ℝ) / 100000000 := by
  have exp_b12275 : exp (((491 : ℝ) / 400)^2 / 2) ≤ (212416401 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((491 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((491 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (212416401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((491 : ℝ) / 400)).trans (le_trans exp_b12275 (by norm_num))

lemma cosh_b12365_ub : cosh ((2473 : ℝ) / 2000) ≤ (214784801 : ℝ) / 100000000 := by
  have exp_b12365 : exp (((2473 : ℝ) / 2000)^2 / 2) ≤ (214784801 : ℝ) / 100000000 := by
    have ht : ((2473 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2473 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2473 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (214784801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2473 : ℝ) / 2000)).trans (le_trans exp_b12365 (by norm_num))

lemma cosh_b12455_ub : cosh ((2491 : ℝ) / 2000) ≤ (217197201 : ℝ) / 100000000 := by
  have exp_b12455 : exp (((2491 : ℝ) / 2000)^2 / 2) ≤ (217197201 : ℝ) / 100000000 := by
    have ht : ((2491 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2491 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2491 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (217197201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2491 : ℝ) / 2000)).trans (le_trans exp_b12455 (by norm_num))

lemma cosh_b12550_ub : cosh ((251 : ℝ) / 200) ≤ (219792301 : ℝ) / 100000000 := by
  have exp_b12550 : exp (((251 : ℝ) / 200)^2 / 2) ≤ (219792301 : ℝ) / 100000000 := by
    have ht : ((251 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((251 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((251 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (219792301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((251 : ℝ) / 200)).trans (le_trans exp_b12550 (by norm_num))

lemma cosh_b12640_ub : cosh ((158 : ℝ) / 125) ≤ (222297901 : ℝ) / 100000000 := by
  have exp_b12640 : exp (((158 : ℝ) / 125)^2 / 2) ≤ (222297901 : ℝ) / 100000000 := by
    have ht : ((158 : ℝ) / 125)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((158 : ℝ) / 125)^2 / 2) ^ m / (Nat.factorial m)) +
          (((158 : ℝ) / 125)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (222297901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((158 : ℝ) / 125)).trans (le_trans exp_b12640 (by norm_num))

lemma cosh_b12730_ub : cosh ((1273 : ℝ) / 1000) ≤ (224850301 : ℝ) / 100000000 := by
  have exp_b12730 : exp (((1273 : ℝ) / 1000)^2 / 2) ≤ (224850301 : ℝ) / 100000000 := by
    have ht : ((1273 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1273 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1273 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (224850301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1273 : ℝ) / 1000)).trans (le_trans exp_b12730 (by norm_num))

lemma cosh_b12820_ub : cosh ((641 : ℝ) / 500) ≤ (227450501 : ℝ) / 100000000 := by
  have exp_b12820 : exp (((641 : ℝ) / 500)^2 / 2) ≤ (227450501 : ℝ) / 100000000 := by
    have ht : ((641 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((641 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((641 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (227450501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((641 : ℝ) / 500)).trans (le_trans exp_b12820 (by norm_num))

lemma cosh_b12910_ub : cosh ((1291 : ℝ) / 1000) ≤ (230099301 : ℝ) / 100000000 := by
  have exp_b12910 : exp (((1291 : ℝ) / 1000)^2 / 2) ≤ (230099301 : ℝ) / 100000000 := by
    have ht : ((1291 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1291 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1291 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (230099301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1291 : ℝ) / 1000)).trans (le_trans exp_b12910 (by norm_num))

lemma cosh_b13000_ub : cosh ((13 : ℝ) / 10) ≤ (232797801 : ℝ) / 100000000 := by
  have exp_b13000 : exp (((13 : ℝ) / 10)^2 / 2) ≤ (232797801 : ℝ) / 100000000 := by
    have ht : ((13 : ℝ) / 10)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((13 : ℝ) / 10)^2 / 2) ^ m / (Nat.factorial m)) +
          (((13 : ℝ) / 10)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (232797801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((13 : ℝ) / 10)).trans (le_trans exp_b13000 (by norm_num))

lemma cosh_b13095_ub : cosh ((2619 : ℝ) / 2000) ≤ (235701401 : ℝ) / 100000000 := by
  have exp_b13095 : exp (((2619 : ℝ) / 2000)^2 / 2) ≤ (235701401 : ℝ) / 100000000 := by
    have ht : ((2619 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2619 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2619 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (235701401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2619 : ℝ) / 2000)).trans (le_trans exp_b13095 (by norm_num))

lemma cosh_b13185_ub : cosh ((2637 : ℝ) / 2000) ≤ (238505301 : ℝ) / 100000000 := by
  have exp_b13185 : exp (((2637 : ℝ) / 2000)^2 / 2) ≤ (238505301 : ℝ) / 100000000 := by
    have ht : ((2637 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2637 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2637 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (238505301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2637 : ℝ) / 2000)).trans (le_trans exp_b13185 (by norm_num))

lemma cosh_b13275_ub : cosh ((531 : ℝ) / 400) ≤ (241362201 : ℝ) / 100000000 := by
  have exp_b13275 : exp (((531 : ℝ) / 400)^2 / 2) ≤ (241362201 : ℝ) / 100000000 := by
    have ht : ((531 : ℝ) / 400)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((531 : ℝ) / 400)^2 / 2) ^ m / (Nat.factorial m)) +
          (((531 : ℝ) / 400)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (241362201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((531 : ℝ) / 400)).trans (le_trans exp_b13275 (by norm_num))

lemma cosh_b13365_ub : cosh ((2673 : ℝ) / 2000) ≤ (244273001 : ℝ) / 100000000 := by
  have exp_b13365 : exp (((2673 : ℝ) / 2000)^2 / 2) ≤ (244273001 : ℝ) / 100000000 := by
    have ht : ((2673 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2673 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2673 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (244273001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2673 : ℝ) / 2000)).trans (le_trans exp_b13365 (by norm_num))

lemma cosh_b13455_ub : cosh ((2691 : ℝ) / 2000) ≤ (247239001 : ℝ) / 100000000 := by
  have exp_b13455 : exp (((2691 : ℝ) / 2000)^2 / 2) ≤ (247239001 : ℝ) / 100000000 := by
    have ht : ((2691 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2691 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2691 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (247239001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2691 : ℝ) / 2000)).trans (le_trans exp_b13455 (by norm_num))

lemma cosh_b13550_ub : cosh ((271 : ℝ) / 200) ≤ (250430901 : ℝ) / 100000000 := by
  have exp_b13550 : exp (((271 : ℝ) / 200)^2 / 2) ≤ (250430901 : ℝ) / 100000000 := by
    have ht : ((271 : ℝ) / 200)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((271 : ℝ) / 200)^2 / 2) ^ m / (Nat.factorial m)) +
          (((271 : ℝ) / 200)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (250430901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((271 : ℝ) / 200)).trans (le_trans exp_b13550 (by norm_num))

lemma cosh_b13640_ub : cosh ((341 : ℝ) / 250) ≤ (253513801 : ℝ) / 100000000 := by
  have exp_b13640 : exp (((341 : ℝ) / 250)^2 / 2) ≤ (253513801 : ℝ) / 100000000 := by
    have ht : ((341 : ℝ) / 250)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((341 : ℝ) / 250)^2 / 2) ^ m / (Nat.factorial m)) +
          (((341 : ℝ) / 250)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (253513801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((341 : ℝ) / 250)).trans (le_trans exp_b13640 (by norm_num))

lemma cosh_b13730_ub : cosh ((1373 : ℝ) / 1000) ≤ (256655601 : ℝ) / 100000000 := by
  have exp_b13730 : exp (((1373 : ℝ) / 1000)^2 / 2) ≤ (256655601 : ℝ) / 100000000 := by
    have ht : ((1373 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1373 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1373 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (256655601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1373 : ℝ) / 1000)).trans (le_trans exp_b13730 (by norm_num))

lemma cosh_b13820_ub : cosh ((691 : ℝ) / 500) ≤ (259857201 : ℝ) / 100000000 := by
  have exp_b13820 : exp (((691 : ℝ) / 500)^2 / 2) ≤ (259857201 : ℝ) / 100000000 := by
    have ht : ((691 : ℝ) / 500)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((691 : ℝ) / 500)^2 / 2) ^ m / (Nat.factorial m)) +
          (((691 : ℝ) / 500)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (259857201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((691 : ℝ) / 500)).trans (le_trans exp_b13820 (by norm_num))

lemma cosh_b13910_ub : cosh ((1391 : ℝ) / 1000) ≤ (263120201 : ℝ) / 100000000 := by
  have exp_b13910 : exp (((1391 : ℝ) / 1000)^2 / 2) ≤ (263120201 : ℝ) / 100000000 := by
    have ht : ((1391 : ℝ) / 1000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((1391 : ℝ) / 1000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((1391 : ℝ) / 1000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (263120201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((1391 : ℝ) / 1000)).trans (le_trans exp_b13910 (by norm_num))

lemma cosh_b14000_ub : cosh ((7 : ℝ) / 5) ≤ (266445701 : ℝ) / 100000000 := by
  have exp_b14000 : exp (((7 : ℝ) / 5)^2 / 2) ≤ (266445701 : ℝ) / 100000000 := by
    have ht : ((7 : ℝ) / 5)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((7 : ℝ) / 5)^2 / 2) ^ m / (Nat.factorial m)) +
          (((7 : ℝ) / 5)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (266445701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((7 : ℝ) / 5)).trans (le_trans exp_b14000 (by norm_num))

lemma cosh_b14095_ub : cosh ((2819 : ℝ) / 2000) ≤ (270025301 : ℝ) / 100000000 := by
  have exp_b14095 : exp (((2819 : ℝ) / 2000)^2 / 2) ≤ (270025301 : ℝ) / 100000000 := by
    have ht : ((2819 : ℝ) / 2000)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, (((2819 : ℝ) / 2000)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2819 : ℝ) / 2000)^2 / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (270025301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2819 : ℝ) / 2000)).trans (le_trans exp_b14095 (by norm_num))

lemma cosh_b14185_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b14185 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b14185 (by norm_num))

lemma cosh_b14275_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b14275 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b14275 (by norm_num))

lemma cosh_b14365_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b14365 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b14365 (by norm_num))

lemma cosh_b14455_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b14455 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b14455 (by norm_num))

lemma cosh_b14550_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b14550 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b14550 (by norm_num))

lemma cosh_b14640_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b14640 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b14640 (by norm_num))

lemma cosh_b14730_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b14730 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b14730 (by norm_num))

lemma cosh_b14820_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b14820 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b14820 (by norm_num))

lemma cosh_b14910_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b14910 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b14910 (by norm_num))

lemma cosh_b15000_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b15000 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b15000 (by norm_num))

lemma cosh_b15095_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b15095 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b15095 (by norm_num))

lemma cosh_b15185_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b15185 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b15185 (by norm_num))

lemma cosh_b15275_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b15275 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b15275 (by norm_num))

lemma cosh_b15365_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b15365 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b15365 (by norm_num))

lemma cosh_b15455_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b15455 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b15455 (by norm_num))

lemma cosh_b15550_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b15550 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b15550 (by norm_num))

lemma cosh_b15640_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b15640 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b15640 (by norm_num))

lemma cosh_b15730_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b15730 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b15730 (by norm_num))

lemma cosh_b15820_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b15820 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b15820 (by norm_num))

lemma cosh_b15910_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b15910 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b15910 (by norm_num))

lemma cosh_b16000_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b16000 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b16000 (by norm_num))

lemma cosh_b16095_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b16095 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b16095 (by norm_num))

lemma cosh_b16185_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b16185 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b16185 (by norm_num))

lemma cosh_b16275_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b16275 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b16275 (by norm_num))

lemma cosh_b16365_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b16365 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b16365 (by norm_num))

lemma cosh_b16455_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b16455 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b16455 (by norm_num))

lemma cosh_b16550_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b16550 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b16550 (by norm_num))

lemma cosh_b16640_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b16640 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b16640 (by norm_num))

lemma cosh_b16730_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b16730 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b16730 (by norm_num))

lemma cosh_b16820_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b16820 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b16820 (by norm_num))

lemma cosh_b16910_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b16910 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b16910 (by norm_num))

lemma cosh_b17000_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b17000 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b17000 (by norm_num))

lemma cosh_b17095_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b17095 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b17095 (by norm_num))

lemma cosh_b17185_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b17185 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b17185 (by norm_num))

lemma cosh_b17275_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b17275 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b17275 (by norm_num))

lemma cosh_b17365_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b17365 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b17365 (by norm_num))

lemma cosh_b17455_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b17455 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b17455 (by norm_num))

lemma cosh_b17550_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b17550 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b17550 (by norm_num))

lemma cosh_b17640_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b17640 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b17640 (by norm_num))

lemma cosh_b17730_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b17730 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b17730 (by norm_num))

lemma cosh_b17820_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b17820 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b17820 (by norm_num))

lemma cosh_b17910_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b17910 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b17910 (by norm_num))

lemma cosh_b18000_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b18000 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b18000 (by norm_num))

lemma cosh_b18095_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b18095 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b18095 (by norm_num))

lemma cosh_b18185_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b18185 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b18185 (by norm_num))

lemma cosh_b18275_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b18275 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b18275 (by norm_num))

lemma cosh_b18365_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b18365 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b18365 (by norm_num))

lemma cosh_b18455_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b18455 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b18455 (by norm_num))

lemma cosh_b18550_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b18550 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b18550 (by norm_num))

lemma cosh_b18640_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b18640 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b18640 (by norm_num))

lemma cosh_b18730_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b18730 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b18730 (by norm_num))

lemma cosh_b18820_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b18820 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b18820 (by norm_num))

lemma cosh_b18910_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b18910 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b18910 (by norm_num))

lemma cosh_b19000_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b19000 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b19000 (by norm_num))

lemma cosh_b19095_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b19095 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b19095 (by norm_num))

lemma cosh_b19185_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b19185 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b19185 (by norm_num))

lemma cosh_b19275_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b19275 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b19275 (by norm_num))

lemma cosh_b19365_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b19365 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b19365 (by norm_num))

lemma cosh_b19455_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b19455 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b19455 (by norm_num))

lemma cosh_b19550_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b19550 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b19550 (by norm_num))

lemma cosh_b19640_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b19640 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b19640 (by norm_num))

lemma cosh_b19730_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b19730 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b19730 (by norm_num))

lemma cosh_b19820_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b19820 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b19820 (by norm_num))

lemma cosh_b19910_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b19910 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b19910 (by norm_num))

lemma cosh_b20000_ub : cosh ((2 : ℝ) / 1) ≤ (738905701 : ℝ) / 100000000 := by
  have exp_b20000 : exp (((2 : ℝ) / 1)^2 / 2) ≤ (738905701 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 14) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 14, (((2 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((2 : ℝ) / 1)^2 / 2) ^ 14 * (14 + 1) / (Nat.factorial 14 * 14) ≤
          (738905701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((2 : ℝ) / 1)).trans (le_trans exp_b20000 (by norm_num))

lemma cosh_b20095_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b20095 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b20095 (by norm_num))

lemma cosh_b20185_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b20185 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b20185 (by norm_num))

lemma cosh_b20275_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b20275 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b20275 (by norm_num))

lemma cosh_b20365_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b20365 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b20365 (by norm_num))

lemma cosh_b20455_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b20455 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b20455 (by norm_num))

lemma cosh_b20550_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b20550 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b20550 (by norm_num))

lemma cosh_b20640_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b20640 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b20640 (by norm_num))

lemma cosh_b20730_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b20730 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b20730 (by norm_num))

lemma cosh_b20820_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b20820 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b20820 (by norm_num))

lemma cosh_b20910_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b20910 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b20910 (by norm_num))

lemma cosh_b21000_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b21000 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b21000 (by norm_num))

lemma cosh_b21095_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b21095 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b21095 (by norm_num))

lemma cosh_b21185_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b21185 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b21185 (by norm_num))

lemma cosh_b21275_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b21275 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b21275 (by norm_num))

lemma cosh_b21365_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b21365 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b21365 (by norm_num))

lemma cosh_b21455_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b21455 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b21455 (by norm_num))

lemma cosh_b21550_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b21550 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b21550 (by norm_num))

lemma cosh_b21640_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b21640 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b21640 (by norm_num))

lemma cosh_b21730_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b21730 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b21730 (by norm_num))

lemma cosh_b21820_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b21820 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b21820 (by norm_num))

lemma cosh_b21910_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b21910 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b21910 (by norm_num))

lemma cosh_b22000_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b22000 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b22000 (by norm_num))

lemma cosh_b22095_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b22095 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b22095 (by norm_num))

lemma cosh_b22185_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b22185 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b22185 (by norm_num))

lemma cosh_b22275_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b22275 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b22275 (by norm_num))

lemma cosh_b22365_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b22365 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b22365 (by norm_num))

lemma cosh_b22455_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b22455 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b22455 (by norm_num))

lemma cosh_b22550_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b22550 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b22550 (by norm_num))

lemma cosh_b22640_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b22640 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b22640 (by norm_num))

lemma cosh_b22730_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b22730 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b22730 (by norm_num))

lemma cosh_b22820_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b22820 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b22820 (by norm_num))

lemma cosh_b22910_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b22910 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b22910 (by norm_num))

lemma cosh_b23000_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b23000 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b23000 (by norm_num))

lemma cosh_b23095_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b23095 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b23095 (by norm_num))

lemma cosh_b23185_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b23185 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b23185 (by norm_num))

lemma cosh_b23275_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b23275 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b23275 (by norm_num))

lemma cosh_b23365_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b23365 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b23365 (by norm_num))

lemma cosh_b23455_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b23455 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b23455 (by norm_num))

lemma cosh_b23550_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b23550 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b23550 (by norm_num))

lemma cosh_b23640_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b23640 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b23640 (by norm_num))

lemma cosh_b23730_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b23730 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b23730 (by norm_num))

lemma cosh_b23820_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b23820 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b23820 (by norm_num))

lemma cosh_b23910_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b23910 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b23910 (by norm_num))

lemma cosh_b24000_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b24000 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b24000 (by norm_num))

lemma cosh_b24095_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b24095 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b24095 (by norm_num))

lemma cosh_b24185_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b24185 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b24185 (by norm_num))

lemma cosh_b24275_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b24275 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b24275 (by norm_num))

lemma cosh_b24365_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b24365 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b24365 (by norm_num))

lemma cosh_b24455_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b24455 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b24455 (by norm_num))

lemma cosh_b24550_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b24550 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b24550 (by norm_num))

lemma cosh_b24640_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b24640 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b24640 (by norm_num))

lemma cosh_b24730_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b24730 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b24730 (by norm_num))

lemma cosh_b24820_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b24820 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b24820 (by norm_num))

lemma cosh_b24910_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b24910 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b24910 (by norm_num))

lemma cosh_b25000_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b25000 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b25000 (by norm_num))

lemma cosh_b25095_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b25095 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b25095 (by norm_num))

lemma cosh_b25185_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b25185 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b25185 (by norm_num))

lemma cosh_b25275_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b25275 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b25275 (by norm_num))

lemma cosh_b25365_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b25365 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b25365 (by norm_num))

lemma cosh_b25455_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b25455 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b25455 (by norm_num))

lemma cosh_b25550_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b25550 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b25550 (by norm_num))

lemma cosh_b25640_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b25640 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b25640 (by norm_num))

lemma cosh_b25730_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b25730 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b25730 (by norm_num))

lemma cosh_b25820_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b25820 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b25820 (by norm_num))

lemma cosh_b25910_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b25910 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b25910 (by norm_num))

lemma cosh_b26000_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b26000 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b26000 (by norm_num))

lemma cosh_b26095_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b26095 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b26095 (by norm_num))

lemma cosh_b26185_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b26185 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b26185 (by norm_num))

lemma cosh_b26275_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b26275 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b26275 (by norm_num))

lemma cosh_b26365_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b26365 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b26365 (by norm_num))

lemma cosh_b26455_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b26455 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b26455 (by norm_num))

lemma cosh_b26550_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b26550 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b26550 (by norm_num))

lemma cosh_b26640_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b26640 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b26640 (by norm_num))

lemma cosh_b26730_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b26730 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b26730 (by norm_num))

lemma cosh_b26820_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b26820 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b26820 (by norm_num))

lemma cosh_b26910_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b26910 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b26910 (by norm_num))

lemma cosh_b27000_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b27000 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b27000 (by norm_num))

lemma cosh_b27095_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b27095 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b27095 (by norm_num))

lemma cosh_b27185_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b27185 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b27185 (by norm_num))

lemma cosh_b27275_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b27275 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b27275 (by norm_num))

lemma cosh_b27365_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b27365 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b27365 (by norm_num))

lemma cosh_b27455_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b27455 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b27455 (by norm_num))

lemma cosh_b27550_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b27550 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b27550 (by norm_num))

lemma cosh_b27640_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b27640 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b27640 (by norm_num))

lemma cosh_b27730_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b27730 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b27730 (by norm_num))

lemma cosh_b27820_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b27820 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b27820 (by norm_num))

lemma cosh_b27910_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b27910 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b27910 (by norm_num))

lemma cosh_b28000_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b28000 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b28000 (by norm_num))

lemma cosh_b28095_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b28095 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b28095 (by norm_num))

lemma cosh_b28185_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b28185 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b28185 (by norm_num))

lemma cosh_b28275_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b28275 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b28275 (by norm_num))

lemma cosh_b28365_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b28365 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b28365 (by norm_num))

lemma cosh_b28455_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b28455 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b28455 (by norm_num))

lemma cosh_b28550_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b28550 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b28550 (by norm_num))

lemma cosh_b28640_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b28640 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b28640 (by norm_num))

lemma cosh_b28730_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b28730 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b28730 (by norm_num))

lemma cosh_b28820_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b28820 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b28820 (by norm_num))

lemma cosh_b28910_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b28910 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b28910 (by norm_num))

lemma cosh_b29000_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b29000 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b29000 (by norm_num))

lemma cosh_b29095_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b29095 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b29095 (by norm_num))

lemma cosh_b29185_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b29185 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b29185 (by norm_num))

lemma cosh_b29275_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b29275 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b29275 (by norm_num))

lemma cosh_b29365_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b29365 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b29365 (by norm_num))

lemma cosh_b29455_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b29455 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b29455 (by norm_num))

lemma cosh_b29550_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b29550 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b29550 (by norm_num))

lemma cosh_b29640_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b29640 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b29640 (by norm_num))

lemma cosh_b29730_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b29730 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b29730 (by norm_num))

lemma cosh_b29820_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b29820 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b29820 (by norm_num))

lemma cosh_b29910_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b29910 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b29910 (by norm_num))

lemma cosh_b30000_ub : cosh ((3 : ℝ) / 1) ≤ (9001713201 : ℝ) / 100000000 := by
  have exp_b30000 : exp (((3 : ℝ) / 1)^2 / 2) ≤ (9001713201 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 21) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 21, (((3 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((3 : ℝ) / 1)^2 / 2) ^ 21 * (21 + 1) / (Nat.factorial 21 * 21) ≤
          (9001713201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((3 : ℝ) / 1)).trans (le_trans exp_b30000 (by norm_num))

lemma cosh_b30095_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b30095 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b30095 (by norm_num))

lemma cosh_b30185_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b30185 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b30185 (by norm_num))

lemma cosh_b30275_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b30275 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b30275 (by norm_num))

lemma cosh_b30365_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b30365 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b30365 (by norm_num))

lemma cosh_b30455_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b30455 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b30455 (by norm_num))

lemma cosh_b30550_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b30550 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b30550 (by norm_num))

lemma cosh_b30640_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b30640 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b30640 (by norm_num))

lemma cosh_b30730_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b30730 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b30730 (by norm_num))

lemma cosh_b30820_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b30820 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b30820 (by norm_num))

lemma cosh_b30910_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b30910 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b30910 (by norm_num))

lemma cosh_b31000_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b31000 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b31000 (by norm_num))

lemma cosh_b31095_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b31095 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b31095 (by norm_num))

lemma cosh_b31185_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b31185 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b31185 (by norm_num))

lemma cosh_b31275_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b31275 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b31275 (by norm_num))

lemma cosh_b31365_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b31365 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b31365 (by norm_num))

lemma cosh_b31455_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b31455 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b31455 (by norm_num))

lemma cosh_b31550_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b31550 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b31550 (by norm_num))

lemma cosh_b31640_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b31640 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b31640 (by norm_num))

lemma cosh_b31730_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b31730 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b31730 (by norm_num))

lemma cosh_b31820_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b31820 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b31820 (by norm_num))

lemma cosh_b31910_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b31910 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b31910 (by norm_num))

lemma cosh_b32000_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b32000 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b32000 (by norm_num))

lemma cosh_b32095_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b32095 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b32095 (by norm_num))

lemma cosh_b32185_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b32185 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b32185 (by norm_num))

lemma cosh_b32275_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b32275 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b32275 (by norm_num))

lemma cosh_b32365_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b32365 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b32365 (by norm_num))

lemma cosh_b32455_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b32455 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b32455 (by norm_num))

lemma cosh_b32550_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b32550 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b32550 (by norm_num))

lemma cosh_b32640_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b32640 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b32640 (by norm_num))

lemma cosh_b32730_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b32730 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b32730 (by norm_num))

lemma cosh_b32820_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b32820 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b32820 (by norm_num))

lemma cosh_b32910_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b32910 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b32910 (by norm_num))

lemma cosh_b33000_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b33000 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b33000 (by norm_num))

lemma cosh_b33095_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b33095 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b33095 (by norm_num))

lemma cosh_b33185_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b33185 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b33185 (by norm_num))

lemma cosh_b33275_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b33275 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b33275 (by norm_num))

lemma cosh_b33365_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b33365 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b33365 (by norm_num))

lemma cosh_b33455_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b33455 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b33455 (by norm_num))

lemma cosh_b33550_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b33550 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b33550 (by norm_num))

lemma cosh_b33640_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b33640 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b33640 (by norm_num))

lemma cosh_b33730_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b33730 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b33730 (by norm_num))

lemma cosh_b33820_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b33820 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b33820 (by norm_num))

lemma cosh_b33910_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b33910 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b33910 (by norm_num))

lemma cosh_b34000_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b34000 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b34000 (by norm_num))

lemma cosh_b34095_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b34095 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b34095 (by norm_num))

lemma cosh_b34185_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b34185 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b34185 (by norm_num))

lemma cosh_b34275_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b34275 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b34275 (by norm_num))

lemma cosh_b34365_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b34365 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b34365 (by norm_num))

lemma cosh_b34455_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b34455 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b34455 (by norm_num))

lemma cosh_b34550_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b34550 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b34550 (by norm_num))

lemma cosh_b34640_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b34640 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b34640 (by norm_num))

lemma cosh_b34730_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b34730 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b34730 (by norm_num))

lemma cosh_b34820_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b34820 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b34820 (by norm_num))

lemma cosh_b34910_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b34910 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b34910 (by norm_num))

lemma cosh_b35000_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b35000 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b35000 (by norm_num))

lemma cosh_b35095_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b35095 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b35095 (by norm_num))

lemma cosh_b35185_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b35185 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b35185 (by norm_num))

lemma cosh_b35275_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b35275 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b35275 (by norm_num))

lemma cosh_b35365_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b35365 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b35365 (by norm_num))

lemma cosh_b35455_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b35455 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b35455 (by norm_num))

lemma cosh_b35550_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b35550 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b35550 (by norm_num))

lemma cosh_b35640_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b35640 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b35640 (by norm_num))

lemma cosh_b35730_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b35730 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b35730 (by norm_num))

lemma cosh_b35820_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b35820 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b35820 (by norm_num))

lemma cosh_b35910_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b35910 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b35910 (by norm_num))

lemma cosh_b36000_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b36000 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b36000 (by norm_num))

lemma cosh_b36095_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b36095 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b36095 (by norm_num))

lemma cosh_b36185_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b36185 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b36185 (by norm_num))

lemma cosh_b36275_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b36275 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b36275 (by norm_num))

lemma cosh_b36365_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b36365 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b36365 (by norm_num))

lemma cosh_b36455_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b36455 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b36455 (by norm_num))

lemma cosh_b36550_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b36550 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b36550 (by norm_num))

lemma cosh_b36640_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b36640 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b36640 (by norm_num))

lemma cosh_b36730_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b36730 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b36730 (by norm_num))

lemma cosh_b36820_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b36820 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b36820 (by norm_num))

lemma cosh_b36910_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b36910 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b36910 (by norm_num))

lemma cosh_b37000_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b37000 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b37000 (by norm_num))

lemma cosh_b37095_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b37095 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b37095 (by norm_num))

lemma cosh_b37185_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b37185 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b37185 (by norm_num))

lemma cosh_b37275_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b37275 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b37275 (by norm_num))

lemma cosh_b37365_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b37365 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b37365 (by norm_num))

lemma cosh_b37455_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b37455 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b37455 (by norm_num))

lemma cosh_b37550_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b37550 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b37550 (by norm_num))

lemma cosh_b37640_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b37640 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b37640 (by norm_num))

lemma cosh_b37730_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b37730 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b37730 (by norm_num))

lemma cosh_b37820_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b37820 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b37820 (by norm_num))

lemma cosh_b37910_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b37910 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b37910 (by norm_num))

lemma cosh_b38000_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b38000 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b38000 (by norm_num))

lemma cosh_b38095_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b38095 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b38095 (by norm_num))

lemma cosh_b38185_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b38185 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b38185 (by norm_num))

lemma cosh_b38275_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b38275 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b38275 (by norm_num))

lemma cosh_b38365_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b38365 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b38365 (by norm_num))

lemma cosh_b38455_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b38455 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b38455 (by norm_num))

lemma cosh_b38550_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b38550 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b38550 (by norm_num))

lemma cosh_b38640_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b38640 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b38640 (by norm_num))

lemma cosh_b38730_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b38730 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b38730 (by norm_num))

lemma cosh_b38820_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b38820 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b38820 (by norm_num))

lemma cosh_b38910_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b38910 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b38910 (by norm_num))

lemma cosh_b39000_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b39000 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b39000 (by norm_num))

lemma cosh_b39095_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b39095 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b39095 (by norm_num))

lemma cosh_b39185_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b39185 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b39185 (by norm_num))

lemma cosh_b39275_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b39275 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b39275 (by norm_num))

lemma cosh_b39365_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b39365 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b39365 (by norm_num))

lemma cosh_b39455_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b39455 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b39455 (by norm_num))

lemma cosh_b39550_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b39550 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b39550 (by norm_num))

lemma cosh_b39640_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b39640 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b39640 (by norm_num))

lemma cosh_b39730_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b39730 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b39730 (by norm_num))

lemma cosh_b39820_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b39820 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b39820 (by norm_num))

lemma cosh_b39910_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b39910 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b39910 (by norm_num))

lemma cosh_b40000_ub : cosh ((4 : ℝ) / 1) ≤ (298095798801 : ℝ) / 100000000 := by
  have exp_b40000 : exp (((4 : ℝ) / 1)^2 / 2) ≤ (298095798801 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 33) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 33, (((4 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((4 : ℝ) / 1)^2 / 2) ^ 33 * (33 + 1) / (Nat.factorial 33 * 33) ≤
          (298095798801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((4 : ℝ) / 1)).trans (le_trans exp_b40000 (by norm_num))

lemma cosh_b40095_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b40095 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b40095 (by norm_num))

lemma cosh_b40185_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b40185 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b40185 (by norm_num))

lemma cosh_b40275_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b40275 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b40275 (by norm_num))

lemma cosh_b40365_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b40365 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b40365 (by norm_num))

lemma cosh_b40455_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b40455 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b40455 (by norm_num))

lemma cosh_b40550_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b40550 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b40550 (by norm_num))

lemma cosh_b40640_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b40640 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b40640 (by norm_num))

lemma cosh_b40730_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b40730 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b40730 (by norm_num))

lemma cosh_b40820_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b40820 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b40820 (by norm_num))

lemma cosh_b40910_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b40910 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b40910 (by norm_num))

lemma cosh_b41000_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b41000 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b41000 (by norm_num))

lemma cosh_b41095_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b41095 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b41095 (by norm_num))

lemma cosh_b41185_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b41185 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b41185 (by norm_num))

lemma cosh_b41275_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b41275 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b41275 (by norm_num))

lemma cosh_b41365_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b41365 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b41365 (by norm_num))

lemma cosh_b41455_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b41455 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b41455 (by norm_num))

lemma cosh_b41550_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b41550 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b41550 (by norm_num))

lemma cosh_b41640_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b41640 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b41640 (by norm_num))

lemma cosh_b41730_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b41730 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b41730 (by norm_num))

lemma cosh_b41820_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b41820 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b41820 (by norm_num))

lemma cosh_b41910_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b41910 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b41910 (by norm_num))

lemma cosh_b42000_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b42000 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b42000 (by norm_num))

lemma cosh_b42095_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b42095 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b42095 (by norm_num))

lemma cosh_b42185_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b42185 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b42185 (by norm_num))

lemma cosh_b42275_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b42275 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b42275 (by norm_num))

lemma cosh_b42365_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b42365 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b42365 (by norm_num))

lemma cosh_b42455_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b42455 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b42455 (by norm_num))

lemma cosh_b42550_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b42550 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b42550 (by norm_num))

lemma cosh_b42640_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b42640 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b42640 (by norm_num))

lemma cosh_b42730_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b42730 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b42730 (by norm_num))

lemma cosh_b42820_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b42820 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b42820 (by norm_num))

lemma cosh_b42910_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b42910 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b42910 (by norm_num))

lemma cosh_b43000_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b43000 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b43000 (by norm_num))

lemma cosh_b43095_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b43095 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b43095 (by norm_num))

lemma cosh_b43185_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b43185 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b43185 (by norm_num))

lemma cosh_b43275_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b43275 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b43275 (by norm_num))

lemma cosh_b43365_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b43365 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b43365 (by norm_num))

lemma cosh_b43455_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b43455 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b43455 (by norm_num))

lemma cosh_b43550_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b43550 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b43550 (by norm_num))

lemma cosh_b43640_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b43640 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b43640 (by norm_num))

lemma cosh_b43730_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b43730 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b43730 (by norm_num))

lemma cosh_b43820_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b43820 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b43820 (by norm_num))

lemma cosh_b43910_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b43910 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b43910 (by norm_num))

lemma cosh_b44000_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b44000 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b44000 (by norm_num))

lemma cosh_b44095_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b44095 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b44095 (by norm_num))

lemma cosh_b44185_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b44185 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b44185 (by norm_num))

lemma cosh_b44275_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b44275 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b44275 (by norm_num))

lemma cosh_b44365_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b44365 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b44365 (by norm_num))

lemma cosh_b44455_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b44455 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b44455 (by norm_num))

lemma cosh_b44550_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b44550 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b44550 (by norm_num))

lemma cosh_b44640_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b44640 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b44640 (by norm_num))

lemma cosh_b44730_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b44730 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b44730 (by norm_num))

lemma cosh_b44820_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b44820 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b44820 (by norm_num))

lemma cosh_b44910_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b44910 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b44910 (by norm_num))

lemma cosh_b45000_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b45000 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b45000 (by norm_num))

lemma cosh_b45095_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b45095 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b45095 (by norm_num))

lemma cosh_b45185_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b45185 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b45185 (by norm_num))

lemma cosh_b45275_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b45275 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b45275 (by norm_num))

lemma cosh_b45365_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b45365 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b45365 (by norm_num))

lemma cosh_b45455_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b45455 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b45455 (by norm_num))

lemma cosh_b45550_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b45550 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b45550 (by norm_num))

lemma cosh_b45640_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b45640 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b45640 (by norm_num))

lemma cosh_b45730_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b45730 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b45730 (by norm_num))

lemma cosh_b45820_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b45820 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b45820 (by norm_num))

lemma cosh_b45910_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b45910 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b45910 (by norm_num))

lemma cosh_b46000_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b46000 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b46000 (by norm_num))

lemma cosh_b46095_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b46095 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b46095 (by norm_num))

lemma cosh_b46185_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b46185 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b46185 (by norm_num))

lemma cosh_b46275_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b46275 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b46275 (by norm_num))

lemma cosh_b46365_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b46365 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b46365 (by norm_num))

lemma cosh_b46455_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b46455 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b46455 (by norm_num))

lemma cosh_b46550_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b46550 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b46550 (by norm_num))

lemma cosh_b46640_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b46640 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b46640 (by norm_num))

lemma cosh_b46730_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b46730 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b46730 (by norm_num))

lemma cosh_b46820_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b46820 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b46820 (by norm_num))

lemma cosh_b46910_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b46910 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b46910 (by norm_num))

lemma cosh_b47000_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b47000 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b47000 (by norm_num))

lemma cosh_b47095_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b47095 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b47095 (by norm_num))

lemma cosh_b47185_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b47185 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b47185 (by norm_num))

lemma cosh_b47275_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b47275 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b47275 (by norm_num))

lemma cosh_b47365_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b47365 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b47365 (by norm_num))

lemma cosh_b47455_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b47455 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b47455 (by norm_num))

lemma cosh_b47550_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b47550 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b47550 (by norm_num))

lemma cosh_b47640_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b47640 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b47640 (by norm_num))

lemma cosh_b47730_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b47730 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b47730 (by norm_num))

lemma cosh_b47820_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b47820 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b47820 (by norm_num))

lemma cosh_b47910_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b47910 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b47910 (by norm_num))

lemma cosh_b48000_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b48000 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b48000 (by norm_num))

lemma cosh_b48095_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b48095 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b48095 (by norm_num))

lemma cosh_b48185_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b48185 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b48185 (by norm_num))

lemma cosh_b48275_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b48275 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b48275 (by norm_num))

lemma cosh_b48365_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b48365 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b48365 (by norm_num))

lemma cosh_b48455_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b48455 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b48455 (by norm_num))

lemma cosh_b48550_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b48550 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b48550 (by norm_num))

lemma cosh_b48640_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b48640 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b48640 (by norm_num))

lemma cosh_b48730_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b48730 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b48730 (by norm_num))

lemma cosh_b48820_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b48820 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b48820 (by norm_num))

lemma cosh_b48910_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b48910 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b48910 (by norm_num))

lemma cosh_b49000_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b49000 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b49000 (by norm_num))

lemma cosh_b49095_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b49095 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b49095 (by norm_num))

lemma cosh_b49185_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b49185 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b49185 (by norm_num))

lemma cosh_b49275_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b49275 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b49275 (by norm_num))

lemma cosh_b49365_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b49365 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b49365 (by norm_num))

lemma cosh_b49455_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b49455 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b49455 (by norm_num))

lemma cosh_b49550_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b49550 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b49550 (by norm_num))

lemma cosh_b49640_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b49640 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b49640 (by norm_num))

lemma cosh_b49730_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b49730 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b49730 (by norm_num))

lemma cosh_b49820_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b49820 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b49820 (by norm_num))

lemma cosh_b49910_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b49910 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b49910 (by norm_num))

lemma cosh_b50000_ub : cosh ((5 : ℝ) / 1) ≤ (26833728652101 : ℝ) / 100000000 := by
  have exp_b50000 : exp (((5 : ℝ) / 1)^2 / 2) ≤ (26833728652101 : ℝ) / 100000000 := by
    have ht : ((5 : ℝ) / 1)^2 / 2 ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 44) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 44, (((5 : ℝ) / 1)^2 / 2) ^ m / (Nat.factorial m)) +
          (((5 : ℝ) / 1)^2 / 2) ^ 44 * (44 + 1) / (Nat.factorial 44 * 44) ≤
          (26833728652101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  exact (cosh_le_exp_half_sq ((5 : ℝ) / 1)).trans (le_trans exp_b50000 (by norm_num))

end UgpLean.Substrate.PhiMDLFluctuationSpectrum
