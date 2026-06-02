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

lemma cosh_b14185_ub : cosh ((2837 : ℝ) / 2000) ≤ (225000634 : ℝ) / 100000000 := by
  have exp_frac_b14185 : exp ((837 : ℝ) / 2000) ≤ (151968101 : ℝ) / 100000000 := by
    have ht : ((837 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((837 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((837 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (151968101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2837 : ℝ) / 2000) = exp 1 * exp ((837 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (837 : ℝ) / 2000 = (2837 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((2837 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2837 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b14185 (exp_pos ((837 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2837 : ℝ) / 2000), exp_pos (-((2837 : ℝ) / 2000))]

lemma cosh_b14275_ub : cosh ((571 : ℝ) / 400) ≤ (226868451 : ℝ) / 100000000 := by
  have exp_frac_b14275 : exp ((171 : ℝ) / 400) ≤ (153342001 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((171 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((171 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (153342001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((571 : ℝ) / 400) = exp 1 * exp ((171 : ℝ) / 400) := by
    rw [← exp_add, show (1 : ℝ) + (171 : ℝ) / 400 = (571 : ℝ) / 400 by norm_num]
  have hneg : exp (-((571 : ℝ) / 400)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((571 : ℝ) / 400) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b14275 (exp_pos ((171 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((571 : ℝ) / 400), exp_pos (-((571 : ℝ) / 400))]

lemma cosh_b14365_ub : cosh ((2873 : ℝ) / 2000) ≤ (228753126 : ℝ) / 100000000 := by
  have exp_frac_b14365 : exp ((873 : ℝ) / 2000) ≤ (154728301 : ℝ) / 100000000 := by
    have ht : ((873 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((873 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((873 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (154728301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2873 : ℝ) / 2000) = exp 1 * exp ((873 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (873 : ℝ) / 2000 = (2873 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((2873 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2873 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b14365 (exp_pos ((873 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2873 : ℝ) / 2000), exp_pos (-((2873 : ℝ) / 2000))]

lemma cosh_b14455_ub : cosh ((2891 : ℝ) / 2000) ≤ (230654794 : ℝ) / 100000000 := by
  have exp_frac_b14455 : exp ((891 : ℝ) / 2000) ≤ (156127101 : ℝ) / 100000000 := by
    have ht : ((891 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((891 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((891 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (156127101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2891 : ℝ) / 2000) = exp 1 * exp ((891 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (891 : ℝ) / 2000 = (2891 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((2891 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2891 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b14455 (exp_pos ((891 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2891 : ℝ) / 2000), exp_pos (-((2891 : ℝ) / 2000))]

lemma cosh_b14550_ub : cosh ((291 : ℝ) / 200) ≤ (232680857 : ℝ) / 100000000 := by
  have exp_frac_b14550 : exp ((91 : ℝ) / 200) ≤ (157617401 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (157617401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((291 : ℝ) / 200) = exp 1 * exp ((91 : ℝ) / 200) := by
    rw [← exp_add, show (1 : ℝ) + (91 : ℝ) / 200 = (291 : ℝ) / 200 by norm_num]
  have hneg : exp (-((291 : ℝ) / 200)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((291 : ℝ) / 200) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b14550 (exp_pos ((91 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((291 : ℝ) / 200), exp_pos (-((291 : ℝ) / 200))]

lemma cosh_b14640_ub : cosh ((183 : ℝ) / 125) ≤ (234618009 : ℝ) / 100000000 := by
  have exp_frac_b14640 : exp ((58 : ℝ) / 125) ≤ (159042301 : ℝ) / 100000000 := by
    have ht : ((58 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((58 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((58 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (159042301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((183 : ℝ) / 125) = exp 1 * exp ((58 : ℝ) / 125) := by
    rw [← exp_add, show (1 : ℝ) + (58 : ℝ) / 125 = (183 : ℝ) / 125 by norm_num]
  have hneg : exp (-((183 : ℝ) / 125)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((183 : ℝ) / 125) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b14640 (exp_pos ((58 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((183 : ℝ) / 125), exp_pos (-((183 : ℝ) / 125))]

lemma cosh_b14730_ub : cosh ((1473 : ℝ) / 1000) ≤ (236572834 : ℝ) / 100000000 := by
  have exp_frac_b14730 : exp ((473 : ℝ) / 1000) ≤ (160480201 : ℝ) / 100000000 := by
    have ht : ((473 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((473 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((473 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (160480201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1473 : ℝ) / 1000) = exp 1 * exp ((473 : ℝ) / 1000) := by
    rw [← exp_add, show (1 : ℝ) + (473 : ℝ) / 1000 = (1473 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((1473 : ℝ) / 1000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1473 : ℝ) / 1000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b14730 (exp_pos ((473 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1473 : ℝ) / 1000), exp_pos (-((1473 : ℝ) / 1000))]

lemma cosh_b14820_ub : cosh ((741 : ℝ) / 500) ≤ (238545196 : ℝ) / 100000000 := by
  have exp_frac_b14820 : exp ((241 : ℝ) / 500) ≤ (161931001 : ℝ) / 100000000 := by
    have ht : ((241 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((241 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((241 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (161931001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((741 : ℝ) / 500) = exp 1 * exp ((241 : ℝ) / 500) := by
    rw [← exp_add, show (1 : ℝ) + (241 : ℝ) / 500 = (741 : ℝ) / 500 by norm_num]
  have hneg : exp (-((741 : ℝ) / 500)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((741 : ℝ) / 500) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b14820 (exp_pos ((241 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((741 : ℝ) / 500), exp_pos (-((741 : ℝ) / 500))]

lemma cosh_b14910_ub : cosh ((1491 : ℝ) / 1000) ≤ (240535504 : ℝ) / 100000000 := by
  have exp_frac_b14910 : exp ((491 : ℝ) / 1000) ≤ (163395001 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((491 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((491 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (163395001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1491 : ℝ) / 1000) = exp 1 * exp ((491 : ℝ) / 1000) := by
    rw [← exp_add, show (1 : ℝ) + (491 : ℝ) / 1000 = (1491 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((1491 : ℝ) / 1000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1491 : ℝ) / 1000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b14910 (exp_pos ((491 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1491 : ℝ) / 1000), exp_pos (-((1491 : ℝ) / 1000))]

lemma cosh_b15000_ub : cosh ((3 : ℝ) / 2) ≤ (242543758 : ℝ) / 100000000 := by
  have exp_frac_b15000 : exp ((1 : ℝ) / 2) ≤ (164872201 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 2) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1 : ℝ) / 2) ^ m / (Nat.factorial m)) +
          ((1 : ℝ) / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (164872201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3 : ℝ) / 2) = exp 1 * exp ((1 : ℝ) / 2) := by
    rw [← exp_add, show (1 : ℝ) + (1 : ℝ) / 2 = (3 : ℝ) / 2 by norm_num]
  have hneg : exp (-((3 : ℝ) / 2)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3 : ℝ) / 2) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b15000 (exp_pos ((1 : ℝ) / 2)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3 : ℝ) / 2), exp_pos (-((3 : ℝ) / 2))]

lemma cosh_b15095_ub : cosh ((3019 : ℝ) / 2000) ≤ (244683203 : ℝ) / 100000000 := by
  have exp_frac_b15095 : exp ((1019 : ℝ) / 2000) ≤ (166445901 : ℝ) / 100000000 := by
    have ht : ((1019 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1019 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1019 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (166445901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3019 : ℝ) / 2000) = exp 1 * exp ((1019 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1019 : ℝ) / 2000 = (3019 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3019 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3019 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b15095 (exp_pos ((1019 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3019 : ℝ) / 2000), exp_pos (-((3019 : ℝ) / 2000))]

lemma cosh_b15185_ub : cosh ((3037 : ℝ) / 2000) ≤ (246728979 : ℝ) / 100000000 := by
  have exp_frac_b15185 : exp ((1037 : ℝ) / 2000) ≤ (167950701 : ℝ) / 100000000 := by
    have ht : ((1037 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1037 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1037 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (167950701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3037 : ℝ) / 2000) = exp 1 * exp ((1037 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1037 : ℝ) / 2000 = (3037 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3037 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3037 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b15185 (exp_pos ((1037 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3037 : ℝ) / 2000), exp_pos (-((3037 : ℝ) / 2000))]

lemma cosh_b15275_ub : cosh ((611 : ℝ) / 400) ≤ (248793243 : ℝ) / 100000000 := by
  have exp_frac_b15275 : exp ((211 : ℝ) / 400) ≤ (169469101 : ℝ) / 100000000 := by
    have ht : ((211 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((211 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((211 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (169469101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((611 : ℝ) / 400) = exp 1 * exp ((211 : ℝ) / 400) := by
    rw [← exp_add, show (1 : ℝ) + (211 : ℝ) / 400 = (611 : ℝ) / 400 by norm_num]
  have hneg : exp (-((611 : ℝ) / 400)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((611 : ℝ) / 400) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b15275 (exp_pos ((211 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((611 : ℝ) / 400), exp_pos (-((611 : ℝ) / 400))]

lemma cosh_b15365_ub : cosh ((3073 : ℝ) / 2000) ≤ (250876133 : ℝ) / 100000000 := by
  have exp_frac_b15365 : exp ((1073 : ℝ) / 2000) ≤ (171001201 : ℝ) / 100000000 := by
    have ht : ((1073 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1073 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1073 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (171001201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3073 : ℝ) / 2000) = exp 1 * exp ((1073 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1073 : ℝ) / 2000 = (3073 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3073 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3073 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b15365 (exp_pos ((1073 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3073 : ℝ) / 2000), exp_pos (-((3073 : ℝ) / 2000))]

lemma cosh_b15455_ub : cosh ((3091 : ℝ) / 2000) ≤ (252977784 : ℝ) / 100000000 := by
  have exp_frac_b15455 : exp ((1091 : ℝ) / 2000) ≤ (172547101 : ℝ) / 100000000 := by
    have ht : ((1091 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1091 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1091 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (172547101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3091 : ℝ) / 2000) = exp 1 * exp ((1091 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1091 : ℝ) / 2000 = (3091 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3091 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3091 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b15455 (exp_pos ((1091 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3091 : ℝ) / 2000), exp_pos (-((3091 : ℝ) / 2000))]

lemma cosh_b15550_ub : cosh ((311 : ℝ) / 200) ≤ (255216881 : ℝ) / 100000000 := by
  have exp_frac_b15550 : exp ((111 : ℝ) / 200) ≤ (174194101 : ℝ) / 100000000 := by
    have ht : ((111 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((111 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((111 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (174194101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((311 : ℝ) / 200) = exp 1 * exp ((111 : ℝ) / 200) := by
    rw [← exp_add, show (1 : ℝ) + (111 : ℝ) / 200 = (311 : ℝ) / 200 by norm_num]
  have hneg : exp (-((311 : ℝ) / 200)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((311 : ℝ) / 200) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b15550 (exp_pos ((111 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((311 : ℝ) / 200), exp_pos (-((311 : ℝ) / 200))]

lemma cosh_b15640_ub : cosh ((391 : ℝ) / 250) ≤ (257357957 : ℝ) / 100000000 := by
  have exp_frac_b15640 : exp ((141 : ℝ) / 250) ≤ (175769001 : ℝ) / 100000000 := by
    have ht : ((141 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((141 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((141 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (175769001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((391 : ℝ) / 250) = exp 1 * exp ((141 : ℝ) / 250) := by
    rw [← exp_add, show (1 : ℝ) + (141 : ℝ) / 250 = (391 : ℝ) / 250 by norm_num]
  have hneg : exp (-((391 : ℝ) / 250)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((391 : ℝ) / 250) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b15640 (exp_pos ((141 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((391 : ℝ) / 250), exp_pos (-((391 : ℝ) / 250))]

lemma cosh_b15730_ub : cosh ((1573 : ℝ) / 1000) ≤ (259518203 : ℝ) / 100000000 := by
  have exp_frac_b15730 : exp ((573 : ℝ) / 1000) ≤ (177358001 : ℝ) / 100000000 := by
    have ht : ((573 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((573 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((573 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (177358001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1573 : ℝ) / 1000) = exp 1 * exp ((573 : ℝ) / 1000) := by
    rw [← exp_add, show (1 : ℝ) + (573 : ℝ) / 1000 = (1573 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((1573 : ℝ) / 1000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1573 : ℝ) / 1000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b15730 (exp_pos ((573 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1573 : ℝ) / 1000), exp_pos (-((1573 : ℝ) / 1000))]

lemma cosh_b15820_ub : cosh ((791 : ℝ) / 500) ≤ (261698161 : ℝ) / 100000000 := by
  have exp_frac_b15820 : exp ((291 : ℝ) / 500) ≤ (178961501 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (178961501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((791 : ℝ) / 500) = exp 1 * exp ((291 : ℝ) / 500) := by
    rw [← exp_add, show (1 : ℝ) + (291 : ℝ) / 500 = (791 : ℝ) / 500 by norm_num]
  have hneg : exp (-((791 : ℝ) / 500)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((791 : ℝ) / 500) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b15820 (exp_pos ((291 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((791 : ℝ) / 500), exp_pos (-((791 : ℝ) / 500))]

lemma cosh_b15910_ub : cosh ((1591 : ℝ) / 1000) ≤ (263897696 : ℝ) / 100000000 := by
  have exp_frac_b15910 : exp ((591 : ℝ) / 1000) ≤ (180579401 : ℝ) / 100000000 := by
    have ht : ((591 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((591 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((591 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (180579401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1591 : ℝ) / 1000) = exp 1 * exp ((591 : ℝ) / 1000) := by
    rw [← exp_add, show (1 : ℝ) + (591 : ℝ) / 1000 = (1591 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((1591 : ℝ) / 1000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1591 : ℝ) / 1000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b15910 (exp_pos ((591 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1591 : ℝ) / 1000), exp_pos (-((1591 : ℝ) / 1000))]

lemma cosh_b16000_ub : cosh ((8 : ℝ) / 5) ≤ (266117080 : ℝ) / 100000000 := by
  have exp_frac_b16000 : exp ((3 : ℝ) / 5) ≤ (182211901 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((3 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((3 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (182211901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8 : ℝ) / 5) = exp 1 * exp ((3 : ℝ) / 5) := by
    rw [← exp_add, show (1 : ℝ) + (3 : ℝ) / 5 = (8 : ℝ) / 5 by norm_num]
  have hneg : exp (-((8 : ℝ) / 5)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8 : ℝ) / 5) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b16000 (exp_pos ((3 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8 : ℝ) / 5), exp_pos (-((8 : ℝ) / 5))]

lemma cosh_b16095_ub : cosh ((3219 : ℝ) / 2000) ≤ (268481658 : ℝ) / 100000000 := by
  have exp_frac_b16095 : exp ((1219 : ℝ) / 2000) ≤ (183951201 : ℝ) / 100000000 := by
    have ht : ((1219 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1219 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1219 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (183951201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3219 : ℝ) / 2000) = exp 1 * exp ((1219 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1219 : ℝ) / 2000 = (3219 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3219 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3219 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b16095 (exp_pos ((1219 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3219 : ℝ) / 2000), exp_pos (-((3219 : ℝ) / 2000))]

lemma cosh_b16185_ub : cosh ((3237 : ℝ) / 2000) ≤ (270742507 : ℝ) / 100000000 := by
  have exp_frac_b16185 : exp ((1237 : ℝ) / 2000) ≤ (185614201 : ℝ) / 100000000 := by
    have ht : ((1237 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1237 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1237 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (185614201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3237 : ℝ) / 2000) = exp 1 * exp ((1237 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1237 : ℝ) / 2000 = (3237 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3237 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3237 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b16185 (exp_pos ((1237 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3237 : ℝ) / 2000), exp_pos (-((3237 : ℝ) / 2000))]

lemma cosh_b16275_ub : cosh ((651 : ℝ) / 400) ≤ (273023884 : ℝ) / 100000000 := by
  have exp_frac_b16275 : exp ((251 : ℝ) / 400) ≤ (187292301 : ℝ) / 100000000 := by
    have ht : ((251 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((251 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((251 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (187292301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((651 : ℝ) / 400) = exp 1 * exp ((251 : ℝ) / 400) := by
    rw [← exp_add, show (1 : ℝ) + (251 : ℝ) / 400 = (651 : ℝ) / 400 by norm_num]
  have hneg : exp (-((651 : ℝ) / 400)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((651 : ℝ) / 400) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b16275 (exp_pos ((251 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((651 : ℝ) / 400), exp_pos (-((651 : ℝ) / 400))]

lemma cosh_b16365_ub : cosh ((3273 : ℝ) / 2000) ≤ (275325789 : ℝ) / 100000000 := by
  have exp_frac_b16365 : exp ((1273 : ℝ) / 2000) ≤ (188985501 : ℝ) / 100000000 := by
    have ht : ((1273 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1273 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1273 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (188985501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3273 : ℝ) / 2000) = exp 1 * exp ((1273 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1273 : ℝ) / 2000 = (3273 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3273 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3273 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b16365 (exp_pos ((1273 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3273 : ℝ) / 2000), exp_pos (-((3273 : ℝ) / 2000))]

lemma cosh_b16455_ub : cosh ((3291 : ℝ) / 2000) ≤ (277648631 : ℝ) / 100000000 := by
  have exp_frac_b16455 : exp ((1291 : ℝ) / 2000) ≤ (190694101 : ℝ) / 100000000 := by
    have ht : ((1291 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1291 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1291 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (190694101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3291 : ℝ) / 2000) = exp 1 * exp ((1291 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1291 : ℝ) / 2000 = (3291 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3291 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3291 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b16455 (exp_pos ((1291 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3291 : ℝ) / 2000), exp_pos (-((3291 : ℝ) / 2000))]

lemma cosh_b16550_ub : cosh ((331 : ℝ) / 200) ≤ (280123193 : ℝ) / 100000000 := by
  have exp_frac_b16550 : exp ((131 : ℝ) / 200) ≤ (192514301 : ℝ) / 100000000 := by
    have ht : ((131 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((131 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((131 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (192514301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((331 : ℝ) / 200) = exp 1 * exp ((131 : ℝ) / 200) := by
    rw [← exp_add, show (1 : ℝ) + (131 : ℝ) / 200 = (331 : ℝ) / 200 by norm_num]
  have hneg : exp (-((331 : ℝ) / 200)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((331 : ℝ) / 200) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b16550 (exp_pos ((131 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((331 : ℝ) / 200), exp_pos (-((331 : ℝ) / 200))]

lemma cosh_b16640_ub : cosh ((208 : ℝ) / 125) ≤ (282489402 : ℝ) / 100000000 := by
  have exp_frac_b16640 : exp ((83 : ℝ) / 125) ≤ (194254801 : ℝ) / 100000000 := by
    have ht : ((83 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((83 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((83 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (194254801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((208 : ℝ) / 125) = exp 1 * exp ((83 : ℝ) / 125) := by
    rw [← exp_add, show (1 : ℝ) + (83 : ℝ) / 125 = (208 : ℝ) / 125 by norm_num]
  have hneg : exp (-((208 : ℝ) / 125)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((208 : ℝ) / 125) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b16640 (exp_pos ((83 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((208 : ℝ) / 125), exp_pos (-((208 : ℝ) / 125))]

lemma cosh_b16730_ub : cosh ((1673 : ℝ) / 1000) ≤ (284876820 : ℝ) / 100000000 := by
  have exp_frac_b16730 : exp ((673 : ℝ) / 1000) ≤ (196010901 : ℝ) / 100000000 := by
    have ht : ((673 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((673 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((673 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (196010901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1673 : ℝ) / 1000) = exp 1 * exp ((673 : ℝ) / 1000) := by
    rw [← exp_add, show (1 : ℝ) + (673 : ℝ) / 1000 = (1673 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((1673 : ℝ) / 1000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1673 : ℝ) / 1000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b16730 (exp_pos ((673 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1673 : ℝ) / 1000), exp_pos (-((1673 : ℝ) / 1000))]

lemma cosh_b16820_ub : cosh ((841 : ℝ) / 500) ≤ (287285990 : ℝ) / 100000000 := by
  have exp_frac_b16820 : exp ((341 : ℝ) / 500) ≤ (197783001 : ℝ) / 100000000 := by
    have ht : ((341 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((341 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((341 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (197783001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((841 : ℝ) / 500) = exp 1 * exp ((341 : ℝ) / 500) := by
    rw [← exp_add, show (1 : ℝ) + (341 : ℝ) / 500 = (841 : ℝ) / 500 by norm_num]
  have hneg : exp (-((841 : ℝ) / 500)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((841 : ℝ) / 500) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b16820 (exp_pos ((341 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((841 : ℝ) / 500), exp_pos (-((841 : ℝ) / 500))]

lemma cosh_b16910_ub : cosh ((1691 : ℝ) / 1000) ≤ (289716912 : ℝ) / 100000000 := by
  have exp_frac_b16910 : exp ((691 : ℝ) / 1000) ≤ (199571101 : ℝ) / 100000000 := by
    have ht : ((691 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((691 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((691 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (199571101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1691 : ℝ) / 1000) = exp 1 * exp ((691 : ℝ) / 1000) := by
    rw [← exp_add, show (1 : ℝ) + (691 : ℝ) / 1000 = (1691 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((1691 : ℝ) / 1000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1691 : ℝ) / 1000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b16910 (exp_pos ((691 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1691 : ℝ) / 1000), exp_pos (-((1691 : ℝ) / 1000))]

lemma cosh_b17000_ub : cosh ((17 : ℝ) / 10) ≤ (292169722 : ℝ) / 100000000 := by
  have exp_frac_b17000 : exp ((7 : ℝ) / 10) ≤ (201375301 : ℝ) / 100000000 := by
    have ht : ((7 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((7 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((7 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (201375301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((17 : ℝ) / 10) = exp 1 * exp ((7 : ℝ) / 10) := by
    rw [← exp_add, show (1 : ℝ) + (7 : ℝ) / 10 = (17 : ℝ) / 10 by norm_num]
  have hneg : exp (-((17 : ℝ) / 10)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((17 : ℝ) / 10) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b17000 (exp_pos ((7 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((17 : ℝ) / 10), exp_pos (-((17 : ℝ) / 10))]

lemma cosh_b17095_ub : cosh ((3419 : ℝ) / 2000) ≤ (294782953 : ℝ) / 100000000 := by
  have exp_frac_b17095 : exp ((1419 : ℝ) / 2000) ≤ (203297501 : ℝ) / 100000000 := by
    have ht : ((1419 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1419 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1419 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (203297501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3419 : ℝ) / 2000) = exp 1 * exp ((1419 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1419 : ℝ) / 2000 = (3419 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3419 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3419 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b17095 (exp_pos ((1419 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3419 : ℝ) / 2000), exp_pos (-((3419 : ℝ) / 2000))]

lemma cosh_b17185_ub : cosh ((3437 : ℝ) / 2000) ≤ (297281578 : ℝ) / 100000000 := by
  have exp_frac_b17185 : exp ((1437 : ℝ) / 2000) ≤ (205135401 : ℝ) / 100000000 := by
    have ht : ((1437 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1437 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1437 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (205135401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3437 : ℝ) / 2000) = exp 1 * exp ((1437 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1437 : ℝ) / 2000 = (3437 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3437 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3437 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b17185 (exp_pos ((1437 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3437 : ℝ) / 2000), exp_pos (-((3437 : ℝ) / 2000))]

lemma cosh_b17275_ub : cosh ((691 : ℝ) / 400) ≤ (299802907 : ℝ) / 100000000 := by
  have exp_frac_b17275 : exp ((291 : ℝ) / 400) ≤ (206990001 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (206990001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((691 : ℝ) / 400) = exp 1 * exp ((291 : ℝ) / 400) := by
    rw [← exp_add, show (1 : ℝ) + (291 : ℝ) / 400 = (691 : ℝ) / 400 by norm_num]
  have hneg : exp (-((691 : ℝ) / 400)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((691 : ℝ) / 400) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b17275 (exp_pos ((291 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((691 : ℝ) / 400), exp_pos (-((691 : ℝ) / 400))]

lemma cosh_b17365_ub : cosh ((3473 : ℝ) / 2000) ≤ (302346939 : ℝ) / 100000000 := by
  have exp_frac_b17365 : exp ((1473 : ℝ) / 2000) ≤ (208861301 : ℝ) / 100000000 := by
    have ht : ((1473 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1473 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1473 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (208861301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3473 : ℝ) / 2000) = exp 1 * exp ((1473 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1473 : ℝ) / 2000 = (3473 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3473 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3473 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b17365 (exp_pos ((1473 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3473 : ℝ) / 2000), exp_pos (-((3473 : ℝ) / 2000))]

lemma cosh_b17455_ub : cosh ((3491 : ℝ) / 2000) ≤ (304914083 : ℝ) / 100000000 := by
  have exp_frac_b17455 : exp ((1491 : ℝ) / 2000) ≤ (210749601 : ℝ) / 100000000 := by
    have ht : ((1491 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1491 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1491 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (210749601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3491 : ℝ) / 2000) = exp 1 * exp ((1491 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1491 : ℝ) / 2000 = (3491 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3491 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3491 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b17455 (exp_pos ((1491 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3491 : ℝ) / 2000), exp_pos (-((3491 : ℝ) / 2000))]

lemma cosh_b17550_ub : cosh ((351 : ℝ) / 200) ≤ (307648853 : ℝ) / 100000000 := by
  have exp_frac_b17550 : exp ((151 : ℝ) / 200) ≤ (212761201 : ℝ) / 100000000 := by
    have ht : ((151 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((151 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((151 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (212761201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((351 : ℝ) / 200) = exp 1 * exp ((151 : ℝ) / 200) := by
    rw [← exp_add, show (1 : ℝ) + (151 : ℝ) / 200 = (351 : ℝ) / 200 by norm_num]
  have hneg : exp (-((351 : ℝ) / 200)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((351 : ℝ) / 200) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b17550 (exp_pos ((151 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((351 : ℝ) / 200), exp_pos (-((351 : ℝ) / 200))]

lemma cosh_b17640_ub : cosh ((441 : ℝ) / 250) ≤ (310263852 : ℝ) / 100000000 := by
  have exp_frac_b17640 : exp ((191 : ℝ) / 250) ≤ (214684701 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (214684701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((441 : ℝ) / 250) = exp 1 * exp ((191 : ℝ) / 250) := by
    rw [← exp_add, show (1 : ℝ) + (191 : ℝ) / 250 = (441 : ℝ) / 250 by norm_num]
  have hneg : exp (-((441 : ℝ) / 250)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((441 : ℝ) / 250) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b17640 (exp_pos ((191 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((441 : ℝ) / 250), exp_pos (-((441 : ℝ) / 250))]

lemma cosh_b17730_ub : cosh ((1773 : ℝ) / 1000) ≤ (312902505 : ℝ) / 100000000 := by
  have exp_frac_b17730 : exp ((773 : ℝ) / 1000) ≤ (216625601 : ℝ) / 100000000 := by
    have ht : ((773 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((773 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((773 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (216625601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1773 : ℝ) / 1000) = exp 1 * exp ((773 : ℝ) / 1000) := by
    rw [← exp_add, show (1 : ℝ) + (773 : ℝ) / 1000 = (1773 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((1773 : ℝ) / 1000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1773 : ℝ) / 1000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b17730 (exp_pos ((773 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1773 : ℝ) / 1000), exp_pos (-((1773 : ℝ) / 1000))]

lemma cosh_b17820_ub : cosh ((891 : ℝ) / 500) ≤ (315564950 : ℝ) / 100000000 := by
  have exp_frac_b17820 : exp ((391 : ℝ) / 500) ≤ (218584001 : ℝ) / 100000000 := by
    have ht : ((391 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((391 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((391 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (218584001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((891 : ℝ) / 500) = exp 1 * exp ((391 : ℝ) / 500) := by
    rw [← exp_add, show (1 : ℝ) + (391 : ℝ) / 500 = (891 : ℝ) / 500 by norm_num]
  have hneg : exp (-((891 : ℝ) / 500)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((891 : ℝ) / 500) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b17820 (exp_pos ((391 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((891 : ℝ) / 500), exp_pos (-((891 : ℝ) / 500))]

lemma cosh_b17910_ub : cosh ((1791 : ℝ) / 1000) ≤ (318251594 : ℝ) / 100000000 := by
  have exp_frac_b17910 : exp ((791 : ℝ) / 1000) ≤ (220560201 : ℝ) / 100000000 := by
    have ht : ((791 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((791 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((791 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (220560201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1791 : ℝ) / 1000) = exp 1 * exp ((791 : ℝ) / 1000) := by
    rw [← exp_add, show (1 : ℝ) + (791 : ℝ) / 1000 = (1791 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((1791 : ℝ) / 1000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1791 : ℝ) / 1000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b17910 (exp_pos ((791 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1791 : ℝ) / 1000), exp_pos (-((1791 : ℝ) / 1000))]

lemma cosh_b18000_ub : cosh ((9 : ℝ) / 5) ≤ (320962437 : ℝ) / 100000000 := by
  have exp_frac_b18000 : exp ((4 : ℝ) / 5) ≤ (222554201 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((4 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((4 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (222554201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9 : ℝ) / 5) = exp 1 * exp ((4 : ℝ) / 5) := by
    rw [← exp_add, show (1 : ℝ) + (4 : ℝ) / 5 = (9 : ℝ) / 5 by norm_num]
  have hneg : exp (-((9 : ℝ) / 5)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9 : ℝ) / 5) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b18000 (exp_pos ((4 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9 : ℝ) / 5), exp_pos (-((9 : ℝ) / 5))]

lemma cosh_b18095_ub : cosh ((3619 : ℝ) / 2000) ≤ (323850423 : ℝ) / 100000000 := by
  have exp_frac_b18095 : exp ((1619 : ℝ) / 2000) ≤ (224678501 : ℝ) / 100000000 := by
    have ht : ((1619 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1619 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1619 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (224678501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3619 : ℝ) / 2000) = exp 1 * exp ((1619 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1619 : ℝ) / 2000 = (3619 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3619 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3619 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b18095 (exp_pos ((1619 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3619 : ℝ) / 2000), exp_pos (-((3619 : ℝ) / 2000))]

lemma cosh_b18185_ub : cosh ((3637 : ℝ) / 2000) ≤ (326611839 : ℝ) / 100000000 := by
  have exp_frac_b18185 : exp ((1637 : ℝ) / 2000) ≤ (226709701 : ℝ) / 100000000 := by
    have ht : ((1637 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1637 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1637 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (226709701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3637 : ℝ) / 2000) = exp 1 * exp ((1637 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1637 : ℝ) / 2000 = (3637 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3637 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3637 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b18185 (exp_pos ((1637 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3637 : ℝ) / 2000), exp_pos (-((3637 : ℝ) / 2000))]

lemma cosh_b18275_ub : cosh ((731 : ℝ) / 400) ≤ (329398270 : ℝ) / 100000000 := by
  have exp_frac_b18275 : exp ((331 : ℝ) / 400) ≤ (228759301 : ℝ) / 100000000 := by
    have ht : ((331 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((331 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((331 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (228759301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((731 : ℝ) / 400) = exp 1 * exp ((331 : ℝ) / 400) := by
    rw [← exp_add, show (1 : ℝ) + (331 : ℝ) / 400 = (731 : ℝ) / 400 by norm_num]
  have hneg : exp (-((731 : ℝ) / 400)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((731 : ℝ) / 400) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b18275 (exp_pos ((331 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((731 : ℝ) / 400), exp_pos (-((731 : ℝ) / 400))]

lemma cosh_b18365_ub : cosh ((3673 : ℝ) / 2000) ≤ (332209988 : ℝ) / 100000000 := by
  have exp_frac_b18365 : exp ((1673 : ℝ) / 2000) ≤ (230827501 : ℝ) / 100000000 := by
    have ht : ((1673 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1673 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1673 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (230827501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3673 : ℝ) / 2000) = exp 1 * exp ((1673 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1673 : ℝ) / 2000 = (3673 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3673 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3673 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b18365 (exp_pos ((1673 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3673 : ℝ) / 2000), exp_pos (-((3673 : ℝ) / 2000))]

lemma cosh_b18455_ub : cosh ((3691 : ℝ) / 2000) ≤ (335046993 : ℝ) / 100000000 := by
  have exp_frac_b18455 : exp ((1691 : ℝ) / 2000) ≤ (232914301 : ℝ) / 100000000 := by
    have ht : ((1691 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1691 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1691 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (232914301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3691 : ℝ) / 2000) = exp 1 * exp ((1691 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1691 : ℝ) / 2000 = (3691 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3691 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3691 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b18455 (exp_pos ((1691 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3691 : ℝ) / 2000), exp_pos (-((3691 : ℝ) / 2000))]

lemma cosh_b18550_ub : cosh ((371 : ℝ) / 200) ≤ (338069433 : ℝ) / 100000000 := by
  have exp_frac_b18550 : exp ((171 : ℝ) / 200) ≤ (235137501 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((171 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((171 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (235137501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((371 : ℝ) / 200) = exp 1 * exp ((171 : ℝ) / 200) := by
    rw [← exp_add, show (1 : ℝ) + (171 : ℝ) / 200 = (371 : ℝ) / 200 by norm_num]
  have hneg : exp (-((371 : ℝ) / 200)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((371 : ℝ) / 200) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b18550 (exp_pos ((171 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((371 : ℝ) / 200), exp_pos (-((371 : ℝ) / 200))]

lemma cosh_b18640_ub : cosh ((233 : ℝ) / 125) ≤ (340959458 : ℝ) / 100000000 := by
  have exp_frac_b18640 : exp ((108 : ℝ) / 125) ≤ (237263301 : ℝ) / 100000000 := by
    have ht : ((108 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((108 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((108 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (237263301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((233 : ℝ) / 125) = exp 1 * exp ((108 : ℝ) / 125) := by
    rw [← exp_add, show (1 : ℝ) + (108 : ℝ) / 125 = (233 : ℝ) / 125 by norm_num]
  have hneg : exp (-((233 : ℝ) / 125)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((233 : ℝ) / 125) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b18640 (exp_pos ((108 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((233 : ℝ) / 125), exp_pos (-((233 : ℝ) / 125))]

lemma cosh_b18730_ub : cosh ((1873 : ℝ) / 1000) ≤ (343875586 : ℝ) / 100000000 := by
  have exp_frac_b18730 : exp ((873 : ℝ) / 1000) ≤ (239408301 : ℝ) / 100000000 := by
    have ht : ((873 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((873 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((873 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (239408301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1873 : ℝ) / 1000) = exp 1 * exp ((873 : ℝ) / 1000) := by
    rw [← exp_add, show (1 : ℝ) + (873 : ℝ) / 1000 = (1873 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((1873 : ℝ) / 1000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1873 : ℝ) / 1000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b18730 (exp_pos ((873 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1873 : ℝ) / 1000), exp_pos (-((1873 : ℝ) / 1000))]

lemma cosh_b18820_ub : cosh ((941 : ℝ) / 500) ≤ (346818088 : ℝ) / 100000000 := by
  have exp_frac_b18820 : exp ((441 : ℝ) / 500) ≤ (241572701 : ℝ) / 100000000 := by
    have ht : ((441 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((441 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((441 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (241572701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((941 : ℝ) / 500) = exp 1 * exp ((441 : ℝ) / 500) := by
    rw [← exp_add, show (1 : ℝ) + (441 : ℝ) / 500 = (941 : ℝ) / 500 by norm_num]
  have hneg : exp (-((941 : ℝ) / 500)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((941 : ℝ) / 500) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b18820 (exp_pos ((441 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((941 : ℝ) / 500), exp_pos (-((941 : ℝ) / 500))]

lemma cosh_b18910_ub : cosh ((1891 : ℝ) / 1000) ≤ (349787236 : ℝ) / 100000000 := by
  have exp_frac_b18910 : exp ((891 : ℝ) / 1000) ≤ (243756701 : ℝ) / 100000000 := by
    have ht : ((891 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((891 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((891 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (243756701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1891 : ℝ) / 1000) = exp 1 * exp ((891 : ℝ) / 1000) := by
    rw [← exp_add, show (1 : ℝ) + (891 : ℝ) / 1000 = (1891 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((1891 : ℝ) / 1000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1891 : ℝ) / 1000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b18910 (exp_pos ((891 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1891 : ℝ) / 1000), exp_pos (-((1891 : ℝ) / 1000))]

lemma cosh_b19000_ub : cosh ((19 : ℝ) / 10) ≤ (352783166 : ℝ) / 100000000 := by
  have exp_frac_b19000 : exp ((9 : ℝ) / 10) ≤ (245960401 : ℝ) / 100000000 := by
    have ht : ((9 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((9 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((9 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (245960401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((19 : ℝ) / 10) = exp 1 * exp ((9 : ℝ) / 10) := by
    rw [← exp_add, show (1 : ℝ) + (9 : ℝ) / 10 = (19 : ℝ) / 10 by norm_num]
  have hneg : exp (-((19 : ℝ) / 10)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((19 : ℝ) / 10) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b19000 (exp_pos ((9 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((19 : ℝ) / 10), exp_pos (-((19 : ℝ) / 10))]

lemma cosh_b19095_ub : cosh ((3819 : ℝ) / 2000) ≤ (355974864 : ℝ) / 100000000 := by
  have exp_frac_b19095 : exp ((1819 : ℝ) / 2000) ≤ (248308101 : ℝ) / 100000000 := by
    have ht : ((1819 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1819 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1819 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (248308101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3819 : ℝ) / 2000) = exp 1 * exp ((1819 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1819 : ℝ) / 2000 = (3819 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3819 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3819 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b19095 (exp_pos ((1819 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3819 : ℝ) / 2000), exp_pos (-((3819 : ℝ) / 2000))]

lemma cosh_b19185_ub : cosh ((3837 : ℝ) / 2000) ≤ (359026805 : ℝ) / 100000000 := by
  have exp_frac_b19185 : exp ((1837 : ℝ) / 2000) ≤ (250553001 : ℝ) / 100000000 := by
    have ht : ((1837 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1837 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1837 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (250553001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3837 : ℝ) / 2000) = exp 1 * exp ((1837 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1837 : ℝ) / 2000 = (3837 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3837 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3837 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b19185 (exp_pos ((1837 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3837 : ℝ) / 2000), exp_pos (-((3837 : ℝ) / 2000))]

lemma cosh_b19275_ub : cosh ((771 : ℝ) / 400) ≤ (362106209 : ℝ) / 100000000 := by
  have exp_frac_b19275 : exp ((371 : ℝ) / 400) ≤ (252818101 : ℝ) / 100000000 := by
    have ht : ((371 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((371 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((371 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (252818101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((771 : ℝ) / 400) = exp 1 * exp ((371 : ℝ) / 400) := by
    rw [← exp_add, show (1 : ℝ) + (371 : ℝ) / 400 = (771 : ℝ) / 400 by norm_num]
  have hneg : exp (-((771 : ℝ) / 400)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((771 : ℝ) / 400) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b19275 (exp_pos ((371 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((771 : ℝ) / 400), exp_pos (-((771 : ℝ) / 400))]

lemma cosh_b19365_ub : cosh ((3873 : ℝ) / 2000) ≤ (365213618 : ℝ) / 100000000 := by
  have exp_frac_b19365 : exp ((1873 : ℝ) / 2000) ≤ (255103801 : ℝ) / 100000000 := by
    have ht : ((1873 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1873 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1873 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (255103801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3873 : ℝ) / 2000) = exp 1 * exp ((1873 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1873 : ℝ) / 2000 = (3873 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3873 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3873 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b19365 (exp_pos ((1873 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3873 : ℝ) / 2000), exp_pos (-((3873 : ℝ) / 2000))]

lemma cosh_b19455_ub : cosh ((3891 : ℝ) / 2000) ≤ (368349033 : ℝ) / 100000000 := by
  have exp_frac_b19455 : exp ((1891 : ℝ) / 2000) ≤ (257410101 : ℝ) / 100000000 := by
    have ht : ((1891 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1891 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1891 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (257410101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3891 : ℝ) / 2000) = exp 1 * exp ((1891 : ℝ) / 2000) := by
    rw [← exp_add, show (1 : ℝ) + (1891 : ℝ) / 2000 = (3891 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((3891 : ℝ) / 2000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3891 : ℝ) / 2000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b19455 (exp_pos ((1891 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3891 : ℝ) / 2000), exp_pos (-((3891 : ℝ) / 2000))]

lemma cosh_b19550_ub : cosh ((391 : ℝ) / 200) ≤ (371689324 : ℝ) / 100000000 := by
  have exp_frac_b19550 : exp ((191 : ℝ) / 200) ≤ (259867101 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (259867101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((391 : ℝ) / 200) = exp 1 * exp ((191 : ℝ) / 200) := by
    rw [← exp_add, show (1 : ℝ) + (191 : ℝ) / 200 = (391 : ℝ) / 200 by norm_num]
  have hneg : exp (-((391 : ℝ) / 200)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((391 : ℝ) / 200) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b19550 (exp_pos ((191 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((391 : ℝ) / 200), exp_pos (-((391 : ℝ) / 200))]

lemma cosh_b19640_ub : cosh ((491 : ℝ) / 250) ≤ (374883334 : ℝ) / 100000000 := by
  have exp_frac_b19640 : exp ((241 : ℝ) / 250) ≤ (262216501 : ℝ) / 100000000 := by
    have ht : ((241 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((241 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((241 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (262216501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((491 : ℝ) / 250) = exp 1 * exp ((241 : ℝ) / 250) := by
    rw [← exp_add, show (1 : ℝ) + (241 : ℝ) / 250 = (491 : ℝ) / 250 by norm_num]
  have hneg : exp (-((491 : ℝ) / 250)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((491 : ℝ) / 250) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b19640 (exp_pos ((241 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((491 : ℝ) / 250), exp_pos (-((491 : ℝ) / 250))]

lemma cosh_b19730_ub : cosh ((1973 : ℝ) / 1000) ≤ (378106164 : ℝ) / 100000000 := by
  have exp_frac_b19730 : exp ((973 : ℝ) / 1000) ≤ (264587101 : ℝ) / 100000000 := by
    have ht : ((973 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((973 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((973 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (264587101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1973 : ℝ) / 1000) = exp 1 * exp ((973 : ℝ) / 1000) := by
    rw [← exp_add, show (1 : ℝ) + (973 : ℝ) / 1000 = (1973 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((1973 : ℝ) / 1000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1973 : ℝ) / 1000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b19730 (exp_pos ((973 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1973 : ℝ) / 1000), exp_pos (-((1973 : ℝ) / 1000))]

lemma cosh_b19820_ub : cosh ((991 : ℝ) / 500) ≤ (381358088 : ℝ) / 100000000 := by
  have exp_frac_b19820 : exp ((491 : ℝ) / 500) ≤ (266979101 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((491 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((491 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (266979101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((991 : ℝ) / 500) = exp 1 * exp ((491 : ℝ) / 500) := by
    rw [← exp_add, show (1 : ℝ) + (491 : ℝ) / 500 = (991 : ℝ) / 500 by norm_num]
  have hneg : exp (-((991 : ℝ) / 500)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((991 : ℝ) / 500) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b19820 (exp_pos ((491 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((991 : ℝ) / 500), exp_pos (-((991 : ℝ) / 500))]

lemma cosh_b19910_ub : cosh ((1991 : ℝ) / 1000) ≤ (384639513 : ℝ) / 100000000 := by
  have exp_frac_b19910 : exp ((991 : ℝ) / 1000) ≤ (269392801 : ℝ) / 100000000 := by
    have ht : ((991 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((991 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((991 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (269392801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1991 : ℝ) / 1000) = exp 1 * exp ((991 : ℝ) / 1000) := by
    rw [← exp_add, show (1 : ℝ) + (991 : ℝ) / 1000 = (1991 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((1991 : ℝ) / 1000)) ≤ (368 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1991 : ℝ) / 1000) ≤ -(1 : ℝ))).trans exp_neg_one_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_one_le exp_frac_b19910 (exp_pos ((991 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1991 : ℝ) / 1000), exp_pos (-((1991 : ℝ) / 1000))]

lemma cosh_b20000_ub : cosh ((2 : ℝ) / 1) ≤ (376300001 : ℝ) / 100000000 := by
  rw [show (2 : ℝ) / 1 = (2 : ℝ) by norm_num]
  exact (cosh_two_le).trans (by norm_num)

lemma cosh_b20095_ub : cosh ((4019 : ℝ) / 2000) ≤ (379827251 : ℝ) / 100000000 := by
  have exp_frac_b20095 : exp ((19 : ℝ) / 2000) ≤ (100954601 : ℝ) / 100000000 := by
    have ht : ((19 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((19 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((19 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100954601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4019 : ℝ) / 2000) = exp 2 * exp ((19 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (19 : ℝ) / 2000 = (4019 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4019 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4019 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b20095 (exp_pos ((19 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4019 : ℝ) / 2000), exp_pos (-((4019 : ℝ) / 2000))]

lemma cosh_b20185_ub : cosh ((4037 : ℝ) / 2000) ≤ (383199678 : ℝ) / 100000000 := by
  have exp_frac_b20185 : exp ((37 : ℝ) / 2000) ≤ (101867301 : ℝ) / 100000000 := by
    have ht : ((37 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((37 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((37 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101867301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4037 : ℝ) / 2000) = exp 2 * exp ((37 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (37 : ℝ) / 2000 = (4037 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4037 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4037 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b20185 (exp_pos ((37 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4037 : ℝ) / 2000), exp_pos (-((4037 : ℝ) / 2000))]

lemma cosh_b20275_ub : cosh ((811 : ℝ) / 400) ≤ (386602403 : ℝ) / 100000000 := by
  have exp_frac_b20275 : exp ((11 : ℝ) / 400) ≤ (102788201 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((11 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((11 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102788201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((811 : ℝ) / 400) = exp 2 * exp ((11 : ℝ) / 400) := by
    rw [← exp_add, show (2 : ℝ) + (11 : ℝ) / 400 = (811 : ℝ) / 400 by norm_num]
  have hneg : exp (-((811 : ℝ) / 400)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((811 : ℝ) / 400) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b20275 (exp_pos ((11 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((811 : ℝ) / 400), exp_pos (-((811 : ℝ) / 400))]

lemma cosh_b20365_ub : cosh ((4073 : ℝ) / 2000) ≤ (390036167 : ℝ) / 100000000 := by
  have exp_frac_b20365 : exp ((73 : ℝ) / 2000) ≤ (103717501 : ℝ) / 100000000 := by
    have ht : ((73 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((73 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((73 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103717501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4073 : ℝ) / 2000) = exp 2 * exp ((73 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (73 : ℝ) / 2000 = (4073 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4073 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4073 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b20365 (exp_pos ((73 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4073 : ℝ) / 2000), exp_pos (-((4073 : ℝ) / 2000))]

lemma cosh_b20455_ub : cosh ((4091 : ℝ) / 2000) ≤ (393500968 : ℝ) / 100000000 := by
  have exp_frac_b20455 : exp ((91 : ℝ) / 2000) ≤ (104655201 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104655201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4091 : ℝ) / 2000) = exp 2 * exp ((91 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (91 : ℝ) / 2000 = (4091 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4091 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4091 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b20455 (exp_pos ((91 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4091 : ℝ) / 2000), exp_pos (-((4091 : ℝ) / 2000))]

lemma cosh_b20550_ub : cosh ((411 : ℝ) / 200) ≤ (397191904 : ℝ) / 100000000 := by
  have exp_frac_b20550 : exp ((11 : ℝ) / 200) ≤ (105654101 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((11 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((11 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105654101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((411 : ℝ) / 200) = exp 2 * exp ((11 : ℝ) / 200) := by
    rw [← exp_add, show (2 : ℝ) + (11 : ℝ) / 200 = (411 : ℝ) / 200 by norm_num]
  have hneg : exp (-((411 : ℝ) / 200)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((411 : ℝ) / 200) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b20550 (exp_pos ((11 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((411 : ℝ) / 200), exp_pos (-((411 : ℝ) / 200))]

lemma cosh_b20640_ub : cosh ((258 : ℝ) / 125) ≤ (400721368 : ℝ) / 100000000 := by
  have exp_frac_b20640 : exp ((8 : ℝ) / 125) ≤ (106609301 : ℝ) / 100000000 := by
    have ht : ((8 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((8 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((8 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106609301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((258 : ℝ) / 125) = exp 2 * exp ((8 : ℝ) / 125) := by
    rw [← exp_add, show (2 : ℝ) + (8 : ℝ) / 125 = (258 : ℝ) / 125 by norm_num]
  have hneg : exp (-((258 : ℝ) / 125)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((258 : ℝ) / 125) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b20640 (exp_pos ((8 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((258 : ℝ) / 125), exp_pos (-((258 : ℝ) / 125))]

lemma cosh_b20730_ub : cosh ((2073 : ℝ) / 1000) ≤ (404282609 : ℝ) / 100000000 := by
  have exp_frac_b20730 : exp ((73 : ℝ) / 1000) ≤ (107573101 : ℝ) / 100000000 := by
    have ht : ((73 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((73 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((73 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107573101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2073 : ℝ) / 1000) = exp 2 * exp ((73 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (73 : ℝ) / 1000 = (2073 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2073 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2073 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b20730 (exp_pos ((73 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2073 : ℝ) / 1000), exp_pos (-((2073 : ℝ) / 1000))]

lemma cosh_b20820_ub : cosh ((1041 : ℝ) / 500) ≤ (407875996 : ℝ) / 100000000 := by
  have exp_frac_b20820 : exp ((41 : ℝ) / 500) ≤ (108545601 : ℝ) / 100000000 := by
    have ht : ((41 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((41 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((41 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108545601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1041 : ℝ) / 500) = exp 2 * exp ((41 : ℝ) / 500) := by
    rw [← exp_add, show (2 : ℝ) + (41 : ℝ) / 500 = (1041 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1041 : ℝ) / 500)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1041 : ℝ) / 500) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b20820 (exp_pos ((41 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1041 : ℝ) / 500), exp_pos (-((1041 : ℝ) / 500))]

lemma cosh_b20910_ub : cosh ((2091 : ℝ) / 1000) ≤ (411502269 : ℝ) / 100000000 := by
  have exp_frac_b20910 : exp ((91 : ℝ) / 1000) ≤ (109527001 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109527001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2091 : ℝ) / 1000) = exp 2 * exp ((91 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (91 : ℝ) / 1000 = (2091 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2091 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2091 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b20910 (exp_pos ((91 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2091 : ℝ) / 1000), exp_pos (-((2091 : ℝ) / 1000))]

lemma cosh_b21000_ub : cosh ((21 : ℝ) / 10) ≤ (415160689 : ℝ) / 100000000 := by
  have exp_frac_b21000 : exp ((1 : ℝ) / 10) ≤ (110517101 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((1 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110517101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((21 : ℝ) / 10) = exp 2 * exp ((1 : ℝ) / 10) := by
    rw [← exp_add, show (2 : ℝ) + (1 : ℝ) / 10 = (21 : ℝ) / 10 by norm_num]
  have hneg : exp (-((21 : ℝ) / 10)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((21 : ℝ) / 10) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b21000 (exp_pos ((1 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((21 : ℝ) / 10), exp_pos (-((21 : ℝ) / 10))]

lemma cosh_b21095_ub : cosh ((4219 : ℝ) / 2000) ≤ (419058914 : ℝ) / 100000000 := by
  have exp_frac_b21095 : exp ((219 : ℝ) / 2000) ≤ (111572101 : ℝ) / 100000000 := by
    have ht : ((219 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((219 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((219 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (111572101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4219 : ℝ) / 2000) = exp 2 * exp ((219 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (219 : ℝ) / 2000 = (4219 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4219 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4219 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b21095 (exp_pos ((219 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4219 : ℝ) / 2000), exp_pos (-((4219 : ℝ) / 2000))]

lemma cosh_b21185_ub : cosh ((4237 : ℝ) / 2000) ≤ (422785691 : ℝ) / 100000000 := by
  have exp_frac_b21185 : exp ((237 : ℝ) / 2000) ≤ (112580701 : ℝ) / 100000000 := by
    have ht : ((237 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((237 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((237 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (112580701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4237 : ℝ) / 2000) = exp 2 * exp ((237 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (237 : ℝ) / 2000 = (4237 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4237 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4237 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b21185 (exp_pos ((237 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4237 : ℝ) / 2000), exp_pos (-((4237 : ℝ) / 2000))]

lemma cosh_b21275_ub : cosh ((851 : ℝ) / 400) ≤ (426546462 : ℝ) / 100000000 := by
  have exp_frac_b21275 : exp ((51 : ℝ) / 400) ≤ (113598501 : ℝ) / 100000000 := by
    have ht : ((51 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((51 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((51 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (113598501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((851 : ℝ) / 400) = exp 2 * exp ((51 : ℝ) / 400) := by
    rw [← exp_add, show (2 : ℝ) + (51 : ℝ) / 400 = (851 : ℝ) / 400 by norm_num]
  have hneg : exp (-((851 : ℝ) / 400)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((851 : ℝ) / 400) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b21275 (exp_pos ((51 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((851 : ℝ) / 400), exp_pos (-((851 : ℝ) / 400))]

lemma cosh_b21365_ub : cosh ((4273 : ℝ) / 2000) ≤ (430341227 : ℝ) / 100000000 := by
  have exp_frac_b21365 : exp ((273 : ℝ) / 2000) ≤ (114625501 : ℝ) / 100000000 := by
    have ht : ((273 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((273 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((273 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (114625501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4273 : ℝ) / 2000) = exp 2 * exp ((273 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (273 : ℝ) / 2000 = (4273 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4273 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4273 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b21365 (exp_pos ((273 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4273 : ℝ) / 2000), exp_pos (-((4273 : ℝ) / 2000))]

lemma cosh_b21455_ub : cosh ((4291 : ℝ) / 2000) ≤ (434170355 : ℝ) / 100000000 := by
  have exp_frac_b21455 : exp ((291 : ℝ) / 2000) ≤ (115661801 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (115661801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4291 : ℝ) / 2000) = exp 2 * exp ((291 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (291 : ℝ) / 2000 = (4291 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4291 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4291 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b21455 (exp_pos ((291 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4291 : ℝ) / 2000), exp_pos (-((4291 : ℝ) / 2000))]

lemma cosh_b21550_ub : cosh ((431 : ℝ) / 200) ≤ (438249635 : ℝ) / 100000000 := by
  have exp_frac_b21550 : exp ((31 : ℝ) / 200) ≤ (116765801 : ℝ) / 100000000 := by
    have ht : ((31 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((31 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((31 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (116765801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((431 : ℝ) / 200) = exp 2 * exp ((31 : ℝ) / 200) := by
    rw [← exp_add, show (2 : ℝ) + (31 : ℝ) / 200 = (431 : ℝ) / 200 by norm_num]
  have hneg : exp (-((431 : ℝ) / 200)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((431 : ℝ) / 200) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b21550 (exp_pos ((31 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((431 : ℝ) / 200), exp_pos (-((431 : ℝ) / 200))]

lemma cosh_b21640_ub : cosh ((541 : ℝ) / 250) ≤ (442150447 : ℝ) / 100000000 := by
  have exp_frac_b21640 : exp ((41 : ℝ) / 250) ≤ (117821501 : ℝ) / 100000000 := by
    have ht : ((41 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((41 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((41 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (117821501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((541 : ℝ) / 250) = exp 2 * exp ((41 : ℝ) / 250) := by
    rw [← exp_add, show (2 : ℝ) + (41 : ℝ) / 250 = (541 : ℝ) / 250 by norm_num]
  have hneg : exp (-((541 : ℝ) / 250)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((541 : ℝ) / 250) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b21640 (exp_pos ((41 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((541 : ℝ) / 250), exp_pos (-((541 : ℝ) / 250))]

lemma cosh_b21730_ub : cosh ((2173 : ℝ) / 1000) ≤ (446086361 : ℝ) / 100000000 := by
  have exp_frac_b21730 : exp ((173 : ℝ) / 1000) ≤ (118886701 : ℝ) / 100000000 := by
    have ht : ((173 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((173 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((173 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (118886701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2173 : ℝ) / 1000) = exp 2 * exp ((173 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (173 : ℝ) / 1000 = (2173 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2173 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2173 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b21730 (exp_pos ((173 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2173 : ℝ) / 1000), exp_pos (-((2173 : ℝ) / 1000))]

lemma cosh_b21820_ub : cosh ((1091 : ℝ) / 500) ≤ (450057747 : ℝ) / 100000000 := by
  have exp_frac_b21820 : exp ((91 : ℝ) / 500) ≤ (119961501 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (119961501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1091 : ℝ) / 500) = exp 2 * exp ((91 : ℝ) / 500) := by
    rw [← exp_add, show (2 : ℝ) + (91 : ℝ) / 500 = (1091 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1091 : ℝ) / 500)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1091 : ℝ) / 500) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b21820 (exp_pos ((91 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1091 : ℝ) / 500), exp_pos (-((1091 : ℝ) / 500))]

lemma cosh_b21910_ub : cosh ((2191 : ℝ) / 1000) ≤ (454064974 : ℝ) / 100000000 := by
  have exp_frac_b21910 : exp ((191 : ℝ) / 1000) ≤ (121046001 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (121046001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2191 : ℝ) / 1000) = exp 2 * exp ((191 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (191 : ℝ) / 1000 = (2191 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2191 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2191 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b21910 (exp_pos ((191 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2191 : ℝ) / 1000), exp_pos (-((2191 : ℝ) / 1000))]

lemma cosh_b22000_ub : cosh ((11 : ℝ) / 5) ≤ (458108413 : ℝ) / 100000000 := by
  have exp_frac_b22000 : exp ((1 : ℝ) / 5) ≤ (122140301 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((1 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (122140301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((11 : ℝ) / 5) = exp 2 * exp ((1 : ℝ) / 5) := by
    rw [← exp_add, show (2 : ℝ) + (1 : ℝ) / 5 = (11 : ℝ) / 5 by norm_num]
  have hneg : exp (-((11 : ℝ) / 5)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((11 : ℝ) / 5) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b22000 (exp_pos ((1 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((11 : ℝ) / 5), exp_pos (-((11 : ℝ) / 5))]

lemma cosh_b22095_ub : cosh ((4419 : ℝ) / 2000) ≤ (462416413 : ℝ) / 100000000 := by
  have exp_frac_b22095 : exp ((419 : ℝ) / 2000) ≤ (123306201 : ℝ) / 100000000 := by
    have ht : ((419 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((419 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((419 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (123306201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4419 : ℝ) / 2000) = exp 2 * exp ((419 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (419 : ℝ) / 2000 = (4419 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4419 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4419 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b22095 (exp_pos ((419 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4419 : ℝ) / 2000), exp_pos (-((4419 : ℝ) / 2000))]

lemma cosh_b22185_ub : cosh ((4437 : ℝ) / 2000) ≤ (466535599 : ℝ) / 100000000 := by
  have exp_frac_b22185 : exp ((437 : ℝ) / 2000) ≤ (124421001 : ℝ) / 100000000 := by
    have ht : ((437 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((437 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((437 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (124421001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4437 : ℝ) / 2000) = exp 2 * exp ((437 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (437 : ℝ) / 2000 = (4437 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4437 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4437 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b22185 (exp_pos ((437 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4437 : ℝ) / 2000), exp_pos (-((4437 : ℝ) / 2000))]

lemma cosh_b22275_ub : cosh ((891 : ℝ) / 400) ≤ (470691735 : ℝ) / 100000000 := by
  have exp_frac_b22275 : exp ((91 : ℝ) / 400) ≤ (125545801 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (125545801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((891 : ℝ) / 400) = exp 2 * exp ((91 : ℝ) / 400) := by
    rw [← exp_add, show (2 : ℝ) + (91 : ℝ) / 400 = (891 : ℝ) / 400 by norm_num]
  have hneg : exp (-((891 : ℝ) / 400)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((891 : ℝ) / 400) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b22275 (exp_pos ((91 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((891 : ℝ) / 400), exp_pos (-((891 : ℝ) / 400))]

lemma cosh_b22365_ub : cosh ((4473 : ℝ) / 2000) ≤ (474885560 : ℝ) / 100000000 := by
  have exp_frac_b22365 : exp ((473 : ℝ) / 2000) ≤ (126680801 : ℝ) / 100000000 := by
    have ht : ((473 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((473 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((473 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (126680801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4473 : ℝ) / 2000) = exp 2 * exp ((473 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (473 : ℝ) / 2000 = (4473 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4473 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4473 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b22365 (exp_pos ((473 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4473 : ℝ) / 2000), exp_pos (-((4473 : ℝ) / 2000))]

lemma cosh_b22455_ub : cosh ((4491 : ℝ) / 2000) ≤ (479117444 : ℝ) / 100000000 := by
  have exp_frac_b22455 : exp ((491 : ℝ) / 2000) ≤ (127826101 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((491 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((491 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (127826101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4491 : ℝ) / 2000) = exp 2 * exp ((491 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (491 : ℝ) / 2000 = (4491 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4491 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4491 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b22455 (exp_pos ((491 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4491 : ℝ) / 2000), exp_pos (-((4491 : ℝ) / 2000))]

lemma cosh_b22550_ub : cosh ((451 : ℝ) / 200) ≤ (483625713 : ℝ) / 100000000 := by
  have exp_frac_b22550 : exp ((51 : ℝ) / 200) ≤ (129046201 : ℝ) / 100000000 := by
    have ht : ((51 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((51 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((51 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (129046201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((451 : ℝ) / 200) = exp 2 * exp ((51 : ℝ) / 200) := by
    rw [← exp_add, show (2 : ℝ) + (51 : ℝ) / 200 = (451 : ℝ) / 200 by norm_num]
  have hneg : exp (-((451 : ℝ) / 200)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((451 : ℝ) / 200) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b22550 (exp_pos ((51 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((451 : ℝ) / 200), exp_pos (-((451 : ℝ) / 200))]

lemma cosh_b22640_ub : cosh ((283 : ℝ) / 125) ≤ (487936670 : ℝ) / 100000000 := by
  have exp_frac_b22640 : exp ((33 : ℝ) / 125) ≤ (130212901 : ℝ) / 100000000 := by
    have ht : ((33 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((33 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((33 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (130212901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((283 : ℝ) / 125) = exp 2 * exp ((33 : ℝ) / 125) := by
    rw [← exp_add, show (2 : ℝ) + (33 : ℝ) / 125 = (283 : ℝ) / 125 by norm_num]
  have hneg : exp (-((283 : ℝ) / 125)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((283 : ℝ) / 125) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b22640 (exp_pos ((33 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((283 : ℝ) / 125), exp_pos (-((283 : ℝ) / 125))]

lemma cosh_b22730_ub : cosh ((2273 : ℝ) / 1000) ≤ (492286424 : ℝ) / 100000000 := by
  have exp_frac_b22730 : exp ((273 : ℝ) / 1000) ≤ (131390101 : ℝ) / 100000000 := by
    have ht : ((273 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((273 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((273 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (131390101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2273 : ℝ) / 1000) = exp 2 * exp ((273 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (273 : ℝ) / 1000 = (2273 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2273 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2273 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b22730 (exp_pos ((273 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2273 : ℝ) / 1000), exp_pos (-((2273 : ℝ) / 1000))]

lemma cosh_b22820_ub : cosh ((1141 : ℝ) / 500) ≤ (496675345 : ℝ) / 100000000 := by
  have exp_frac_b22820 : exp ((141 : ℝ) / 500) ≤ (132577901 : ℝ) / 100000000 := by
    have ht : ((141 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((141 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((141 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (132577901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1141 : ℝ) / 500) = exp 2 * exp ((141 : ℝ) / 500) := by
    rw [← exp_add, show (2 : ℝ) + (141 : ℝ) / 500 = (1141 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1141 : ℝ) / 500)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1141 : ℝ) / 500) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b22820 (exp_pos ((141 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1141 : ℝ) / 500), exp_pos (-((1141 : ℝ) / 500))]

lemma cosh_b22910_ub : cosh ((2291 : ℝ) / 1000) ≤ (501104172 : ℝ) / 100000000 := by
  have exp_frac_b22910 : exp ((291 : ℝ) / 1000) ≤ (133776501 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (133776501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2291 : ℝ) / 1000) = exp 2 * exp ((291 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (291 : ℝ) / 1000 = (2291 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2291 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2291 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b22910 (exp_pos ((291 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2291 : ℝ) / 1000), exp_pos (-((2291 : ℝ) / 1000))]

lemma cosh_b23000_ub : cosh ((23 : ℝ) / 10) ≤ (505572905 : ℝ) / 100000000 := by
  have exp_frac_b23000 : exp ((3 : ℝ) / 10) ≤ (134985901 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((3 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((3 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (134985901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((23 : ℝ) / 10) = exp 2 * exp ((3 : ℝ) / 10) := by
    rw [← exp_add, show (2 : ℝ) + (3 : ℝ) / 10 = (23 : ℝ) / 10 by norm_num]
  have hneg : exp (-((23 : ℝ) / 10)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((23 : ℝ) / 10) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b23000 (exp_pos ((3 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((23 : ℝ) / 10), exp_pos (-((23 : ℝ) / 10))]

lemma cosh_b23095_ub : cosh ((4619 : ℝ) / 2000) ≤ (510333912 : ℝ) / 100000000 := by
  have exp_frac_b23095 : exp ((619 : ℝ) / 2000) ≤ (136274401 : ℝ) / 100000000 := by
    have ht : ((619 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((619 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((619 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (136274401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4619 : ℝ) / 2000) = exp 2 * exp ((619 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (619 : ℝ) / 2000 = (4619 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4619 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4619 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b23095 (exp_pos ((619 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4619 : ℝ) / 2000), exp_pos (-((4619 : ℝ) / 2000))]

lemma cosh_b23185_ub : cosh ((4637 : ℝ) / 2000) ≤ (514886152 : ℝ) / 100000000 := by
  have exp_frac_b23185 : exp ((637 : ℝ) / 2000) ≤ (137506401 : ℝ) / 100000000 := by
    have ht : ((637 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((637 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((637 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (137506401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4637 : ℝ) / 2000) = exp 2 * exp ((637 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (637 : ℝ) / 2000 = (4637 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4637 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4637 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b23185 (exp_pos ((637 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4637 : ℝ) / 2000), exp_pos (-((4637 : ℝ) / 2000))]

lemma cosh_b23275_ub : cosh ((931 : ℝ) / 400) ≤ (519479776 : ℝ) / 100000000 := by
  have exp_frac_b23275 : exp ((131 : ℝ) / 400) ≤ (138749601 : ℝ) / 100000000 := by
    have ht : ((131 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((131 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((131 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (138749601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((931 : ℝ) / 400) = exp 2 * exp ((131 : ℝ) / 400) := by
    rw [← exp_add, show (2 : ℝ) + (131 : ℝ) / 400 = (931 : ℝ) / 400 by norm_num]
  have hneg : exp (-((931 : ℝ) / 400)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((931 : ℝ) / 400) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b23275 (exp_pos ((131 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((931 : ℝ) / 400), exp_pos (-((931 : ℝ) / 400))]

lemma cosh_b23365_ub : cosh ((4673 : ℝ) / 2000) ≤ (524114415 : ℝ) / 100000000 := by
  have exp_frac_b23365 : exp ((673 : ℝ) / 2000) ≤ (140003901 : ℝ) / 100000000 := by
    have ht : ((673 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((673 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((673 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (140003901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4673 : ℝ) / 2000) = exp 2 * exp ((673 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (673 : ℝ) / 2000 = (4673 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4673 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4673 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b23365 (exp_pos ((673 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4673 : ℝ) / 2000), exp_pos (-((4673 : ℝ) / 2000))]

lemma cosh_b23455_ub : cosh ((4691 : ℝ) / 2000) ≤ (528791546 : ℝ) / 100000000 := by
  have exp_frac_b23455 : exp ((691 : ℝ) / 2000) ≤ (141269701 : ℝ) / 100000000 := by
    have ht : ((691 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((691 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((691 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (141269701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4691 : ℝ) / 2000) = exp 2 * exp ((691 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (691 : ℝ) / 2000 = (4691 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4691 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4691 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b23455 (exp_pos ((691 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4691 : ℝ) / 2000), exp_pos (-((4691 : ℝ) / 2000))]

lemma cosh_b23550_ub : cosh ((471 : ℝ) / 200) ≤ (533773884 : ℝ) / 100000000 := by
  have exp_frac_b23550 : exp ((71 : ℝ) / 200) ≤ (142618101 : ℝ) / 100000000 := by
    have ht : ((71 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((71 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((71 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (142618101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((471 : ℝ) / 200) = exp 2 * exp ((71 : ℝ) / 200) := by
    rw [← exp_add, show (2 : ℝ) + (71 : ℝ) / 200 = (471 : ℝ) / 200 by norm_num]
  have hneg : exp (-((471 : ℝ) / 200)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((471 : ℝ) / 200) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b23550 (exp_pos ((71 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((471 : ℝ) / 200), exp_pos (-((471 : ℝ) / 200))]

lemma cosh_b23640_ub : cosh ((591 : ℝ) / 250) ≤ (538538217 : ℝ) / 100000000 := by
  have exp_frac_b23640 : exp ((91 : ℝ) / 250) ≤ (143907501 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (143907501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((591 : ℝ) / 250) = exp 2 * exp ((91 : ℝ) / 250) := by
    rw [← exp_add, show (2 : ℝ) + (91 : ℝ) / 250 = (591 : ℝ) / 250 by norm_num]
  have hneg : exp (-((591 : ℝ) / 250)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((591 : ℝ) / 250) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b23640 (exp_pos ((91 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((591 : ℝ) / 250), exp_pos (-((591 : ℝ) / 250))]

lemma cosh_b23730_ub : cosh ((2373 : ℝ) / 1000) ≤ (543345412 : ℝ) / 100000000 := by
  have exp_frac_b23730 : exp ((373 : ℝ) / 1000) ≤ (145208501 : ℝ) / 100000000 := by
    have ht : ((373 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((373 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((373 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (145208501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2373 : ℝ) / 1000) = exp 2 * exp ((373 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (373 : ℝ) / 1000 = (2373 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2373 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2373 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b23730 (exp_pos ((373 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2373 : ℝ) / 1000), exp_pos (-((2373 : ℝ) / 1000))]

lemma cosh_b23820_ub : cosh ((1191 : ℝ) / 500) ≤ (548196208 : ℝ) / 100000000 := by
  have exp_frac_b23820 : exp ((191 : ℝ) / 500) ≤ (146521301 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (146521301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1191 : ℝ) / 500) = exp 2 * exp ((191 : ℝ) / 500) := by
    rw [← exp_add, show (2 : ℝ) + (191 : ℝ) / 500 = (1191 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1191 : ℝ) / 500)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1191 : ℝ) / 500) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b23820 (exp_pos ((191 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1191 : ℝ) / 500), exp_pos (-((1191 : ℝ) / 500))]

lemma cosh_b23910_ub : cosh ((2391 : ℝ) / 1000) ≤ (553090605 : ℝ) / 100000000 := by
  have exp_frac_b23910 : exp ((391 : ℝ) / 1000) ≤ (147845901 : ℝ) / 100000000 := by
    have ht : ((391 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((391 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((391 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (147845901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2391 : ℝ) / 1000) = exp 2 * exp ((391 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (391 : ℝ) / 1000 = (2391 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2391 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2391 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b23910 (exp_pos ((391 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2391 : ℝ) / 1000), exp_pos (-((2391 : ℝ) / 1000))]

lemma cosh_b24000_ub : cosh ((12 : ℝ) / 5) ≤ (558029342 : ℝ) / 100000000 := by
  have exp_frac_b24000 : exp ((2 : ℝ) / 5) ≤ (149182501 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((2 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((2 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (149182501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((12 : ℝ) / 5) = exp 2 * exp ((2 : ℝ) / 5) := by
    rw [← exp_add, show (2 : ℝ) + (2 : ℝ) / 5 = (12 : ℝ) / 5 by norm_num]
  have hneg : exp (-((12 : ℝ) / 5)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((12 : ℝ) / 5) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b24000 (exp_pos ((2 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((12 : ℝ) / 5), exp_pos (-((12 : ℝ) / 5))]

lemma cosh_b24095_ub : cosh ((4819 : ℝ) / 2000) ≤ (563291022 : ℝ) / 100000000 := by
  have exp_frac_b24095 : exp ((819 : ℝ) / 2000) ≤ (150606501 : ℝ) / 100000000 := by
    have ht : ((819 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((819 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((819 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (150606501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4819 : ℝ) / 2000) = exp 2 * exp ((819 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (819 : ℝ) / 2000 = (4819 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4819 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4819 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b24095 (exp_pos ((819 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4819 : ℝ) / 2000), exp_pos (-((4819 : ℝ) / 2000))]

lemma cosh_b24185_ub : cosh ((4837 : ℝ) / 2000) ≤ (568322134 : ℝ) / 100000000 := by
  have exp_frac_b24185 : exp ((837 : ℝ) / 2000) ≤ (151968101 : ℝ) / 100000000 := by
    have ht : ((837 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((837 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((837 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (151968101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4837 : ℝ) / 2000) = exp 2 * exp ((837 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (837 : ℝ) / 2000 = (4837 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4837 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4837 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b24185 (exp_pos ((837 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4837 : ℝ) / 2000), exp_pos (-((4837 : ℝ) / 2000))]

lemma cosh_b24275_ub : cosh ((971 : ℝ) / 400) ≤ (573398694 : ℝ) / 100000000 := by
  have exp_frac_b24275 : exp ((171 : ℝ) / 400) ≤ (153342001 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((171 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((171 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (153342001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((971 : ℝ) / 400) = exp 2 * exp ((171 : ℝ) / 400) := by
    rw [← exp_add, show (2 : ℝ) + (171 : ℝ) / 400 = (971 : ℝ) / 400 by norm_num]
  have hneg : exp (-((971 : ℝ) / 400)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((971 : ℝ) / 400) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b24275 (exp_pos ((171 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((971 : ℝ) / 400), exp_pos (-((971 : ℝ) / 400))]

lemma cosh_b24365_ub : cosh ((4873 : ℝ) / 2000) ≤ (578521073 : ℝ) / 100000000 := by
  have exp_frac_b24365 : exp ((873 : ℝ) / 2000) ≤ (154728301 : ℝ) / 100000000 := by
    have ht : ((873 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((873 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((873 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (154728301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4873 : ℝ) / 2000) = exp 2 * exp ((873 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (873 : ℝ) / 2000 = (4873 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4873 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4873 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b24365 (exp_pos ((873 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4873 : ℝ) / 2000), exp_pos (-((4873 : ℝ) / 2000))]

lemma cosh_b24455_ub : cosh ((4891 : ℝ) / 2000) ≤ (583689639 : ℝ) / 100000000 := by
  have exp_frac_b24455 : exp ((891 : ℝ) / 2000) ≤ (156127101 : ℝ) / 100000000 := by
    have ht : ((891 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((891 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((891 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (156127101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4891 : ℝ) / 2000) = exp 2 * exp ((891 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (891 : ℝ) / 2000 = (4891 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((4891 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4891 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b24455 (exp_pos ((891 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4891 : ℝ) / 2000), exp_pos (-((4891 : ℝ) / 2000))]

lemma cosh_b24550_ub : cosh ((491 : ℝ) / 200) ≤ (589196297 : ℝ) / 100000000 := by
  have exp_frac_b24550 : exp ((91 : ℝ) / 200) ≤ (157617401 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (157617401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((491 : ℝ) / 200) = exp 2 * exp ((91 : ℝ) / 200) := by
    rw [← exp_add, show (2 : ℝ) + (91 : ℝ) / 200 = (491 : ℝ) / 200 by norm_num]
  have hneg : exp (-((491 : ℝ) / 200)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((491 : ℝ) / 200) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b24550 (exp_pos ((91 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((491 : ℝ) / 200), exp_pos (-((491 : ℝ) / 200))]

lemma cosh_b24640_ub : cosh ((308 : ℝ) / 125) ≤ (594461303 : ℝ) / 100000000 := by
  have exp_frac_b24640 : exp ((58 : ℝ) / 125) ≤ (159042301 : ℝ) / 100000000 := by
    have ht : ((58 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((58 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((58 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (159042301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((308 : ℝ) / 125) = exp 2 * exp ((58 : ℝ) / 125) := by
    rw [← exp_add, show (2 : ℝ) + (58 : ℝ) / 125 = (308 : ℝ) / 125 by norm_num]
  have hneg : exp (-((308 : ℝ) / 125)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((308 : ℝ) / 125) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b24640 (exp_pos ((58 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((308 : ℝ) / 125), exp_pos (-((308 : ℝ) / 125))]

lemma cosh_b24730_ub : cosh ((2473 : ℝ) / 1000) ≤ (599774343 : ℝ) / 100000000 := by
  have exp_frac_b24730 : exp ((473 : ℝ) / 1000) ≤ (160480201 : ℝ) / 100000000 := by
    have ht : ((473 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((473 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((473 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (160480201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2473 : ℝ) / 1000) = exp 2 * exp ((473 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (473 : ℝ) / 1000 = (2473 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2473 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2473 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b24730 (exp_pos ((473 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2473 : ℝ) / 1000), exp_pos (-((2473 : ℝ) / 1000))]

lemma cosh_b24820_ub : cosh ((1241 : ℝ) / 500) ≤ (605135049 : ℝ) / 100000000 := by
  have exp_frac_b24820 : exp ((241 : ℝ) / 500) ≤ (161931001 : ℝ) / 100000000 := by
    have ht : ((241 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((241 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((241 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (161931001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1241 : ℝ) / 500) = exp 2 * exp ((241 : ℝ) / 500) := by
    rw [← exp_add, show (2 : ℝ) + (241 : ℝ) / 500 = (1241 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1241 : ℝ) / 500)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1241 : ℝ) / 500) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b24820 (exp_pos ((241 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1241 : ℝ) / 500), exp_pos (-((1241 : ℝ) / 500))]

lemma cosh_b24910_ub : cosh ((2491 : ℝ) / 1000) ≤ (610544529 : ℝ) / 100000000 := by
  have exp_frac_b24910 : exp ((491 : ℝ) / 1000) ≤ (163395001 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((491 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((491 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (163395001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2491 : ℝ) / 1000) = exp 2 * exp ((491 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (491 : ℝ) / 1000 = (2491 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2491 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2491 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b24910 (exp_pos ((491 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2491 : ℝ) / 1000), exp_pos (-((2491 : ℝ) / 1000))]

lemma cosh_b25000_ub : cosh ((5 : ℝ) / 2) ≤ (616002783 : ℝ) / 100000000 := by
  have exp_frac_b25000 : exp ((1 : ℝ) / 2) ≤ (164872201 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 2) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1 : ℝ) / 2) ^ m / (Nat.factorial m)) +
          ((1 : ℝ) / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (164872201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5 : ℝ) / 2) = exp 2 * exp ((1 : ℝ) / 2) := by
    rw [← exp_add, show (2 : ℝ) + (1 : ℝ) / 2 = (5 : ℝ) / 2 by norm_num]
  have hneg : exp (-((5 : ℝ) / 2)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5 : ℝ) / 2) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b25000 (exp_pos ((1 : ℝ) / 2)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5 : ℝ) / 2), exp_pos (-((5 : ℝ) / 2))]

lemma cosh_b25095_ub : cosh ((5019 : ℝ) / 2000) ≤ (621817605 : ℝ) / 100000000 := by
  have exp_frac_b25095 : exp ((1019 : ℝ) / 2000) ≤ (166445901 : ℝ) / 100000000 := by
    have ht : ((1019 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1019 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1019 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (166445901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5019 : ℝ) / 2000) = exp 2 * exp ((1019 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1019 : ℝ) / 2000 = (5019 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5019 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5019 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b25095 (exp_pos ((1019 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5019 : ℝ) / 2000), exp_pos (-((5019 : ℝ) / 2000))]

lemma cosh_b25185_ub : cosh ((5037 : ℝ) / 2000) ≤ (627377841 : ℝ) / 100000000 := by
  have exp_frac_b25185 : exp ((1037 : ℝ) / 2000) ≤ (167950701 : ℝ) / 100000000 := by
    have ht : ((1037 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1037 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1037 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (167950701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5037 : ℝ) / 2000) = exp 2 * exp ((1037 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1037 : ℝ) / 2000 = (5037 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5037 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5037 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b25185 (exp_pos ((1037 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5037 : ℝ) / 2000), exp_pos (-((5037 : ℝ) / 2000))]

lemma cosh_b25275_ub : cosh ((1011 : ℝ) / 400) ≤ (632988329 : ℝ) / 100000000 := by
  have exp_frac_b25275 : exp ((211 : ℝ) / 400) ≤ (169469101 : ℝ) / 100000000 := by
    have ht : ((211 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((211 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((211 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (169469101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1011 : ℝ) / 400) = exp 2 * exp ((211 : ℝ) / 400) := by
    rw [← exp_add, show (2 : ℝ) + (211 : ℝ) / 400 = (1011 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1011 : ℝ) / 400)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1011 : ℝ) / 400) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b25275 (exp_pos ((211 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1011 : ℝ) / 400), exp_pos (-((1011 : ℝ) / 400))]

lemma cosh_b25365_ub : cosh ((5073 : ℝ) / 2000) ≤ (638649438 : ℝ) / 100000000 := by
  have exp_frac_b25365 : exp ((1073 : ℝ) / 2000) ≤ (171001201 : ℝ) / 100000000 := by
    have ht : ((1073 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1073 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1073 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (171001201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5073 : ℝ) / 2000) = exp 2 * exp ((1073 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1073 : ℝ) / 2000 = (5073 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5073 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5073 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b25365 (exp_pos ((1073 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5073 : ℝ) / 2000), exp_pos (-((5073 : ℝ) / 2000))]

lemma cosh_b25455_ub : cosh ((5091 : ℝ) / 2000) ≤ (644361539 : ℝ) / 100000000 := by
  have exp_frac_b25455 : exp ((1091 : ℝ) / 2000) ≤ (172547101 : ℝ) / 100000000 := by
    have ht : ((1091 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1091 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1091 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (172547101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5091 : ℝ) / 2000) = exp 2 * exp ((1091 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1091 : ℝ) / 2000 = (5091 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5091 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5091 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b25455 (exp_pos ((1091 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5091 : ℝ) / 2000), exp_pos (-((5091 : ℝ) / 2000))]

lemma cosh_b25550_ub : cosh ((511 : ℝ) / 200) ≤ (650447204 : ℝ) / 100000000 := by
  have exp_frac_b25550 : exp ((111 : ℝ) / 200) ≤ (174194101 : ℝ) / 100000000 := by
    have ht : ((111 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((111 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((111 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (174194101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((511 : ℝ) / 200) = exp 2 * exp ((111 : ℝ) / 200) := by
    rw [← exp_add, show (2 : ℝ) + (111 : ℝ) / 200 = (511 : ℝ) / 200 by norm_num]
  have hneg : exp (-((511 : ℝ) / 200)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((511 : ℝ) / 200) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b25550 (exp_pos ((111 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((511 : ℝ) / 200), exp_pos (-((511 : ℝ) / 200))]

lemma cosh_b25640_ub : cosh ((641 : ℝ) / 250) ≤ (656266459 : ℝ) / 100000000 := by
  have exp_frac_b25640 : exp ((141 : ℝ) / 250) ≤ (175769001 : ℝ) / 100000000 := by
    have ht : ((141 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((141 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((141 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (175769001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((641 : ℝ) / 250) = exp 2 * exp ((141 : ℝ) / 250) := by
    rw [← exp_add, show (2 : ℝ) + (141 : ℝ) / 250 = (641 : ℝ) / 250 by norm_num]
  have hneg : exp (-((641 : ℝ) / 250)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((641 : ℝ) / 250) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b25640 (exp_pos ((141 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((641 : ℝ) / 250), exp_pos (-((641 : ℝ) / 250))]

lemma cosh_b25730_ub : cosh ((2573 : ℝ) / 1000) ≤ (662137814 : ℝ) / 100000000 := by
  have exp_frac_b25730 : exp ((573 : ℝ) / 1000) ≤ (177358001 : ℝ) / 100000000 := by
    have ht : ((573 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((573 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((573 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (177358001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2573 : ℝ) / 1000) = exp 2 * exp ((573 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (573 : ℝ) / 1000 = (2573 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2573 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2573 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b25730 (exp_pos ((573 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2573 : ℝ) / 1000), exp_pos (-((2573 : ℝ) / 1000))]

lemma cosh_b25820_ub : cosh ((1291 : ℝ) / 500) ≤ (668062747 : ℝ) / 100000000 := by
  have exp_frac_b25820 : exp ((291 : ℝ) / 500) ≤ (178961501 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (178961501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1291 : ℝ) / 500) = exp 2 * exp ((291 : ℝ) / 500) := by
    rw [← exp_add, show (2 : ℝ) + (291 : ℝ) / 500 = (1291 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1291 : ℝ) / 500)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1291 : ℝ) / 500) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b25820 (exp_pos ((291 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1291 : ℝ) / 500), exp_pos (-((1291 : ℝ) / 500))]

lemma cosh_b25910_ub : cosh ((2591 : ℝ) / 1000) ≤ (674040887 : ℝ) / 100000000 := by
  have exp_frac_b25910 : exp ((591 : ℝ) / 1000) ≤ (180579401 : ℝ) / 100000000 := by
    have ht : ((591 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((591 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((591 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (180579401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2591 : ℝ) / 1000) = exp 2 * exp ((591 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (591 : ℝ) / 1000 = (2591 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2591 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2591 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b25910 (exp_pos ((591 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2591 : ℝ) / 1000), exp_pos (-((2591 : ℝ) / 1000))]

lemma cosh_b26000_ub : cosh ((13 : ℝ) / 5) ≤ (680072975 : ℝ) / 100000000 := by
  have exp_frac_b26000 : exp ((3 : ℝ) / 5) ≤ (182211901 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((3 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((3 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (182211901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((13 : ℝ) / 5) = exp 2 * exp ((3 : ℝ) / 5) := by
    rw [← exp_add, show (2 : ℝ) + (3 : ℝ) / 5 = (13 : ℝ) / 5 by norm_num]
  have hneg : exp (-((13 : ℝ) / 5)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((13 : ℝ) / 5) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b26000 (exp_pos ((3 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((13 : ℝ) / 5), exp_pos (-((13 : ℝ) / 5))]

lemma cosh_b26095_ub : cosh ((5219 : ℝ) / 2000) ≤ (686499688 : ℝ) / 100000000 := by
  have exp_frac_b26095 : exp ((1219 : ℝ) / 2000) ≤ (183951201 : ℝ) / 100000000 := by
    have ht : ((1219 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1219 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1219 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (183951201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5219 : ℝ) / 2000) = exp 2 * exp ((1219 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1219 : ℝ) / 2000 = (5219 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5219 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5219 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b26095 (exp_pos ((1219 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5219 : ℝ) / 2000), exp_pos (-((5219 : ℝ) / 2000))]

lemma cosh_b26185_ub : cosh ((5237 : ℝ) / 2000) ≤ (692644473 : ℝ) / 100000000 := by
  have exp_frac_b26185 : exp ((1237 : ℝ) / 2000) ≤ (185614201 : ℝ) / 100000000 := by
    have ht : ((1237 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1237 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1237 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (185614201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5237 : ℝ) / 2000) = exp 2 * exp ((1237 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1237 : ℝ) / 2000 = (5237 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5237 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5237 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b26185 (exp_pos ((1237 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5237 : ℝ) / 2000), exp_pos (-((5237 : ℝ) / 2000))]

lemma cosh_b26275_ub : cosh ((1051 : ℝ) / 400) ≤ (698845053 : ℝ) / 100000000 := by
  have exp_frac_b26275 : exp ((251 : ℝ) / 400) ≤ (187292301 : ℝ) / 100000000 := by
    have ht : ((251 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((251 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((251 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (187292301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1051 : ℝ) / 400) = exp 2 * exp ((251 : ℝ) / 400) := by
    rw [← exp_add, show (2 : ℝ) + (251 : ℝ) / 400 = (1051 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1051 : ℝ) / 400)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1051 : ℝ) / 400) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b26275 (exp_pos ((251 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1051 : ℝ) / 400), exp_pos (-((1051 : ℝ) / 400))]

lemma cosh_b26365_ub : cosh ((5273 : ℝ) / 2000) ≤ (705101427 : ℝ) / 100000000 := by
  have exp_frac_b26365 : exp ((1273 : ℝ) / 2000) ≤ (188985501 : ℝ) / 100000000 := by
    have ht : ((1273 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1273 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1273 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (188985501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5273 : ℝ) / 2000) = exp 2 * exp ((1273 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1273 : ℝ) / 2000 = (5273 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5273 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5273 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b26365 (exp_pos ((1273 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5273 : ℝ) / 2000), exp_pos (-((5273 : ℝ) / 2000))]

lemma cosh_b26455_ub : cosh ((5291 : ℝ) / 2000) ≤ (711414704 : ℝ) / 100000000 := by
  have exp_frac_b26455 : exp ((1291 : ℝ) / 2000) ≤ (190694101 : ℝ) / 100000000 := by
    have ht : ((1291 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1291 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1291 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (190694101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5291 : ℝ) / 2000) = exp 2 * exp ((1291 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1291 : ℝ) / 2000 = (5291 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5291 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5291 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b26455 (exp_pos ((1291 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5291 : ℝ) / 2000), exp_pos (-((5291 : ℝ) / 2000))]

lemma cosh_b26550_ub : cosh ((531 : ℝ) / 200) ≤ (718140343 : ℝ) / 100000000 := by
  have exp_frac_b26550 : exp ((131 : ℝ) / 200) ≤ (192514301 : ℝ) / 100000000 := by
    have ht : ((131 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((131 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((131 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (192514301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((531 : ℝ) / 200) = exp 2 * exp ((131 : ℝ) / 200) := by
    rw [← exp_add, show (2 : ℝ) + (131 : ℝ) / 200 = (531 : ℝ) / 200 by norm_num]
  have hneg : exp (-((531 : ℝ) / 200)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((531 : ℝ) / 200) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b26550 (exp_pos ((131 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((531 : ℝ) / 200), exp_pos (-((531 : ℝ) / 200))]

lemma cosh_b26640_ub : cosh ((333 : ℝ) / 125) ≤ (724571490 : ℝ) / 100000000 := by
  have exp_frac_b26640 : exp ((83 : ℝ) / 125) ≤ (194254801 : ℝ) / 100000000 := by
    have ht : ((83 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((83 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((83 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (194254801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((333 : ℝ) / 125) = exp 2 * exp ((83 : ℝ) / 125) := by
    rw [← exp_add, show (2 : ℝ) + (83 : ℝ) / 125 = (333 : ℝ) / 125 by norm_num]
  have hneg : exp (-((333 : ℝ) / 125)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((333 : ℝ) / 125) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b26640 (exp_pos ((83 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((333 : ℝ) / 125), exp_pos (-((333 : ℝ) / 125))]

lemma cosh_b26730_ub : cosh ((2673 : ℝ) / 1000) ≤ (731060280 : ℝ) / 100000000 := by
  have exp_frac_b26730 : exp ((673 : ℝ) / 1000) ≤ (196010901 : ℝ) / 100000000 := by
    have ht : ((673 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((673 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((673 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (196010901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2673 : ℝ) / 1000) = exp 2 * exp ((673 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (673 : ℝ) / 1000 = (2673 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2673 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2673 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b26730 (exp_pos ((673 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2673 : ℝ) / 1000), exp_pos (-((2673 : ℝ) / 1000))]

lemma cosh_b26820_ub : cosh ((1341 : ℝ) / 500) ≤ (737608189 : ℝ) / 100000000 := by
  have exp_frac_b26820 : exp ((341 : ℝ) / 500) ≤ (197783001 : ℝ) / 100000000 := by
    have ht : ((341 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((341 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((341 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (197783001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1341 : ℝ) / 500) = exp 2 * exp ((341 : ℝ) / 500) := by
    rw [← exp_add, show (2 : ℝ) + (341 : ℝ) / 500 = (1341 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1341 : ℝ) / 500)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1341 : ℝ) / 500) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b26820 (exp_pos ((341 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1341 : ℝ) / 500), exp_pos (-((1341 : ℝ) / 500))]

lemma cosh_b26910_ub : cosh ((2691 : ℝ) / 1000) ≤ (744215219 : ℝ) / 100000000 := by
  have exp_frac_b26910 : exp ((691 : ℝ) / 1000) ≤ (199571101 : ℝ) / 100000000 := by
    have ht : ((691 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((691 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((691 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (199571101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2691 : ℝ) / 1000) = exp 2 * exp ((691 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (691 : ℝ) / 1000 = (2691 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2691 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2691 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b26910 (exp_pos ((691 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2691 : ℝ) / 1000), exp_pos (-((2691 : ℝ) / 1000))]

lemma cosh_b27000_ub : cosh ((27 : ℝ) / 10) ≤ (750881738 : ℝ) / 100000000 := by
  have exp_frac_b27000 : exp ((7 : ℝ) / 10) ≤ (201375301 : ℝ) / 100000000 := by
    have ht : ((7 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((7 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((7 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (201375301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((27 : ℝ) / 10) = exp 2 * exp ((7 : ℝ) / 10) := by
    rw [← exp_add, show (2 : ℝ) + (7 : ℝ) / 10 = (27 : ℝ) / 10 by norm_num]
  have hneg : exp (-((27 : ℝ) / 10)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((27 : ℝ) / 10) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b27000 (exp_pos ((7 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((27 : ℝ) / 10), exp_pos (-((27 : ℝ) / 10))]

lemma cosh_b27095_ub : cosh ((5419 : ℝ) / 2000) ≤ (757984267 : ℝ) / 100000000 := by
  have exp_frac_b27095 : exp ((1419 : ℝ) / 2000) ≤ (203297501 : ℝ) / 100000000 := by
    have ht : ((1419 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1419 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1419 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (203297501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5419 : ℝ) / 2000) = exp 2 * exp ((1419 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1419 : ℝ) / 2000 = (5419 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5419 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5419 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b27095 (exp_pos ((1419 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5419 : ℝ) / 2000), exp_pos (-((5419 : ℝ) / 2000))]

lemma cosh_b27185_ub : cosh ((5437 : ℝ) / 2000) ≤ (764775307 : ℝ) / 100000000 := by
  have exp_frac_b27185 : exp ((1437 : ℝ) / 2000) ≤ (205135401 : ℝ) / 100000000 := by
    have ht : ((1437 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1437 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1437 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (205135401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5437 : ℝ) / 2000) = exp 2 * exp ((1437 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1437 : ℝ) / 2000 = (5437 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5437 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5437 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b27185 (exp_pos ((1437 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5437 : ℝ) / 2000), exp_pos (-((5437 : ℝ) / 2000))]

lemma cosh_b27275_ub : cosh ((1091 : ℝ) / 400) ≤ (771628054 : ℝ) / 100000000 := by
  have exp_frac_b27275 : exp ((291 : ℝ) / 400) ≤ (206990001 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (206990001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1091 : ℝ) / 400) = exp 2 * exp ((291 : ℝ) / 400) := by
    rw [← exp_add, show (2 : ℝ) + (291 : ℝ) / 400 = (1091 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1091 : ℝ) / 400)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1091 : ℝ) / 400) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b27275 (exp_pos ((291 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1091 : ℝ) / 400), exp_pos (-((1091 : ℝ) / 400))]

lemma cosh_b27365_ub : cosh ((5473 : ℝ) / 2000) ≤ (778542508 : ℝ) / 100000000 := by
  have exp_frac_b27365 : exp ((1473 : ℝ) / 2000) ≤ (208861301 : ℝ) / 100000000 := by
    have ht : ((1473 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1473 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1473 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (208861301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5473 : ℝ) / 2000) = exp 2 * exp ((1473 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1473 : ℝ) / 2000 = (5473 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5473 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5473 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b27365 (exp_pos ((1473 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5473 : ℝ) / 2000), exp_pos (-((5473 : ℝ) / 2000))]

lemma cosh_b27455_ub : cosh ((5491 : ℝ) / 2000) ≤ (785519776 : ℝ) / 100000000 := by
  have exp_frac_b27455 : exp ((1491 : ℝ) / 2000) ≤ (210749601 : ℝ) / 100000000 := by
    have ht : ((1491 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1491 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1491 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (210749601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5491 : ℝ) / 2000) = exp 2 * exp ((1491 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1491 : ℝ) / 2000 = (5491 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5491 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5491 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b27455 (exp_pos ((1491 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5491 : ℝ) / 2000), exp_pos (-((5491 : ℝ) / 2000))]

lemma cosh_b27550_ub : cosh ((551 : ℝ) / 200) ≤ (792952638 : ℝ) / 100000000 := by
  have exp_frac_b27550 : exp ((151 : ℝ) / 200) ≤ (212761201 : ℝ) / 100000000 := by
    have ht : ((151 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((151 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((151 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (212761201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((551 : ℝ) / 200) = exp 2 * exp ((151 : ℝ) / 200) := by
    rw [← exp_add, show (2 : ℝ) + (151 : ℝ) / 200 = (551 : ℝ) / 200 by norm_num]
  have hneg : exp (-((551 : ℝ) / 200)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((551 : ℝ) / 200) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b27550 (exp_pos ((151 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((551 : ℝ) / 200), exp_pos (-((551 : ℝ) / 200))]

lemma cosh_b27640_ub : cosh ((691 : ℝ) / 250) ≤ (800059971 : ℝ) / 100000000 := by
  have exp_frac_b27640 : exp ((191 : ℝ) / 250) ≤ (214684701 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (214684701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((691 : ℝ) / 250) = exp 2 * exp ((191 : ℝ) / 250) := by
    rw [← exp_add, show (2 : ℝ) + (191 : ℝ) / 250 = (691 : ℝ) / 250 by norm_num]
  have hneg : exp (-((691 : ℝ) / 250)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((691 : ℝ) / 250) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b27640 (exp_pos ((191 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((691 : ℝ) / 250), exp_pos (-((691 : ℝ) / 250))]

lemma cosh_b27730_ub : cosh ((2773 : ℝ) / 1000) ≤ (807231596 : ℝ) / 100000000 := by
  have exp_frac_b27730 : exp ((773 : ℝ) / 1000) ≤ (216625601 : ℝ) / 100000000 := by
    have ht : ((773 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((773 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((773 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (216625601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2773 : ℝ) / 1000) = exp 2 * exp ((773 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (773 : ℝ) / 1000 = (2773 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2773 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2773 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b27730 (exp_pos ((773 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2773 : ℝ) / 1000), exp_pos (-((2773 : ℝ) / 1000))]

lemma cosh_b27820_ub : cosh ((1391 : ℝ) / 500) ≤ (814467884 : ℝ) / 100000000 := by
  have exp_frac_b27820 : exp ((391 : ℝ) / 500) ≤ (218584001 : ℝ) / 100000000 := by
    have ht : ((391 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((391 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((391 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (218584001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1391 : ℝ) / 500) = exp 2 * exp ((391 : ℝ) / 500) := by
    rw [← exp_add, show (2 : ℝ) + (391 : ℝ) / 500 = (1391 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1391 : ℝ) / 500)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1391 : ℝ) / 500) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b27820 (exp_pos ((391 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1391 : ℝ) / 500), exp_pos (-((1391 : ℝ) / 500))]

lemma cosh_b27910_ub : cosh ((2791 : ℝ) / 1000) ≤ (821769943 : ℝ) / 100000000 := by
  have exp_frac_b27910 : exp ((791 : ℝ) / 1000) ≤ (220560201 : ℝ) / 100000000 := by
    have ht : ((791 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((791 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((791 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (220560201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2791 : ℝ) / 1000) = exp 2 * exp ((791 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (791 : ℝ) / 1000 = (2791 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2791 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2791 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b27910 (exp_pos ((791 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2791 : ℝ) / 1000), exp_pos (-((2791 : ℝ) / 1000))]

lemma cosh_b28000_ub : cosh ((14 : ℝ) / 5) ≤ (829137773 : ℝ) / 100000000 := by
  have exp_frac_b28000 : exp ((4 : ℝ) / 5) ≤ (222554201 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((4 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((4 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (222554201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((14 : ℝ) / 5) = exp 2 * exp ((4 : ℝ) / 5) := by
    rw [← exp_add, show (2 : ℝ) + (4 : ℝ) / 5 = (14 : ℝ) / 5 by norm_num]
  have hneg : exp (-((14 : ℝ) / 5)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((14 : ℝ) / 5) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b28000 (exp_pos ((4 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((14 : ℝ) / 5), exp_pos (-((14 : ℝ) / 5))]

lemma cosh_b28095_ub : cosh ((5619 : ℝ) / 2000) ≤ (836987062 : ℝ) / 100000000 := by
  have exp_frac_b28095 : exp ((1619 : ℝ) / 2000) ≤ (224678501 : ℝ) / 100000000 := by
    have ht : ((1619 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1619 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1619 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (224678501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5619 : ℝ) / 2000) = exp 2 * exp ((1619 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1619 : ℝ) / 2000 = (5619 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5619 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5619 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b28095 (exp_pos ((1619 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5619 : ℝ) / 2000), exp_pos (-((5619 : ℝ) / 2000))]

lemma cosh_b28185_ub : cosh ((5637 : ℝ) / 2000) ≤ (844492346 : ℝ) / 100000000 := by
  have exp_frac_b28185 : exp ((1637 : ℝ) / 2000) ≤ (226709701 : ℝ) / 100000000 := by
    have ht : ((1637 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1637 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1637 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (226709701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5637 : ℝ) / 2000) = exp 2 * exp ((1637 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1637 : ℝ) / 2000 = (5637 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5637 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5637 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b28185 (exp_pos ((1637 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5637 : ℝ) / 2000), exp_pos (-((5637 : ℝ) / 2000))]

lemma cosh_b28275_ub : cosh ((1131 : ℝ) / 400) ≤ (852065618 : ℝ) / 100000000 := by
  have exp_frac_b28275 : exp ((331 : ℝ) / 400) ≤ (228759301 : ℝ) / 100000000 := by
    have ht : ((331 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((331 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((331 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (228759301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1131 : ℝ) / 400) = exp 2 * exp ((331 : ℝ) / 400) := by
    rw [← exp_add, show (2 : ℝ) + (331 : ℝ) / 400 = (1131 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1131 : ℝ) / 400)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1131 : ℝ) / 400) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b28275 (exp_pos ((331 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1131 : ℝ) / 400), exp_pos (-((1131 : ℝ) / 400))]

lemma cosh_b28365_ub : cosh ((5673 : ℝ) / 2000) ≤ (859707617 : ℝ) / 100000000 := by
  have exp_frac_b28365 : exp ((1673 : ℝ) / 2000) ≤ (230827501 : ℝ) / 100000000 := by
    have ht : ((1673 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1673 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1673 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (230827501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5673 : ℝ) / 2000) = exp 2 * exp ((1673 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1673 : ℝ) / 2000 = (5673 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5673 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5673 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b28365 (exp_pos ((1673 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5673 : ℝ) / 2000), exp_pos (-((5673 : ℝ) / 2000))]

lemma cosh_b28455_ub : cosh ((5691 : ℝ) / 2000) ≤ (867418343 : ℝ) / 100000000 := by
  have exp_frac_b28455 : exp ((1691 : ℝ) / 2000) ≤ (232914301 : ℝ) / 100000000 := by
    have ht : ((1691 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1691 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1691 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (232914301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5691 : ℝ) / 2000) = exp 2 * exp ((1691 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1691 : ℝ) / 2000 = (5691 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5691 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5691 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b28455 (exp_pos ((1691 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5691 : ℝ) / 2000), exp_pos (-((5691 : ℝ) / 2000))]

lemma cosh_b28550_ub : cosh ((571 : ℝ) / 200) ≤ (875633067 : ℝ) / 100000000 := by
  have exp_frac_b28550 : exp ((171 : ℝ) / 200) ≤ (235137501 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((171 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((171 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (235137501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((571 : ℝ) / 200) = exp 2 * exp ((171 : ℝ) / 200) := by
    rw [← exp_add, show (2 : ℝ) + (171 : ℝ) / 200 = (571 : ℝ) / 200 by norm_num]
  have hneg : exp (-((571 : ℝ) / 200)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((571 : ℝ) / 200) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b28550 (exp_pos ((171 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((571 : ℝ) / 200), exp_pos (-((571 : ℝ) / 200))]

lemma cosh_b28640_ub : cosh ((358 : ℝ) / 125) ≤ (883487898 : ℝ) / 100000000 := by
  have exp_frac_b28640 : exp ((108 : ℝ) / 125) ≤ (237263301 : ℝ) / 100000000 := by
    have ht : ((108 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((108 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((108 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (237263301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((358 : ℝ) / 125) = exp 2 * exp ((108 : ℝ) / 125) := by
    rw [← exp_add, show (2 : ℝ) + (108 : ℝ) / 125 = (358 : ℝ) / 125 by norm_num]
  have hneg : exp (-((358 : ℝ) / 125)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((358 : ℝ) / 125) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b28640 (exp_pos ((108 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((358 : ℝ) / 125), exp_pos (-((358 : ℝ) / 125))]

lemma cosh_b28730_ub : cosh ((2873 : ℝ) / 1000) ≤ (891413673 : ℝ) / 100000000 := by
  have exp_frac_b28730 : exp ((873 : ℝ) / 1000) ≤ (239408301 : ℝ) / 100000000 := by
    have ht : ((873 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((873 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((873 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (239408301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2873 : ℝ) / 1000) = exp 2 * exp ((873 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (873 : ℝ) / 1000 = (2873 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2873 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2873 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b28730 (exp_pos ((873 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2873 : ℝ) / 1000), exp_pos (-((2873 : ℝ) / 1000))]

lemma cosh_b28820_ub : cosh ((1441 : ℝ) / 500) ≤ (899411131 : ℝ) / 100000000 := by
  have exp_frac_b28820 : exp ((441 : ℝ) / 500) ≤ (241572701 : ℝ) / 100000000 := by
    have ht : ((441 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((441 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((441 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (241572701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1441 : ℝ) / 500) = exp 2 * exp ((441 : ℝ) / 500) := by
    rw [← exp_add, show (2 : ℝ) + (441 : ℝ) / 500 = (1441 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1441 : ℝ) / 500)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1441 : ℝ) / 500) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b28820 (exp_pos ((441 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1441 : ℝ) / 500), exp_pos (-((1441 : ℝ) / 500))]

lemma cosh_b28910_ub : cosh ((2891 : ℝ) / 1000) ≤ (907481011 : ℝ) / 100000000 := by
  have exp_frac_b28910 : exp ((891 : ℝ) / 1000) ≤ (243756701 : ℝ) / 100000000 := by
    have ht : ((891 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((891 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((891 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (243756701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2891 : ℝ) / 1000) = exp 2 * exp ((891 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (891 : ℝ) / 1000 = (2891 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2891 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2891 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b28910 (exp_pos ((891 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2891 : ℝ) / 1000), exp_pos (-((2891 : ℝ) / 1000))]

lemma cosh_b29000_ub : cosh ((29 : ℝ) / 10) ≤ (915623682 : ℝ) / 100000000 := by
  have exp_frac_b29000 : exp ((9 : ℝ) / 10) ≤ (245960401 : ℝ) / 100000000 := by
    have ht : ((9 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((9 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((9 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (245960401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((29 : ℝ) / 10) = exp 2 * exp ((9 : ℝ) / 10) := by
    rw [← exp_add, show (2 : ℝ) + (9 : ℝ) / 10 = (29 : ℝ) / 10 by norm_num]
  have hneg : exp (-((29 : ℝ) / 10)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((29 : ℝ) / 10) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b29000 (exp_pos ((9 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((29 : ℝ) / 10), exp_pos (-((29 : ℝ) / 10))]

lemma cosh_b29095_ub : cosh ((5819 : ℝ) / 2000) ≤ (924298434 : ℝ) / 100000000 := by
  have exp_frac_b29095 : exp ((1819 : ℝ) / 2000) ≤ (248308101 : ℝ) / 100000000 := by
    have ht : ((1819 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1819 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1819 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (248308101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5819 : ℝ) / 2000) = exp 2 * exp ((1819 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1819 : ℝ) / 2000 = (5819 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5819 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5819 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b29095 (exp_pos ((1819 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5819 : ℝ) / 2000), exp_pos (-((5819 : ℝ) / 2000))]

lemma cosh_b29185_ub : cosh ((5837 : ℝ) / 2000) ≤ (932593339 : ℝ) / 100000000 := by
  have exp_frac_b29185 : exp ((1837 : ℝ) / 2000) ≤ (250553001 : ℝ) / 100000000 := by
    have ht : ((1837 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1837 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1837 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (250553001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5837 : ℝ) / 2000) = exp 2 * exp ((1837 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1837 : ℝ) / 2000 = (5837 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5837 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5837 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b29185 (exp_pos ((1837 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5837 : ℝ) / 2000), exp_pos (-((5837 : ℝ) / 2000))]

lemma cosh_b29275_ub : cosh ((1171 : ℝ) / 400) ≤ (940962884 : ℝ) / 100000000 := by
  have exp_frac_b29275 : exp ((371 : ℝ) / 400) ≤ (252818101 : ℝ) / 100000000 := by
    have ht : ((371 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((371 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((371 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (252818101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1171 : ℝ) / 400) = exp 2 * exp ((371 : ℝ) / 400) := by
    rw [← exp_add, show (2 : ℝ) + (371 : ℝ) / 400 = (1171 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1171 : ℝ) / 400)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1171 : ℝ) / 400) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b29275 (exp_pos ((371 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1171 : ℝ) / 400), exp_pos (-((1171 : ℝ) / 400))]

lemma cosh_b29365_ub : cosh ((5873 : ℝ) / 2000) ≤ (949408545 : ℝ) / 100000000 := by
  have exp_frac_b29365 : exp ((1873 : ℝ) / 2000) ≤ (255103801 : ℝ) / 100000000 := by
    have ht : ((1873 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1873 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1873 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (255103801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5873 : ℝ) / 2000) = exp 2 * exp ((1873 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1873 : ℝ) / 2000 = (5873 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5873 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5873 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b29365 (exp_pos ((1873 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5873 : ℝ) / 2000), exp_pos (-((5873 : ℝ) / 2000))]

lemma cosh_b29455_ub : cosh ((5891 : ℝ) / 2000) ≤ (957930324 : ℝ) / 100000000 := by
  have exp_frac_b29455 : exp ((1891 : ℝ) / 2000) ≤ (257410101 : ℝ) / 100000000 := by
    have ht : ((1891 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1891 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1891 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (257410101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((5891 : ℝ) / 2000) = exp 2 * exp ((1891 : ℝ) / 2000) := by
    rw [← exp_add, show (2 : ℝ) + (1891 : ℝ) / 2000 = (5891 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((5891 : ℝ) / 2000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((5891 : ℝ) / 2000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b29455 (exp_pos ((1891 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((5891 : ℝ) / 2000), exp_pos (-((5891 : ℝ) / 2000))]

lemma cosh_b29550_ub : cosh ((591 : ℝ) / 200) ≤ (967008939 : ℝ) / 100000000 := by
  have exp_frac_b29550 : exp ((191 : ℝ) / 200) ≤ (259867101 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (259867101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((591 : ℝ) / 200) = exp 2 * exp ((191 : ℝ) / 200) := by
    rw [← exp_add, show (2 : ℝ) + (191 : ℝ) / 200 = (591 : ℝ) / 200 by norm_num]
  have hneg : exp (-((591 : ℝ) / 200)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((591 : ℝ) / 200) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b29550 (exp_pos ((191 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((591 : ℝ) / 200), exp_pos (-((591 : ℝ) / 200))]

lemma cosh_b29640_ub : cosh ((741 : ℝ) / 250) ≤ (975689972 : ℝ) / 100000000 := by
  have exp_frac_b29640 : exp ((241 : ℝ) / 250) ≤ (262216501 : ℝ) / 100000000 := by
    have ht : ((241 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((241 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((241 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (262216501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((741 : ℝ) / 250) = exp 2 * exp ((241 : ℝ) / 250) := by
    rw [← exp_add, show (2 : ℝ) + (241 : ℝ) / 250 = (741 : ℝ) / 250 by norm_num]
  have hneg : exp (-((741 : ℝ) / 250)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((741 : ℝ) / 250) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b29640 (exp_pos ((241 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((741 : ℝ) / 250), exp_pos (-((741 : ℝ) / 250))]

lemma cosh_b29730_ub : cosh ((2973 : ℝ) / 1000) ≤ (984449339 : ℝ) / 100000000 := by
  have exp_frac_b29730 : exp ((973 : ℝ) / 1000) ≤ (264587101 : ℝ) / 100000000 := by
    have ht : ((973 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((973 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((973 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (264587101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2973 : ℝ) / 1000) = exp 2 * exp ((973 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (973 : ℝ) / 1000 = (2973 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2973 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2973 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b29730 (exp_pos ((973 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2973 : ℝ) / 1000), exp_pos (-((2973 : ℝ) / 1000))]

lemma cosh_b29820_ub : cosh ((1491 : ℝ) / 500) ≤ (993287779 : ℝ) / 100000000 := by
  have exp_frac_b29820 : exp ((491 : ℝ) / 500) ≤ (266979101 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((491 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((491 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (266979101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1491 : ℝ) / 500) = exp 2 * exp ((491 : ℝ) / 500) := by
    rw [← exp_add, show (2 : ℝ) + (491 : ℝ) / 500 = (1491 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1491 : ℝ) / 500)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1491 : ℝ) / 500) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b29820 (exp_pos ((491 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1491 : ℝ) / 500), exp_pos (-((1491 : ℝ) / 500))]

lemma cosh_b29910_ub : cosh ((2991 : ℝ) / 1000) ≤ (1002206400 : ℝ) / 100000000 := by
  have exp_frac_b29910 : exp ((991 : ℝ) / 1000) ≤ (269392801 : ℝ) / 100000000 := by
    have ht : ((991 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((991 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((991 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (269392801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2991 : ℝ) / 1000) = exp 2 * exp ((991 : ℝ) / 1000) := by
    rw [← exp_add, show (2 : ℝ) + (991 : ℝ) / 1000 = (2991 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((2991 : ℝ) / 1000)) ≤ (136 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2991 : ℝ) / 1000) ≤ -(2 : ℝ))).trans exp_neg_two_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_two_le exp_frac_b29910 (exp_pos ((991 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2991 : ℝ) / 1000), exp_pos (-((2991 : ℝ) / 1000))]

lemma cosh_b30000_ub : cosh ((3 : ℝ) / 1) ≤ (1006800001 : ℝ) / 100000000 := by
  rw [show (3 : ℝ) / 1 = (3 : ℝ) by norm_num]
  exact (cosh_three_le).trans (by norm_num)

lemma cosh_b30095_ub : cosh ((6019 : ℝ) / 2000) ≤ (1016387058 : ℝ) / 100000000 := by
  have exp_frac_b30095 : exp ((19 : ℝ) / 2000) ≤ (100954601 : ℝ) / 100000000 := by
    have ht : ((19 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((19 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((19 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100954601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6019 : ℝ) / 2000) = exp 3 * exp ((19 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (19 : ℝ) / 2000 = (6019 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6019 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6019 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b30095 (exp_pos ((19 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6019 : ℝ) / 2000), exp_pos (-((6019 : ℝ) / 2000))]

lemma cosh_b30185_ub : cosh ((6037 : ℝ) / 2000) ≤ (1025553304 : ℝ) / 100000000 := by
  have exp_frac_b30185 : exp ((37 : ℝ) / 2000) ≤ (101867301 : ℝ) / 100000000 := by
    have ht : ((37 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((37 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((37 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101867301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6037 : ℝ) / 2000) = exp 3 * exp ((37 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (37 : ℝ) / 2000 = (6037 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6037 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6037 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b30185 (exp_pos ((37 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6037 : ℝ) / 2000), exp_pos (-((6037 : ℝ) / 2000))]

lemma cosh_b30275_ub : cosh ((1211 : ℝ) / 400) ≤ (1034801903 : ℝ) / 100000000 := by
  have exp_frac_b30275 : exp ((11 : ℝ) / 400) ≤ (102788201 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((11 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((11 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102788201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1211 : ℝ) / 400) = exp 3 * exp ((11 : ℝ) / 400) := by
    rw [← exp_add, show (3 : ℝ) + (11 : ℝ) / 400 = (1211 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1211 : ℝ) / 400)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1211 : ℝ) / 400) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b30275 (exp_pos ((11 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1211 : ℝ) / 400), exp_pos (-((1211 : ℝ) / 400))]

lemma cosh_b30365_ub : cosh ((6073 : ℝ) / 2000) ≤ (1044134863 : ℝ) / 100000000 := by
  have exp_frac_b30365 : exp ((73 : ℝ) / 2000) ≤ (103717501 : ℝ) / 100000000 := by
    have ht : ((73 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((73 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((73 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103717501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6073 : ℝ) / 2000) = exp 3 * exp ((73 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (73 : ℝ) / 2000 = (6073 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6073 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6073 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b30365 (exp_pos ((73 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6073 : ℝ) / 2000), exp_pos (-((6073 : ℝ) / 2000))]

lemma cosh_b30455_ub : cosh ((6091 : ℝ) / 2000) ≤ (1053552184 : ℝ) / 100000000 := by
  have exp_frac_b30455 : exp ((91 : ℝ) / 2000) ≤ (104655201 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104655201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6091 : ℝ) / 2000) = exp 3 * exp ((91 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (91 : ℝ) / 2000 = (6091 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6091 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6091 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b30455 (exp_pos ((91 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6091 : ℝ) / 2000), exp_pos (-((6091 : ℝ) / 2000))]

lemma cosh_b30550_ub : cosh ((611 : ℝ) / 200) ≤ (1063584137 : ℝ) / 100000000 := by
  have exp_frac_b30550 : exp ((11 : ℝ) / 200) ≤ (105654101 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((11 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((11 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105654101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((611 : ℝ) / 200) = exp 3 * exp ((11 : ℝ) / 200) := by
    rw [← exp_add, show (3 : ℝ) + (11 : ℝ) / 200 = (611 : ℝ) / 200 by norm_num]
  have hneg : exp (-((611 : ℝ) / 200)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((611 : ℝ) / 200) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b30550 (exp_pos ((11 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((611 : ℝ) / 200), exp_pos (-((611 : ℝ) / 200))]

lemma cosh_b30640_ub : cosh ((383 : ℝ) / 125) ≤ (1073177210 : ℝ) / 100000000 := by
  have exp_frac_b30640 : exp ((8 : ℝ) / 125) ≤ (106609301 : ℝ) / 100000000 := by
    have ht : ((8 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((8 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((8 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106609301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((383 : ℝ) / 125) = exp 3 * exp ((8 : ℝ) / 125) := by
    rw [← exp_add, show (3 : ℝ) + (8 : ℝ) / 125 = (383 : ℝ) / 125 by norm_num]
  have hneg : exp (-((383 : ℝ) / 125)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((383 : ℝ) / 125) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b30640 (exp_pos ((8 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((383 : ℝ) / 125), exp_pos (-((383 : ℝ) / 125))]

lemma cosh_b30730_ub : cosh ((3073 : ℝ) / 1000) ≤ (1082856654 : ℝ) / 100000000 := by
  have exp_frac_b30730 : exp ((73 : ℝ) / 1000) ≤ (107573101 : ℝ) / 100000000 := by
    have ht : ((73 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((73 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((73 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107573101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3073 : ℝ) / 1000) = exp 3 * exp ((73 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (73 : ℝ) / 1000 = (3073 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3073 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3073 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b30730 (exp_pos ((73 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3073 : ℝ) / 1000), exp_pos (-((3073 : ℝ) / 1000))]

lemma cosh_b30820_ub : cosh ((1541 : ℝ) / 500) ≤ (1092623471 : ℝ) / 100000000 := by
  have exp_frac_b30820 : exp ((41 : ℝ) / 500) ≤ (108545601 : ℝ) / 100000000 := by
    have ht : ((41 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((41 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((41 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108545601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1541 : ℝ) / 500) = exp 3 * exp ((41 : ℝ) / 500) := by
    rw [← exp_add, show (3 : ℝ) + (41 : ℝ) / 500 = (1541 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1541 : ℝ) / 500)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1541 : ℝ) / 500) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b30820 (exp_pos ((41 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1541 : ℝ) / 500), exp_pos (-((1541 : ℝ) / 500))]

lemma cosh_b30910_ub : cosh ((3091 : ℝ) / 1000) ≤ (1102479672 : ℝ) / 100000000 := by
  have exp_frac_b30910 : exp ((91 : ℝ) / 1000) ≤ (109527001 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109527001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3091 : ℝ) / 1000) = exp 3 * exp ((91 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (91 : ℝ) / 1000 = (3091 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3091 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3091 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b30910 (exp_pos ((91 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3091 : ℝ) / 1000), exp_pos (-((3091 : ℝ) / 1000))]

lemma cosh_b31000_ub : cosh ((31 : ℝ) / 10) ≤ (1112423246 : ℝ) / 100000000 := by
  have exp_frac_b31000 : exp ((1 : ℝ) / 10) ≤ (110517101 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((1 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110517101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((31 : ℝ) / 10) = exp 3 * exp ((1 : ℝ) / 10) := by
    rw [← exp_add, show (3 : ℝ) + (1 : ℝ) / 10 = (31 : ℝ) / 10 by norm_num]
  have hneg : exp (-((31 : ℝ) / 10)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((31 : ℝ) / 10) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b31000 (exp_pos ((1 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((31 : ℝ) / 10), exp_pos (-((31 : ℝ) / 10))]

lemma cosh_b31095_ub : cosh ((6219 : ℝ) / 2000) ≤ (1123018611 : ℝ) / 100000000 := by
  have exp_frac_b31095 : exp ((219 : ℝ) / 2000) ≤ (111572101 : ℝ) / 100000000 := by
    have ht : ((219 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((219 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((219 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (111572101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6219 : ℝ) / 2000) = exp 3 * exp ((219 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (219 : ℝ) / 2000 = (6219 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6219 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6219 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b31095 (exp_pos ((219 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6219 : ℝ) / 2000), exp_pos (-((6219 : ℝ) / 2000))]

lemma cosh_b31185_ub : cosh ((6237 : ℝ) / 2000) ≤ (1133147981 : ℝ) / 100000000 := by
  have exp_frac_b31185 : exp ((237 : ℝ) / 2000) ≤ (112580701 : ℝ) / 100000000 := by
    have ht : ((237 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((237 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((237 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (112580701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6237 : ℝ) / 2000) = exp 3 * exp ((237 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (237 : ℝ) / 2000 = (6237 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6237 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6237 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b31185 (exp_pos ((237 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6237 : ℝ) / 2000), exp_pos (-((6237 : ℝ) / 2000))]

lemma cosh_b31275_ub : cosh ((1251 : ℝ) / 400) ≤ (1143369746 : ℝ) / 100000000 := by
  have exp_frac_b31275 : exp ((51 : ℝ) / 400) ≤ (113598501 : ℝ) / 100000000 := by
    have ht : ((51 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((51 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((51 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (113598501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1251 : ℝ) / 400) = exp 3 * exp ((51 : ℝ) / 400) := by
    rw [← exp_add, show (3 : ℝ) + (51 : ℝ) / 400 = (1251 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1251 : ℝ) / 400)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1251 : ℝ) / 400) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b31275 (exp_pos ((51 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1251 : ℝ) / 400), exp_pos (-((1251 : ℝ) / 400))]

lemma cosh_b31365_ub : cosh ((6273 : ℝ) / 2000) ≤ (1153683907 : ℝ) / 100000000 := by
  have exp_frac_b31365 : exp ((273 : ℝ) / 2000) ≤ (114625501 : ℝ) / 100000000 := by
    have ht : ((273 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((273 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((273 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (114625501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6273 : ℝ) / 2000) = exp 3 * exp ((273 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (273 : ℝ) / 2000 = (6273 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6273 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6273 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b31365 (exp_pos ((273 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6273 : ℝ) / 2000), exp_pos (-((6273 : ℝ) / 2000))]

lemma cosh_b31455_ub : cosh ((6291 : ℝ) / 2000) ≤ (1164091468 : ℝ) / 100000000 := by
  have exp_frac_b31455 : exp ((291 : ℝ) / 2000) ≤ (115661801 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (115661801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6291 : ℝ) / 2000) = exp 3 * exp ((291 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (291 : ℝ) / 2000 = (6291 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6291 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6291 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b31455 (exp_pos ((291 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6291 : ℝ) / 2000), exp_pos (-((6291 : ℝ) / 2000))]

lemma cosh_b31550_ub : cosh ((631 : ℝ) / 200) ≤ (1175178940 : ℝ) / 100000000 := by
  have exp_frac_b31550 : exp ((31 : ℝ) / 200) ≤ (116765801 : ℝ) / 100000000 := by
    have ht : ((31 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((31 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((31 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (116765801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((631 : ℝ) / 200) = exp 3 * exp ((31 : ℝ) / 200) := by
    rw [← exp_add, show (3 : ℝ) + (31 : ℝ) / 200 = (631 : ℝ) / 200 by norm_num]
  have hneg : exp (-((631 : ℝ) / 200)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((631 : ℝ) / 200) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b31550 (exp_pos ((31 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((631 : ℝ) / 200), exp_pos (-((631 : ℝ) / 200))]

lemma cosh_b31640_ub : cosh ((791 : ℝ) / 250) ≤ (1185781335 : ℝ) / 100000000 := by
  have exp_frac_b31640 : exp ((41 : ℝ) / 250) ≤ (117821501 : ℝ) / 100000000 := by
    have ht : ((41 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((41 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((41 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (117821501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((791 : ℝ) / 250) = exp 3 * exp ((41 : ℝ) / 250) := by
    rw [← exp_add, show (3 : ℝ) + (41 : ℝ) / 250 = (791 : ℝ) / 250 by norm_num]
  have hneg : exp (-((791 : ℝ) / 250)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((791 : ℝ) / 250) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b31640 (exp_pos ((41 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((791 : ℝ) / 250), exp_pos (-((791 : ℝ) / 250))]

lemma cosh_b31730_ub : cosh ((3173 : ℝ) / 1000) ≤ (1196479139 : ℝ) / 100000000 := by
  have exp_frac_b31730 : exp ((173 : ℝ) / 1000) ≤ (118886701 : ℝ) / 100000000 := by
    have ht : ((173 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((173 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((173 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (118886701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3173 : ℝ) / 1000) = exp 3 * exp ((173 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (173 : ℝ) / 1000 = (3173 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3173 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3173 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b31730 (exp_pos ((173 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3173 : ℝ) / 1000), exp_pos (-((3173 : ℝ) / 1000))]

lemma cosh_b31820_ub : cosh ((1591 : ℝ) / 500) ≤ (1207273355 : ℝ) / 100000000 := by
  have exp_frac_b31820 : exp ((91 : ℝ) / 500) ≤ (119961501 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (119961501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1591 : ℝ) / 500) = exp 3 * exp ((91 : ℝ) / 500) := by
    rw [← exp_add, show (3 : ℝ) + (91 : ℝ) / 500 = (1591 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1591 : ℝ) / 500)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1591 : ℝ) / 500) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b31820 (exp_pos ((91 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1591 : ℝ) / 500), exp_pos (-((1591 : ℝ) / 500))]

lemma cosh_b31910_ub : cosh ((3191 : ℝ) / 1000) ≤ (1218164989 : ℝ) / 100000000 := by
  have exp_frac_b31910 : exp ((191 : ℝ) / 1000) ≤ (121046001 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (121046001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3191 : ℝ) / 1000) = exp 3 * exp ((191 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (191 : ℝ) / 1000 = (3191 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3191 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3191 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b31910 (exp_pos ((191 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3191 : ℝ) / 1000), exp_pos (-((3191 : ℝ) / 1000))]

lemma cosh_b32000_ub : cosh ((16 : ℝ) / 5) ≤ (1229155043 : ℝ) / 100000000 := by
  have exp_frac_b32000 : exp ((1 : ℝ) / 5) ≤ (122140301 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((1 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (122140301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((16 : ℝ) / 5) = exp 3 * exp ((1 : ℝ) / 5) := by
    rw [← exp_add, show (3 : ℝ) + (1 : ℝ) / 5 = (16 : ℝ) / 5 by norm_num]
  have hneg : exp (-((16 : ℝ) / 5)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((16 : ℝ) / 5) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b32000 (exp_pos ((1 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((16 : ℝ) / 5), exp_pos (-((16 : ℝ) / 5))]

lemma cosh_b32095_ub : cosh ((6419 : ℝ) / 2000) ≤ (1240864177 : ℝ) / 100000000 := by
  have exp_frac_b32095 : exp ((419 : ℝ) / 2000) ≤ (123306201 : ℝ) / 100000000 := by
    have ht : ((419 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((419 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((419 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (123306201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6419 : ℝ) / 2000) = exp 3 * exp ((419 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (419 : ℝ) / 2000 = (6419 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6419 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6419 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b32095 (exp_pos ((419 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6419 : ℝ) / 2000), exp_pos (-((6419 : ℝ) / 2000))]

lemma cosh_b32185_ub : cosh ((6437 : ℝ) / 2000) ≤ (1252060114 : ℝ) / 100000000 := by
  have exp_frac_b32185 : exp ((437 : ℝ) / 2000) ≤ (124421001 : ℝ) / 100000000 := by
    have ht : ((437 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((437 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((437 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (124421001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6437 : ℝ) / 2000) = exp 3 * exp ((437 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (437 : ℝ) / 2000 = (6437 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6437 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6437 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b32185 (exp_pos ((437 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6437 : ℝ) / 2000), exp_pos (-((6437 : ℝ) / 2000))]

lemma cosh_b32275_ub : cosh ((1291 : ℝ) / 400) ≤ (1263356480 : ℝ) / 100000000 := by
  have exp_frac_b32275 : exp ((91 : ℝ) / 400) ≤ (125545801 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (125545801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1291 : ℝ) / 400) = exp 3 * exp ((91 : ℝ) / 400) := by
    rw [← exp_add, show (3 : ℝ) + (91 : ℝ) / 400 = (1291 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1291 : ℝ) / 400)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1291 : ℝ) / 400) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b32275 (exp_pos ((91 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1291 : ℝ) / 400), exp_pos (-((1291 : ℝ) / 400))]

lemma cosh_b32365_ub : cosh ((6473 : ℝ) / 2000) ≤ (1274755285 : ℝ) / 100000000 := by
  have exp_frac_b32365 : exp ((473 : ℝ) / 2000) ≤ (126680801 : ℝ) / 100000000 := by
    have ht : ((473 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((473 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((473 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (126680801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6473 : ℝ) / 2000) = exp 3 * exp ((473 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (473 : ℝ) / 2000 = (6473 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6473 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6473 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b32365 (exp_pos ((473 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6473 : ℝ) / 2000), exp_pos (-((6473 : ℝ) / 2000))]

lemma cosh_b32455_ub : cosh ((6491 : ℝ) / 2000) ≤ (1286257533 : ℝ) / 100000000 := by
  have exp_frac_b32455 : exp ((491 : ℝ) / 2000) ≤ (127826101 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((491 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((491 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (127826101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6491 : ℝ) / 2000) = exp 3 * exp ((491 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (491 : ℝ) / 2000 = (6491 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6491 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6491 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b32455 (exp_pos ((491 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6491 : ℝ) / 2000), exp_pos (-((6491 : ℝ) / 2000))]

lemma cosh_b32550_ub : cosh ((651 : ℝ) / 200) ≤ (1298510997 : ℝ) / 100000000 := by
  have exp_frac_b32550 : exp ((51 : ℝ) / 200) ≤ (129046201 : ℝ) / 100000000 := by
    have ht : ((51 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((51 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((51 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (129046201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((651 : ℝ) / 200) = exp 3 * exp ((51 : ℝ) / 200) := by
    rw [← exp_add, show (3 : ℝ) + (51 : ℝ) / 200 = (651 : ℝ) / 200 by norm_num]
  have hneg : exp (-((651 : ℝ) / 200)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((651 : ℝ) / 200) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b32550 (exp_pos ((51 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((651 : ℝ) / 200), exp_pos (-((651 : ℝ) / 200))]

lemma cosh_b32640_ub : cosh ((408 : ℝ) / 125) ≤ (1310228165 : ℝ) / 100000000 := by
  have exp_frac_b32640 : exp ((33 : ℝ) / 125) ≤ (130212901 : ℝ) / 100000000 := by
    have ht : ((33 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((33 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((33 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (130212901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((408 : ℝ) / 125) = exp 3 * exp ((33 : ℝ) / 125) := by
    rw [← exp_add, show (3 : ℝ) + (33 : ℝ) / 125 = (408 : ℝ) / 125 by norm_num]
  have hneg : exp (-((408 : ℝ) / 125)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((408 : ℝ) / 125) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b32640 (exp_pos ((33 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((408 : ℝ) / 125), exp_pos (-((408 : ℝ) / 125))]

lemma cosh_b32730_ub : cosh ((3273 : ℝ) / 1000) ≤ (1322050785 : ℝ) / 100000000 := by
  have exp_frac_b32730 : exp ((273 : ℝ) / 1000) ≤ (131390101 : ℝ) / 100000000 := by
    have ht : ((273 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((273 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((273 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (131390101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3273 : ℝ) / 1000) = exp 3 * exp ((273 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (273 : ℝ) / 1000 = (3273 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3273 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3273 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b32730 (exp_pos ((273 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3273 : ℝ) / 1000), exp_pos (-((3273 : ℝ) / 1000))]

lemma cosh_b32820_ub : cosh ((1641 : ℝ) / 500) ≤ (1333979860 : ℝ) / 100000000 := by
  have exp_frac_b32820 : exp ((141 : ℝ) / 500) ≤ (132577901 : ℝ) / 100000000 := by
    have ht : ((141 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((141 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((141 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (132577901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1641 : ℝ) / 500) = exp 3 * exp ((141 : ℝ) / 500) := by
    rw [← exp_add, show (3 : ℝ) + (141 : ℝ) / 500 = (1641 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1641 : ℝ) / 500)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1641 : ℝ) / 500) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b32820 (exp_pos ((141 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1641 : ℝ) / 500), exp_pos (-((1641 : ℝ) / 500))]

lemma cosh_b32910_ub : cosh ((3291 : ℝ) / 1000) ≤ (1346017400 : ℝ) / 100000000 := by
  have exp_frac_b32910 : exp ((291 : ℝ) / 1000) ≤ (133776501 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (133776501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3291 : ℝ) / 1000) = exp 3 * exp ((291 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (291 : ℝ) / 1000 = (3291 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3291 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3291 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b32910 (exp_pos ((291 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3291 : ℝ) / 1000), exp_pos (-((3291 : ℝ) / 1000))]

lemma cosh_b33000_ub : cosh ((33 : ℝ) / 10) ≤ (1358163404 : ℝ) / 100000000 := by
  have exp_frac_b33000 : exp ((3 : ℝ) / 10) ≤ (134985901 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((3 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((3 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (134985901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((33 : ℝ) / 10) = exp 3 * exp ((3 : ℝ) / 10) := by
    rw [← exp_add, show (3 : ℝ) + (3 : ℝ) / 10 = (33 : ℝ) / 10 by norm_num]
  have hneg : exp (-((33 : ℝ) / 10)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((33 : ℝ) / 10) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b33000 (exp_pos ((3 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((33 : ℝ) / 10), exp_pos (-((33 : ℝ) / 10))]

lemma cosh_b33095_ub : cosh ((6619 : ℝ) / 2000) ≤ (1371103810 : ℝ) / 100000000 := by
  have exp_frac_b33095 : exp ((619 : ℝ) / 2000) ≤ (136274401 : ℝ) / 100000000 := by
    have ht : ((619 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((619 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((619 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (136274401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6619 : ℝ) / 2000) = exp 3 * exp ((619 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (619 : ℝ) / 2000 = (6619 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6619 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6619 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b33095 (exp_pos ((619 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6619 : ℝ) / 2000), exp_pos (-((6619 : ℝ) / 2000))]

lemma cosh_b33185_ub : cosh ((6637 : ℝ) / 2000) ≤ (1383476786 : ℝ) / 100000000 := by
  have exp_frac_b33185 : exp ((637 : ℝ) / 2000) ≤ (137506401 : ℝ) / 100000000 := by
    have ht : ((637 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((637 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((637 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (137506401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6637 : ℝ) / 2000) = exp 3 * exp ((637 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (637 : ℝ) / 2000 = (6637 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6637 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6637 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b33185 (exp_pos ((637 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6637 : ℝ) / 2000), exp_pos (-((6637 : ℝ) / 2000))]

lemma cosh_b33275_ub : cosh ((1331 : ℝ) / 400) ≤ (1395962243 : ℝ) / 100000000 := by
  have exp_frac_b33275 : exp ((131 : ℝ) / 400) ≤ (138749601 : ℝ) / 100000000 := by
    have ht : ((131 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((131 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((131 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (138749601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1331 : ℝ) / 400) = exp 3 * exp ((131 : ℝ) / 400) := by
    rw [← exp_add, show (3 : ℝ) + (131 : ℝ) / 400 = (1331 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1331 : ℝ) / 400)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1331 : ℝ) / 400) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b33275 (exp_pos ((131 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1331 : ℝ) / 400), exp_pos (-((1331 : ℝ) / 400))]

lemma cosh_b33365_ub : cosh ((6673 : ℝ) / 2000) ≤ (1408559178 : ℝ) / 100000000 := by
  have exp_frac_b33365 : exp ((673 : ℝ) / 2000) ≤ (140003901 : ℝ) / 100000000 := by
    have ht : ((673 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((673 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((673 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (140003901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6673 : ℝ) / 2000) = exp 3 * exp ((673 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (673 : ℝ) / 2000 = (6673 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6673 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6673 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b33365 (exp_pos ((673 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6673 : ℝ) / 2000), exp_pos (-((6673 : ℝ) / 2000))]

lemma cosh_b33455_ub : cosh ((6691 : ℝ) / 2000) ≤ (1421271608 : ℝ) / 100000000 := by
  have exp_frac_b33455 : exp ((691 : ℝ) / 2000) ≤ (141269701 : ℝ) / 100000000 := by
    have ht : ((691 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((691 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((691 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (141269701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6691 : ℝ) / 2000) = exp 3 * exp ((691 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (691 : ℝ) / 2000 = (6691 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6691 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6691 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b33455 (exp_pos ((691 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6691 : ℝ) / 2000), exp_pos (-((6691 : ℝ) / 2000))]

lemma cosh_b33550_ub : cosh ((671 : ℝ) / 200) ≤ (1434813589 : ℝ) / 100000000 := by
  have exp_frac_b33550 : exp ((71 : ℝ) / 200) ≤ (142618101 : ℝ) / 100000000 := by
    have ht : ((71 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((71 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((71 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (142618101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((671 : ℝ) / 200) = exp 3 * exp ((71 : ℝ) / 200) := by
    rw [← exp_add, show (3 : ℝ) + (71 : ℝ) / 200 = (671 : ℝ) / 200 by norm_num]
  have hneg : exp (-((671 : ℝ) / 200)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((671 : ℝ) / 200) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b33550 (exp_pos ((71 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((671 : ℝ) / 200), exp_pos (-((671 : ℝ) / 200))]

lemma cosh_b33640_ub : cosh ((841 : ℝ) / 250) ≤ (1447763033 : ℝ) / 100000000 := by
  have exp_frac_b33640 : exp ((91 : ℝ) / 250) ≤ (143907501 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (143907501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((841 : ℝ) / 250) = exp 3 * exp ((91 : ℝ) / 250) := by
    rw [← exp_add, show (3 : ℝ) + (91 : ℝ) / 250 = (841 : ℝ) / 250 by norm_num]
  have hneg : exp (-((841 : ℝ) / 250)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((841 : ℝ) / 250) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b33640 (exp_pos ((91 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((841 : ℝ) / 250), exp_pos (-((841 : ℝ) / 250))]

lemma cosh_b33730_ub : cosh ((3373 : ℝ) / 1000) ≤ (1460828976 : ℝ) / 100000000 := by
  have exp_frac_b33730 : exp ((373 : ℝ) / 1000) ≤ (145208501 : ℝ) / 100000000 := by
    have ht : ((373 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((373 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((373 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (145208501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3373 : ℝ) / 1000) = exp 3 * exp ((373 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (373 : ℝ) / 1000 = (3373 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3373 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3373 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b33730 (exp_pos ((373 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3373 : ℝ) / 1000), exp_pos (-((3373 : ℝ) / 1000))]

lemma cosh_b33820_ub : cosh ((1691 : ℝ) / 500) ≤ (1474013426 : ℝ) / 100000000 := by
  have exp_frac_b33820 : exp ((191 : ℝ) / 500) ≤ (146521301 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (146521301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1691 : ℝ) / 500) = exp 3 * exp ((191 : ℝ) / 500) := by
    rw [← exp_add, show (3 : ℝ) + (191 : ℝ) / 500 = (1691 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1691 : ℝ) / 500)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1691 : ℝ) / 500) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b33820 (exp_pos ((191 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1691 : ℝ) / 500), exp_pos (-((1691 : ℝ) / 500))]

lemma cosh_b33910_ub : cosh ((3391 : ℝ) / 1000) ≤ (1487316384 : ℝ) / 100000000 := by
  have exp_frac_b33910 : exp ((391 : ℝ) / 1000) ≤ (147845901 : ℝ) / 100000000 := by
    have ht : ((391 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((391 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((391 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (147845901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3391 : ℝ) / 1000) = exp 3 * exp ((391 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (391 : ℝ) / 1000 = (3391 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3391 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3391 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b33910 (exp_pos ((391 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3391 : ℝ) / 1000), exp_pos (-((3391 : ℝ) / 1000))]

lemma cosh_b34000_ub : cosh ((17 : ℝ) / 5) ≤ (1500739858 : ℝ) / 100000000 := by
  have exp_frac_b34000 : exp ((2 : ℝ) / 5) ≤ (149182501 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((2 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((2 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (149182501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((17 : ℝ) / 5) = exp 3 * exp ((2 : ℝ) / 5) := by
    rw [← exp_add, show (3 : ℝ) + (2 : ℝ) / 5 = (17 : ℝ) / 5 by norm_num]
  have hneg : exp (-((17 : ℝ) / 5)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((17 : ℝ) / 5) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b34000 (exp_pos ((2 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((17 : ℝ) / 5), exp_pos (-((17 : ℝ) / 5))]

lemma cosh_b34095_ub : cosh ((6819 : ℝ) / 2000) ≤ (1515041090 : ℝ) / 100000000 := by
  have exp_frac_b34095 : exp ((819 : ℝ) / 2000) ≤ (150606501 : ℝ) / 100000000 := by
    have ht : ((819 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((819 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((819 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (150606501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6819 : ℝ) / 2000) = exp 3 * exp ((819 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (819 : ℝ) / 2000 = (6819 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6819 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6819 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b34095 (exp_pos ((819 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6819 : ℝ) / 2000), exp_pos (-((6819 : ℝ) / 2000))]

lemma cosh_b34185_ub : cosh ((6837 : ℝ) / 2000) ≤ (1528715639 : ℝ) / 100000000 := by
  have exp_frac_b34185 : exp ((837 : ℝ) / 2000) ≤ (151968101 : ℝ) / 100000000 := by
    have ht : ((837 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((837 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((837 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (151968101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6837 : ℝ) / 2000) = exp 3 * exp ((837 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (837 : ℝ) / 2000 = (6837 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6837 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6837 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b34185 (exp_pos ((837 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6837 : ℝ) / 2000), exp_pos (-((6837 : ℝ) / 2000))]

lemma cosh_b34275_ub : cosh ((1371 : ℝ) / 400) ≤ (1542513717 : ℝ) / 100000000 := by
  have exp_frac_b34275 : exp ((171 : ℝ) / 400) ≤ (153342001 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((171 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((171 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (153342001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1371 : ℝ) / 400) = exp 3 * exp ((171 : ℝ) / 400) := by
    rw [← exp_add, show (3 : ℝ) + (171 : ℝ) / 400 = (1371 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1371 : ℝ) / 400)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1371 : ℝ) / 400) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b34275 (exp_pos ((171 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1371 : ℝ) / 400), exp_pos (-((1371 : ℝ) / 400))]

lemma cosh_b34365_ub : cosh ((6873 : ℝ) / 2000) ≤ (1556436327 : ℝ) / 100000000 := by
  have exp_frac_b34365 : exp ((873 : ℝ) / 2000) ≤ (154728301 : ℝ) / 100000000 := by
    have ht : ((873 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((873 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((873 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (154728301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6873 : ℝ) / 2000) = exp 3 * exp ((873 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (873 : ℝ) / 2000 = (6873 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6873 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6873 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b34365 (exp_pos ((873 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6873 : ℝ) / 2000), exp_pos (-((6873 : ℝ) / 2000))]

lemma cosh_b34455_ub : cosh ((6891 : ℝ) / 2000) ≤ (1570484476 : ℝ) / 100000000 := by
  have exp_frac_b34455 : exp ((891 : ℝ) / 2000) ≤ (156127101 : ℝ) / 100000000 := by
    have ht : ((891 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((891 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((891 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (156127101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((6891 : ℝ) / 2000) = exp 3 * exp ((891 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (891 : ℝ) / 2000 = (6891 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((6891 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((6891 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b34455 (exp_pos ((891 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((6891 : ℝ) / 2000), exp_pos (-((6891 : ℝ) / 2000))]

lemma cosh_b34550_ub : cosh ((691 : ℝ) / 200) ≤ (1585451559 : ℝ) / 100000000 := by
  have exp_frac_b34550 : exp ((91 : ℝ) / 200) ≤ (157617401 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (157617401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((691 : ℝ) / 200) = exp 3 * exp ((91 : ℝ) / 200) := by
    rw [← exp_add, show (3 : ℝ) + (91 : ℝ) / 200 = (691 : ℝ) / 200 by norm_num]
  have hneg : exp (-((691 : ℝ) / 200)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((691 : ℝ) / 200) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b34550 (exp_pos ((91 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((691 : ℝ) / 200), exp_pos (-((691 : ℝ) / 200))]

lemma cosh_b34640_ub : cosh ((433 : ℝ) / 125) ≤ (1599761829 : ℝ) / 100000000 := by
  have exp_frac_b34640 : exp ((58 : ℝ) / 125) ≤ (159042301 : ℝ) / 100000000 := by
    have ht : ((58 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((58 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((58 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (159042301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((433 : ℝ) / 125) = exp 3 * exp ((58 : ℝ) / 125) := by
    rw [← exp_add, show (3 : ℝ) + (58 : ℝ) / 125 = (433 : ℝ) / 125 by norm_num]
  have hneg : exp (-((433 : ℝ) / 125)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((433 : ℝ) / 125) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b34640 (exp_pos ((58 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((433 : ℝ) / 125), exp_pos (-((433 : ℝ) / 125))]

lemma cosh_b34730_ub : cosh ((3473 : ℝ) / 1000) ≤ (1614202659 : ℝ) / 100000000 := by
  have exp_frac_b34730 : exp ((473 : ℝ) / 1000) ≤ (160480201 : ℝ) / 100000000 := by
    have ht : ((473 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((473 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((473 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (160480201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3473 : ℝ) / 1000) = exp 3 * exp ((473 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (473 : ℝ) / 1000 = (3473 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3473 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3473 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b34730 (exp_pos ((473 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3473 : ℝ) / 1000), exp_pos (-((3473 : ℝ) / 1000))]

lemma cosh_b34820_ub : cosh ((1741 : ℝ) / 500) ≤ (1628773044 : ℝ) / 100000000 := by
  have exp_frac_b34820 : exp ((241 : ℝ) / 500) ≤ (161931001 : ℝ) / 100000000 := by
    have ht : ((241 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((241 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((241 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (161931001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1741 : ℝ) / 500) = exp 3 * exp ((241 : ℝ) / 500) := by
    rw [← exp_add, show (3 : ℝ) + (241 : ℝ) / 500 = (1741 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1741 : ℝ) / 500)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1741 : ℝ) / 500) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b34820 (exp_pos ((241 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1741 : ℝ) / 500), exp_pos (-((1741 : ℝ) / 500))]

lemma cosh_b34910_ub : cosh ((3491 : ℝ) / 1000) ≤ (1643475996 : ℝ) / 100000000 := by
  have exp_frac_b34910 : exp ((491 : ℝ) / 1000) ≤ (163395001 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((491 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((491 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (163395001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3491 : ℝ) / 1000) = exp 3 * exp ((491 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (491 : ℝ) / 1000 = (3491 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3491 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3491 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b34910 (exp_pos ((491 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3491 : ℝ) / 1000), exp_pos (-((3491 : ℝ) / 1000))]

lemma cosh_b35000_ub : cosh ((7 : ℝ) / 2) ≤ (1658311515 : ℝ) / 100000000 := by
  have exp_frac_b35000 : exp ((1 : ℝ) / 2) ≤ (164872201 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 2) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1 : ℝ) / 2) ^ m / (Nat.factorial m)) +
          ((1 : ℝ) / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (164872201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7 : ℝ) / 2) = exp 3 * exp ((1 : ℝ) / 2) := by
    rw [← exp_add, show (3 : ℝ) + (1 : ℝ) / 2 = (7 : ℝ) / 2 by norm_num]
  have hneg : exp (-((7 : ℝ) / 2)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7 : ℝ) / 2) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b35000 (exp_pos ((1 : ℝ) / 2)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7 : ℝ) / 2), exp_pos (-((7 : ℝ) / 2))]

lemma cosh_b35095_ub : cosh ((7019 : ℝ) / 2000) ≤ (1674116184 : ℝ) / 100000000 := by
  have exp_frac_b35095 : exp ((1019 : ℝ) / 2000) ≤ (166445901 : ℝ) / 100000000 := by
    have ht : ((1019 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1019 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1019 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (166445901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7019 : ℝ) / 2000) = exp 3 * exp ((1019 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1019 : ℝ) / 2000 = (7019 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7019 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7019 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b35095 (exp_pos ((1019 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7019 : ℝ) / 2000), exp_pos (-((7019 : ℝ) / 2000))]

lemma cosh_b35185_ub : cosh ((7037 : ℝ) / 2000) ≤ (1689228891 : ℝ) / 100000000 := by
  have exp_frac_b35185 : exp ((1037 : ℝ) / 2000) ≤ (167950701 : ℝ) / 100000000 := by
    have ht : ((1037 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1037 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1037 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (167950701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7037 : ℝ) / 2000) = exp 3 * exp ((1037 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1037 : ℝ) / 2000 = (7037 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7037 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7037 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b35185 (exp_pos ((1037 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7037 : ℝ) / 2000), exp_pos (-((7037 : ℝ) / 2000))]

lemma cosh_b35275_ub : cosh ((1411 : ℝ) / 400) ≤ (1704478182 : ℝ) / 100000000 := by
  have exp_frac_b35275 : exp ((211 : ℝ) / 400) ≤ (169469101 : ℝ) / 100000000 := by
    have ht : ((211 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((211 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((211 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (169469101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1411 : ℝ) / 400) = exp 3 * exp ((211 : ℝ) / 400) := by
    rw [← exp_add, show (3 : ℝ) + (211 : ℝ) / 400 = (1411 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1411 : ℝ) / 400)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1411 : ℝ) / 400) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b35275 (exp_pos ((211 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1411 : ℝ) / 400), exp_pos (-((1411 : ℝ) / 400))]

lemma cosh_b35365_ub : cosh ((7073 : ℝ) / 2000) ≤ (1719865062 : ℝ) / 100000000 := by
  have exp_frac_b35365 : exp ((1073 : ℝ) / 2000) ≤ (171001201 : ℝ) / 100000000 := by
    have ht : ((1073 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1073 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1073 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (171001201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7073 : ℝ) / 2000) = exp 3 * exp ((1073 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1073 : ℝ) / 2000 = (7073 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7073 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7073 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b35365 (exp_pos ((1073 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7073 : ℝ) / 2000), exp_pos (-((7073 : ℝ) / 2000))]

lemma cosh_b35455_ub : cosh ((7091 : ℝ) / 2000) ≤ (1735390536 : ℝ) / 100000000 := by
  have exp_frac_b35455 : exp ((1091 : ℝ) / 2000) ≤ (172547101 : ℝ) / 100000000 := by
    have ht : ((1091 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1091 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1091 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (172547101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7091 : ℝ) / 2000) = exp 3 * exp ((1091 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1091 : ℝ) / 2000 = (7091 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7091 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7091 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b35455 (exp_pos ((1091 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7091 : ℝ) / 2000), exp_pos (-((7091 : ℝ) / 2000))]

lemma cosh_b35550_ub : cosh ((711 : ℝ) / 200) ≤ (1751931357 : ℝ) / 100000000 := by
  have exp_frac_b35550 : exp ((111 : ℝ) / 200) ≤ (174194101 : ℝ) / 100000000 := by
    have ht : ((111 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((111 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((111 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (174194101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((711 : ℝ) / 200) = exp 3 * exp ((111 : ℝ) / 200) := by
    rw [← exp_add, show (3 : ℝ) + (111 : ℝ) / 200 = (711 : ℝ) / 200 by norm_num]
  have hneg : exp (-((711 : ℝ) / 200)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((711 : ℝ) / 200) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b35550 (exp_pos ((111 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((711 : ℝ) / 200), exp_pos (-((711 : ℝ) / 200))]

lemma cosh_b35640_ub : cosh ((891 : ℝ) / 250) ≤ (1767748078 : ℝ) / 100000000 := by
  have exp_frac_b35640 : exp ((141 : ℝ) / 250) ≤ (175769001 : ℝ) / 100000000 := by
    have ht : ((141 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((141 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((141 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (175769001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((891 : ℝ) / 250) = exp 3 * exp ((141 : ℝ) / 250) := by
    rw [← exp_add, show (3 : ℝ) + (141 : ℝ) / 250 = (891 : ℝ) / 250 by norm_num]
  have hneg : exp (-((891 : ℝ) / 250)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((891 : ℝ) / 250) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b35640 (exp_pos ((141 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((891 : ℝ) / 250), exp_pos (-((891 : ℝ) / 250))]

lemma cosh_b35730_ub : cosh ((3573 : ℝ) / 1000) ≤ (1783706405 : ℝ) / 100000000 := by
  have exp_frac_b35730 : exp ((573 : ℝ) / 1000) ≤ (177358001 : ℝ) / 100000000 := by
    have ht : ((573 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((573 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((573 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (177358001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3573 : ℝ) / 1000) = exp 3 * exp ((573 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (573 : ℝ) / 1000 = (3573 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3573 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3573 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b35730 (exp_pos ((573 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3573 : ℝ) / 1000), exp_pos (-((3573 : ℝ) / 1000))]

lemma cosh_b35820_ub : cosh ((1791 : ℝ) / 500) ≤ (1799810355 : ℝ) / 100000000 := by
  have exp_frac_b35820 : exp ((291 : ℝ) / 500) ≤ (178961501 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (178961501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1791 : ℝ) / 500) = exp 3 * exp ((291 : ℝ) / 500) := by
    rw [← exp_add, show (3 : ℝ) + (291 : ℝ) / 500 = (1791 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1791 : ℝ) / 500)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1791 : ℝ) / 500) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b35820 (exp_pos ((291 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1791 : ℝ) / 500), exp_pos (-((1791 : ℝ) / 500))]

lemma cosh_b35910_ub : cosh ((3591 : ℝ) / 1000) ≤ (1816058925 : ℝ) / 100000000 := by
  have exp_frac_b35910 : exp ((591 : ℝ) / 1000) ≤ (180579401 : ℝ) / 100000000 := by
    have ht : ((591 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((591 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((591 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (180579401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3591 : ℝ) / 1000) = exp 3 * exp ((591 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (591 : ℝ) / 1000 = (3591 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3591 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3591 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b35910 (exp_pos ((591 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3591 : ℝ) / 1000), exp_pos (-((3591 : ℝ) / 1000))]

lemma cosh_b36000_ub : cosh ((18 : ℝ) / 5) ≤ (1832454122 : ℝ) / 100000000 := by
  have exp_frac_b36000 : exp ((3 : ℝ) / 5) ≤ (182211901 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((3 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((3 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (182211901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((18 : ℝ) / 5) = exp 3 * exp ((3 : ℝ) / 5) := by
    rw [← exp_add, show (3 : ℝ) + (3 : ℝ) / 5 = (18 : ℝ) / 5 by norm_num]
  have hneg : exp (-((18 : ℝ) / 5)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((18 : ℝ) / 5) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b36000 (exp_pos ((3 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((18 : ℝ) / 5), exp_pos (-((18 : ℝ) / 5))]

lemma cosh_b36095_ub : cosh ((7219 : ℝ) / 2000) ≤ (1849921912 : ℝ) / 100000000 := by
  have exp_frac_b36095 : exp ((1219 : ℝ) / 2000) ≤ (183951201 : ℝ) / 100000000 := by
    have ht : ((1219 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1219 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1219 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (183951201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7219 : ℝ) / 2000) = exp 3 * exp ((1219 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1219 : ℝ) / 2000 = (7219 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7219 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7219 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b36095 (exp_pos ((1219 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7219 : ℝ) / 2000), exp_pos (-((7219 : ℝ) / 2000))]

lemma cosh_b36185_ub : cosh ((7237 : ℝ) / 2000) ≤ (1866623421 : ℝ) / 100000000 := by
  have exp_frac_b36185 : exp ((1237 : ℝ) / 2000) ≤ (185614201 : ℝ) / 100000000 := by
    have ht : ((1237 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1237 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1237 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (185614201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7237 : ℝ) / 2000) = exp 3 * exp ((1237 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1237 : ℝ) / 2000 = (7237 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7237 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7237 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b36185 (exp_pos ((1237 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7237 : ℝ) / 2000), exp_pos (-((7237 : ℝ) / 2000))]

lemma cosh_b36275_ub : cosh ((1451 : ℝ) / 400) ≤ (1883476579 : ℝ) / 100000000 := by
  have exp_frac_b36275 : exp ((251 : ℝ) / 400) ≤ (187292301 : ℝ) / 100000000 := by
    have ht : ((251 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((251 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((251 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (187292301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1451 : ℝ) / 400) = exp 3 * exp ((251 : ℝ) / 400) := by
    rw [← exp_add, show (3 : ℝ) + (251 : ℝ) / 400 = (1451 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1451 : ℝ) / 400)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1451 : ℝ) / 400) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b36275 (exp_pos ((251 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1451 : ℝ) / 400), exp_pos (-((1451 : ℝ) / 400))]

lemma cosh_b36365_ub : cosh ((7273 : ℝ) / 2000) ≤ (1900481387 : ℝ) / 100000000 := by
  have exp_frac_b36365 : exp ((1273 : ℝ) / 2000) ≤ (188985501 : ℝ) / 100000000 := by
    have ht : ((1273 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1273 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1273 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (188985501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7273 : ℝ) / 2000) = exp 3 * exp ((1273 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1273 : ℝ) / 2000 = (7273 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7273 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7273 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b36365 (exp_pos ((1273 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7273 : ℝ) / 2000), exp_pos (-((7273 : ℝ) / 2000))]

lemma cosh_b36455_ub : cosh ((7291 : ℝ) / 2000) ≤ (1917640857 : ℝ) / 100000000 := by
  have exp_frac_b36455 : exp ((1291 : ℝ) / 2000) ≤ (190694101 : ℝ) / 100000000 := by
    have ht : ((1291 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1291 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1291 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (190694101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7291 : ℝ) / 2000) = exp 3 * exp ((1291 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1291 : ℝ) / 2000 = (7291 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7291 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7291 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b36455 (exp_pos ((1291 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7291 : ℝ) / 2000), exp_pos (-((7291 : ℝ) / 2000))]

lemma cosh_b36550_ub : cosh ((731 : ℝ) / 200) ≤ (1935921125 : ℝ) / 100000000 := by
  have exp_frac_b36550 : exp ((131 : ℝ) / 200) ≤ (192514301 : ℝ) / 100000000 := by
    have ht : ((131 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((131 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((131 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (192514301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((731 : ℝ) / 200) = exp 3 * exp ((131 : ℝ) / 200) := by
    rw [← exp_add, show (3 : ℝ) + (131 : ℝ) / 200 = (731 : ℝ) / 200 by norm_num]
  have hneg : exp (-((731 : ℝ) / 200)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((731 : ℝ) / 200) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b36550 (exp_pos ((131 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((731 : ℝ) / 200), exp_pos (-((731 : ℝ) / 200))]

lemma cosh_b36640_ub : cosh ((458 : ℝ) / 125) ≤ (1953400967 : ℝ) / 100000000 := by
  have exp_frac_b36640 : exp ((83 : ℝ) / 125) ≤ (194254801 : ℝ) / 100000000 := by
    have ht : ((83 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((83 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((83 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (194254801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((458 : ℝ) / 125) = exp 3 * exp ((83 : ℝ) / 125) := by
    rw [← exp_add, show (3 : ℝ) + (83 : ℝ) / 125 = (458 : ℝ) / 125 by norm_num]
  have hneg : exp (-((458 : ℝ) / 125)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((458 : ℝ) / 125) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b36640 (exp_pos ((83 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((458 : ℝ) / 125), exp_pos (-((458 : ℝ) / 125))]

lemma cosh_b36730_ub : cosh ((3673 : ℝ) / 1000) ≤ (1971037479 : ℝ) / 100000000 := by
  have exp_frac_b36730 : exp ((673 : ℝ) / 1000) ≤ (196010901 : ℝ) / 100000000 := by
    have ht : ((673 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((673 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((673 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (196010901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3673 : ℝ) / 1000) = exp 3 * exp ((673 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (673 : ℝ) / 1000 = (3673 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3673 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3673 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b36730 (exp_pos ((673 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3673 : ℝ) / 1000), exp_pos (-((3673 : ℝ) / 1000))]

lemma cosh_b36820_ub : cosh ((1841 : ℝ) / 500) ≤ (1988834680 : ℝ) / 100000000 := by
  have exp_frac_b36820 : exp ((341 : ℝ) / 500) ≤ (197783001 : ℝ) / 100000000 := by
    have ht : ((341 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((341 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((341 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (197783001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1841 : ℝ) / 500) = exp 3 * exp ((341 : ℝ) / 500) := by
    rw [← exp_add, show (3 : ℝ) + (341 : ℝ) / 500 = (1841 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1841 : ℝ) / 500)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1841 : ℝ) / 500) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b36820 (exp_pos ((341 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1841 : ℝ) / 500), exp_pos (-((1841 : ℝ) / 500))]

lemma cosh_b36910_ub : cosh ((3691 : ℝ) / 1000) ≤ (2006792568 : ℝ) / 100000000 := by
  have exp_frac_b36910 : exp ((691 : ℝ) / 1000) ≤ (199571101 : ℝ) / 100000000 := by
    have ht : ((691 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((691 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((691 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (199571101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3691 : ℝ) / 1000) = exp 3 * exp ((691 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (691 : ℝ) / 1000 = (3691 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3691 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3691 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b36910 (exp_pos ((691 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3691 : ℝ) / 1000), exp_pos (-((3691 : ℝ) / 1000))]

lemma cosh_b37000_ub : cosh ((37 : ℝ) / 10) ≤ (2024912148 : ℝ) / 100000000 := by
  have exp_frac_b37000 : exp ((7 : ℝ) / 10) ≤ (201375301 : ℝ) / 100000000 := by
    have ht : ((7 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((7 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((7 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (201375301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((37 : ℝ) / 10) = exp 3 * exp ((7 : ℝ) / 10) := by
    rw [← exp_add, show (3 : ℝ) + (7 : ℝ) / 10 = (37 : ℝ) / 10 by norm_num]
  have hneg : exp (-((37 : ℝ) / 10)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((37 : ℝ) / 10) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b37000 (exp_pos ((7 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((37 : ℝ) / 10), exp_pos (-((37 : ℝ) / 10))]

lemma cosh_b37095_ub : cosh ((7419 : ℝ) / 2000) ≤ (2044216803 : ℝ) / 100000000 := by
  have exp_frac_b37095 : exp ((1419 : ℝ) / 2000) ≤ (203297501 : ℝ) / 100000000 := by
    have ht : ((1419 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1419 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1419 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (203297501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7419 : ℝ) / 2000) = exp 3 * exp ((1419 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1419 : ℝ) / 2000 = (7419 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7419 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7419 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b37095 (exp_pos ((1419 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7419 : ℝ) / 2000), exp_pos (-((7419 : ℝ) / 2000))]

lemma cosh_b37185_ub : cosh ((7437 : ℝ) / 2000) ≤ (2062674833 : ℝ) / 100000000 := by
  have exp_frac_b37185 : exp ((1437 : ℝ) / 2000) ≤ (205135401 : ℝ) / 100000000 := by
    have ht : ((1437 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1437 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1437 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (205135401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7437 : ℝ) / 2000) = exp 3 * exp ((1437 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1437 : ℝ) / 2000 = (7437 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7437 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7437 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b37185 (exp_pos ((1437 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7437 : ℝ) / 2000), exp_pos (-((7437 : ℝ) / 2000))]

lemma cosh_b37275_ub : cosh ((1491 : ℝ) / 400) ≤ (2081300581 : ℝ) / 100000000 := by
  have exp_frac_b37275 : exp ((291 : ℝ) / 400) ≤ (206990001 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (206990001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1491 : ℝ) / 400) = exp 3 * exp ((291 : ℝ) / 400) := by
    rw [← exp_add, show (3 : ℝ) + (291 : ℝ) / 400 = (1491 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1491 : ℝ) / 400)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1491 : ℝ) / 400) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b37275 (exp_pos ((291 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1491 : ℝ) / 400), exp_pos (-((1491 : ℝ) / 400))]

lemma cosh_b37365_ub : cosh ((7473 : ℝ) / 2000) ≤ (2100094046 : ℝ) / 100000000 := by
  have exp_frac_b37365 : exp ((1473 : ℝ) / 2000) ≤ (208861301 : ℝ) / 100000000 := by
    have ht : ((1473 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1473 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1473 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (208861301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7473 : ℝ) / 2000) = exp 3 * exp ((1473 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1473 : ℝ) / 2000 = (7473 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7473 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7473 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b37365 (exp_pos ((1473 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7473 : ℝ) / 2000), exp_pos (-((7473 : ℝ) / 2000))]

lemma cosh_b37455_ub : cosh ((7491 : ℝ) / 2000) ≤ (2119058243 : ℝ) / 100000000 := by
  have exp_frac_b37455 : exp ((1491 : ℝ) / 2000) ≤ (210749601 : ℝ) / 100000000 := by
    have ht : ((1491 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1491 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1491 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (210749601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7491 : ℝ) / 2000) = exp 3 * exp ((1491 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1491 : ℝ) / 2000 = (7491 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7491 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7491 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b37455 (exp_pos ((1491 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7491 : ℝ) / 2000), exp_pos (-((7491 : ℝ) / 2000))]

lemma cosh_b37550_ub : cosh ((751 : ℝ) / 200) ≤ (2139260742 : ℝ) / 100000000 := by
  have exp_frac_b37550 : exp ((151 : ℝ) / 200) ≤ (212761201 : ℝ) / 100000000 := by
    have ht : ((151 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((151 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((151 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (212761201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((751 : ℝ) / 200) = exp 3 * exp ((151 : ℝ) / 200) := by
    rw [← exp_add, show (3 : ℝ) + (151 : ℝ) / 200 = (751 : ℝ) / 200 by norm_num]
  have hneg : exp (-((751 : ℝ) / 200)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((751 : ℝ) / 200) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b37550 (exp_pos ((151 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((751 : ℝ) / 200), exp_pos (-((751 : ℝ) / 200))]

lemma cosh_b37640_ub : cosh ((941 : ℝ) / 250) ≤ (2158578453 : ℝ) / 100000000 := by
  have exp_frac_b37640 : exp ((191 : ℝ) / 250) ≤ (214684701 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (214684701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((941 : ℝ) / 250) = exp 3 * exp ((191 : ℝ) / 250) := by
    rw [← exp_add, show (3 : ℝ) + (191 : ℝ) / 250 = (941 : ℝ) / 250 by norm_num]
  have hneg : exp (-((941 : ℝ) / 250)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((941 : ℝ) / 250) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b37640 (exp_pos ((191 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((941 : ℝ) / 250), exp_pos (-((941 : ℝ) / 250))]

lemma cosh_b37730_ub : cosh ((3773 : ℝ) / 1000) ≤ (2178070911 : ℝ) / 100000000 := by
  have exp_frac_b37730 : exp ((773 : ℝ) / 1000) ≤ (216625601 : ℝ) / 100000000 := by
    have ht : ((773 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((773 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((773 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (216625601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3773 : ℝ) / 1000) = exp 3 * exp ((773 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (773 : ℝ) / 1000 = (3773 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3773 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3773 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b37730 (exp_pos ((773 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3773 : ℝ) / 1000), exp_pos (-((3773 : ℝ) / 1000))]

lemma cosh_b37820_ub : cosh ((1891 : ℝ) / 500) ≤ (2197739123 : ℝ) / 100000000 := by
  have exp_frac_b37820 : exp ((391 : ℝ) / 500) ≤ (218584001 : ℝ) / 100000000 := by
    have ht : ((391 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((391 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((391 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (218584001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1891 : ℝ) / 500) = exp 3 * exp ((391 : ℝ) / 500) := by
    rw [← exp_add, show (3 : ℝ) + (391 : ℝ) / 500 = (1891 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1891 : ℝ) / 500)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1891 : ℝ) / 500) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b37820 (exp_pos ((391 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1891 : ℝ) / 500), exp_pos (-((1891 : ℝ) / 500))]

lemma cosh_b37910_ub : cosh ((3791 : ℝ) / 1000) ≤ (2217586099 : ℝ) / 100000000 := by
  have exp_frac_b37910 : exp ((791 : ℝ) / 1000) ≤ (220560201 : ℝ) / 100000000 := by
    have ht : ((791 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((791 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((791 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (220560201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3791 : ℝ) / 1000) = exp 3 * exp ((791 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (791 : ℝ) / 1000 = (3791 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3791 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3791 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b37910 (exp_pos ((791 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3791 : ℝ) / 1000), exp_pos (-((3791 : ℝ) / 1000))]

lemma cosh_b38000_ub : cosh ((19 : ℝ) / 5) ≤ (2237611841 : ℝ) / 100000000 := by
  have exp_frac_b38000 : exp ((4 : ℝ) / 5) ≤ (222554201 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((4 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((4 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (222554201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((19 : ℝ) / 5) = exp 3 * exp ((4 : ℝ) / 5) := by
    rw [← exp_add, show (3 : ℝ) + (4 : ℝ) / 5 = (19 : ℝ) / 5 by norm_num]
  have hneg : exp (-((19 : ℝ) / 5)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((19 : ℝ) / 5) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b38000 (exp_pos ((4 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((19 : ℝ) / 5), exp_pos (-((19 : ℝ) / 5))]

lemma cosh_b38095_ub : cosh ((7619 : ℝ) / 2000) ≤ (2258946186 : ℝ) / 100000000 := by
  have exp_frac_b38095 : exp ((1619 : ℝ) / 2000) ≤ (224678501 : ℝ) / 100000000 := by
    have ht : ((1619 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1619 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1619 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (224678501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7619 : ℝ) / 2000) = exp 3 * exp ((1619 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1619 : ℝ) / 2000 = (7619 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7619 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7619 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b38095 (exp_pos ((1619 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7619 : ℝ) / 2000), exp_pos (-((7619 : ℝ) / 2000))]

lemma cosh_b38185_ub : cosh ((7637 : ℝ) / 2000) ≤ (2279345528 : ℝ) / 100000000 := by
  have exp_frac_b38185 : exp ((1637 : ℝ) / 2000) ≤ (226709701 : ℝ) / 100000000 := by
    have ht : ((1637 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1637 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1637 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (226709701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7637 : ℝ) / 2000) = exp 3 * exp ((1637 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1637 : ℝ) / 2000 = (7637 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7637 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7637 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b38185 (exp_pos ((1637 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7637 : ℝ) / 2000), exp_pos (-((7637 : ℝ) / 2000))]

lemma cosh_b38275_ub : cosh ((1531 : ℝ) / 400) ≤ (2299929660 : ℝ) / 100000000 := by
  have exp_frac_b38275 : exp ((331 : ℝ) / 400) ≤ (228759301 : ℝ) / 100000000 := by
    have ht : ((331 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((331 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((331 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (228759301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1531 : ℝ) / 400) = exp 3 * exp ((331 : ℝ) / 400) := by
    rw [← exp_add, show (3 : ℝ) + (331 : ℝ) / 400 = (1531 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1531 : ℝ) / 400)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1531 : ℝ) / 400) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b38275 (exp_pos ((331 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1531 : ℝ) / 400), exp_pos (-((1531 : ℝ) / 400))]

lemma cosh_b38365_ub : cosh ((7673 : ℝ) / 2000) ≤ (2320700593 : ℝ) / 100000000 := by
  have exp_frac_b38365 : exp ((1673 : ℝ) / 2000) ≤ (230827501 : ℝ) / 100000000 := by
    have ht : ((1673 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1673 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1673 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (230827501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7673 : ℝ) / 2000) = exp 3 * exp ((1673 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1673 : ℝ) / 2000 = (7673 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7673 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7673 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b38365 (exp_pos ((1673 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7673 : ℝ) / 2000), exp_pos (-((7673 : ℝ) / 2000))]

lemma cosh_b38455_ub : cosh ((7691 : ℝ) / 2000) ≤ (2341658325 : ℝ) / 100000000 := by
  have exp_frac_b38455 : exp ((1691 : ℝ) / 2000) ≤ (232914301 : ℝ) / 100000000 := by
    have ht : ((1691 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1691 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1691 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (232914301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7691 : ℝ) / 2000) = exp 3 * exp ((1691 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1691 : ℝ) / 2000 = (7691 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7691 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7691 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b38455 (exp_pos ((1691 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7691 : ℝ) / 2000), exp_pos (-((7691 : ℝ) / 2000))]

lemma cosh_b38550_ub : cosh ((771 : ℝ) / 200) ≤ (2363985923 : ℝ) / 100000000 := by
  have exp_frac_b38550 : exp ((171 : ℝ) / 200) ≤ (235137501 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((171 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((171 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (235137501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((771 : ℝ) / 200) = exp 3 * exp ((171 : ℝ) / 200) := by
    rw [← exp_add, show (3 : ℝ) + (171 : ℝ) / 200 = (771 : ℝ) / 200 by norm_num]
  have hneg : exp (-((771 : ℝ) / 200)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((771 : ℝ) / 200) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b38550 (exp_pos ((171 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((771 : ℝ) / 200), exp_pos (-((771 : ℝ) / 200))]

lemma cosh_b38640_ub : cosh ((483 : ℝ) / 125) ≤ (2385335332 : ℝ) / 100000000 := by
  have exp_frac_b38640 : exp ((108 : ℝ) / 125) ≤ (237263301 : ℝ) / 100000000 := by
    have ht : ((108 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((108 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((108 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (237263301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((483 : ℝ) / 125) = exp 3 * exp ((108 : ℝ) / 125) := by
    rw [← exp_add, show (3 : ℝ) + (108 : ℝ) / 125 = (483 : ℝ) / 125 by norm_num]
  have hneg : exp (-((483 : ℝ) / 125)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((483 : ℝ) / 125) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b38640 (exp_pos ((108 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((483 : ℝ) / 125), exp_pos (-((483 : ℝ) / 125))]

lemma cosh_b38730_ub : cosh ((3873 : ℝ) / 1000) ≤ (2406877567 : ℝ) / 100000000 := by
  have exp_frac_b38730 : exp ((873 : ℝ) / 1000) ≤ (239408301 : ℝ) / 100000000 := by
    have ht : ((873 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((873 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((873 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (239408301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3873 : ℝ) / 1000) = exp 3 * exp ((873 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (873 : ℝ) / 1000 = (3873 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3873 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3873 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b38730 (exp_pos ((873 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3873 : ℝ) / 1000), exp_pos (-((3873 : ℝ) / 1000))]

lemma cosh_b38820_ub : cosh ((1941 : ℝ) / 500) ≤ (2428614637 : ℝ) / 100000000 := by
  have exp_frac_b38820 : exp ((441 : ℝ) / 500) ≤ (241572701 : ℝ) / 100000000 := by
    have ht : ((441 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((441 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((441 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (241572701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1941 : ℝ) / 500) = exp 3 * exp ((441 : ℝ) / 500) := by
    rw [← exp_add, show (3 : ℝ) + (441 : ℝ) / 500 = (1941 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1941 : ℝ) / 500)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1941 : ℝ) / 500) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b38820 (exp_pos ((441 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1941 : ℝ) / 500), exp_pos (-((1941 : ℝ) / 500))]

lemma cosh_b38910_ub : cosh ((3891 : ℝ) / 1000) ≤ (2450548549 : ℝ) / 100000000 := by
  have exp_frac_b38910 : exp ((891 : ℝ) / 1000) ≤ (243756701 : ℝ) / 100000000 := by
    have ht : ((891 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((891 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((891 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (243756701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3891 : ℝ) / 1000) = exp 3 * exp ((891 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (891 : ℝ) / 1000 = (3891 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3891 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3891 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b38910 (exp_pos ((891 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3891 : ℝ) / 1000), exp_pos (-((3891 : ℝ) / 1000))]

lemma cosh_b39000_ub : cosh ((39 : ℝ) / 10) ≤ (2472680308 : ℝ) / 100000000 := by
  have exp_frac_b39000 : exp ((9 : ℝ) / 10) ≤ (245960401 : ℝ) / 100000000 := by
    have ht : ((9 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((9 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((9 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (245960401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((39 : ℝ) / 10) = exp 3 * exp ((9 : ℝ) / 10) := by
    rw [← exp_add, show (3 : ℝ) + (9 : ℝ) / 10 = (39 : ℝ) / 10 by norm_num]
  have hneg : exp (-((39 : ℝ) / 10)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((39 : ℝ) / 10) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b39000 (exp_pos ((9 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((39 : ℝ) / 10), exp_pos (-((39 : ℝ) / 10))]

lemma cosh_b39095_ub : cosh ((7819 : ℝ) / 2000) ≤ (2496258259 : ℝ) / 100000000 := by
  have exp_frac_b39095 : exp ((1819 : ℝ) / 2000) ≤ (248308101 : ℝ) / 100000000 := by
    have ht : ((1819 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1819 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1819 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (248308101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7819 : ℝ) / 2000) = exp 3 * exp ((1819 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1819 : ℝ) / 2000 = (7819 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7819 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7819 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b39095 (exp_pos ((1819 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7819 : ℝ) / 2000), exp_pos (-((7819 : ℝ) / 2000))]

lemma cosh_b39185_ub : cosh ((7837 : ℝ) / 2000) ≤ (2518803790 : ℝ) / 100000000 := by
  have exp_frac_b39185 : exp ((1837 : ℝ) / 2000) ≤ (250553001 : ℝ) / 100000000 := by
    have ht : ((1837 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1837 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1837 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (250553001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7837 : ℝ) / 2000) = exp 3 * exp ((1837 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1837 : ℝ) / 2000 = (7837 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7837 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7837 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b39185 (exp_pos ((1837 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7837 : ℝ) / 2000), exp_pos (-((7837 : ℝ) / 2000))]

lemma cosh_b39275_ub : cosh ((1571 : ℝ) / 400) ≤ (2541552189 : ℝ) / 100000000 := by
  have exp_frac_b39275 : exp ((371 : ℝ) / 400) ≤ (252818101 : ℝ) / 100000000 := by
    have ht : ((371 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((371 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((371 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (252818101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1571 : ℝ) / 400) = exp 3 * exp ((371 : ℝ) / 400) := by
    rw [← exp_add, show (3 : ℝ) + (371 : ℝ) / 400 = (1571 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1571 : ℝ) / 400)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1571 : ℝ) / 400) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b39275 (exp_pos ((371 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1571 : ℝ) / 400), exp_pos (-((1571 : ℝ) / 400))]

lemma cosh_b39365_ub : cosh ((7873 : ℝ) / 2000) ≤ (2564507474 : ℝ) / 100000000 := by
  have exp_frac_b39365 : exp ((1873 : ℝ) / 2000) ≤ (255103801 : ℝ) / 100000000 := by
    have ht : ((1873 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1873 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1873 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (255103801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7873 : ℝ) / 2000) = exp 3 * exp ((1873 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1873 : ℝ) / 2000 = (7873 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7873 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7873 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b39365 (exp_pos ((1873 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7873 : ℝ) / 2000), exp_pos (-((7873 : ℝ) / 2000))]

lemma cosh_b39455_ub : cosh ((7891 : ℝ) / 2000) ≤ (2587669645 : ℝ) / 100000000 := by
  have exp_frac_b39455 : exp ((1891 : ℝ) / 2000) ≤ (257410101 : ℝ) / 100000000 := by
    have ht : ((1891 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1891 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1891 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (257410101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((7891 : ℝ) / 2000) = exp 3 * exp ((1891 : ℝ) / 2000) := by
    rw [← exp_add, show (3 : ℝ) + (1891 : ℝ) / 2000 = (7891 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((7891 : ℝ) / 2000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((7891 : ℝ) / 2000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b39455 (exp_pos ((1891 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((7891 : ℝ) / 2000), exp_pos (-((7891 : ℝ) / 2000))]

lemma cosh_b39550_ub : cosh ((791 : ℝ) / 200) ≤ (2612345296 : ℝ) / 100000000 := by
  have exp_frac_b39550 : exp ((191 : ℝ) / 200) ≤ (259867101 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (259867101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((791 : ℝ) / 200) = exp 3 * exp ((191 : ℝ) / 200) := by
    rw [← exp_add, show (3 : ℝ) + (191 : ℝ) / 200 = (791 : ℝ) / 200 by norm_num]
  have hneg : exp (-((791 : ℝ) / 200)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((791 : ℝ) / 200) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b39550 (exp_pos ((191 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((791 : ℝ) / 200), exp_pos (-((791 : ℝ) / 200))]

lemma cosh_b39640_ub : cosh ((991 : ℝ) / 250) ≤ (2635940320 : ℝ) / 100000000 := by
  have exp_frac_b39640 : exp ((241 : ℝ) / 250) ≤ (262216501 : ℝ) / 100000000 := by
    have ht : ((241 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((241 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((241 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (262216501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((991 : ℝ) / 250) = exp 3 * exp ((241 : ℝ) / 250) := by
    rw [← exp_add, show (3 : ℝ) + (241 : ℝ) / 250 = (991 : ℝ) / 250 by norm_num]
  have hneg : exp (-((991 : ℝ) / 250)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((991 : ℝ) / 250) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b39640 (exp_pos ((241 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((991 : ℝ) / 250), exp_pos (-((991 : ℝ) / 250))]

lemma cosh_b39730_ub : cosh ((3973 : ℝ) / 1000) ≤ (2659748256 : ℝ) / 100000000 := by
  have exp_frac_b39730 : exp ((973 : ℝ) / 1000) ≤ (264587101 : ℝ) / 100000000 := by
    have ht : ((973 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((973 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((973 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (264587101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3973 : ℝ) / 1000) = exp 3 * exp ((973 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (973 : ℝ) / 1000 = (3973 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3973 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3973 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b39730 (exp_pos ((973 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3973 : ℝ) / 1000), exp_pos (-((3973 : ℝ) / 1000))]

lemma cosh_b39820_ub : cosh ((1991 : ℝ) / 500) ≤ (2683771112 : ℝ) / 100000000 := by
  have exp_frac_b39820 : exp ((491 : ℝ) / 500) ≤ (266979101 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((491 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((491 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (266979101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1991 : ℝ) / 500) = exp 3 * exp ((491 : ℝ) / 500) := by
    rw [← exp_add, show (3 : ℝ) + (491 : ℝ) / 500 = (1991 : ℝ) / 500 by norm_num]
  have hneg : exp (-((1991 : ℝ) / 500)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1991 : ℝ) / 500) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b39820 (exp_pos ((491 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1991 : ℝ) / 500), exp_pos (-((1991 : ℝ) / 500))]

lemma cosh_b39910_ub : cosh ((3991 : ℝ) / 1000) ≤ (2708011901 : ℝ) / 100000000 := by
  have exp_frac_b39910 : exp ((991 : ℝ) / 1000) ≤ (269392801 : ℝ) / 100000000 := by
    have ht : ((991 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((991 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((991 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (269392801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((3991 : ℝ) / 1000) = exp 3 * exp ((991 : ℝ) / 1000) := by
    rw [← exp_add, show (3 : ℝ) + (991 : ℝ) / 1000 = (3991 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((3991 : ℝ) / 1000)) ≤ (50 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((3991 : ℝ) / 1000) ≤ -(3 : ℝ))).trans exp_neg_three_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_three_le exp_frac_b39910 (exp_pos ((991 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((3991 : ℝ) / 1000), exp_pos (-((3991 : ℝ) / 1000))]

lemma cosh_b40000_ub : cosh ((4 : ℝ) / 1) ≤ (2730900001 : ℝ) / 100000000 := by
  rw [show (4 : ℝ) / 1 = (4 : ℝ) by norm_num]
  exact (cosh_four_le).trans (by norm_num)

lemma cosh_b40095_ub : cosh ((8019 : ℝ) / 2000) ≤ (2756960130 : ℝ) / 100000000 := by
  have exp_frac_b40095 : exp ((19 : ℝ) / 2000) ≤ (100954601 : ℝ) / 100000000 := by
    have ht : ((19 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((19 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((19 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (100954601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8019 : ℝ) / 2000) = exp 4 * exp ((19 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (19 : ℝ) / 2000 = (8019 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8019 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8019 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b40095 (exp_pos ((19 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8019 : ℝ) / 2000), exp_pos (-((8019 : ℝ) / 2000))]

lemma cosh_b40185_ub : cosh ((8037 : ℝ) / 2000) ≤ (2781876384 : ℝ) / 100000000 := by
  have exp_frac_b40185 : exp ((37 : ℝ) / 2000) ≤ (101867301 : ℝ) / 100000000 := by
    have ht : ((37 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((37 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((37 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (101867301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8037 : ℝ) / 2000) = exp 4 * exp ((37 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (37 : ℝ) / 2000 = (8037 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8037 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8037 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b40185 (exp_pos ((37 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8037 : ℝ) / 2000), exp_pos (-((8037 : ℝ) / 2000))]

lemma cosh_b40275_ub : cosh ((1611 : ℝ) / 400) ≤ (2807016494 : ℝ) / 100000000 := by
  have exp_frac_b40275 : exp ((11 : ℝ) / 400) ≤ (102788201 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((11 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((11 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (102788201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1611 : ℝ) / 400) = exp 4 * exp ((11 : ℝ) / 400) := by
    rw [← exp_add, show (4 : ℝ) + (11 : ℝ) / 400 = (1611 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1611 : ℝ) / 400)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1611 : ℝ) / 400) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b40275 (exp_pos ((11 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1611 : ℝ) / 400), exp_pos (-((1611 : ℝ) / 400))]

lemma cosh_b40365_ub : cosh ((8073 : ℝ) / 2000) ≤ (2832385919 : ℝ) / 100000000 := by
  have exp_frac_b40365 : exp ((73 : ℝ) / 2000) ≤ (103717501 : ℝ) / 100000000 := by
    have ht : ((73 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((73 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((73 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (103717501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8073 : ℝ) / 2000) = exp 4 * exp ((73 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (73 : ℝ) / 2000 = (8073 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8073 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8073 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b40365 (exp_pos ((73 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8073 : ℝ) / 2000), exp_pos (-((8073 : ℝ) / 2000))]

lemma cosh_b40455_ub : cosh ((8091 : ℝ) / 2000) ≤ (2857984660 : ℝ) / 100000000 := by
  have exp_frac_b40455 : exp ((91 : ℝ) / 2000) ≤ (104655201 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (104655201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8091 : ℝ) / 2000) = exp 4 * exp ((91 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (91 : ℝ) / 2000 = (8091 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8091 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8091 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b40455 (exp_pos ((91 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8091 : ℝ) / 2000), exp_pos (-((8091 : ℝ) / 2000))]

lemma cosh_b40550_ub : cosh ((811 : ℝ) / 200) ≤ (2885254131 : ℝ) / 100000000 := by
  have exp_frac_b40550 : exp ((11 : ℝ) / 200) ≤ (105654101 : ℝ) / 100000000 := by
    have ht : ((11 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((11 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((11 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (105654101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((811 : ℝ) / 200) = exp 4 * exp ((11 : ℝ) / 200) := by
    rw [← exp_add, show (4 : ℝ) + (11 : ℝ) / 200 = (811 : ℝ) / 200 by norm_num]
  have hneg : exp (-((811 : ℝ) / 200)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((811 : ℝ) / 200) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b40550 (exp_pos ((11 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((811 : ℝ) / 200), exp_pos (-((811 : ℝ) / 200))]

lemma cosh_b40640_ub : cosh ((508 : ℝ) / 125) ≤ (2911330613 : ℝ) / 100000000 := by
  have exp_frac_b40640 : exp ((8 : ℝ) / 125) ≤ (106609301 : ℝ) / 100000000 := by
    have ht : ((8 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((8 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((8 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (106609301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((508 : ℝ) / 125) = exp 4 * exp ((8 : ℝ) / 125) := by
    rw [← exp_add, show (4 : ℝ) + (8 : ℝ) / 125 = (508 : ℝ) / 125 by norm_num]
  have hneg : exp (-((508 : ℝ) / 125)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((508 : ℝ) / 125) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b40640 (exp_pos ((8 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((508 : ℝ) / 125), exp_pos (-((508 : ℝ) / 125))]

lemma cosh_b40730_ub : cosh ((4073 : ℝ) / 1000) ≤ (2937641871 : ℝ) / 100000000 := by
  have exp_frac_b40730 : exp ((73 : ℝ) / 1000) ≤ (107573101 : ℝ) / 100000000 := by
    have ht : ((73 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((73 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((73 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (107573101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4073 : ℝ) / 1000) = exp 4 * exp ((73 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (73 : ℝ) / 1000 = (4073 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4073 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4073 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b40730 (exp_pos ((73 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4073 : ℝ) / 1000), exp_pos (-((4073 : ℝ) / 1000))]

lemma cosh_b40820_ub : cosh ((2041 : ℝ) / 500) ≤ (2964190635 : ℝ) / 100000000 := by
  have exp_frac_b40820 : exp ((41 : ℝ) / 500) ≤ (108545601 : ℝ) / 100000000 := by
    have ht : ((41 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((41 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((41 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (108545601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2041 : ℝ) / 500) = exp 4 * exp ((41 : ℝ) / 500) := by
    rw [← exp_add, show (4 : ℝ) + (41 : ℝ) / 500 = (2041 : ℝ) / 500 by norm_num]
  have hneg : exp (-((2041 : ℝ) / 500)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2041 : ℝ) / 500) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b40820 (exp_pos ((41 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2041 : ℝ) / 500), exp_pos (-((2041 : ℝ) / 500))]

lemma cosh_b40910_ub : cosh ((4091 : ℝ) / 1000) ≤ (2990982364 : ℝ) / 100000000 := by
  have exp_frac_b40910 : exp ((91 : ℝ) / 1000) ≤ (109527001 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (109527001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4091 : ℝ) / 1000) = exp 4 * exp ((91 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (91 : ℝ) / 1000 = (4091 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4091 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4091 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b40910 (exp_pos ((91 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4091 : ℝ) / 1000), exp_pos (-((4091 : ℝ) / 1000))]

lemma cosh_b41000_ub : cosh ((41 : ℝ) / 10) ≤ (3018011599 : ℝ) / 100000000 := by
  have exp_frac_b41000 : exp ((1 : ℝ) / 10) ≤ (110517101 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((1 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (110517101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((41 : ℝ) / 10) = exp 4 * exp ((1 : ℝ) / 10) := by
    rw [← exp_add, show (4 : ℝ) + (1 : ℝ) / 10 = (41 : ℝ) / 10 by norm_num]
  have hneg : exp (-((41 : ℝ) / 10)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((41 : ℝ) / 10) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b41000 (exp_pos ((1 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((41 : ℝ) / 10), exp_pos (-((41 : ℝ) / 10))]

lemma cosh_b41095_ub : cosh ((8219 : ℝ) / 2000) ≤ (3046812572 : ℝ) / 100000000 := by
  have exp_frac_b41095 : exp ((219 : ℝ) / 2000) ≤ (111572101 : ℝ) / 100000000 := by
    have ht : ((219 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((219 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((219 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (111572101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8219 : ℝ) / 2000) = exp 4 * exp ((219 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (219 : ℝ) / 2000 = (8219 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8219 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8219 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b41095 (exp_pos ((219 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8219 : ℝ) / 2000), exp_pos (-((8219 : ℝ) / 2000))]

lemma cosh_b41185_ub : cosh ((8237 : ℝ) / 2000) ≤ (3074346847 : ℝ) / 100000000 := by
  have exp_frac_b41185 : exp ((237 : ℝ) / 2000) ≤ (112580701 : ℝ) / 100000000 := by
    have ht : ((237 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((237 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((237 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (112580701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8237 : ℝ) / 2000) = exp 4 * exp ((237 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (237 : ℝ) / 2000 = (8237 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8237 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8237 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b41185 (exp_pos ((237 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8237 : ℝ) / 2000), exp_pos (-((8237 : ℝ) / 2000))]

lemma cosh_b41275_ub : cosh ((1651 : ℝ) / 400) ≤ (3102132279 : ℝ) / 100000000 := by
  have exp_frac_b41275 : exp ((51 : ℝ) / 400) ≤ (113598501 : ℝ) / 100000000 := by
    have ht : ((51 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((51 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((51 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (113598501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1651 : ℝ) / 400) = exp 4 * exp ((51 : ℝ) / 400) := by
    rw [← exp_add, show (4 : ℝ) + (51 : ℝ) / 400 = (1651 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1651 : ℝ) / 400)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1651 : ℝ) / 400) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b41275 (exp_pos ((51 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1651 : ℝ) / 400), exp_pos (-((1651 : ℝ) / 400))]

lemma cosh_b41365_ub : cosh ((8273 : ℝ) / 2000) ≤ (3130168865 : ℝ) / 100000000 := by
  have exp_frac_b41365 : exp ((273 : ℝ) / 2000) ≤ (114625501 : ℝ) / 100000000 := by
    have ht : ((273 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((273 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((273 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (114625501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8273 : ℝ) / 2000) = exp 4 * exp ((273 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (273 : ℝ) / 2000 = (8273 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8273 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8273 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b41365 (exp_pos ((273 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8273 : ℝ) / 2000), exp_pos (-((8273 : ℝ) / 2000))]

lemma cosh_b41455_ub : cosh ((8291 : ℝ) / 2000) ≤ (3158459337 : ℝ) / 100000000 := by
  have exp_frac_b41455 : exp ((291 : ℝ) / 2000) ≤ (115661801 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (115661801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8291 : ℝ) / 2000) = exp 4 * exp ((291 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (291 : ℝ) / 2000 = (8291 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8291 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8291 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b41455 (exp_pos ((291 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8291 : ℝ) / 2000), exp_pos (-((8291 : ℝ) / 2000))]

lemma cosh_b41550_ub : cosh ((831 : ℝ) / 200) ≤ (3188597985 : ℝ) / 100000000 := by
  have exp_frac_b41550 : exp ((31 : ℝ) / 200) ≤ (116765801 : ℝ) / 100000000 := by
    have ht : ((31 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((31 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((31 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (116765801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((831 : ℝ) / 200) = exp 4 * exp ((31 : ℝ) / 200) := by
    rw [← exp_add, show (4 : ℝ) + (31 : ℝ) / 200 = (831 : ℝ) / 200 by norm_num]
  have hneg : exp (-((831 : ℝ) / 200)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((831 : ℝ) / 200) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b41550 (exp_pos ((31 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((831 : ℝ) / 200), exp_pos (-((831 : ℝ) / 200))]

lemma cosh_b41640_ub : cosh ((1041 : ℝ) / 250) ≤ (3217418067 : ℝ) / 100000000 := by
  have exp_frac_b41640 : exp ((41 : ℝ) / 250) ≤ (117821501 : ℝ) / 100000000 := by
    have ht : ((41 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((41 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((41 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (117821501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1041 : ℝ) / 250) = exp 4 * exp ((41 : ℝ) / 250) := by
    rw [← exp_add, show (4 : ℝ) + (41 : ℝ) / 250 = (1041 : ℝ) / 250 by norm_num]
  have hneg : exp (-((1041 : ℝ) / 250)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1041 : ℝ) / 250) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b41640 (exp_pos ((41 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1041 : ℝ) / 250), exp_pos (-((1041 : ℝ) / 250))]

lemma cosh_b41730_ub : cosh ((4173 : ℝ) / 1000) ≤ (3246497494 : ℝ) / 100000000 := by
  have exp_frac_b41730 : exp ((173 : ℝ) / 1000) ≤ (118886701 : ℝ) / 100000000 := by
    have ht : ((173 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((173 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((173 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (118886701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4173 : ℝ) / 1000) = exp 4 * exp ((173 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (173 : ℝ) / 1000 = (4173 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4173 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4173 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b41730 (exp_pos ((173 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4173 : ℝ) / 1000), exp_pos (-((4173 : ℝ) / 1000))]

lemma cosh_b41820_ub : cosh ((2091 : ℝ) / 500) ≤ (3275838997 : ℝ) / 100000000 := by
  have exp_frac_b41820 : exp ((91 : ℝ) / 500) ≤ (119961501 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (119961501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2091 : ℝ) / 500) = exp 4 * exp ((91 : ℝ) / 500) := by
    rw [← exp_add, show (4 : ℝ) + (91 : ℝ) / 500 = (2091 : ℝ) / 500 by norm_num]
  have hneg : exp (-((2091 : ℝ) / 500)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2091 : ℝ) / 500) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b41820 (exp_pos ((91 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2091 : ℝ) / 500), exp_pos (-((2091 : ℝ) / 500))]

lemma cosh_b41910_ub : cosh ((4191 : ℝ) / 1000) ≤ (3305445305 : ℝ) / 100000000 := by
  have exp_frac_b41910 : exp ((191 : ℝ) / 1000) ≤ (121046001 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (121046001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4191 : ℝ) / 1000) = exp 4 * exp ((191 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (191 : ℝ) / 1000 = (4191 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4191 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4191 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b41910 (exp_pos ((191 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4191 : ℝ) / 1000), exp_pos (-((4191 : ℝ) / 1000))]

lemma cosh_b42000_ub : cosh ((21 : ℝ) / 5) ≤ (3335319148 : ℝ) / 100000000 := by
  have exp_frac_b42000 : exp ((1 : ℝ) / 5) ≤ (122140301 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((1 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (122140301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((21 : ℝ) / 5) = exp 4 * exp ((1 : ℝ) / 5) := by
    rw [← exp_add, show (4 : ℝ) + (1 : ℝ) / 5 = (21 : ℝ) / 5 by norm_num]
  have hneg : exp (-((21 : ℝ) / 5)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((21 : ℝ) / 5) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b42000 (exp_pos ((1 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((21 : ℝ) / 5), exp_pos (-((21 : ℝ) / 5))]

lemma cosh_b42095_ub : cosh ((8419 : ℝ) / 2000) ≤ (3367147635 : ℝ) / 100000000 := by
  have exp_frac_b42095 : exp ((419 : ℝ) / 2000) ≤ (123306201 : ℝ) / 100000000 := by
    have ht : ((419 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((419 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((419 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (123306201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8419 : ℝ) / 2000) = exp 4 * exp ((419 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (419 : ℝ) / 2000 = (8419 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8419 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8419 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b42095 (exp_pos ((419 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8419 : ℝ) / 2000), exp_pos (-((8419 : ℝ) / 2000))]

lemma cosh_b42185_ub : cosh ((8437 : ℝ) / 2000) ≤ (3397581117 : ℝ) / 100000000 := by
  have exp_frac_b42185 : exp ((437 : ℝ) / 2000) ≤ (124421001 : ℝ) / 100000000 := by
    have ht : ((437 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((437 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((437 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (124421001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8437 : ℝ) / 2000) = exp 4 * exp ((437 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (437 : ℝ) / 2000 = (8437 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8437 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8437 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b42185 (exp_pos ((437 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8437 : ℝ) / 2000), exp_pos (-((8437 : ℝ) / 2000))]

lemma cosh_b42275_ub : cosh ((1691 : ℝ) / 400) ≤ (3428287595 : ℝ) / 100000000 := by
  have exp_frac_b42275 : exp ((91 : ℝ) / 400) ≤ (125545801 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (125545801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1691 : ℝ) / 400) = exp 4 * exp ((91 : ℝ) / 400) := by
    rw [← exp_add, show (4 : ℝ) + (91 : ℝ) / 400 = (1691 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1691 : ℝ) / 400)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1691 : ℝ) / 400) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b42275 (exp_pos ((91 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1691 : ℝ) / 400), exp_pos (-((1691 : ℝ) / 400))]

lemma cosh_b42365_ub : cosh ((8473 : ℝ) / 2000) ≤ (3459272527 : ℝ) / 100000000 := by
  have exp_frac_b42365 : exp ((473 : ℝ) / 2000) ≤ (126680801 : ℝ) / 100000000 := by
    have ht : ((473 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((473 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((473 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (126680801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8473 : ℝ) / 2000) = exp 4 * exp ((473 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (473 : ℝ) / 2000 = (8473 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8473 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8473 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b42365 (exp_pos ((473 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8473 : ℝ) / 2000), exp_pos (-((8473 : ℝ) / 2000))]

lemma cosh_b42455_ub : cosh ((8491 : ℝ) / 2000) ≤ (3490538645 : ℝ) / 100000000 := by
  have exp_frac_b42455 : exp ((491 : ℝ) / 2000) ≤ (127826101 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((491 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((491 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (127826101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8491 : ℝ) / 2000) = exp 4 * exp ((491 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (491 : ℝ) / 2000 = (8491 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8491 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8491 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b42455 (exp_pos ((491 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8491 : ℝ) / 2000), exp_pos (-((8491 : ℝ) / 2000))]

lemma cosh_b42550_ub : cosh ((851 : ℝ) / 200) ≤ (3523846765 : ℝ) / 100000000 := by
  have exp_frac_b42550 : exp ((51 : ℝ) / 200) ≤ (129046201 : ℝ) / 100000000 := by
    have ht : ((51 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((51 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((51 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (129046201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((851 : ℝ) / 200) = exp 4 * exp ((51 : ℝ) / 200) := by
    rw [← exp_add, show (4 : ℝ) + (51 : ℝ) / 200 = (851 : ℝ) / 200 by norm_num]
  have hneg : exp (-((851 : ℝ) / 200)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((851 : ℝ) / 200) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b42550 (exp_pos ((51 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((851 : ℝ) / 200), exp_pos (-((851 : ℝ) / 200))]

lemma cosh_b42640_ub : cosh ((533 : ℝ) / 125) ≤ (3555697091 : ℝ) / 100000000 := by
  have exp_frac_b42640 : exp ((33 : ℝ) / 125) ≤ (130212901 : ℝ) / 100000000 := by
    have ht : ((33 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((33 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((33 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (130212901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((533 : ℝ) / 125) = exp 4 * exp ((33 : ℝ) / 125) := by
    rw [← exp_add, show (4 : ℝ) + (33 : ℝ) / 125 = (533 : ℝ) / 125 by norm_num]
  have hneg : exp (-((533 : ℝ) / 125)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((533 : ℝ) / 125) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b42640 (exp_pos ((33 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((533 : ℝ) / 125), exp_pos (-((533 : ℝ) / 125))]

lemma cosh_b42730_ub : cosh ((4273 : ℝ) / 1000) ≤ (3587834063 : ℝ) / 100000000 := by
  have exp_frac_b42730 : exp ((273 : ℝ) / 1000) ≤ (131390101 : ℝ) / 100000000 := by
    have ht : ((273 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((273 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((273 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (131390101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4273 : ℝ) / 1000) = exp 4 * exp ((273 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (273 : ℝ) / 1000 = (4273 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4273 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4273 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b42730 (exp_pos ((273 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4273 : ℝ) / 1000), exp_pos (-((4273 : ℝ) / 1000))]

lemma cosh_b42820_ub : cosh ((2141 : ℝ) / 500) ≤ (3620260409 : ℝ) / 100000000 := by
  have exp_frac_b42820 : exp ((141 : ℝ) / 500) ≤ (132577901 : ℝ) / 100000000 := by
    have ht : ((141 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((141 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((141 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (132577901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2141 : ℝ) / 500) = exp 4 * exp ((141 : ℝ) / 500) := by
    rw [← exp_add, show (4 : ℝ) + (141 : ℝ) / 500 = (2141 : ℝ) / 500 by norm_num]
  have hneg : exp (-((2141 : ℝ) / 500)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2141 : ℝ) / 500) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b42820 (exp_pos ((141 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2141 : ℝ) / 500), exp_pos (-((2141 : ℝ) / 500))]

lemma cosh_b42910_ub : cosh ((4291 : ℝ) / 1000) ≤ (3652981590 : ℝ) / 100000000 := by
  have exp_frac_b42910 : exp ((291 : ℝ) / 1000) ≤ (133776501 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (133776501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4291 : ℝ) / 1000) = exp 4 * exp ((291 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (291 : ℝ) / 1000 = (4291 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4291 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4291 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b42910 (exp_pos ((291 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4291 : ℝ) / 1000), exp_pos (-((4291 : ℝ) / 1000))]

lemma cosh_b43000_ub : cosh ((43 : ℝ) / 10) ≤ (3685997605 : ℝ) / 100000000 := by
  have exp_frac_b43000 : exp ((3 : ℝ) / 10) ≤ (134985901 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((3 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((3 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (134985901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((43 : ℝ) / 10) = exp 4 * exp ((3 : ℝ) / 10) := by
    rw [← exp_add, show (4 : ℝ) + (3 : ℝ) / 10 = (43 : ℝ) / 10 by norm_num]
  have hneg : exp (-((43 : ℝ) / 10)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((43 : ℝ) / 10) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b43000 (exp_pos ((3 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((43 : ℝ) / 10), exp_pos (-((43 : ℝ) / 10))]

lemma cosh_b43095_ub : cosh ((8619 : ℝ) / 2000) ≤ (3721173011 : ℝ) / 100000000 := by
  have exp_frac_b43095 : exp ((619 : ℝ) / 2000) ≤ (136274401 : ℝ) / 100000000 := by
    have ht : ((619 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((619 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((619 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (136274401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8619 : ℝ) / 2000) = exp 4 * exp ((619 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (619 : ℝ) / 2000 = (8619 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8619 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8619 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b43095 (exp_pos ((619 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8619 : ℝ) / 2000), exp_pos (-((8619 : ℝ) / 2000))]

lemma cosh_b43185_ub : cosh ((8637 : ℝ) / 2000) ≤ (3754805995 : ℝ) / 100000000 := by
  have exp_frac_b43185 : exp ((637 : ℝ) / 2000) ≤ (137506401 : ℝ) / 100000000 := by
    have ht : ((637 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((637 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((637 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (137506401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8637 : ℝ) / 2000) = exp 4 * exp ((637 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (637 : ℝ) / 2000 = (8637 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8637 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8637 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b43185 (exp_pos ((637 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8637 : ℝ) / 2000), exp_pos (-((8637 : ℝ) / 2000))]

lemma cosh_b43275_ub : cosh ((1731 : ℝ) / 400) ≤ (3788744733 : ℝ) / 100000000 := by
  have exp_frac_b43275 : exp ((131 : ℝ) / 400) ≤ (138749601 : ℝ) / 100000000 := by
    have ht : ((131 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((131 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((131 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (138749601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1731 : ℝ) / 400) = exp 4 * exp ((131 : ℝ) / 400) := by
    rw [← exp_add, show (4 : ℝ) + (131 : ℝ) / 400 = (1731 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1731 : ℝ) / 400)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1731 : ℝ) / 400) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b43275 (exp_pos ((131 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1731 : ℝ) / 400), exp_pos (-((1731 : ℝ) / 400))]

lemma cosh_b43365_ub : cosh ((8673 : ℝ) / 2000) ≤ (3822986496 : ℝ) / 100000000 := by
  have exp_frac_b43365 : exp ((673 : ℝ) / 2000) ≤ (140003901 : ℝ) / 100000000 := by
    have ht : ((673 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((673 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((673 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (140003901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8673 : ℝ) / 2000) = exp 4 * exp ((673 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (673 : ℝ) / 2000 = (8673 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8673 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8673 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b43365 (exp_pos ((673 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8673 : ℝ) / 2000), exp_pos (-((8673 : ℝ) / 2000))]

lemma cosh_b43455_ub : cosh ((8691 : ℝ) / 2000) ≤ (3857542203 : ℝ) / 100000000 := by
  have exp_frac_b43455 : exp ((691 : ℝ) / 2000) ≤ (141269701 : ℝ) / 100000000 := by
    have ht : ((691 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((691 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((691 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (141269701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8691 : ℝ) / 2000) = exp 4 * exp ((691 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (691 : ℝ) / 2000 = (8691 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8691 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8691 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b43455 (exp_pos ((691 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8691 : ℝ) / 2000), exp_pos (-((8691 : ℝ) / 2000))]

lemma cosh_b43550_ub : cosh ((871 : ℝ) / 200) ≤ (3894352849 : ℝ) / 100000000 := by
  have exp_frac_b43550 : exp ((71 : ℝ) / 200) ≤ (142618101 : ℝ) / 100000000 := by
    have ht : ((71 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((71 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((71 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (142618101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((871 : ℝ) / 200) = exp 4 * exp ((71 : ℝ) / 200) := by
    rw [← exp_add, show (4 : ℝ) + (71 : ℝ) / 200 = (871 : ℝ) / 200 by norm_num]
  have hneg : exp (-((871 : ℝ) / 200)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((871 : ℝ) / 200) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b43550 (exp_pos ((71 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((871 : ℝ) / 200), exp_pos (-((871 : ℝ) / 200))]

lemma cosh_b43640_ub : cosh ((1091 : ℝ) / 250) ≤ (3929552824 : ℝ) / 100000000 := by
  have exp_frac_b43640 : exp ((91 : ℝ) / 250) ≤ (143907501 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (143907501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1091 : ℝ) / 250) = exp 4 * exp ((91 : ℝ) / 250) := by
    rw [← exp_add, show (4 : ℝ) + (91 : ℝ) / 250 = (1091 : ℝ) / 250 by norm_num]
  have hneg : exp (-((1091 : ℝ) / 250)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1091 : ℝ) / 250) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b43640 (exp_pos ((91 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1091 : ℝ) / 250), exp_pos (-((1091 : ℝ) / 250))]

lemma cosh_b43730_ub : cosh ((4373 : ℝ) / 1000) ≤ (3965069474 : ℝ) / 100000000 := by
  have exp_frac_b43730 : exp ((373 : ℝ) / 1000) ≤ (145208501 : ℝ) / 100000000 := by
    have ht : ((373 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((373 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((373 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (145208501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4373 : ℝ) / 1000) = exp 4 * exp ((373 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (373 : ℝ) / 1000 = (4373 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4373 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4373 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b43730 (exp_pos ((373 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4373 : ℝ) / 1000), exp_pos (-((4373 : ℝ) / 1000))]

lemma cosh_b43820_ub : cosh ((2191 : ℝ) / 500) ≤ (4000908257 : ℝ) / 100000000 := by
  have exp_frac_b43820 : exp ((191 : ℝ) / 500) ≤ (146521301 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (146521301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2191 : ℝ) / 500) = exp 4 * exp ((191 : ℝ) / 500) := by
    rw [← exp_add, show (4 : ℝ) + (191 : ℝ) / 500 = (2191 : ℝ) / 500 by norm_num]
  have hneg : exp (-((2191 : ℝ) / 500)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2191 : ℝ) / 500) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b43820 (exp_pos ((191 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2191 : ℝ) / 500), exp_pos (-((2191 : ℝ) / 500))]

lemma cosh_b43910_ub : cosh ((4391 : ℝ) / 1000) ≤ (4037069175 : ℝ) / 100000000 := by
  have exp_frac_b43910 : exp ((391 : ℝ) / 1000) ≤ (147845901 : ℝ) / 100000000 := by
    have ht : ((391 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((391 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((391 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (147845901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4391 : ℝ) / 1000) = exp 4 * exp ((391 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (391 : ℝ) / 1000 = (4391 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4391 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4391 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b43910 (exp_pos ((391 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4391 : ℝ) / 1000), exp_pos (-((4391 : ℝ) / 1000))]

lemma cosh_b44000_ub : cosh ((22 : ℝ) / 5) ≤ (4073557687 : ℝ) / 100000000 := by
  have exp_frac_b44000 : exp ((2 : ℝ) / 5) ≤ (149182501 : ℝ) / 100000000 := by
    have ht : ((2 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((2 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((2 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (149182501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((22 : ℝ) / 5) = exp 4 * exp ((2 : ℝ) / 5) := by
    rw [← exp_add, show (4 : ℝ) + (2 : ℝ) / 5 = (22 : ℝ) / 5 by norm_num]
  have hneg : exp (-((22 : ℝ) / 5)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((22 : ℝ) / 5) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b44000 (exp_pos ((2 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((22 : ℝ) / 5), exp_pos (-((22 : ℝ) / 5))]

lemma cosh_b44095_ub : cosh ((8819 : ℝ) / 2000) ≤ (4112432175 : ℝ) / 100000000 := by
  have exp_frac_b44095 : exp ((819 : ℝ) / 2000) ≤ (150606501 : ℝ) / 100000000 := by
    have ht : ((819 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((819 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((819 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (150606501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8819 : ℝ) / 2000) = exp 4 * exp ((819 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (819 : ℝ) / 2000 = (8819 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8819 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8819 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b44095 (exp_pos ((819 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8819 : ℝ) / 2000), exp_pos (-((8819 : ℝ) / 2000))]

lemma cosh_b44185_ub : cosh ((8837 : ℝ) / 2000) ≤ (4149603174 : ℝ) / 100000000 := by
  have exp_frac_b44185 : exp ((837 : ℝ) / 2000) ≤ (151968101 : ℝ) / 100000000 := by
    have ht : ((837 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((837 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((837 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (151968101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8837 : ℝ) / 2000) = exp 4 * exp ((837 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (837 : ℝ) / 2000 = (8837 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8837 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8837 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b44185 (exp_pos ((837 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8837 : ℝ) / 2000), exp_pos (-((8837 : ℝ) / 2000))]

lemma cosh_b44275_ub : cosh ((1771 : ℝ) / 400) ≤ (4187109957 : ℝ) / 100000000 := by
  have exp_frac_b44275 : exp ((171 : ℝ) / 400) ≤ (153342001 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((171 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((171 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (153342001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1771 : ℝ) / 400) = exp 4 * exp ((171 : ℝ) / 400) := by
    rw [← exp_add, show (4 : ℝ) + (171 : ℝ) / 400 = (1771 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1771 : ℝ) / 400)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1771 : ℝ) / 400) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b44275 (exp_pos ((171 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1771 : ℝ) / 400), exp_pos (-((1771 : ℝ) / 400))]

lemma cosh_b44365_ub : cosh ((8873 : ℝ) / 2000) ≤ (4224955254 : ℝ) / 100000000 := by
  have exp_frac_b44365 : exp ((873 : ℝ) / 2000) ≤ (154728301 : ℝ) / 100000000 := by
    have ht : ((873 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((873 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((873 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (154728301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8873 : ℝ) / 2000) = exp 4 * exp ((873 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (873 : ℝ) / 2000 = (8873 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8873 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8873 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b44365 (exp_pos ((873 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8873 : ℝ) / 2000), exp_pos (-((8873 : ℝ) / 2000))]

lemma cosh_b44455_ub : cosh ((8891 : ℝ) / 2000) ≤ (4263141794 : ℝ) / 100000000 := by
  have exp_frac_b44455 : exp ((891 : ℝ) / 2000) ≤ (156127101 : ℝ) / 100000000 := by
    have ht : ((891 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((891 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((891 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (156127101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((8891 : ℝ) / 2000) = exp 4 * exp ((891 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (891 : ℝ) / 2000 = (8891 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((8891 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((8891 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b44455 (exp_pos ((891 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((8891 : ℝ) / 2000), exp_pos (-((8891 : ℝ) / 2000))]

lemma cosh_b44550_ub : cosh ((891 : ℝ) / 200) ≤ (4303826239 : ℝ) / 100000000 := by
  have exp_frac_b44550 : exp ((91 : ℝ) / 200) ≤ (157617401 : ℝ) / 100000000 := by
    have ht : ((91 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((91 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((91 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (157617401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((891 : ℝ) / 200) = exp 4 * exp ((91 : ℝ) / 200) := by
    rw [← exp_add, show (4 : ℝ) + (91 : ℝ) / 200 = (891 : ℝ) / 200 by norm_num]
  have hneg : exp (-((891 : ℝ) / 200)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((891 : ℝ) / 200) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b44550 (exp_pos ((91 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((891 : ℝ) / 200), exp_pos (-((891 : ℝ) / 200))]

lemma cosh_b44640_ub : cosh ((558 : ℝ) / 125) ≤ (4342725297 : ℝ) / 100000000 := by
  have exp_frac_b44640 : exp ((58 : ℝ) / 125) ≤ (159042301 : ℝ) / 100000000 := by
    have ht : ((58 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((58 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((58 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (159042301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((558 : ℝ) / 125) = exp 4 * exp ((58 : ℝ) / 125) := by
    rw [← exp_add, show (4 : ℝ) + (58 : ℝ) / 125 = (558 : ℝ) / 125 by norm_num]
  have hneg : exp (-((558 : ℝ) / 125)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((558 : ℝ) / 125) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b44640 (exp_pos ((58 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((558 : ℝ) / 125), exp_pos (-((558 : ℝ) / 125))]

lemma cosh_b44730_ub : cosh ((4473 : ℝ) / 1000) ≤ (4381979248 : ℝ) / 100000000 := by
  have exp_frac_b44730 : exp ((473 : ℝ) / 1000) ≤ (160480201 : ℝ) / 100000000 := by
    have ht : ((473 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((473 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((473 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (160480201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4473 : ℝ) / 1000) = exp 4 * exp ((473 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (473 : ℝ) / 1000 = (4473 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4473 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4473 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b44730 (exp_pos ((473 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4473 : ℝ) / 1000), exp_pos (-((4473 : ℝ) / 1000))]

lemma cosh_b44820_ub : cosh ((2241 : ℝ) / 500) ≤ (4421585362 : ℝ) / 100000000 := by
  have exp_frac_b44820 : exp ((241 : ℝ) / 500) ≤ (161931001 : ℝ) / 100000000 := by
    have ht : ((241 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((241 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((241 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (161931001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2241 : ℝ) / 500) = exp 4 * exp ((241 : ℝ) / 500) := by
    rw [← exp_add, show (4 : ℝ) + (241 : ℝ) / 500 = (2241 : ℝ) / 500 by norm_num]
  have hneg : exp (-((2241 : ℝ) / 500)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2241 : ℝ) / 500) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b44820 (exp_pos ((241 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2241 : ℝ) / 500), exp_pos (-((2241 : ℝ) / 500))]

lemma cosh_b44910_ub : cosh ((4491 : ℝ) / 1000) ≤ (4461551830 : ℝ) / 100000000 := by
  have exp_frac_b44910 : exp ((491 : ℝ) / 1000) ≤ (163395001 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((491 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((491 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (163395001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4491 : ℝ) / 1000) = exp 4 * exp ((491 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (491 : ℝ) / 1000 = (4491 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4491 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4491 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b44910 (exp_pos ((491 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4491 : ℝ) / 1000), exp_pos (-((4491 : ℝ) / 1000))]

lemma cosh_b45000_ub : cosh ((9 : ℝ) / 2) ≤ (4501878652 : ℝ) / 100000000 := by
  have exp_frac_b45000 : exp ((1 : ℝ) / 2) ≤ (164872201 : ℝ) / 100000000 := by
    have ht : ((1 : ℝ) / 2) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1 : ℝ) / 2) ^ m / (Nat.factorial m)) +
          ((1 : ℝ) / 2) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (164872201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9 : ℝ) / 2) = exp 4 * exp ((1 : ℝ) / 2) := by
    rw [← exp_add, show (4 : ℝ) + (1 : ℝ) / 2 = (9 : ℝ) / 2 by norm_num]
  have hneg : exp (-((9 : ℝ) / 2)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9 : ℝ) / 2) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b45000 (exp_pos ((1 : ℝ) / 2)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9 : ℝ) / 2), exp_pos (-((9 : ℝ) / 2))]

lemma cosh_b45095_ub : cosh ((9019 : ℝ) / 2000) ≤ (4544839875 : ℝ) / 100000000 := by
  have exp_frac_b45095 : exp ((1019 : ℝ) / 2000) ≤ (166445901 : ℝ) / 100000000 := by
    have ht : ((1019 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1019 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1019 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (166445901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9019 : ℝ) / 2000) = exp 4 * exp ((1019 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1019 : ℝ) / 2000 = (9019 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9019 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9019 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b45095 (exp_pos ((1019 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9019 : ℝ) / 2000), exp_pos (-((9019 : ℝ) / 2000))]

lemma cosh_b45185_ub : cosh ((9037 : ℝ) / 2000) ≤ (4585920162 : ℝ) / 100000000 := by
  have exp_frac_b45185 : exp ((1037 : ℝ) / 2000) ≤ (167950701 : ℝ) / 100000000 := by
    have ht : ((1037 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1037 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1037 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (167950701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9037 : ℝ) / 2000) = exp 4 * exp ((1037 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1037 : ℝ) / 2000 = (9037 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9037 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9037 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b45185 (exp_pos ((1037 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9037 : ℝ) / 2000), exp_pos (-((9037 : ℝ) / 2000))]

lemma cosh_b45275_ub : cosh ((1811 : ℝ) / 400) ≤ (4627371723 : ℝ) / 100000000 := by
  have exp_frac_b45275 : exp ((211 : ℝ) / 400) ≤ (169469101 : ℝ) / 100000000 := by
    have ht : ((211 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((211 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((211 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (169469101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1811 : ℝ) / 400) = exp 4 * exp ((211 : ℝ) / 400) := by
    rw [← exp_add, show (4 : ℝ) + (211 : ℝ) / 400 = (1811 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1811 : ℝ) / 400)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1811 : ℝ) / 400) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b45275 (exp_pos ((211 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1811 : ℝ) / 400), exp_pos (-((1811 : ℝ) / 400))]

lemma cosh_b45365_ub : cosh ((9073 : ℝ) / 2000) ≤ (4669197287 : ℝ) / 100000000 := by
  have exp_frac_b45365 : exp ((1073 : ℝ) / 2000) ≤ (171001201 : ℝ) / 100000000 := by
    have ht : ((1073 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1073 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1073 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (171001201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9073 : ℝ) / 2000) = exp 4 * exp ((1073 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1073 : ℝ) / 2000 = (9073 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9073 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9073 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b45365 (exp_pos ((1073 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9073 : ℝ) / 2000), exp_pos (-((9073 : ℝ) / 2000))]

lemma cosh_b45455_ub : cosh ((9091 : ℝ) / 2000) ≤ (4711399584 : ℝ) / 100000000 := by
  have exp_frac_b45455 : exp ((1091 : ℝ) / 2000) ≤ (172547101 : ℝ) / 100000000 := by
    have ht : ((1091 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1091 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1091 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (172547101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9091 : ℝ) / 2000) = exp 4 * exp ((1091 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1091 : ℝ) / 2000 = (9091 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9091 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9091 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b45455 (exp_pos ((1091 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9091 : ℝ) / 2000), exp_pos (-((9091 : ℝ) / 2000))]

lemma cosh_b45550_ub : cosh ((911 : ℝ) / 200) ≤ (4756361861 : ℝ) / 100000000 := by
  have exp_frac_b45550 : exp ((111 : ℝ) / 200) ≤ (174194101 : ℝ) / 100000000 := by
    have ht : ((111 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((111 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((111 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (174194101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((911 : ℝ) / 200) = exp 4 * exp ((111 : ℝ) / 200) := by
    rw [← exp_add, show (4 : ℝ) + (111 : ℝ) / 200 = (911 : ℝ) / 200 by norm_num]
  have hneg : exp (-((911 : ℝ) / 200)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((911 : ℝ) / 200) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b45550 (exp_pos ((111 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((911 : ℝ) / 200), exp_pos (-((911 : ℝ) / 200))]

lemma cosh_b45640_ub : cosh ((1141 : ℝ) / 250) ≤ (4799355843 : ℝ) / 100000000 := by
  have exp_frac_b45640 : exp ((141 : ℝ) / 250) ≤ (175769001 : ℝ) / 100000000 := by
    have ht : ((141 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((141 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((141 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (175769001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1141 : ℝ) / 250) = exp 4 * exp ((141 : ℝ) / 250) := by
    rw [← exp_add, show (4 : ℝ) + (141 : ℝ) / 250 = (1141 : ℝ) / 250 by norm_num]
  have hneg : exp (-((1141 : ℝ) / 250)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1141 : ℝ) / 250) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b45640 (exp_pos ((141 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1141 : ℝ) / 250), exp_pos (-((1141 : ℝ) / 250))]

lemma cosh_b45730_ub : cosh ((4573 : ℝ) / 1000) ≤ (4842734749 : ℝ) / 100000000 := by
  have exp_frac_b45730 : exp ((573 : ℝ) / 1000) ≤ (177358001 : ℝ) / 100000000 := by
    have ht : ((573 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((573 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((573 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (177358001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4573 : ℝ) / 1000) = exp 4 * exp ((573 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (573 : ℝ) / 1000 = (4573 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4573 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4573 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b45730 (exp_pos ((573 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4573 : ℝ) / 1000), exp_pos (-((4573 : ℝ) / 1000))]

lemma cosh_b45820_ub : cosh ((2291 : ℝ) / 500) ≤ (4886509497 : ℝ) / 100000000 := by
  have exp_frac_b45820 : exp ((291 : ℝ) / 500) ≤ (178961501 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (178961501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2291 : ℝ) / 500) = exp 4 * exp ((291 : ℝ) / 500) := by
    rw [← exp_add, show (4 : ℝ) + (291 : ℝ) / 500 = (2291 : ℝ) / 500 by norm_num]
  have hneg : exp (-((2291 : ℝ) / 500)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2291 : ℝ) / 500) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b45820 (exp_pos ((291 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2291 : ℝ) / 500), exp_pos (-((2291 : ℝ) / 500))]

lemma cosh_b45910_ub : cosh ((4591 : ℝ) / 1000) ≤ (4930677358 : ℝ) / 100000000 := by
  have exp_frac_b45910 : exp ((591 : ℝ) / 1000) ≤ (180579401 : ℝ) / 100000000 := by
    have ht : ((591 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((591 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((591 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (180579401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4591 : ℝ) / 1000) = exp 4 * exp ((591 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (591 : ℝ) / 1000 = (4591 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4591 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4591 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b45910 (exp_pos ((591 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4591 : ℝ) / 1000), exp_pos (-((4591 : ℝ) / 1000))]

lemma cosh_b46000_ub : cosh ((23 : ℝ) / 5) ≤ (4975243792 : ℝ) / 100000000 := by
  have exp_frac_b46000 : exp ((3 : ℝ) / 5) ≤ (182211901 : ℝ) / 100000000 := by
    have ht : ((3 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((3 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((3 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (182211901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((23 : ℝ) / 5) = exp 4 * exp ((3 : ℝ) / 5) := by
    rw [← exp_add, show (4 : ℝ) + (3 : ℝ) / 5 = (23 : ℝ) / 5 by norm_num]
  have hneg : exp (-((23 : ℝ) / 5)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((23 : ℝ) / 5) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b46000 (exp_pos ((3 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((23 : ℝ) / 5), exp_pos (-((23 : ℝ) / 5))]

lemma cosh_b46095_ub : cosh ((9219 : ℝ) / 2000) ≤ (5022725812 : ℝ) / 100000000 := by
  have exp_frac_b46095 : exp ((1219 : ℝ) / 2000) ≤ (183951201 : ℝ) / 100000000 := by
    have ht : ((1219 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1219 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1219 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (183951201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9219 : ℝ) / 2000) = exp 4 * exp ((1219 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1219 : ℝ) / 2000 = (9219 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9219 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9219 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b46095 (exp_pos ((1219 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9219 : ℝ) / 2000), exp_pos (-((9219 : ℝ) / 2000))]

lemma cosh_b46185_ub : cosh ((9237 : ℝ) / 2000) ≤ (5068124881 : ℝ) / 100000000 := by
  have exp_frac_b46185 : exp ((1237 : ℝ) / 2000) ≤ (185614201 : ℝ) / 100000000 := by
    have ht : ((1237 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1237 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1237 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (185614201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9237 : ℝ) / 2000) = exp 4 * exp ((1237 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1237 : ℝ) / 2000 = (9237 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9237 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9237 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b46185 (exp_pos ((1237 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9237 : ℝ) / 2000), exp_pos (-((9237 : ℝ) / 2000))]

lemma cosh_b46275_ub : cosh ((1851 : ℝ) / 400) ≤ (5113936172 : ℝ) / 100000000 := by
  have exp_frac_b46275 : exp ((251 : ℝ) / 400) ≤ (187292301 : ℝ) / 100000000 := by
    have ht : ((251 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((251 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((251 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (187292301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1851 : ℝ) / 400) = exp 4 * exp ((251 : ℝ) / 400) := by
    rw [← exp_add, show (4 : ℝ) + (251 : ℝ) / 400 = (1851 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1851 : ℝ) / 400)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1851 : ℝ) / 400) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b46275 (exp_pos ((251 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1851 : ℝ) / 400), exp_pos (-((1851 : ℝ) / 400))]

lemma cosh_b46365_ub : cosh ((9273 : ℝ) / 2000) ≤ (5160159685 : ℝ) / 100000000 := by
  have exp_frac_b46365 : exp ((1273 : ℝ) / 2000) ≤ (188985501 : ℝ) / 100000000 := by
    have ht : ((1273 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1273 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1273 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (188985501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9273 : ℝ) / 2000) = exp 4 * exp ((1273 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1273 : ℝ) / 2000 = (9273 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9273 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9273 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b46365 (exp_pos ((1273 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9273 : ℝ) / 2000), exp_pos (-((9273 : ℝ) / 2000))]

lemma cosh_b46455_ub : cosh ((9291 : ℝ) / 2000) ≤ (5206803611 : ℝ) / 100000000 := by
  have exp_frac_b46455 : exp ((1291 : ℝ) / 2000) ≤ (190694101 : ℝ) / 100000000 := by
    have ht : ((1291 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1291 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1291 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (190694101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9291 : ℝ) / 2000) = exp 4 * exp ((1291 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1291 : ℝ) / 2000 = (9291 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9291 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9291 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b46455 (exp_pos ((1291 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9291 : ℝ) / 2000), exp_pos (-((9291 : ℝ) / 2000))]

lemma cosh_b46550_ub : cosh ((931 : ℝ) / 200) ≤ (5256494161 : ℝ) / 100000000 := by
  have exp_frac_b46550 : exp ((131 : ℝ) / 200) ≤ (192514301 : ℝ) / 100000000 := by
    have ht : ((131 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((131 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((131 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (192514301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((931 : ℝ) / 200) = exp 4 * exp ((131 : ℝ) / 200) := by
    rw [← exp_add, show (4 : ℝ) + (131 : ℝ) / 200 = (931 : ℝ) / 200 by norm_num]
  have hneg : exp (-((931 : ℝ) / 200)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((931 : ℝ) / 200) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b46550 (exp_pos ((131 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((931 : ℝ) / 200), exp_pos (-((931 : ℝ) / 200))]

lemma cosh_b46640_ub : cosh ((583 : ℝ) / 125) ≤ (5304008940 : ℝ) / 100000000 := by
  have exp_frac_b46640 : exp ((83 : ℝ) / 125) ≤ (194254801 : ℝ) / 100000000 := by
    have ht : ((83 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((83 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((83 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (194254801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((583 : ℝ) / 125) = exp 4 * exp ((83 : ℝ) / 125) := by
    rw [← exp_add, show (4 : ℝ) + (83 : ℝ) / 125 = (583 : ℝ) / 125 by norm_num]
  have hneg : exp (-((583 : ℝ) / 125)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((583 : ℝ) / 125) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b46640 (exp_pos ((83 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((583 : ℝ) / 125), exp_pos (-((583 : ℝ) / 125))]

lemma cosh_b46730_ub : cosh ((4673 : ℝ) / 1000) ≤ (5351949592 : ℝ) / 100000000 := by
  have exp_frac_b46730 : exp ((673 : ℝ) / 1000) ≤ (196010901 : ℝ) / 100000000 := by
    have ht : ((673 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((673 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((673 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (196010901 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4673 : ℝ) / 1000) = exp 4 * exp ((673 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (673 : ℝ) / 1000 = (4673 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4673 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4673 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b46730 (exp_pos ((673 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4673 : ℝ) / 1000), exp_pos (-((4673 : ℝ) / 1000))]

lemma cosh_b46820_ub : cosh ((2341 : ℝ) / 500) ≤ (5400327036 : ℝ) / 100000000 := by
  have exp_frac_b46820 : exp ((341 : ℝ) / 500) ≤ (197783001 : ℝ) / 100000000 := by
    have ht : ((341 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((341 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((341 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (197783001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2341 : ℝ) / 500) = exp 4 * exp ((341 : ℝ) / 500) := by
    rw [← exp_add, show (4 : ℝ) + (341 : ℝ) / 500 = (2341 : ℝ) / 500 by norm_num]
  have hneg : exp (-((2341 : ℝ) / 500)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2341 : ℝ) / 500) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b46820 (exp_pos ((341 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2341 : ℝ) / 500), exp_pos (-((2341 : ℝ) / 500))]

lemma cosh_b46910_ub : cosh ((4691 : ℝ) / 1000) ≤ (5449141272 : ℝ) / 100000000 := by
  have exp_frac_b46910 : exp ((691 : ℝ) / 1000) ≤ (199571101 : ℝ) / 100000000 := by
    have ht : ((691 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((691 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((691 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (199571101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4691 : ℝ) / 1000) = exp 4 * exp ((691 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (691 : ℝ) / 1000 = (4691 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4691 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4691 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b46910 (exp_pos ((691 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4691 : ℝ) / 1000), exp_pos (-((4691 : ℝ) / 1000))]

lemma cosh_b47000_ub : cosh ((47 : ℝ) / 10) ≤ (5498395030 : ℝ) / 100000000 := by
  have exp_frac_b47000 : exp ((7 : ℝ) / 10) ≤ (201375301 : ℝ) / 100000000 := by
    have ht : ((7 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((7 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((7 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (201375301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((47 : ℝ) / 10) = exp 4 * exp ((7 : ℝ) / 10) := by
    rw [← exp_add, show (4 : ℝ) + (7 : ℝ) / 10 = (47 : ℝ) / 10 by norm_num]
  have hneg : exp (-((47 : ℝ) / 10)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((47 : ℝ) / 10) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b47000 (exp_pos ((7 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((47 : ℝ) / 10), exp_pos (-((47 : ℝ) / 10))]

lemma cosh_b47095_ub : cosh ((9419 : ℝ) / 2000) ≤ (5550870129 : ℝ) / 100000000 := by
  have exp_frac_b47095 : exp ((1419 : ℝ) / 2000) ≤ (203297501 : ℝ) / 100000000 := by
    have ht : ((1419 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1419 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1419 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (203297501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9419 : ℝ) / 2000) = exp 4 * exp ((1419 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1419 : ℝ) / 2000 = (9419 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9419 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9419 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b47095 (exp_pos ((1419 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9419 : ℝ) / 2000), exp_pos (-((9419 : ℝ) / 2000))]

lemma cosh_b47185_ub : cosh ((9437 : ℝ) / 2000) ≤ (5601043880 : ℝ) / 100000000 := by
  have exp_frac_b47185 : exp ((1437 : ℝ) / 2000) ≤ (205135401 : ℝ) / 100000000 := by
    have ht : ((1437 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1437 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1437 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (205135401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9437 : ℝ) / 2000) = exp 4 * exp ((1437 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1437 : ℝ) / 2000 = (9437 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9437 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9437 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b47185 (exp_pos ((1437 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9437 : ℝ) / 2000), exp_pos (-((9437 : ℝ) / 2000))]

lemma cosh_b47275_ub : cosh ((1891 : ℝ) / 400) ≤ (5651673533 : ℝ) / 100000000 := by
  have exp_frac_b47275 : exp ((291 : ℝ) / 400) ≤ (206990001 : ℝ) / 100000000 := by
    have ht : ((291 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((291 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((291 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (206990001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1891 : ℝ) / 400) = exp 4 * exp ((291 : ℝ) / 400) := by
    rw [← exp_add, show (4 : ℝ) + (291 : ℝ) / 400 = (1891 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1891 : ℝ) / 400)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1891 : ℝ) / 400) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b47275 (exp_pos ((291 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1891 : ℝ) / 400), exp_pos (-((1891 : ℝ) / 400))]

lemma cosh_b47365_ub : cosh ((9473 : ℝ) / 2000) ≤ (5702759087 : ℝ) / 100000000 := by
  have exp_frac_b47365 : exp ((1473 : ℝ) / 2000) ≤ (208861301 : ℝ) / 100000000 := by
    have ht : ((1473 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1473 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1473 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (208861301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9473 : ℝ) / 2000) = exp 4 * exp ((1473 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1473 : ℝ) / 2000 = (9473 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9473 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9473 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b47365 (exp_pos ((1473 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9473 : ℝ) / 2000), exp_pos (-((9473 : ℝ) / 2000))]

lemma cosh_b47455_ub : cosh ((9491 : ℝ) / 2000) ≤ (5754308733 : ℝ) / 100000000 := by
  have exp_frac_b47455 : exp ((1491 : ℝ) / 2000) ≤ (210749601 : ℝ) / 100000000 := by
    have ht : ((1491 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1491 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1491 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (210749601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9491 : ℝ) / 2000) = exp 4 * exp ((1491 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1491 : ℝ) / 2000 = (9491 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9491 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9491 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b47455 (exp_pos ((1491 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9491 : ℝ) / 2000), exp_pos (-((9491 : ℝ) / 2000))]

lemma cosh_b47550_ub : cosh ((951 : ℝ) / 200) ≤ (5809224407 : ℝ) / 100000000 := by
  have exp_frac_b47550 : exp ((151 : ℝ) / 200) ≤ (212761201 : ℝ) / 100000000 := by
    have ht : ((151 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((151 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((151 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (212761201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((951 : ℝ) / 200) = exp 4 * exp ((151 : ℝ) / 200) := by
    rw [← exp_add, show (4 : ℝ) + (151 : ℝ) / 200 = (951 : ℝ) / 200 by norm_num]
  have hneg : exp (-((951 : ℝ) / 200)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((951 : ℝ) / 200) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b47550 (exp_pos ((151 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((951 : ℝ) / 200), exp_pos (-((951 : ℝ) / 200))]

lemma cosh_b47640_ub : cosh ((1191 : ℝ) / 250) ≤ (5861734995 : ℝ) / 100000000 := by
  have exp_frac_b47640 : exp ((191 : ℝ) / 250) ≤ (214684701 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (214684701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1191 : ℝ) / 250) = exp 4 * exp ((191 : ℝ) / 250) := by
    rw [← exp_add, show (4 : ℝ) + (191 : ℝ) / 250 = (1191 : ℝ) / 250 by norm_num]
  have hneg : exp (-((1191 : ℝ) / 250)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1191 : ℝ) / 250) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b47640 (exp_pos ((191 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1191 : ℝ) / 250), exp_pos (-((1191 : ℝ) / 250))]

lemma cosh_b47730_ub : cosh ((4773 : ℝ) / 1000) ≤ (5914720595 : ℝ) / 100000000 := by
  have exp_frac_b47730 : exp ((773 : ℝ) / 1000) ≤ (216625601 : ℝ) / 100000000 := by
    have ht : ((773 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((773 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((773 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (216625601 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4773 : ℝ) / 1000) = exp 4 * exp ((773 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (773 : ℝ) / 1000 = (4773 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4773 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4773 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b47730 (exp_pos ((773 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4773 : ℝ) / 1000), exp_pos (-((4773 : ℝ) / 1000))]

lemma cosh_b47820_ub : cosh ((2391 : ℝ) / 500) ≤ (5968183936 : ℝ) / 100000000 := by
  have exp_frac_b47820 : exp ((391 : ℝ) / 500) ≤ (218584001 : ℝ) / 100000000 := by
    have ht : ((391 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((391 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((391 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (218584001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2391 : ℝ) / 500) = exp 4 * exp ((391 : ℝ) / 500) := by
    rw [← exp_add, show (4 : ℝ) + (391 : ℝ) / 500 = (2391 : ℝ) / 500 by norm_num]
  have hneg : exp (-((2391 : ℝ) / 500)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2391 : ℝ) / 500) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b47820 (exp_pos ((391 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2391 : ℝ) / 500), exp_pos (-((2391 : ℝ) / 500))]

lemma cosh_b47910_ub : cosh ((4791 : ℝ) / 1000) ≤ (6022133208 : ℝ) / 100000000 := by
  have exp_frac_b47910 : exp ((791 : ℝ) / 1000) ≤ (220560201 : ℝ) / 100000000 := by
    have ht : ((791 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((791 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((791 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (220560201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4791 : ℝ) / 1000) = exp 4 * exp ((791 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (791 : ℝ) / 1000 = (4791 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4791 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4791 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b47910 (exp_pos ((791 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4791 : ℝ) / 1000), exp_pos (-((4791 : ℝ) / 1000))]

lemma cosh_b48000_ub : cosh ((24 : ℝ) / 5) ≤ (6076568411 : ℝ) / 100000000 := by
  have exp_frac_b48000 : exp ((4 : ℝ) / 5) ≤ (222554201 : ℝ) / 100000000 := by
    have ht : ((4 : ℝ) / 5) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((4 : ℝ) / 5) ^ m / (Nat.factorial m)) +
          ((4 : ℝ) / 5) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (222554201 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((24 : ℝ) / 5) = exp 4 * exp ((4 : ℝ) / 5) := by
    rw [← exp_add, show (4 : ℝ) + (4 : ℝ) / 5 = (24 : ℝ) / 5 by norm_num]
  have hneg : exp (-((24 : ℝ) / 5)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((24 : ℝ) / 5) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b48000 (exp_pos ((4 : ℝ) / 5)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((24 : ℝ) / 5), exp_pos (-((24 : ℝ) / 5))]

lemma cosh_b48095_ub : cosh ((9619 : ℝ) / 2000) ≤ (6134560739 : ℝ) / 100000000 := by
  have exp_frac_b48095 : exp ((1619 : ℝ) / 2000) ≤ (224678501 : ℝ) / 100000000 := by
    have ht : ((1619 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1619 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1619 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (224678501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9619 : ℝ) / 2000) = exp 4 * exp ((1619 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1619 : ℝ) / 2000 = (9619 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9619 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9619 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b48095 (exp_pos ((1619 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9619 : ℝ) / 2000), exp_pos (-((9619 : ℝ) / 2000))]

lemma cosh_b48185_ub : cosh ((9637 : ℝ) / 2000) ≤ (6190011483 : ℝ) / 100000000 := by
  have exp_frac_b48185 : exp ((1637 : ℝ) / 2000) ≤ (226709701 : ℝ) / 100000000 := by
    have ht : ((1637 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1637 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1637 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (226709701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9637 : ℝ) / 2000) = exp 4 * exp ((1637 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1637 : ℝ) / 2000 = (9637 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9637 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9637 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b48185 (exp_pos ((1637 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9637 : ℝ) / 2000), exp_pos (-((9637 : ℝ) / 2000))]

lemma cosh_b48275_ub : cosh ((1931 : ℝ) / 400) ≤ (6245964538 : ℝ) / 100000000 := by
  have exp_frac_b48275 : exp ((331 : ℝ) / 400) ≤ (228759301 : ℝ) / 100000000 := by
    have ht : ((331 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((331 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((331 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (228759301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1931 : ℝ) / 400) = exp 4 * exp ((331 : ℝ) / 400) := by
    rw [← exp_add, show (4 : ℝ) + (331 : ℝ) / 400 = (1931 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1931 : ℝ) / 400)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1931 : ℝ) / 400) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b48275 (exp_pos ((331 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1931 : ℝ) / 400), exp_pos (-((1931 : ℝ) / 400))]

lemma cosh_b48365_ub : cosh ((9673 : ℝ) / 2000) ≤ (6302425364 : ℝ) / 100000000 := by
  have exp_frac_b48365 : exp ((1673 : ℝ) / 2000) ≤ (230827501 : ℝ) / 100000000 := by
    have ht : ((1673 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1673 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1673 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (230827501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9673 : ℝ) / 2000) = exp 4 * exp ((1673 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1673 : ℝ) / 2000 = (9673 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9673 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9673 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b48365 (exp_pos ((1673 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9673 : ℝ) / 2000), exp_pos (-((9673 : ℝ) / 2000))]

lemma cosh_b48455_ub : cosh ((9691 : ℝ) / 2000) ≤ (6359393961 : ℝ) / 100000000 := by
  have exp_frac_b48455 : exp ((1691 : ℝ) / 2000) ≤ (232914301 : ℝ) / 100000000 := by
    have ht : ((1691 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1691 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1691 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (232914301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9691 : ℝ) / 2000) = exp 4 * exp ((1691 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1691 : ℝ) / 2000 = (9691 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9691 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9691 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b48455 (exp_pos ((1691 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9691 : ℝ) / 2000), exp_pos (-((9691 : ℝ) / 2000))]

lemma cosh_b48550_ub : cosh ((971 : ℝ) / 200) ≤ (6420086209 : ℝ) / 100000000 := by
  have exp_frac_b48550 : exp ((171 : ℝ) / 200) ≤ (235137501 : ℝ) / 100000000 := by
    have ht : ((171 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((171 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((171 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (235137501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((971 : ℝ) / 200) = exp 4 * exp ((171 : ℝ) / 200) := by
    rw [← exp_add, show (4 : ℝ) + (171 : ℝ) / 200 = (971 : ℝ) / 200 by norm_num]
  have hneg : exp (-((971 : ℝ) / 200)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((971 : ℝ) / 200) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b48550 (exp_pos ((171 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((971 : ℝ) / 200), exp_pos (-((971 : ℝ) / 200))]

lemma cosh_b48640_ub : cosh ((608 : ℝ) / 125) ≤ (6478119486 : ℝ) / 100000000 := by
  have exp_frac_b48640 : exp ((108 : ℝ) / 125) ≤ (237263301 : ℝ) / 100000000 := by
    have ht : ((108 : ℝ) / 125) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((108 : ℝ) / 125) ^ m / (Nat.factorial m)) +
          ((108 : ℝ) / 125) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (237263301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((608 : ℝ) / 125) = exp 4 * exp ((108 : ℝ) / 125) := by
    rw [← exp_add, show (4 : ℝ) + (108 : ℝ) / 125 = (608 : ℝ) / 125 by norm_num]
  have hneg : exp (-((608 : ℝ) / 125)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((608 : ℝ) / 125) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b48640 (exp_pos ((108 : ℝ) / 125)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((608 : ℝ) / 125), exp_pos (-((608 : ℝ) / 125))]

lemma cosh_b48730_ub : cosh ((4873 : ℝ) / 1000) ≤ (6536676914 : ℝ) / 100000000 := by
  have exp_frac_b48730 : exp ((873 : ℝ) / 1000) ≤ (239408301 : ℝ) / 100000000 := by
    have ht : ((873 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((873 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((873 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (239408301 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4873 : ℝ) / 1000) = exp 4 * exp ((873 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (873 : ℝ) / 1000 = (4873 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4873 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4873 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b48730 (exp_pos ((873 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4873 : ℝ) / 1000), exp_pos (-((4873 : ℝ) / 1000))]

lemma cosh_b48820_ub : cosh ((2441 : ℝ) / 500) ≤ (6595763951 : ℝ) / 100000000 := by
  have exp_frac_b48820 : exp ((441 : ℝ) / 500) ≤ (241572701 : ℝ) / 100000000 := by
    have ht : ((441 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((441 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((441 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (241572701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2441 : ℝ) / 500) = exp 4 * exp ((441 : ℝ) / 500) := by
    rw [← exp_add, show (4 : ℝ) + (441 : ℝ) / 500 = (2441 : ℝ) / 500 by norm_num]
  have hneg : exp (-((2441 : ℝ) / 500)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2441 : ℝ) / 500) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b48820 (exp_pos ((441 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2441 : ℝ) / 500), exp_pos (-((2441 : ℝ) / 500))]

lemma cosh_b48910_ub : cosh ((4891 : ℝ) / 1000) ≤ (6655386059 : ℝ) / 100000000 := by
  have exp_frac_b48910 : exp ((891 : ℝ) / 1000) ≤ (243756701 : ℝ) / 100000000 := by
    have ht : ((891 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((891 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((891 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (243756701 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4891 : ℝ) / 1000) = exp 4 * exp ((891 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (891 : ℝ) / 1000 = (4891 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4891 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4891 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b48910 (exp_pos ((891 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4891 : ℝ) / 1000), exp_pos (-((4891 : ℝ) / 1000))]

lemma cosh_b49000_ub : cosh ((49 : ℝ) / 10) ≤ (6715545968 : ℝ) / 100000000 := by
  have exp_frac_b49000 : exp ((9 : ℝ) / 10) ≤ (245960401 : ℝ) / 100000000 := by
    have ht : ((9 : ℝ) / 10) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((9 : ℝ) / 10) ^ m / (Nat.factorial m)) +
          ((9 : ℝ) / 10) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (245960401 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((49 : ℝ) / 10) = exp 4 * exp ((9 : ℝ) / 10) := by
    rw [← exp_add, show (4 : ℝ) + (9 : ℝ) / 10 = (49 : ℝ) / 10 by norm_num]
  have hneg : exp (-((49 : ℝ) / 10)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((49 : ℝ) / 10) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b49000 (exp_pos ((9 : ℝ) / 10)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((49 : ℝ) / 10), exp_pos (-((49 : ℝ) / 10))]

lemma cosh_b49095_ub : cosh ((9819 : ℝ) / 2000) ≤ (6779637004 : ℝ) / 100000000 := by
  have exp_frac_b49095 : exp ((1819 : ℝ) / 2000) ≤ (248308101 : ℝ) / 100000000 := by
    have ht : ((1819 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1819 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1819 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (248308101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9819 : ℝ) / 2000) = exp 4 * exp ((1819 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1819 : ℝ) / 2000 = (9819 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9819 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9819 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b49095 (exp_pos ((1819 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9819 : ℝ) / 2000), exp_pos (-((9819 : ℝ) / 2000))]

lemma cosh_b49185_ub : cosh ((9837 : ℝ) / 2000) ≤ (6840921651 : ℝ) / 100000000 := by
  have exp_frac_b49185 : exp ((1837 : ℝ) / 2000) ≤ (250553001 : ℝ) / 100000000 := by
    have ht : ((1837 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1837 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1837 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (250553001 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9837 : ℝ) / 2000) = exp 4 * exp ((1837 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1837 : ℝ) / 2000 = (9837 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9837 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9837 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b49185 (exp_pos ((1837 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9837 : ℝ) / 2000), exp_pos (-((9837 : ℝ) / 2000))]

lemma cosh_b49275_ub : cosh ((1971 : ℝ) / 400) ≤ (6902757749 : ℝ) / 100000000 := by
  have exp_frac_b49275 : exp ((371 : ℝ) / 400) ≤ (252818101 : ℝ) / 100000000 := by
    have ht : ((371 : ℝ) / 400) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((371 : ℝ) / 400) ^ m / (Nat.factorial m)) +
          ((371 : ℝ) / 400) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (252818101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1971 : ℝ) / 400) = exp 4 * exp ((371 : ℝ) / 400) := by
    rw [← exp_add, show (4 : ℝ) + (371 : ℝ) / 400 = (1971 : ℝ) / 400 by norm_num]
  have hneg : exp (-((1971 : ℝ) / 400)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1971 : ℝ) / 400) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b49275 (exp_pos ((371 : ℝ) / 400)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1971 : ℝ) / 400), exp_pos (-((1971 : ℝ) / 400))]

lemma cosh_b49365_ub : cosh ((9873 : ℝ) / 2000) ≤ (6965156216 : ℝ) / 100000000 := by
  have exp_frac_b49365 : exp ((1873 : ℝ) / 2000) ≤ (255103801 : ℝ) / 100000000 := by
    have ht : ((1873 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1873 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1873 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (255103801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9873 : ℝ) / 2000) = exp 4 * exp ((1873 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1873 : ℝ) / 2000 = (9873 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9873 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9873 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b49365 (exp_pos ((1873 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9873 : ℝ) / 2000), exp_pos (-((9873 : ℝ) / 2000))]

lemma cosh_b49455_ub : cosh ((9891 : ℝ) / 2000) ≤ (7028117053 : ℝ) / 100000000 := by
  have exp_frac_b49455 : exp ((1891 : ℝ) / 2000) ≤ (257410101 : ℝ) / 100000000 := by
    have ht : ((1891 : ℝ) / 2000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((1891 : ℝ) / 2000) ^ m / (Nat.factorial m)) +
          ((1891 : ℝ) / 2000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (257410101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((9891 : ℝ) / 2000) = exp 4 * exp ((1891 : ℝ) / 2000) := by
    rw [← exp_add, show (4 : ℝ) + (1891 : ℝ) / 2000 = (9891 : ℝ) / 2000 by norm_num]
  have hneg : exp (-((9891 : ℝ) / 2000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((9891 : ℝ) / 2000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b49455 (exp_pos ((1891 : ℝ) / 2000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((9891 : ℝ) / 2000), exp_pos (-((9891 : ℝ) / 2000))]

lemma cosh_b49550_ub : cosh ((991 : ℝ) / 200) ≤ (7095191924 : ℝ) / 100000000 := by
  have exp_frac_b49550 : exp ((191 : ℝ) / 200) ≤ (259867101 : ℝ) / 100000000 := by
    have ht : ((191 : ℝ) / 200) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((191 : ℝ) / 200) ^ m / (Nat.factorial m)) +
          ((191 : ℝ) / 200) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (259867101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((991 : ℝ) / 200) = exp 4 * exp ((191 : ℝ) / 200) := by
    rw [← exp_add, show (4 : ℝ) + (191 : ℝ) / 200 = (991 : ℝ) / 200 by norm_num]
  have hneg : exp (-((991 : ℝ) / 200)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((991 : ℝ) / 200) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b49550 (exp_pos ((191 : ℝ) / 200)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((991 : ℝ) / 200), exp_pos (-((991 : ℝ) / 200))]

lemma cosh_b49640_ub : cosh ((1241 : ℝ) / 250) ≤ (7159329370 : ℝ) / 100000000 := by
  have exp_frac_b49640 : exp ((241 : ℝ) / 250) ≤ (262216501 : ℝ) / 100000000 := by
    have ht : ((241 : ℝ) / 250) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((241 : ℝ) / 250) ^ m / (Nat.factorial m)) +
          ((241 : ℝ) / 250) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (262216501 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((1241 : ℝ) / 250) = exp 4 * exp ((241 : ℝ) / 250) := by
    rw [← exp_add, show (4 : ℝ) + (241 : ℝ) / 250 = (1241 : ℝ) / 250 by norm_num]
  have hneg : exp (-((1241 : ℝ) / 250)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((1241 : ℝ) / 250) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b49640 (exp_pos ((241 : ℝ) / 250)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((1241 : ℝ) / 250), exp_pos (-((1241 : ℝ) / 250))]

lemma cosh_b49730_ub : cosh ((4973 : ℝ) / 1000) ≤ (7224045564 : ℝ) / 100000000 := by
  have exp_frac_b49730 : exp ((973 : ℝ) / 1000) ≤ (264587101 : ℝ) / 100000000 := by
    have ht : ((973 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((973 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((973 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (264587101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4973 : ℝ) / 1000) = exp 4 * exp ((973 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (973 : ℝ) / 1000 = (4973 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4973 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4973 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b49730 (exp_pos ((973 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4973 : ℝ) / 1000), exp_pos (-((4973 : ℝ) / 1000))]

lemma cosh_b49820_ub : cosh ((2491 : ℝ) / 500) ≤ (7289345968 : ℝ) / 100000000 := by
  have exp_frac_b49820 : exp ((491 : ℝ) / 500) ≤ (266979101 : ℝ) / 100000000 := by
    have ht : ((491 : ℝ) / 500) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((491 : ℝ) / 500) ^ m / (Nat.factorial m)) +
          ((491 : ℝ) / 500) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (266979101 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((2491 : ℝ) / 500) = exp 4 * exp ((491 : ℝ) / 500) := by
    rw [← exp_add, show (4 : ℝ) + (491 : ℝ) / 500 = (2491 : ℝ) / 500 by norm_num]
  have hneg : exp (-((2491 : ℝ) / 500)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((2491 : ℝ) / 500) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b49820 (exp_pos ((491 : ℝ) / 500)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((2491 : ℝ) / 500), exp_pos (-((2491 : ℝ) / 500))]

lemma cosh_b49910_ub : cosh ((4991 : ℝ) / 1000) ≤ (7355238771 : ℝ) / 100000000 := by
  have exp_frac_b49910 : exp ((991 : ℝ) / 1000) ≤ (269392801 : ℝ) / 100000000 := by
    have ht : ((991 : ℝ) / 1000) ≤ 1 := by norm_num
    have hupper := Real.exp_bound' (by norm_num) ht (n := 8) (by norm_num)
    have htaylor :
        (∑ m ∈ Finset.range 8, ((991 : ℝ) / 1000) ^ m / (Nat.factorial m)) +
          ((991 : ℝ) / 1000) ^ 8 * (8 + 1) / (Nat.factorial 8 * 8) ≤
          (269392801 : ℝ) / 100000000 := by
      simp [Finset.sum_range_succ, Nat.factorial]
      norm_num
    linarith [hupper, htaylor]
  have hexp : exp ((4991 : ℝ) / 1000) = exp 4 * exp ((991 : ℝ) / 1000) := by
    rw [← exp_add, show (4 : ℝ) + (991 : ℝ) / 1000 = (4991 : ℝ) / 1000 by norm_num]
  have hneg : exp (-((4991 : ℝ) / 1000)) ≤ (19 : ℝ) / 1000 := by
    exact (exp_le_exp_of_le (by norm_num : -((4991 : ℝ) / 1000) ≤ -(4 : ℝ))).trans exp_neg_four_le
  rw [cosh_eq]
  have hmul := mul_le_mul exp_four_le exp_frac_b49910 (exp_pos ((991 : ℝ) / 1000)).le (by norm_num)
  nlinarith [hmul, hneg, hexp, exp_pos ((4991 : ℝ) / 1000), exp_pos (-((4991 : ℝ) / 1000))]

lemma cosh_b50000_ub : cosh ((5 : ℝ) / 1) ≤ (7421100001 : ℝ) / 100000000 := by
  rw [show (5 : ℝ) / 1 = (5 : ℝ) by norm_num]
  exact (cosh_five_le).trans (by norm_num)

end UgpLean.Substrate.PhiMDLFluctuationSpectrum
