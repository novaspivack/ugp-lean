import Mathlib.Analysis.Complex.ExponentialBounds
import Mathlib.Analysis.SpecialFunctions.Log.Basic
import Mathlib.Analysis.SpecialFunctions.Log.Deriv
import Mathlib.NumberTheory.Real.GoldenRatio
import Mathlib.Analysis.SpecialFunctions.Trigonometric.Basic
import Mathlib.Analysis.Real.Pi.Bounds
import UgpLean.ElegantKernel
import UgpLean.ElegantKernel.Unconditional.KConstFullClosure
import UgpLean.ElegantKernel.Unconditional.KLFullClosure
import UgpLean.ElegantKernel.Unconditional.KGenFullClosure

namespace UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval

open Real
open UgpLean.ElegantKernel.Unconditional.KConstFullClosure
open UgpLean.ElegantKernel.Unconditional.KLFullClosure
open UgpLean.ElegantKernel.Unconditional.KGenFullClosure

/-! Interval bounds for log ratios used in UCL mass ordering. -/

private lemma log_two_lo : (6931471803 : ℝ) / 10^10 < Real.log 2 := by
  have h : (6931471803 : ℝ) / 10^10 = (0.6931471803 : ℝ) := by norm_num
  rw [h]
  exact Real.log_two_gt_d9
private lemma log_two_hi : Real.log 2 < (6931471808 : ℝ) / 10^10 := by
  have h : (6931471808 : ℝ) / 10^10 = (0.6931471808 : ℝ) := by norm_num
  rw [h]
  exact Real.log_two_lt_d9

private lemma log_73_decomp : Real.log 73 = 6 * Real.log 2 + Real.log (73 / 64 : ℝ) := by
  have hpow : (64 : ℝ) * (73 / 64 : ℝ) = (73 : ℝ) := by norm_num
  rw [← hpow, Real.log_mul (by norm_num) (by norm_num), show (64 : ℝ) = (2 : ℝ) ^ 6 by norm_num, Real.log_pow]
  ring_nf

private lemma log_73_tail_eq : Real.log (73 / 64 : ℝ) = Real.log (1 + (9 : ℝ) / 64) := by
  field_simp; ring_nf

private lemma log_73_tail_lo : (18 : ℝ) / (137) < Real.log (1 + (9 : ℝ) / 64) := by
  have hx : 0 < (9 : ℝ) / 64 := by norm_num
  have hform : 2 * ((9 : ℝ) / 64) / ((9 : ℝ) / 64 + 2) = (18 : ℝ) / (137) := by field_simp; ring
  rw [← hform]
  exact Real.lt_log_one_add_of_pos hx

private lemma log_73_tail_hi : Real.log (1 + (9 : ℝ) / 64) < (9 : ℝ) / 64 := by
  have hx : 0 < (9 : ℝ) / 64 := by norm_num
  have h1 : (1 : ℝ) + (9 : ℝ) / 64 ≠ 1 := by norm_num
  have := Real.log_lt_sub_one_of_pos (by norm_num : 0 < 1 + (9 : ℝ) / 64) h1
  linarith

theorem log_73_lo : (5877669822066 : ℝ) / 1370000000000 < Real.log 73 := by
  rw [log_73_decomp, log_73_tail_eq]
  have hklo : (6 : ℝ) * ((6931471803 : ℝ) / 10^10) ≤ 6 * Real.log 2 := by
    nlinarith [log_two_lo]
  have htail := log_73_tail_lo
  linarith

theorem log_73_hi : Real.log 73 < (2751685174272 : ℝ) / 640000000000 := by
  rw [log_73_decomp, log_73_tail_eq]
  have hkhi : 6 * Real.log 2 ≤ (6 : ℝ) * ((6931471808 : ℝ) / 10^10) := by
    nlinarith [log_two_hi]
  have htail := log_73_tail_hi
  linarith

private lemma log_823_decomp : Real.log 823 = 9 * Real.log 2 + Real.log (823 / 512 : ℝ) := by
  have hpow : (512 : ℝ) * (823 / 512 : ℝ) = (823 : ℝ) := by norm_num
  rw [← hpow, Real.log_mul (by norm_num) (by norm_num), show (512 : ℝ) = (2 : ℝ) ^ 9 by norm_num, Real.log_pow]
  ring_nf

private lemma log_823_tail_eq : Real.log (823 / 512 : ℝ) = Real.log (1 + (311 : ℝ) / 512) := by
  field_simp; ring_nf

private lemma log_823_tail_lo : (622 : ℝ) / (1335) < Real.log (1 + (311 : ℝ) / 512) := by
  have hx : 0 < (311 : ℝ) / 512 := by norm_num
  have hform : 2 * ((311 : ℝ) / 512) / ((311 : ℝ) / 512 + 2) = (622 : ℝ) / (1335) := by field_simp; ring
  rw [← hform]
  exact Real.lt_log_one_add_of_pos hx

private lemma log_823_tail_hi : Real.log (1 + (311 : ℝ) / 512) < (311 : ℝ) / 512 := by
  have hx : 0 < (311 : ℝ) / 512 := by norm_num
  have h1 : (1 : ℝ) + (311 : ℝ) / 512 ≠ 1 := by norm_num
  have := Real.log_lt_sub_one_of_pos (by norm_num : 0 < 1 + (311 : ℝ) / 512) h1
  linarith

theorem log_823_lo : (89501633713045 : ℝ) / 13350000000000 < Real.log 823 := by
  rw [log_823_decomp, log_823_tail_eq]
  have hklo : (9 : ℝ) * ((6931471803 : ℝ) / 10^10) ≤ 9 * Real.log 2 := by
    nlinarith [log_two_lo]
  have htail := log_823_tail_lo
  linarith

theorem log_823_hi : Real.log 823 < (35050222091264 : ℝ) / 5120000000000 := by
  rw [log_823_decomp, log_823_tail_eq]
  have hkhi : 9 * Real.log 2 ≤ (9 : ℝ) * ((6931471808 : ℝ) / 10^10) := by
    nlinarith [log_two_hi]
  have htail := log_823_tail_hi
  linarith

private lemma log_42_decomp : Real.log 42 = 5 * Real.log 2 + Real.log (42 / 32 : ℝ) := by
  have hpow : (32 : ℝ) * (42 / 32 : ℝ) = (42 : ℝ) := by norm_num
  rw [← hpow, Real.log_mul (by norm_num) (by norm_num), show (32 : ℝ) = (2 : ℝ) ^ 5 by norm_num, Real.log_pow]
  ring_nf

private lemma log_42_tail_eq : Real.log (42 / 32 : ℝ) = Real.log (1 + (10 : ℝ) / 32) := by
  field_simp; ring_nf

private lemma log_42_tail_lo : (20 : ℝ) / (74) < Real.log (1 + (10 : ℝ) / 32) := by
  have hx : 0 < (10 : ℝ) / 32 := by norm_num
  have hform : 2 * ((10 : ℝ) / 32) / ((10 : ℝ) / 32 + 2) = (20 : ℝ) / (74) := by field_simp; ring
  rw [← hform]
  exact Real.lt_log_one_add_of_pos hx

private lemma log_42_tail_hi : Real.log (1 + (10 : ℝ) / 32) < (10 : ℝ) / 32 := by
  have hx : 0 < (10 : ℝ) / 32 := by norm_num
  have h1 : (1 : ℝ) + (10 : ℝ) / 32 ≠ 1 := by norm_num
  have := Real.log_lt_sub_one_of_pos (by norm_num : 0 < 1 + (10 : ℝ) / 32) h1
  linarith

theorem log_42_lo : (2764644567110 : ℝ) / 740000000000 < Real.log 42 := by
  rw [log_42_decomp, log_42_tail_eq]
  have hklo : (5 : ℝ) * ((6931471803 : ℝ) / 10^10) ≤ 5 * Real.log 2 := by
    nlinarith [log_two_lo]
  have htail := log_42_tail_lo
  linarith

theorem log_42_hi : Real.log 42 < (1209035489280 : ℝ) / 320000000000 := by
  rw [log_42_decomp, log_42_tail_eq]
  have hkhi : 5 * Real.log 2 ≤ (5 : ℝ) * ((6931471808 : ℝ) / 10^10) := by
    nlinarith [log_two_hi]
  have htail := log_42_tail_hi
  linarith

private lemma log_1023_decomp : Real.log 1023 = 9 * Real.log 2 + Real.log (1023 / 512 : ℝ) := by
  have hpow : (512 : ℝ) * (1023 / 512 : ℝ) = (1023 : ℝ) := by norm_num
  rw [← hpow, Real.log_mul (by norm_num) (by norm_num), show (512 : ℝ) = (2 : ℝ) ^ 9 by norm_num, Real.log_pow]
  ring_nf

private lemma log_1023_tail_eq : Real.log (1023 / 512 : ℝ) = Real.log (1 + (511 : ℝ) / 512) := by
  field_simp; ring_nf

private lemma log_1023_tail_lo : (1022 : ℝ) / (1535) < Real.log (1 + (511 : ℝ) / 512) := by
  have hx : 0 < (511 : ℝ) / 512 := by norm_num
  have hform : 2 * ((511 : ℝ) / 512) / ((511 : ℝ) / 512 + 2) = (1022 : ℝ) / (1535) := by field_simp; ring
  rw [← hform]
  exact Real.lt_log_one_add_of_pos hx

private lemma log_1023_tail_hi : Real.log (1 + (511 : ℝ) / 512) < (511 : ℝ) / 512 := by
  have hx : 0 < (511 : ℝ) / 512 := by norm_num
  have h1 : (1 : ℝ) + (511 : ℝ) / 512 ≠ 1 := by norm_num
  have := Real.log_lt_sub_one_of_pos (by norm_num : 0 < 1 + (511 : ℝ) / 512) h1
  linarith

theorem log_1023_lo : (105978282958445 : ℝ) / 15350000000000 < Real.log 1023 := by
  rw [log_1023_decomp, log_1023_tail_eq]
  have hklo : (9 : ℝ) * ((6931471803 : ℝ) / 10^10) ≤ 9 * Real.log 2 := by
    nlinarith [log_two_lo]
  have htail := log_1023_tail_lo
  linarith

theorem log_1023_hi : Real.log 1023 < (37050222091264 : ℝ) / 5120000000000 := by
  rw [log_1023_decomp, log_1023_tail_eq]
  have hkhi : 9 * Real.log 2 ≤ (9 : ℝ) * ((6931471808 : ℝ) / 10^10) := by
    nlinarith [log_two_hi]
  have htail := log_1023_tail_hi
  linarith

private lemma log_275_decomp : Real.log 275 = 8 * Real.log 2 + Real.log (275 / 256 : ℝ) := by
  have hpow : (256 : ℝ) * (275 / 256 : ℝ) = (275 : ℝ) := by norm_num
  rw [← hpow, Real.log_mul (by norm_num) (by norm_num), show (256 : ℝ) = (2 : ℝ) ^ 8 by norm_num, Real.log_pow]
  ring_nf

private lemma log_275_tail_eq : Real.log (275 / 256 : ℝ) = Real.log (1 + (19 : ℝ) / 256) := by
  field_simp; ring_nf

private lemma log_275_tail_lo : (38 : ℝ) / (531) < Real.log (1 + (19 : ℝ) / 256) := by
  have hx : 0 < (19 : ℝ) / 256 := by norm_num
  have hform : 2 * ((19 : ℝ) / 256) / ((19 : ℝ) / 256 + 2) = (38 : ℝ) / (531) := by field_simp; ring
  rw [← hform]
  exact Real.lt_log_one_add_of_pos hx

private lemma log_275_tail_hi : Real.log (1 + (19 : ℝ) / 256) < (19 : ℝ) / 256 := by
  have hx : 0 < (19 : ℝ) / 256 := by norm_num
  have h1 : (1 : ℝ) + (19 : ℝ) / 256 ≠ 1 := by norm_num
  have := Real.log_lt_sub_one_of_pos (by norm_num : 0 < 1 + (19 : ℝ) / 256) h1
  linarith

theorem log_275_lo : (29824892219144 : ℝ) / 5310000000000 < Real.log 275 := by
  rw [log_275_decomp, log_275_tail_eq]
  have hklo : (8 : ℝ) * ((6931471803 : ℝ) / 10^10) ≤ 8 * Real.log 2 := by
    nlinarith [log_two_lo]
  have htail := log_275_tail_lo
  linarith

theorem log_275_hi : Real.log 275 < (14385654262784 : ℝ) / 2560000000000 := by
  rw [log_275_decomp, log_275_tail_eq]
  have hkhi : 8 * Real.log 2 ≤ (8 : ℝ) * ((6931471808 : ℝ) / 10^10) := by
    nlinarith [log_two_hi]
  have htail := log_275_tail_hi
  linarith

private lemma log_65535_decomp : Real.log 65535 = 15 * Real.log 2 + Real.log (65535 / 32768 : ℝ) := by
  have hpow : (32768 : ℝ) * (65535 / 32768 : ℝ) = (65535 : ℝ) := by norm_num
  rw [← hpow, Real.log_mul (by norm_num) (by norm_num), show (32768 : ℝ) = (2 : ℝ) ^ 15 by norm_num, Real.log_pow]
  ring_nf

private lemma log_65535_tail_eq : Real.log (65535 / 32768 : ℝ) = Real.log (1 + (32767 : ℝ) / 32768) := by
  field_simp; ring_nf

private lemma log_65535_tail_lo : (65534 : ℝ) / (98303) < Real.log (1 + (32767 : ℝ) / 32768) := by
  have hx : 0 < (32767 : ℝ) / 32768 := by norm_num
  have hform : 2 * ((32767 : ℝ) / 32768) / ((32767 : ℝ) / 32768 + 2) = (65534 : ℝ) / (98303) := by field_simp; ring
  rw [← hform]
  exact Real.lt_log_one_add_of_pos hx

private lemma log_65535_tail_hi : Real.log (1 + (32767 : ℝ) / 32768) < (32767 : ℝ) / 32768 := by
  have hx : 0 < (32767 : ℝ) / 32768 := by norm_num
  have h1 : (1 : ℝ) + (32767 : ℝ) / 32768 ≠ 1 := by norm_num
  have := Real.log_lt_sub_one_of_pos (by norm_num : 0 < 1 + (32767 : ℝ) / 32768) h1
  linarith

theorem log_65535_lo : (10876107089754635 : ℝ) / 983030000000000 < Real.log 65535 := by
  rw [log_65535_decomp, log_65535_tail_eq]
  have hklo : (15 : ℝ) * ((6931471803 : ℝ) / 10^10) ≤ 15 * Real.log 2 := by
    nlinarith [log_two_lo]
  have htail := log_65535_tail_lo
  linarith

theorem log_65535_hi : Real.log 65535 < (3734627023068160 : ℝ) / 327680000000000 := by
  rw [log_65535_decomp, log_65535_tail_eq]
  have hkhi : 15 * Real.log 2 ≤ (15 : ℝ) * ((6931471808 : ℝ) / 10^10) := by
    nlinarith [log_two_hi]
  have htail := log_65535_tail_hi
  linarith

private lemma log_9_decomp : Real.log 9 = 3 * Real.log 2 + Real.log (9 / 8 : ℝ) := by
  have hpow : (8 : ℝ) * (9 / 8 : ℝ) = (9 : ℝ) := by norm_num
  rw [← hpow, Real.log_mul (by norm_num) (by norm_num), show (8 : ℝ) = (2 : ℝ) ^ 3 by norm_num, Real.log_pow]
  ring_nf

private lemma log_9_tail_eq : Real.log (9 / 8 : ℝ) = Real.log (1 + (1 : ℝ) / 8) := by
  field_simp; ring_nf

private lemma log_9_tail_lo : (2 : ℝ) / (17) < Real.log (1 + (1 : ℝ) / 8) := by
  have hx : 0 < (1 : ℝ) / 8 := by norm_num
  have hform : 2 * ((1 : ℝ) / 8) / ((1 : ℝ) / 8 + 2) = (2 : ℝ) / (17) := by field_simp; ring
  rw [← hform]
  exact Real.lt_log_one_add_of_pos hx

private lemma log_9_tail_hi : Real.log (1 + (1 : ℝ) / 8) < (1 : ℝ) / 8 := by
  have hx : 0 < (1 : ℝ) / 8 := by norm_num
  have h1 : (1 : ℝ) + (1 : ℝ) / 8 ≠ 1 := by norm_num
  have := Real.log_lt_sub_one_of_pos (by norm_num : 0 < 1 + (1 : ℝ) / 8) h1
  linarith

theorem log_9_lo : (373505061953 : ℝ) / 170000000000 < Real.log 9 := by
  rw [log_9_decomp, log_9_tail_eq]
  have hklo : (3 : ℝ) * ((6931471803 : ℝ) / 10^10) ≤ 3 * Real.log 2 := by
    nlinarith [log_two_lo]
  have htail := log_9_tail_lo
  linarith

theorem log_9_hi : Real.log 9 < (176355323392 : ℝ) / 80000000000 := by
  rw [log_9_decomp, log_9_tail_eq]
  have hkhi : 3 * Real.log 2 ≤ (3 : ℝ) * ((6931471808 : ℝ) / 10^10) := by
    nlinarith [log_two_hi]
  have htail := log_9_tail_hi
  linarith

private lemma log_337920_decomp : Real.log 337920 = 18 * Real.log 2 + Real.log (337920 / 262144 : ℝ) := by
  have hpow : (262144 : ℝ) * (337920 / 262144 : ℝ) = (337920 : ℝ) := by norm_num
  rw [← hpow, Real.log_mul (by norm_num) (by norm_num), show (262144 : ℝ) = (2 : ℝ) ^ 18 by norm_num, Real.log_pow]
  ring_nf

private lemma log_337920_tail_eq : Real.log (337920 / 262144 : ℝ) = Real.log (1 + (75776 : ℝ) / 262144) := by
  field_simp; ring_nf

private lemma log_337920_tail_lo : (151552 : ℝ) / (600064) < Real.log (1 + (75776 : ℝ) / 262144) := by
  have hx : 0 < (75776 : ℝ) / 262144 := by norm_num
  have hform : 2 * ((75776 : ℝ) / 262144) / ((75776 : ℝ) / 262144 + 2) = (151552 : ℝ) / (600064) := by field_simp; ring
  rw [← hform]
  exact Real.lt_log_one_add_of_pos hx

private lemma log_337920_tail_hi : Real.log (1 + (75776 : ℝ) / 262144) < (75776 : ℝ) / 262144 := by
  have hx : 0 < (75776 : ℝ) / 262144 := by norm_num
  have h1 : (1 : ℝ) + (75776 : ℝ) / 262144 ≠ 1 := by norm_num
  have := Real.log_lt_sub_one_of_pos (by norm_num : 0 < 1 + (75776 : ℝ) / 262144) h1
  linarith

theorem log_337920_lo : (76383400527917056 : ℝ) / 6000640000000000 < Real.log 337920 := by
  rw [log_337920_decomp, log_337920_tail_eq]
  have hklo : (18 : ℝ) * ((6931471803 : ℝ) / 10^10) ≤ 18 * Real.log 2 := by
    nlinarith [log_two_lo]
  have htail := log_337920_tail_lo
  linarith

theorem log_337920_hi : Real.log 337920 < (33464547421454336 : ℝ) / 2621440000000000 := by
  rw [log_337920_decomp, log_337920_tail_eq]
  have hkhi : 18 * Real.log 2 ≤ (18 : ℝ) * ((6931471808 : ℝ) / 10^10) := by
    nlinarith [log_two_hi]
  have htail := log_337920_tail_hi
  linarith

private lemma log_5_decomp : Real.log 5 = 2 * Real.log 2 + Real.log (5 / 4 : ℝ) := by
  have hpow : (4 : ℝ) * (5 / 4 : ℝ) = (5 : ℝ) := by norm_num
  rw [← hpow, Real.log_mul (by norm_num) (by norm_num), show (4 : ℝ) = (2 : ℝ) ^ 2 by norm_num, Real.log_pow]
  ring_nf

private lemma log_5_tail_eq : Real.log (5 / 4 : ℝ) = Real.log (1 + (1 : ℝ) / 4) := by
  field_simp; ring_nf

private lemma log_5_tail_lo : (2 : ℝ) / (9) < Real.log (1 + (1 : ℝ) / 4) := by
  have hx : 0 < (1 : ℝ) / 4 := by norm_num
  have hform : 2 * ((1 : ℝ) / 4) / ((1 : ℝ) / 4 + 2) = (2 : ℝ) / (9) := by field_simp; ring
  rw [← hform]
  exact Real.lt_log_one_add_of_pos hx

private lemma log_5_tail_hi : Real.log (1 + (1 : ℝ) / 4) < (1 : ℝ) / 4 := by
  have hx : 0 < (1 : ℝ) / 4 := by norm_num
  have h1 : (1 : ℝ) + (1 : ℝ) / 4 ≠ 1 := by norm_num
  have := Real.log_lt_sub_one_of_pos (by norm_num : 0 < 1 + (1 : ℝ) / 4) h1
  linarith

theorem log_5_lo : (144766492454 : ℝ) / 90000000000 < Real.log 5 := by
  rw [log_5_decomp, log_5_tail_eq]
  have hklo : (2 : ℝ) * ((6931471803 : ℝ) / 10^10) ≤ 2 * Real.log 2 := by
    nlinarith [log_two_lo]
  have htail := log_5_tail_lo
  linarith

theorem log_5_hi : Real.log 5 < (65451774464 : ℝ) / 40000000000 := by
  rw [log_5_decomp, log_5_tail_eq]
  have hkhi : 2 * Real.log 2 ≤ (2 : ℝ) * ((6931471808 : ℝ) / 10^10) := by
    nlinarith [log_two_hi]
  have htail := log_5_tail_hi
  linarith

private lemma log_186_decomp : Real.log 186 = 7 * Real.log 2 + Real.log (186 / 128 : ℝ) := by
  have hpow : (128 : ℝ) * (186 / 128 : ℝ) = (186 : ℝ) := by norm_num
  rw [← hpow, Real.log_mul (by norm_num) (by norm_num), show (128 : ℝ) = (2 : ℝ) ^ 7 by norm_num, Real.log_pow]
  ring_nf

private lemma log_186_tail_eq : Real.log (186 / 128 : ℝ) = Real.log (1 + (58 : ℝ) / 128) := by
  field_simp; ring_nf

private lemma log_186_tail_lo : (116 : ℝ) / (314) < Real.log (1 + (58 : ℝ) / 128) := by
  have hx : 0 < (58 : ℝ) / 128 := by norm_num
  have hform : 2 * ((58 : ℝ) / 128) / ((58 : ℝ) / 128 + 2) = (116 : ℝ) / (314) := by field_simp; ring
  rw [← hform]
  exact Real.lt_log_one_add_of_pos hx

private lemma log_186_tail_hi : Real.log (1 + (58 : ℝ) / 128) < (58 : ℝ) / 128 := by
  have hx : 0 < (58 : ℝ) / 128 := by norm_num
  have h1 : (1 : ℝ) + (58 : ℝ) / 128 ≠ 1 := by norm_num
  have := Real.log_lt_sub_one_of_pos (by norm_num : 0 < 1 + (58 : ℝ) / 128) h1
  linarith

theorem log_186_lo : (16395375022994 : ℝ) / 3140000000000 < Real.log 186 := by
  rw [log_186_decomp, log_186_tail_eq]
  have hklo : (7 : ℝ) * ((6931471803 : ℝ) / 10^10) ≤ 7 * Real.log 2 := by
    nlinarith [log_two_lo]
  have htail := log_186_tail_lo
  linarith

theorem log_186_hi : Real.log 186 < (6790598739968 : ℝ) / 1280000000000 := by
  rw [log_186_decomp, log_186_tail_eq]
  have hkhi : 7 * Real.log 2 ≤ (7 : ℝ) * ((6931471808 : ℝ) / 10^10) := by
    nlinarith [log_two_hi]
  have htail := log_186_tail_hi
  linarith

private lemma log_8191_decomp : Real.log 8191 = 12 * Real.log 2 + Real.log (8191 / 4096 : ℝ) := by
  have hpow : (4096 : ℝ) * (8191 / 4096 : ℝ) = (8191 : ℝ) := by norm_num
  rw [← hpow, Real.log_mul (by norm_num) (by norm_num), show (4096 : ℝ) = (2 : ℝ) ^ 12 by norm_num, Real.log_pow]
  ring_nf

private lemma log_8191_tail_eq : Real.log (8191 / 4096 : ℝ) = Real.log (1 + (4095 : ℝ) / 4096) := by
  field_simp; ring_nf

private lemma log_8191_tail_lo : (8190 : ℝ) / (12287) < Real.log (1 + (4095 : ℝ) / 4096) := by
  have hx : 0 < (4095 : ℝ) / 4096 := by norm_num
  have hform : 2 * ((4095 : ℝ) / 4096) / ((4095 : ℝ) / 4096 + 2) = (8190 : ℝ) / (12287) := by field_simp; ring
  rw [← hform]
  exact Real.lt_log_one_add_of_pos hx

private lemma log_8191_tail_hi : Real.log (1 + (4095 : ℝ) / 4096) < (4095 : ℝ) / 4096 := by
  have hx : 0 < (4095 : ℝ) / 4096 := by norm_num
  have h1 : (1 : ℝ) + (4095 : ℝ) / 4096 ≠ 1 := by norm_num
  have := Real.log_lt_sub_one_of_pos (by norm_num : 0 < 1 + (4095 : ℝ) / 4096) h1
  linarith

theorem log_8191_lo : (1103903928521532 : ℝ) / 122870000000000 < Real.log 8191 := by
  rw [log_8191_decomp, log_8191_tail_eq]
  have hklo : (12 : ℝ) * ((6931471803 : ℝ) / 10^10) ≤ 12 * Real.log 2 := by
    nlinarith [log_two_lo]
  have htail := log_8191_tail_lo
  linarith

theorem log_8191_hi : Real.log 8191 < (381645702306816 : ℝ) / 40960000000000 := by
  rw [log_8191_decomp, log_8191_tail_eq]
  have hkhi : 12 * Real.log 2 ≤ (12 : ℝ) * ((6931471808 : ℝ) / 10^10) := by
    nlinarith [log_two_hi]
  have htail := log_8191_tail_hi
  linarith

theorem L_lep1_lo : (5877669822066 : ℝ) / 1370000000000 - (35050222091264 : ℝ) / 5120000000000 < Real.log (73 : ℝ) - Real.log (823 : ℝ) := by
  linarith [log_73_lo, log_823_hi]

theorem L_lep1_hi : Real.log (73 : ℝ) - Real.log (823 : ℝ) < (2751685174272 : ℝ) / 640000000000 - (89501633713045 : ℝ) / 13350000000000 := by
  linarith [log_73_hi, log_823_lo]

theorem L_lep2_lo : (2764644567110 : ℝ) / 740000000000 - (37050222091264 : ℝ) / 5120000000000 < Real.log (42 : ℝ) - Real.log (1023 : ℝ) := by
  linarith [log_42_lo, log_1023_hi]

theorem L_lep2_hi : Real.log (42 : ℝ) - Real.log (1023 : ℝ) < (1209035489280 : ℝ) / 320000000000 - (105978282958445 : ℝ) / 15350000000000 := by
  linarith [log_42_hi, log_1023_lo]

theorem L_lep3_lo : (29824892219144 : ℝ) / 5310000000000 - (3734627023068160 : ℝ) / 327680000000000 < Real.log (275 : ℝ) - Real.log (65535 : ℝ) := by
  linarith [log_275_lo, log_65535_hi]

theorem L_lep3_hi : Real.log (275 : ℝ) - Real.log (65535 : ℝ) < (14385654262784 : ℝ) / 2560000000000 - (10876107089754635 : ℝ) / 983030000000000 := by
  linarith [log_275_hi, log_65535_lo]

theorem L_up1_lo : (373505061953 : ℝ) / 170000000000 - (14385654262784 : ℝ) / 2560000000000 < Real.log (9 : ℝ) - Real.log (275 : ℝ) := by
  linarith [log_9_lo, log_275_hi]

theorem L_up1_hi : Real.log (9 : ℝ) - Real.log (275 : ℝ) < (176355323392 : ℝ) / 80000000000 - (29824892219144 : ℝ) / 5310000000000 := by
  linarith [log_9_hi, log_275_lo]

theorem L_up2_lo : (29824892219144 : ℝ) / 5310000000000 - (3734627023068160 : ℝ) / 327680000000000 < Real.log (275 : ℝ) - Real.log (65535 : ℝ) := by
  linarith [log_275_lo, log_65535_hi]

theorem L_up2_hi : Real.log (275 : ℝ) - Real.log (65535 : ℝ) < (14385654262784 : ℝ) / 2560000000000 - (10876107089754635 : ℝ) / 983030000000000 := by
  linarith [log_275_hi, log_65535_lo]

theorem L_up3_lo : (76383400527917056 : ℝ) / 6000640000000000 < Real.log (337920 : ℝ) - Real.log 1 := by
  simp [Real.log_one]
  exact log_337920_lo

theorem L_up3_hi : Real.log (337920 : ℝ) - Real.log 1 < (33464547421454336 : ℝ) / 2621440000000000 := by
  simp [Real.log_one]
  exact log_337920_hi

theorem L_dn1_lo : (144766492454 : ℝ) / 90000000000 - (1209035489280 : ℝ) / 320000000000 < Real.log (5 : ℝ) - Real.log (42 : ℝ) := by
  linarith [log_5_lo, log_42_hi]

theorem L_dn1_hi : Real.log (5 : ℝ) - Real.log (42 : ℝ) < (65451774464 : ℝ) / 40000000000 - (2764644567110 : ℝ) / 740000000000 := by
  linarith [log_5_hi, log_42_lo]

theorem L_dn2_lo : (16395375022994 : ℝ) / 3140000000000 - (37050222091264 : ℝ) / 5120000000000 < Real.log (186 : ℝ) - Real.log (1023 : ℝ) := by
  linarith [log_186_lo, log_1023_hi]

theorem L_dn2_hi : Real.log (186 : ℝ) - Real.log (1023 : ℝ) < (6790598739968 : ℝ) / 1280000000000 - (105978282958445 : ℝ) / 15350000000000 := by
  linarith [log_186_hi, log_1023_lo]

theorem L_dn3_lo : (1103903928521532 : ℝ) / 122870000000000 - (3734627023068160 : ℝ) / 327680000000000 < Real.log (8191 : ℝ) - Real.log (65535 : ℝ) := by
  linarith [log_8191_lo, log_65535_hi]

theorem L_dn3_hi : Real.log (8191 : ℝ) - Real.log (65535 : ℝ) < (381645702306816 : ℝ) / 40960000000000 - (10876107089754635 : ℝ) / 983030000000000 := by
  linarith [log_8191_hi, log_65535_lo]

end UgpLean.ElegantKernel.Unconditional.UCLMassOrderingInterval
