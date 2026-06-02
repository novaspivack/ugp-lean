import UgpLean.Substrate.SechOverlapIntegralBounds_r5bins

namespace UgpLean.Substrate.PhiMDLFluctuationSpectrum

open Real

lemma sech_ge_of_cosh_le {x C : ℝ} (hC : 0 < C) (hc : cosh x ≤ C) :
    1 / C ≤ sech x := by
  unfold sech
  exact (one_div_le_one_div (cosh_pos x) hC).2 hc

def sech5_meshN : Nat := 550

private lemma cosh5_u_0_le : cosh (1 : ℝ) / 110 ≤ (100004513 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 110) (by norm_num) (by norm_num : ((1 : ℝ) / 110) ≤ ((19 : ℝ) / 2000))
  exact hmono.trans cosh_b95_ub

private lemma cosh5_v_0_le : cosh (1 : ℝ) / 550 ≤ (100000201 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 550) (by norm_num) (by norm_num : ((1 : ℝ) / 550) ≤ ((1 : ℝ) / 500))
  exact hmono.trans cosh_b20_ub

private lemma sech5_pt_0_ge : (9090 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_0_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_0_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_1_le : cosh (1 : ℝ) / 55 ≤ (100017113 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 55) (by norm_num) (by norm_num : ((1 : ℝ) / 55) ≤ ((37 : ℝ) / 2000))
  exact hmono.trans cosh_b185_ub

private lemma cosh5_v_1_le : cosh (1 : ℝ) / 275 ≤ (100000801 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 275) (by norm_num) (by norm_num : ((1 : ℝ) / 275) ≤ ((1 : ℝ) / 250))
  exact hmono.trans cosh_b40_ub

private lemma sech5_pt_1_ge : (9089 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_1_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_1_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_2_le : cosh (3 : ℝ) / 110 ≤ (100037815 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 110) (by norm_num) (by norm_num : ((3 : ℝ) / 110) ≤ ((11 : ℝ) / 400))
  exact hmono.trans cosh_b275_ub

private lemma cosh5_v_2_le : cosh (3 : ℝ) / 550 ≤ (100001513 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 550) (by norm_num) (by norm_num : ((3 : ℝ) / 550) ≤ ((11 : ℝ) / 2000))
  exact hmono.trans cosh_b55_ub

private lemma sech5_pt_2_ge : (9087 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_2_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_2_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_3_le : cosh (2 : ℝ) / 55 ≤ (100066620 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((2 : ℝ) / 55) (by norm_num) (by norm_num : ((2 : ℝ) / 55) ≤ ((73 : ℝ) / 2000))
  exact hmono.trans cosh_b365_ub

private lemma cosh5_v_3_le : cosh (2 : ℝ) / 275 ≤ (100002813 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((2 : ℝ) / 275) (by norm_num) (by norm_num : ((2 : ℝ) / 275) ≤ ((3 : ℝ) / 400))
  exact hmono.trans cosh_b75_ub

private lemma sech5_pt_3_ge : (9084 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (2 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_3_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_3_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_4_le : cosh (1 : ℝ) / 22 ≤ (100103531 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 22) (by norm_num) (by norm_num : ((1 : ℝ) / 22) ≤ ((91 : ℝ) / 2000))
  exact hmono.trans cosh_b455_ub

private lemma cosh5_v_4_le : cosh (1 : ℝ) / 110 ≤ (100004513 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 110) (by norm_num) (by norm_num : ((1 : ℝ) / 110) ≤ ((19 : ℝ) / 2000))
  exact hmono.trans cosh_b95_ub

private lemma sech5_pt_4_ge : (9081 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_4_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_4_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_5_le : cosh (3 : ℝ) / 55 ≤ (100151289 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 55) (by norm_num) (by norm_num : ((3 : ℝ) / 55) ≤ ((11 : ℝ) / 200))
  exact hmono.trans cosh_b550_ub

private lemma cosh5_v_5_le : cosh (3 : ℝ) / 275 ≤ (100006051 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 275) (by norm_num) (by norm_num : ((3 : ℝ) / 275) ≤ ((11 : ℝ) / 1000))
  exact hmono.trans cosh_b110_ub

private lemma sech5_pt_5_ge : (9076 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_5_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_5_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_6_le : cosh (7 : ℝ) / 110 ≤ (100204870 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 110) (by norm_num) (by norm_num : ((7 : ℝ) / 110) ≤ ((8 : ℝ) / 125))
  exact hmono.trans cosh_b640_ub

private lemma cosh5_v_6_le : cosh (7 : ℝ) / 550 ≤ (100008451 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 550) (by norm_num) (by norm_num : ((7 : ℝ) / 550) ≤ ((13 : ℝ) / 1000))
  exact hmono.trans cosh_b130_ub

private lemma sech5_pt_6_ge : (9071 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_6_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_6_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_7_le : cosh (4 : ℝ) / 55 ≤ (100266569 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((4 : ℝ) / 55) (by norm_num) (by norm_num : ((4 : ℝ) / 55) ≤ ((73 : ℝ) / 1000))
  exact hmono.trans cosh_b730_ub

private lemma cosh5_v_7_le : cosh (4 : ℝ) / 275 ≤ (100011251 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((4 : ℝ) / 275) (by norm_num) (by norm_num : ((4 : ℝ) / 275) ≤ ((3 : ℝ) / 200))
  exact hmono.trans cosh_b150_ub

private lemma sech5_pt_7_ge : (9065 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (4 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_7_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_7_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_8_le : cosh (9 : ℝ) / 110 ≤ (100336389 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 110) (by norm_num) (by norm_num : ((9 : ℝ) / 110) ≤ ((41 : ℝ) / 500))
  exact hmono.trans cosh_b820_ub

private lemma cosh5_v_8_le : cosh (9 : ℝ) / 550 ≤ (100013613 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 550) (by norm_num) (by norm_num : ((9 : ℝ) / 550) ≤ ((33 : ℝ) / 2000))
  exact hmono.trans cosh_b165_ub

private lemma sech5_pt_8_ge : (9059 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_8_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_8_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_9_le : cosh (1 : ℝ) / 11 ≤ (100414336 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 11) (by norm_num) (by norm_num : ((1 : ℝ) / 11) ≤ ((91 : ℝ) / 1000))
  exact hmono.trans cosh_b910_ub

private lemma cosh5_v_9_le : cosh (1 : ℝ) / 55 ≤ (100017113 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 55) (by norm_num) (by norm_num : ((1 : ℝ) / 55) ≤ ((37 : ℝ) / 2000))
  exact hmono.trans cosh_b185_ub

private lemma sech5_pt_9_ge : (9051 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_9_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_9_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_10_le : cosh (1 : ℝ) / 10 ≤ (100500417 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 10) (by norm_num) (by norm_num : ((1 : ℝ) / 10) ≤ ((1 : ℝ) / 10))
  exact hmono.trans cosh_b1000_ub

private lemma cosh5_v_10_le : cosh (1 : ℝ) / 50 ≤ (100020001 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 50) (by norm_num) (by norm_num : ((1 : ℝ) / 50) ≤ ((1 : ℝ) / 50))
  exact hmono.trans cosh_b200_ub

private lemma sech5_pt_10_ge : (9043 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_10_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_10_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_11_le : cosh (6 : ℝ) / 55 ≤ (100600112 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((6 : ℝ) / 55) (by norm_num) (by norm_num : ((6 : ℝ) / 55) ≤ ((219 : ℝ) / 2000))
  exact hmono.trans cosh_b1095_ub

private lemma cosh5_v_11_le : cosh (6 : ℝ) / 275 ≤ (100024201 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((6 : ℝ) / 275) (by norm_num) (by norm_num : ((6 : ℝ) / 275) ≤ ((11 : ℝ) / 500))
  exact hmono.trans cosh_b220_ub

private lemma sech5_pt_11_ge : (9034 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (6 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_11_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_11_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_12_le : cosh (13 : ℝ) / 110 ≤ (100702935 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((13 : ℝ) / 110) (by norm_num) (by norm_num : ((13 : ℝ) / 110) ≤ ((237 : ℝ) / 2000))
  exact hmono.trans cosh_b1185_ub

private lemma cosh5_v_12_le : cosh (13 : ℝ) / 550 ≤ (100028802 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((13 : ℝ) / 550) (by norm_num) (by norm_num : ((13 : ℝ) / 550) ≤ ((3 : ℝ) / 125))
  exact hmono.trans cosh_b240_ub

private lemma sech5_pt_12_ge : (9024 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_12_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_12_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_13_le : cosh (7 : ℝ) / 55 ≤ (100813915 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 55) (by norm_num) (by norm_num : ((7 : ℝ) / 55) ≤ ((51 : ℝ) / 400))
  exact hmono.trans cosh_b1275_ub

private lemma cosh5_v_13_le : cosh (7 : ℝ) / 275 ≤ (100032515 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 275) (by norm_num) (by norm_num : ((7 : ℝ) / 275) ≤ ((51 : ℝ) / 2000))
  exact hmono.trans cosh_b255_ub

private lemma sech5_pt_13_ge : (9014 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_13_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_13_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_14_le : cosh (3 : ℝ) / 22 ≤ (100933060 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 22) (by norm_num) (by norm_num : ((3 : ℝ) / 22) ≤ ((273 : ℝ) / 2000))
  exact hmono.trans cosh_b1365_ub

private lemma cosh5_v_14_le : cosh (3 : ℝ) / 110 ≤ (100037815 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 110) (by norm_num) (by norm_num : ((3 : ℝ) / 110) ≤ ((11 : ℝ) / 400))
  exact hmono.trans cosh_b275_ub

private lemma sech5_pt_14_ge : (9003 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_14_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_14_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_15_le : cosh (8 : ℝ) / 55 ≤ (101060382 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((8 : ℝ) / 55) (by norm_num) (by norm_num : ((8 : ℝ) / 55) ≤ ((291 : ℝ) / 2000))
  exact hmono.trans cosh_b1455_ub

private lemma cosh5_v_15_le : cosh (8 : ℝ) / 275 ≤ (100043516 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((8 : ℝ) / 275) (by norm_num) (by norm_num : ((8 : ℝ) / 275) ≤ ((59 : ℝ) / 2000))
  exact hmono.trans cosh_b295_ub

private lemma sech5_pt_15_ge : (8991 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (8 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_15_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_15_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_16_le : cosh (17 : ℝ) / 110 ≤ (101203657 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((17 : ℝ) / 110) (by norm_num) (by norm_num : ((17 : ℝ) / 110) ≤ ((31 : ℝ) / 200))
  exact hmono.trans cosh_b1550_ub

private lemma cosh5_v_16_le : cosh (17 : ℝ) / 550 ≤ (100048054 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((17 : ℝ) / 550) (by norm_num) (by norm_num : ((17 : ℝ) / 550) ≤ ((31 : ℝ) / 1000))
  exact hmono.trans cosh_b310_ub

private lemma sech5_pt_16_ge : (8978 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_16_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_16_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_17_le : cosh (9 : ℝ) / 55 ≤ (101347817 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 55) (by norm_num) (by norm_num : ((9 : ℝ) / 55) ≤ ((41 : ℝ) / 250))
  exact hmono.trans cosh_b1640_ub

private lemma cosh5_v_17_le : cosh (9 : ℝ) / 275 ≤ (100054455 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 275) (by norm_num) (by norm_num : ((9 : ℝ) / 275) ≤ ((33 : ℝ) / 1000))
  exact hmono.trans cosh_b330_ub

private lemma sech5_pt_17_ge : (8965 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_17_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_17_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_18_le : cosh (19 : ℝ) / 110 ≤ (101500186 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((19 : ℝ) / 110) (by norm_num) (by norm_num : ((19 : ℝ) / 110) ≤ ((173 : ℝ) / 1000))
  exact hmono.trans cosh_b1730_ub

private lemma cosh5_v_18_le : cosh (19 : ℝ) / 550 ≤ (100061257 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((19 : ℝ) / 550) (by norm_num) (by norm_num : ((19 : ℝ) / 550) ≤ ((7 : ℝ) / 200))
  exact hmono.trans cosh_b350_ub

private lemma sech5_pt_18_ge : (8951 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_18_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_18_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_19_le : cosh (2 : ℝ) / 11 ≤ (101660777 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((2 : ℝ) / 11) (by norm_num) (by norm_num : ((2 : ℝ) / 11) ≤ ((91 : ℝ) / 500))
  exact hmono.trans cosh_b1820_ub

private lemma cosh5_v_19_le : cosh (2 : ℝ) / 55 ≤ (100066620 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((2 : ℝ) / 55) (by norm_num) (by norm_num : ((2 : ℝ) / 55) ≤ ((73 : ℝ) / 2000))
  exact hmono.trans cosh_b365_ub

private lemma sech5_pt_19_ge : (8936 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (2 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_19_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_19_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_20_le : cosh (21 : ℝ) / 110 ≤ (101829603 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((21 : ℝ) / 110) (by norm_num) (by norm_num : ((21 : ℝ) / 110) ≤ ((191 : ℝ) / 1000))
  exact hmono.trans cosh_b1910_ub

private lemma cosh5_v_20_le : cosh (21 : ℝ) / 550 ≤ (100074122 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((21 : ℝ) / 550) (by norm_num) (by norm_num : ((21 : ℝ) / 550) ≤ ((77 : ℝ) / 2000))
  exact hmono.trans cosh_b385_ub

private lemma sech5_pt_20_ge : (8920 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_20_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_20_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_21_le : cosh (1 : ℝ) / 5 ≤ (102006676 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 5) (by norm_num) (by norm_num : ((1 : ℝ) / 5) ≤ ((1 : ℝ) / 5))
  exact hmono.trans cosh_b2000_ub

private lemma cosh5_v_21_le : cosh (1 : ℝ) / 25 ≤ (100080011 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 25) (by norm_num) (by norm_num : ((1 : ℝ) / 25) ≤ ((1 : ℝ) / 25))
  exact hmono.trans cosh_b400_ub

private lemma sech5_pt_21_ge : (8904 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_21_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_21_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_22_le : cosh (23 : ℝ) / 110 ≤ (102202551 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((23 : ℝ) / 110) (by norm_num) (by norm_num : ((23 : ℝ) / 110) ≤ ((419 : ℝ) / 2000))
  exact hmono.trans cosh_b2095_ub

private lemma cosh5_v_22_le : cosh (23 : ℝ) / 550 ≤ (100088213 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((23 : ℝ) / 550) (by norm_num) (by norm_num : ((23 : ℝ) / 550) ≤ ((21 : ℝ) / 500))
  exact hmono.trans cosh_b420_ub

private lemma sech5_pt_22_ge : (8887 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_22_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_22_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_23_le : cosh (12 : ℝ) / 55 ≤ (102396625 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((12 : ℝ) / 55) (by norm_num) (by norm_num : ((12 : ℝ) / 55) ≤ ((437 : ℝ) / 2000))
  exact hmono.trans cosh_b2185_ub

private lemma cosh5_v_23_le : cosh (12 : ℝ) / 275 ≤ (100096816 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((12 : ℝ) / 275) (by norm_num) (by norm_num : ((12 : ℝ) / 275) ≤ ((11 : ℝ) / 250))
  exact hmono.trans cosh_b440_ub

private lemma sech5_pt_23_ge : (8869 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (12 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_23_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_23_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_24_le : cosh (5 : ℝ) / 22 ≤ (102598994 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((5 : ℝ) / 22) (by norm_num) (by norm_num : ((5 : ℝ) / 22) ≤ ((91 : ℝ) / 400))
  exact hmono.trans cosh_b2275_ub

private lemma cosh5_v_24_le : cosh (1 : ℝ) / 22 ≤ (100103531 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 22) (by norm_num) (by norm_num : ((1 : ℝ) / 22) ≤ ((91 : ℝ) / 2000))
  exact hmono.trans cosh_b455_ub

private lemma sech5_pt_24_ge : (8851 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (5 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_24_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_24_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_25_le : cosh (13 : ℝ) / 55 ≤ (102809672 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((13 : ℝ) / 55) (by norm_num) (by norm_num : ((13 : ℝ) / 55) ≤ ((473 : ℝ) / 2000))
  exact hmono.trans cosh_b2365_ub

private lemma cosh5_v_25_le : cosh (13 : ℝ) / 275 ≤ (100112834 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((13 : ℝ) / 275) (by norm_num) (by norm_num : ((13 : ℝ) / 275) ≤ ((19 : ℝ) / 400))
  exact hmono.trans cosh_b475_ub

private lemma sech5_pt_25_ge : (8832 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_25_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_25_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_26_le : cosh (27 : ℝ) / 110 ≤ (103028679 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((27 : ℝ) / 110) (by norm_num) (by norm_num : ((27 : ℝ) / 110) ≤ ((491 : ℝ) / 2000))
  exact hmono.trans cosh_b2455_ub

private lemma cosh5_v_26_le : cosh (27 : ℝ) / 550 ≤ (100122538 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((27 : ℝ) / 550) (by norm_num) (by norm_num : ((27 : ℝ) / 550) ≤ ((99 : ℝ) / 2000))
  exact hmono.trans cosh_b495_ub

private lemma sech5_pt_26_ge : (8812 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_26_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_26_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_27_le : cosh (14 : ℝ) / 55 ≤ (103268906 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((14 : ℝ) / 55) (by norm_num) (by norm_num : ((14 : ℝ) / 55) ≤ ((51 : ℝ) / 200))
  exact hmono.trans cosh_b2550_ub

private lemma cosh5_v_27_le : cosh (14 : ℝ) / 275 ≤ (100130079 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((14 : ℝ) / 275) (by norm_num) (by norm_num : ((14 : ℝ) / 275) ≤ ((51 : ℝ) / 1000))
  exact hmono.trans cosh_b510_ub

private lemma sech5_pt_27_ge : (8791 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (14 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_27_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_27_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_28_le : cosh (29 : ℝ) / 110 ≤ (103505087 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((29 : ℝ) / 110) (by norm_num) (by norm_num : ((29 : ℝ) / 110) ≤ ((33 : ℝ) / 125))
  exact hmono.trans cosh_b2640_ub

private lemma cosh5_v_28_le : cosh (29 : ℝ) / 550 ≤ (100140483 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((29 : ℝ) / 550) (by norm_num) (by norm_num : ((29 : ℝ) / 550) ≤ ((53 : ℝ) / 1000))
  exact hmono.trans cosh_b530_ub

private lemma sech5_pt_28_ge : (8770 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_28_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_28_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_29_le : cosh (3 : ℝ) / 11 ≤ (103749652 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 11) (by norm_num) (by norm_num : ((3 : ℝ) / 11) ≤ ((273 : ℝ) / 1000))
  exact hmono.trans cosh_b2730_ub

private lemma cosh5_v_29_le : cosh (3 : ℝ) / 55 ≤ (100151289 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 55) (by norm_num) (by norm_num : ((3 : ℝ) / 55) ≤ ((11 : ℝ) / 200))
  exact hmono.trans cosh_b550_ub

private lemma sech5_pt_29_ge : (8749 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_29_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_29_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_30_le : cosh (31 : ℝ) / 110 ≤ (104002621 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((31 : ℝ) / 110) (by norm_num) (by norm_num : ((31 : ℝ) / 110) ≤ ((141 : ℝ) / 500))
  exact hmono.trans cosh_b2820_ub

private lemma cosh5_v_30_le : cosh (31 : ℝ) / 550 ≤ (100159655 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((31 : ℝ) / 550) (by norm_num) (by norm_num : ((31 : ℝ) / 550) ≤ ((113 : ℝ) / 2000))
  exact hmono.trans cosh_b565_ub

private lemma sech5_pt_30_ge : (8727 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_30_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_30_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_31_le : cosh (16 : ℝ) / 55 ≤ (104264014 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((16 : ℝ) / 55) (by norm_num) (by norm_num : ((16 : ℝ) / 55) ≤ ((291 : ℝ) / 1000))
  exact hmono.trans cosh_b2910_ub

private lemma cosh5_v_31_le : cosh (16 : ℝ) / 275 ≤ (100171162 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((16 : ℝ) / 275) (by norm_num) (by norm_num : ((16 : ℝ) / 275) ≤ ((117 : ℝ) / 2000))
  exact hmono.trans cosh_b585_ub

private lemma sech5_pt_31_ge : (8704 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (16 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_31_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_31_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_32_le : cosh (3 : ℝ) / 10 ≤ (104533852 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 10) (by norm_num) (by norm_num : ((3 : ℝ) / 10) ≤ ((3 : ℝ) / 10))
  exact hmono.trans cosh_b3000_ub

private lemma cosh5_v_32_le : cosh (3 : ℝ) / 50 ≤ (100180055 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 50) (by norm_num) (by norm_num : ((3 : ℝ) / 50) ≤ ((3 : ℝ) / 50))
  exact hmono.trans cosh_b600_ub

private lemma sech5_pt_32_ge : (8680 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_32_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_32_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_33_le : cosh (17 : ℝ) / 55 ≤ (104827868 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((17 : ℝ) / 55) (by norm_num) (by norm_num : ((17 : ℝ) / 55) ≤ ((619 : ℝ) / 2000))
  exact hmono.trans cosh_b3095_ub

private lemma cosh5_v_33_le : cosh (17 : ℝ) / 275 ≤ (100192262 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((17 : ℝ) / 275) (by norm_num) (by norm_num : ((17 : ℝ) / 275) ≤ ((31 : ℝ) / 500))
  exact hmono.trans cosh_b620_ub

private lemma sech5_pt_33_ge : (8655 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_33_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_33_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_34_le : cosh (7 : ℝ) / 22 ≤ (105115135 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 22) (by norm_num) (by norm_num : ((7 : ℝ) / 22) ≤ ((637 : ℝ) / 2000))
  exact hmono.trans cosh_b3185_ub

private lemma cosh5_v_34_le : cosh (7 : ℝ) / 110 ≤ (100204870 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 110) (by norm_num) (by norm_num : ((7 : ℝ) / 110) ≤ ((8 : ℝ) / 125))
  exact hmono.trans cosh_b640_ub

private lemma sech5_pt_34_ge : (8630 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_34_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_34_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_35_le : cosh (18 : ℝ) / 55 ≤ (105410918 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((18 : ℝ) / 55) (by norm_num) (by norm_num : ((18 : ℝ) / 55) ≤ ((131 : ℝ) / 400))
  exact hmono.trans cosh_b3275_ub

private lemma cosh5_v_35_le : cosh (18 : ℝ) / 275 ≤ (100214590 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((18 : ℝ) / 275) (by norm_num) (by norm_num : ((18 : ℝ) / 275) ≤ ((131 : ℝ) / 2000))
  exact hmono.trans cosh_b655_ub

private lemma sech5_pt_35_ge : (8605 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (18 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_35_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_35_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_36_le : cosh (37 : ℝ) / 110 ≤ (105715238 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((37 : ℝ) / 110) (by norm_num) (by norm_num : ((37 : ℝ) / 110) ≤ ((673 : ℝ) / 2000))
  exact hmono.trans cosh_b3365_ub

private lemma cosh5_v_36_le : cosh (37 : ℝ) / 550 ≤ (100227900 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((37 : ℝ) / 550) (by norm_num) (by norm_num : ((37 : ℝ) / 550) ≤ ((27 : ℝ) / 400))
  exact hmono.trans cosh_b675_ub

private lemma sech5_pt_36_ge : (8579 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_36_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_36_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_37_le : cosh (19 : ℝ) / 55 ≤ (106028122 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((19 : ℝ) / 55) (by norm_num) (by norm_num : ((19 : ℝ) / 55) ≤ ((691 : ℝ) / 2000))
  exact hmono.trans cosh_b3455_ub

private lemma cosh5_v_37_le : cosh (19 : ℝ) / 275 ≤ (100241610 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((19 : ℝ) / 275) (by norm_num) (by norm_num : ((19 : ℝ) / 275) ≤ ((139 : ℝ) / 2000))
  exact hmono.trans cosh_b695_ub

private lemma sech5_pt_37_ge : (8553 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_37_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_37_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_38_le : cosh (39 : ℝ) / 110 ≤ (106367705 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((39 : ℝ) / 110) (by norm_num) (by norm_num : ((39 : ℝ) / 110) ≤ ((71 : ℝ) / 200))
  exact hmono.trans cosh_b3550_ub

private lemma cosh5_v_38_le : cosh (39 : ℝ) / 550 ≤ (100252156 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((39 : ℝ) / 550) (by norm_num) (by norm_num : ((39 : ℝ) / 550) ≤ ((71 : ℝ) / 1000))
  exact hmono.trans cosh_b710_ub

private lemma sech5_pt_38_ge : (8525 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_38_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_38_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_39_le : cosh (4 : ℝ) / 11 ≤ (106698271 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((4 : ℝ) / 11) (by norm_num) (by norm_num : ((4 : ℝ) / 11) ≤ ((91 : ℝ) / 250))
  exact hmono.trans cosh_b3640_ub

private lemma cosh5_v_39_le : cosh (4 : ℝ) / 55 ≤ (100266569 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((4 : ℝ) / 55) (by norm_num) (by norm_num : ((4 : ℝ) / 55) ≤ ((73 : ℝ) / 1000))
  exact hmono.trans cosh_b730_ub

private lemma sech5_pt_39_ge : (8497 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (4 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_39_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_39_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_40_le : cosh (41 : ℝ) / 110 ≤ (107037479 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((41 : ℝ) / 110) (by norm_num) (by norm_num : ((41 : ℝ) / 110) ≤ ((373 : ℝ) / 1000))
  exact hmono.trans cosh_b3730_ub

private lemma cosh5_v_40_le : cosh (41 : ℝ) / 550 ≤ (100281382 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((41 : ℝ) / 550) (by norm_num) (by norm_num : ((41 : ℝ) / 550) ≤ ((3 : ℝ) / 40))
  exact hmono.trans cosh_b750_ub

private lemma sech5_pt_40_ge : (8469 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_40_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_40_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_41_le : cosh (21 : ℝ) / 55 ≤ (107385357 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((21 : ℝ) / 55) (by norm_num) (by norm_num : ((21 : ℝ) / 55) ≤ ((191 : ℝ) / 500))
  exact hmono.trans cosh_b3820_ub

private lemma cosh5_v_41_le : cosh (21 : ℝ) / 275 ≤ (100292756 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((21 : ℝ) / 275) (by norm_num) (by norm_num : ((21 : ℝ) / 275) ≤ ((153 : ℝ) / 2000))
  exact hmono.trans cosh_b765_ub

private lemma sech5_pt_41_ge : (8440 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_41_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_41_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_42_le : cosh (43 : ℝ) / 110 ≤ (107741934 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((43 : ℝ) / 110) (by norm_num) (by norm_num : ((43 : ℝ) / 110) ≤ ((391 : ℝ) / 1000))
  exact hmono.trans cosh_b3910_ub

private lemma cosh5_v_42_le : cosh (43 : ℝ) / 550 ≤ (100308271 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((43 : ℝ) / 550) (by norm_num) (by norm_num : ((43 : ℝ) / 550) ≤ ((157 : ℝ) / 2000))
  exact hmono.trans cosh_b785_ub

private lemma sech5_pt_42_ge : (8411 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_42_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_42_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_43_le : cosh (2 : ℝ) / 5 ≤ (108107238 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((2 : ℝ) / 5) (by norm_num) (by norm_num : ((2 : ℝ) / 5) ≤ ((2 : ℝ) / 5))
  exact hmono.trans cosh_b4000_ub

private lemma cosh5_v_43_le : cosh (2 : ℝ) / 25 ≤ (100320171 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((2 : ℝ) / 25) (by norm_num) (by norm_num : ((2 : ℝ) / 25) ≤ ((2 : ℝ) / 25))
  exact hmono.trans cosh_b800_ub

private lemma sech5_pt_43_ge : (8382 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (2 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_43_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_43_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_44_le : cosh (9 : ℝ) / 22 ≤ (108502337 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 22) (by norm_num) (by norm_num : ((9 : ℝ) / 22) ≤ ((819 : ℝ) / 2000))
  exact hmono.trans cosh_b4095_ub

private lemma cosh5_v_44_le : cosh (9 : ℝ) / 110 ≤ (100336389 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 110) (by norm_num) (by norm_num : ((9 : ℝ) / 110) ≤ ((41 : ℝ) / 500))
  exact hmono.trans cosh_b820_ub

private lemma sech5_pt_44_ge : (8350 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_44_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_44_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_45_le : cosh (23 : ℝ) / 55 ≤ (108885673 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((23 : ℝ) / 55) (by norm_num) (by norm_num : ((23 : ℝ) / 55) ≤ ((837 : ℝ) / 2000))
  exact hmono.trans cosh_b4185_ub

private lemma cosh5_v_45_le : cosh (23 : ℝ) / 275 ≤ (100353008 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((23 : ℝ) / 275) (by norm_num) (by norm_num : ((23 : ℝ) / 275) ≤ ((21 : ℝ) / 250))
  exact hmono.trans cosh_b840_ub

private lemma sech5_pt_45_ge : (8319 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_45_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_45_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_46_le : cosh (47 : ℝ) / 110 ≤ (109277830 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((47 : ℝ) / 110) (by norm_num) (by norm_num : ((47 : ℝ) / 110) ≤ ((171 : ℝ) / 400))
  exact hmono.trans cosh_b4275_ub

private lemma cosh5_v_46_le : cosh (47 : ℝ) / 550 ≤ (100365736 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((47 : ℝ) / 550) (by norm_num) (by norm_num : ((47 : ℝ) / 550) ≤ ((171 : ℝ) / 2000))
  exact hmono.trans cosh_b855_ub

private lemma sech5_pt_46_ge : (8288 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_46_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_46_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_47_le : cosh (24 : ℝ) / 55 ≤ (109678838 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((24 : ℝ) / 55) (by norm_num) (by norm_num : ((24 : ℝ) / 55) ≤ ((873 : ℝ) / 2000))
  exact hmono.trans cosh_b4365_ub

private lemma cosh5_v_47_le : cosh (24 : ℝ) / 275 ≤ (100383057 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((24 : ℝ) / 275) (by norm_num) (by norm_num : ((24 : ℝ) / 275) ≤ ((7 : ℝ) / 80))
  exact hmono.trans cosh_b875_ub

private lemma sech5_pt_47_ge : (8257 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (24 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_47_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_47_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_48_le : cosh (49 : ℝ) / 110 ≤ (110088730 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((49 : ℝ) / 110) (by norm_num) (by norm_num : ((49 : ℝ) / 110) ≤ ((891 : ℝ) / 2000))
  exact hmono.trans cosh_b4455_ub

private lemma cosh5_v_48_le : cosh (49 : ℝ) / 550 ≤ (100400780 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((49 : ℝ) / 550) (by norm_num) (by norm_num : ((49 : ℝ) / 550) ≤ ((179 : ℝ) / 2000))
  exact hmono.trans cosh_b895_ub

private lemma sech5_pt_48_ge : (8224 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_48_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_48_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_49_le : cosh (5 : ℝ) / 11 ≤ (110531068 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((5 : ℝ) / 11) (by norm_num) (by norm_num : ((5 : ℝ) / 11) ≤ ((91 : ℝ) / 200))
  exact hmono.trans cosh_b4550_ub

private lemma cosh5_v_49_le : cosh (1 : ℝ) / 11 ≤ (100414336 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 11) (by norm_num) (by norm_num : ((1 : ℝ) / 11) ≤ ((91 : ℝ) / 1000))
  exact hmono.trans cosh_b910_ub

private lemma sech5_pt_49_ge : (8190 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (5 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_49_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_49_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma sech5_batch_0_ge : (438589 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (2 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (4 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (6 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (8 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (2 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (12 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (5 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (14 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (16 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (18 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (4 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (2 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (24 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (5 : ℝ) / 11 := by
  linarith [sech5_pt_0_ge, sech5_pt_1_ge, sech5_pt_2_ge, sech5_pt_3_ge, sech5_pt_4_ge, sech5_pt_5_ge, sech5_pt_6_ge, sech5_pt_7_ge, sech5_pt_8_ge, sech5_pt_9_ge, sech5_pt_10_ge, sech5_pt_11_ge, sech5_pt_12_ge, sech5_pt_13_ge, sech5_pt_14_ge, sech5_pt_15_ge, sech5_pt_16_ge, sech5_pt_17_ge, sech5_pt_18_ge, sech5_pt_19_ge, sech5_pt_20_ge, sech5_pt_21_ge, sech5_pt_22_ge, sech5_pt_23_ge, sech5_pt_24_ge, sech5_pt_25_ge, sech5_pt_26_ge, sech5_pt_27_ge, sech5_pt_28_ge, sech5_pt_29_ge, sech5_pt_30_ge, sech5_pt_31_ge, sech5_pt_32_ge, sech5_pt_33_ge, sech5_pt_34_ge, sech5_pt_35_ge, sech5_pt_36_ge, sech5_pt_37_ge, sech5_pt_38_ge, sech5_pt_39_ge, sech5_pt_40_ge, sech5_pt_41_ge, sech5_pt_42_ge, sech5_pt_43_ge, sech5_pt_44_ge, sech5_pt_45_ge, sech5_pt_46_ge, sech5_pt_47_ge, sech5_pt_48_ge, sech5_pt_49_ge]

private lemma cosh5_u_50_le : cosh (51 : ℝ) / 110 ≤ (110959327 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((51 : ℝ) / 110) (by norm_num) (by norm_num : ((51 : ℝ) / 110) ≤ ((58 : ℝ) / 125))
  exact hmono.trans cosh_b4640_ub

private lemma cosh5_v_50_le : cosh (51 : ℝ) / 550 ≤ (100432762 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((51 : ℝ) / 550) (by norm_num) (by norm_num : ((51 : ℝ) / 550) ≤ ((93 : ℝ) / 1000))
  exact hmono.trans cosh_b930_ub

private lemma sech5_pt_50_ge : (8157 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (51 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_50_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_50_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_51_le : cosh (26 : ℝ) / 55 ≤ (111396573 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((26 : ℝ) / 55) (by norm_num) (by norm_num : ((26 : ℝ) / 55) ≤ ((473 : ℝ) / 1000))
  exact hmono.trans cosh_b4730_ub

private lemma cosh5_v_51_le : cosh (26 : ℝ) / 275 ≤ (100451590 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((26 : ℝ) / 275) (by norm_num) (by norm_num : ((26 : ℝ) / 275) ≤ ((19 : ℝ) / 200))
  exact hmono.trans cosh_b950_ub

private lemma sech5_pt_51_ge : (8124 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (26 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_51_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_51_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_52_le : cosh (53 : ℝ) / 110 ≤ (111842843 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((53 : ℝ) / 110) (by norm_num) (by norm_num : ((53 : ℝ) / 110) ≤ ((241 : ℝ) / 500))
  exact hmono.trans cosh_b4820_ub

private lemma cosh5_v_52_le : cosh (53 : ℝ) / 550 ≤ (100465974 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((53 : ℝ) / 550) (by norm_num) (by norm_num : ((53 : ℝ) / 550) ≤ ((193 : ℝ) / 2000))
  exact hmono.trans cosh_b965_ub

private lemma sech5_pt_52_ge : (8090 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (53 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_52_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_52_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_53_le : cosh (27 : ℝ) / 55 ≤ (112298172 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((27 : ℝ) / 55) (by norm_num) (by norm_num : ((27 : ℝ) / 55) ≤ ((491 : ℝ) / 1000))
  exact hmono.trans cosh_b4910_ub

private lemma cosh5_v_53_le : cosh (27 : ℝ) / 275 ≤ (100485505 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((27 : ℝ) / 275) (by norm_num) (by norm_num : ((27 : ℝ) / 275) ≤ ((197 : ℝ) / 2000))
  exact hmono.trans cosh_b985_ub

private lemma sech5_pt_53_ge : (8056 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_53_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_53_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_54_le : cosh (1 : ℝ) / 2 ≤ (112762597 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 2) (by norm_num) (by norm_num : ((1 : ℝ) / 2) ≤ ((1 : ℝ) / 2))
  exact hmono.trans cosh_b5000_ub

private lemma cosh5_v_54_le : cosh (1 : ℝ) / 10 ≤ (100500417 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 10) (by norm_num) (by norm_num : ((1 : ℝ) / 10) ≤ ((1 : ℝ) / 10))
  exact hmono.trans cosh_b1000_ub

private lemma sech5_pt_54_ge : (8021 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 2 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_54_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_54_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_55_le : cosh (28 : ℝ) / 55 ≤ (113262733 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((28 : ℝ) / 55) (by norm_num) (by norm_num : ((28 : ℝ) / 55) ≤ ((1019 : ℝ) / 2000))
  exact hmono.trans cosh_b5095_ub

private lemma cosh5_v_55_le : cosh (28 : ℝ) / 275 ≤ (100520652 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((28 : ℝ) / 275) (by norm_num) (by norm_num : ((28 : ℝ) / 275) ≤ ((51 : ℝ) / 500))
  exact hmono.trans cosh_b1020_ub

private lemma sech5_pt_55_ge : (7984 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (28 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_55_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_55_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_56_le : cosh (57 : ℝ) / 110 ≤ (113745975 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((57 : ℝ) / 110) (by norm_num) (by norm_num : ((57 : ℝ) / 110) ≤ ((1037 : ℝ) / 2000))
  exact hmono.trans cosh_b5185_ub

private lemma cosh5_v_56_le : cosh (57 : ℝ) / 550 ≤ (100541288 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((57 : ℝ) / 550) (by norm_num) (by norm_num : ((57 : ℝ) / 550) ≤ ((13 : ℝ) / 125))
  exact hmono.trans cosh_b1040_ub

private lemma sech5_pt_56_ge : (7949 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (57 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_56_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_56_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_57_le : cosh (29 : ℝ) / 55 ≤ (114238431 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((29 : ℝ) / 55) (by norm_num) (by norm_num : ((29 : ℝ) / 55) ≤ ((211 : ℝ) / 400))
  exact hmono.trans cosh_b5275_ub

private lemma cosh5_v_57_le : cosh (29 : ℝ) / 275 ≤ (100557029 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((29 : ℝ) / 275) (by norm_num) (by norm_num : ((29 : ℝ) / 275) ≤ ((211 : ℝ) / 2000))
  exact hmono.trans cosh_b1055_ub

private lemma sech5_pt_57_ge : (7913 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_57_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_57_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_58_le : cosh (59 : ℝ) / 110 ≤ (114740140 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((59 : ℝ) / 110) (by norm_num) (by norm_num : ((59 : ℝ) / 110) ≤ ((1073 : ℝ) / 2000))
  exact hmono.trans cosh_b5365_ub

private lemma cosh5_v_58_le : cosh (59 : ℝ) / 550 ≤ (100578370 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((59 : ℝ) / 550) (by norm_num) (by norm_num : ((59 : ℝ) / 550) ≤ ((43 : ℝ) / 400))
  exact hmono.trans cosh_b1075_ub

private lemma sech5_pt_58_ge : (7877 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (59 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_58_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_58_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_59_le : cosh (6 : ℝ) / 11 ≤ (115251142 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((6 : ℝ) / 11) (by norm_num) (by norm_num : ((6 : ℝ) / 11) ≤ ((1091 : ℝ) / 2000))
  exact hmono.trans cosh_b5455_ub

private lemma cosh5_v_59_le : cosh (6 : ℝ) / 55 ≤ (100600112 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((6 : ℝ) / 55) (by norm_num) (by norm_num : ((6 : ℝ) / 55) ≤ ((219 : ℝ) / 2000))
  exact hmono.trans cosh_b1095_ub

private lemma sech5_pt_59_ge : (7840 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (6 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_59_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_59_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_60_le : cosh (61 : ℝ) / 110 ≤ (115800663 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((61 : ℝ) / 110) (by norm_num) (by norm_num : ((61 : ℝ) / 110) ≤ ((111 : ℝ) / 200))
  exact hmono.trans cosh_b5550_ub

private lemma cosh5_v_60_le : cosh (61 : ℝ) / 550 ≤ (100616683 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((61 : ℝ) / 550) (by norm_num) (by norm_num : ((61 : ℝ) / 550) ≤ ((111 : ℝ) / 1000))
  exact hmono.trans cosh_b1110_ub

private lemma sech5_pt_60_ge : (7802 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (61 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_60_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_60_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_61_le : cosh (31 : ℝ) / 55 ≤ (116330901 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((31 : ℝ) / 55) (by norm_num) (by norm_num : ((31 : ℝ) / 55) ≤ ((141 : ℝ) / 250))
  exact hmono.trans cosh_b5640_ub

private lemma cosh5_v_61_le : cosh (31 : ℝ) / 275 ≤ (100639130 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((31 : ℝ) / 275) (by norm_num) (by norm_num : ((31 : ℝ) / 275) ≤ ((113 : ℝ) / 1000))
  exact hmono.trans cosh_b1130_ub

private lemma sech5_pt_61_ge : (7765 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_61_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_61_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_62_le : cosh (63 : ℝ) / 110 ≤ (116870562 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((63 : ℝ) / 110) (by norm_num) (by norm_num : ((63 : ℝ) / 110) ≤ ((573 : ℝ) / 1000))
  exact hmono.trans cosh_b5730_ub

private lemma cosh5_v_62_le : cosh (63 : ℝ) / 550 ≤ (100661980 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((63 : ℝ) / 550) (by norm_num) (by norm_num : ((63 : ℝ) / 550) ≤ ((23 : ℝ) / 200))
  exact hmono.trans cosh_b1150_ub

private lemma sech5_pt_62_ge : (7727 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (63 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_62_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_62_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_63_le : cosh (32 : ℝ) / 55 ≤ (117419689 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((32 : ℝ) / 55) (by norm_num) (by norm_num : ((32 : ℝ) / 55) ≤ ((291 : ℝ) / 500))
  exact hmono.trans cosh_b5820_ub

private lemma cosh5_v_63_le : cosh (32 : ℝ) / 275 ≤ (100679381 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((32 : ℝ) / 275) (by norm_num) (by norm_num : ((32 : ℝ) / 275) ≤ ((233 : ℝ) / 2000))
  exact hmono.trans cosh_b1165_ub

private lemma sech5_pt_63_ge : (7689 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (32 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_63_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_63_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_64_le : cosh (13 : ℝ) / 22 ≤ (117978328 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((13 : ℝ) / 22) (by norm_num) (by norm_num : ((13 : ℝ) / 22) ≤ ((591 : ℝ) / 1000))
  exact hmono.trans cosh_b5910_ub

private lemma cosh5_v_64_le : cosh (13 : ℝ) / 110 ≤ (100702935 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((13 : ℝ) / 110) (by norm_num) (by norm_num : ((13 : ℝ) / 110) ≤ ((237 : ℝ) / 2000))
  exact hmono.trans cosh_b1185_ub

private lemma sech5_pt_64_ge : (7651 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_64_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_64_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_65_le : cosh (3 : ℝ) / 5 ≤ (118546522 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 5) (by norm_num) (by norm_num : ((3 : ℝ) / 5) ≤ ((3 : ℝ) / 5))
  exact hmono.trans cosh_b6000_ub

private lemma cosh5_v_65_le : cosh (3 : ℝ) / 25 ≤ (100720865 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 25) (by norm_num) (by norm_num : ((3 : ℝ) / 25) ≤ ((3 : ℝ) / 25))
  exact hmono.trans cosh_b1200_ub

private lemma sech5_pt_65_ge : (7613 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_65_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_65_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_66_le : cosh (67 : ℝ) / 110 ≤ (119156702 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((67 : ℝ) / 110) (by norm_num) (by norm_num : ((67 : ℝ) / 110) ≤ ((1219 : ℝ) / 2000))
  exact hmono.trans cosh_b6095_ub

private lemma cosh5_v_66_le : cosh (67 : ℝ) / 550 ≤ (100745124 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((67 : ℝ) / 550) (by norm_num) (by norm_num : ((67 : ℝ) / 550) ≤ ((61 : ℝ) / 500))
  exact hmono.trans cosh_b1220_ub

private lemma sech5_pt_66_ge : (7572 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (67 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_66_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_66_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_67_le : cosh (34 : ℝ) / 55 ≤ (119744685 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((34 : ℝ) / 55) (by norm_num) (by norm_num : ((34 : ℝ) / 55) ≤ ((1237 : ℝ) / 2000))
  exact hmono.trans cosh_b6185_ub

private lemma cosh5_v_67_le : cosh (34 : ℝ) / 275 ≤ (100769786 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((34 : ℝ) / 275) (by norm_num) (by norm_num : ((34 : ℝ) / 275) ≤ ((31 : ℝ) / 250))
  exact hmono.trans cosh_b1240_ub

private lemma sech5_pt_67_ge : (7533 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (34 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_67_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_67_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_68_le : cosh (69 : ℝ) / 110 ≤ (120342369 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((69 : ℝ) / 110) (by norm_num) (by norm_num : ((69 : ℝ) / 110) ≤ ((251 : ℝ) / 400))
  exact hmono.trans cosh_b6275_ub

private lemma cosh5_v_68_le : cosh (69 : ℝ) / 550 ≤ (100788547 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((69 : ℝ) / 550) (by norm_num) (by norm_num : ((69 : ℝ) / 550) ≤ ((251 : ℝ) / 2000))
  exact hmono.trans cosh_b1255_ub

private lemma sech5_pt_68_ge : (7495 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (69 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_68_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_68_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_69_le : cosh (7 : ℝ) / 11 ≤ (120949799 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 11) (by norm_num) (by norm_num : ((7 : ℝ) / 11) ≤ ((1273 : ℝ) / 2000))
  exact hmono.trans cosh_b6365_ub

private lemma cosh5_v_69_le : cosh (7 : ℝ) / 55 ≤ (100813915 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 55) (by norm_num) (by norm_num : ((7 : ℝ) / 55) ≤ ((51 : ℝ) / 400))
  exact hmono.trans cosh_b1275_ub

private lemma sech5_pt_69_ge : (7455 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_69_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_69_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_70_le : cosh (71 : ℝ) / 110 ≤ (121567027 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((71 : ℝ) / 110) (by norm_num) (by norm_num : ((71 : ℝ) / 110) ≤ ((1291 : ℝ) / 2000))
  exact hmono.trans cosh_b6455_ub

private lemma cosh5_v_70_le : cosh (71 : ℝ) / 550 ≤ (100839685 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((71 : ℝ) / 550) (by norm_num) (by norm_num : ((71 : ℝ) / 550) ≤ ((259 : ℝ) / 2000))
  exact hmono.trans cosh_b1295_ub

private lemma sech5_pt_70_ge : (7415 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (71 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_70_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_70_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_71_le : cosh (36 : ℝ) / 55 ≤ (122229229 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((36 : ℝ) / 55) (by norm_num) (by norm_num : ((36 : ℝ) / 55) ≤ ((131 : ℝ) / 200))
  exact hmono.trans cosh_b6550_ub

private lemma cosh5_v_71_le : cosh (36 : ℝ) / 275 ≤ (100859278 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((36 : ℝ) / 275) (by norm_num) (by norm_num : ((36 : ℝ) / 275) ≤ ((131 : ℝ) / 1000))
  exact hmono.trans cosh_b1310_ub

private lemma sech5_pt_71_ge : (7374 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (36 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_71_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_71_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_72_le : cosh (73 : ℝ) / 110 ≤ (122866754 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((73 : ℝ) / 110) (by norm_num) (by norm_num : ((73 : ℝ) / 110) ≤ ((83 : ℝ) / 125))
  exact hmono.trans cosh_b6640_ub

private lemma cosh5_v_72_le : cosh (73 : ℝ) / 550 ≤ (100885755 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((73 : ℝ) / 550) (by norm_num) (by norm_num : ((73 : ℝ) / 550) ≤ ((133 : ℝ) / 1000))
  exact hmono.trans cosh_b1330_ub

private lemma sech5_pt_72_ge : (7334 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (73 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_72_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_72_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_73_le : cosh (37 : ℝ) / 55 ≤ (123514230 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((37 : ℝ) / 55) (by norm_num) (by norm_num : ((37 : ℝ) / 55) ≤ ((673 : ℝ) / 1000))
  exact hmono.trans cosh_b6730_ub

private lemma cosh5_v_73_le : cosh (37 : ℝ) / 275 ≤ (100912635 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((37 : ℝ) / 275) (by norm_num) (by norm_num : ((37 : ℝ) / 275) ≤ ((27 : ℝ) / 200))
  exact hmono.trans cosh_b1350_ub

private lemma sech5_pt_73_ge : (7293 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_73_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_73_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_74_le : cosh (15 : ℝ) / 22 ≤ (124171711 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((15 : ℝ) / 22) (by norm_num) (by norm_num : ((15 : ℝ) / 22) ≤ ((341 : ℝ) / 500))
  exact hmono.trans cosh_b6820_ub

private lemma cosh5_v_74_le : cosh (3 : ℝ) / 22 ≤ (100933060 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 22) (by norm_num) (by norm_num : ((3 : ℝ) / 22) ≤ ((273 : ℝ) / 2000))
  exact hmono.trans cosh_b1365_ub

private lemma sech5_pt_74_ge : (7253 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (15 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_74_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_74_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_75_le : cosh (38 : ℝ) / 55 ≤ (124839250 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((38 : ℝ) / 55) (by norm_num) (by norm_num : ((38 : ℝ) / 55) ≤ ((691 : ℝ) / 1000))
  exact hmono.trans cosh_b6910_ub

private lemma cosh5_v_75_le : cosh (38 : ℝ) / 275 ≤ (100960647 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((38 : ℝ) / 275) (by norm_num) (by norm_num : ((38 : ℝ) / 275) ≤ ((277 : ℝ) / 2000))
  exact hmono.trans cosh_b1385_ub

private lemma sech5_pt_75_ge : (7212 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (38 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_75_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_75_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_76_le : cosh (7 : ℝ) / 10 ≤ (125516901 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 10) (by norm_num) (by norm_num : ((7 : ℝ) / 10) ≤ ((7 : ℝ) / 10))
  exact hmono.trans cosh_b7000_ub

private lemma cosh5_v_76_le : cosh (7 : ℝ) / 50 ≤ (100981602 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 50) (by norm_num) (by norm_num : ((7 : ℝ) / 50) ≤ ((7 : ℝ) / 50))
  exact hmono.trans cosh_b1400_ub

private lemma sech5_pt_76_ge : (7172 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_76_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_76_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_77_le : cosh (39 : ℝ) / 55 ≤ (126243230 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((39 : ℝ) / 55) (by norm_num) (by norm_num : ((39 : ℝ) / 55) ≤ ((1419 : ℝ) / 2000))
  exact hmono.trans cosh_b7095_ub

private lemma cosh5_v_77_le : cosh (39 : ℝ) / 275 ≤ (101009896 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((39 : ℝ) / 275) (by norm_num) (by norm_num : ((39 : ℝ) / 275) ≤ ((71 : ℝ) / 500))
  exact hmono.trans cosh_b1420_ub

private lemma sech5_pt_77_ge : (7129 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_77_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_77_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_78_le : cosh (79 : ℝ) / 110 ≤ (126941841 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((79 : ℝ) / 110) (by norm_num) (by norm_num : ((79 : ℝ) / 110) ≤ ((1437 : ℝ) / 2000))
  exact hmono.trans cosh_b7185_ub

private lemma cosh5_v_78_le : cosh (79 : ℝ) / 550 ≤ (101038593 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((79 : ℝ) / 550) (by norm_num) (by norm_num : ((79 : ℝ) / 550) ≤ ((18 : ℝ) / 125))
  exact hmono.trans cosh_b1440_ub

private lemma sech5_pt_78_ge : (7087 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (79 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_78_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_78_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_79_le : cosh (8 : ℝ) / 11 ≤ (127650733 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((8 : ℝ) / 11) (by norm_num) (by norm_num : ((8 : ℝ) / 11) ≤ ((291 : ℝ) / 400))
  exact hmono.trans cosh_b7275_ub

private lemma cosh5_v_79_le : cosh (8 : ℝ) / 55 ≤ (101060382 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((8 : ℝ) / 55) (by norm_num) (by norm_num : ((8 : ℝ) / 55) ≤ ((291 : ℝ) / 2000))
  exact hmono.trans cosh_b1455_ub

private lemma sech5_pt_79_ge : (7046 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (8 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_79_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_79_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_80_le : cosh (81 : ℝ) / 110 ≤ (128369966 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((81 : ℝ) / 110) (by norm_num) (by norm_num : ((81 : ℝ) / 110) ≤ ((1473 : ℝ) / 2000))
  exact hmono.trans cosh_b7365_ub

private lemma cosh5_v_80_le : cosh (81 : ℝ) / 550 ≤ (101089787 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((81 : ℝ) / 550) (by norm_num) (by norm_num : ((81 : ℝ) / 550) ≤ ((59 : ℝ) / 400))
  exact hmono.trans cosh_b1475_ub

private lemma sech5_pt_80_ge : (7005 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (81 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_80_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_80_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_81_le : cosh (41 : ℝ) / 55 ≤ (129099596 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((41 : ℝ) / 55) (by norm_num) (by norm_num : ((41 : ℝ) / 55) ≤ ((1491 : ℝ) / 2000))
  exact hmono.trans cosh_b7455_ub

private lemma cosh5_v_81_le : cosh (41 : ℝ) / 275 ≤ (101119596 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((41 : ℝ) / 275) (by norm_num) (by norm_num : ((41 : ℝ) / 275) ≤ ((299 : ℝ) / 2000))
  exact hmono.trans cosh_b1495_ub

private lemma sech5_pt_81_ge : (6963 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_81_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_81_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_82_le : cosh (83 : ℝ) / 110 ≤ (129881107 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((83 : ℝ) / 110) (by norm_num) (by norm_num : ((83 : ℝ) / 110) ≤ ((151 : ℝ) / 200))
  exact hmono.trans cosh_b7550_ub

private lemma cosh5_v_82_le : cosh (83 : ℝ) / 550 ≤ (101142218 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((83 : ℝ) / 550) (by norm_num) (by norm_num : ((83 : ℝ) / 550) ≤ ((151 : ℝ) / 1000))
  exact hmono.trans cosh_b1510_ub

private lemma sech5_pt_82_ge : (6920 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (83 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_82_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_82_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_83_le : cosh (42 : ℝ) / 55 ≤ (130632298 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((42 : ℝ) / 55) (by norm_num) (by norm_num : ((42 : ℝ) / 55) ≤ ((191 : ℝ) / 250))
  exact hmono.trans cosh_b7640_ub

private lemma cosh5_v_83_le : cosh (42 : ℝ) / 275 ≤ (101172736 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((42 : ℝ) / 275) (by norm_num) (by norm_num : ((42 : ℝ) / 275) ≤ ((153 : ℝ) / 1000))
  exact hmono.trans cosh_b1530_ub

private lemma sech5_pt_83_ge : (6878 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (42 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_83_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_83_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_84_le : cosh (17 : ℝ) / 22 ≤ (131394070 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((17 : ℝ) / 22) (by norm_num) (by norm_num : ((17 : ℝ) / 22) ≤ ((773 : ℝ) / 1000))
  exact hmono.trans cosh_b7730_ub

private lemma cosh5_v_84_le : cosh (17 : ℝ) / 110 ≤ (101203657 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((17 : ℝ) / 110) (by norm_num) (by norm_num : ((17 : ℝ) / 110) ≤ ((31 : ℝ) / 200))
  exact hmono.trans cosh_b1550_ub

private lemma sech5_pt_84_ge : (6836 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_84_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_84_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_85_le : cosh (43 : ℝ) / 55 ≤ (132166485 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((43 : ℝ) / 55) (by norm_num) (by norm_num : ((43 : ℝ) / 55) ≤ ((391 : ℝ) / 500))
  exact hmono.trans cosh_b7820_ub

private lemma cosh5_v_85_le : cosh (43 : ℝ) / 275 ≤ (101227115 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((43 : ℝ) / 275) (by norm_num) (by norm_num : ((43 : ℝ) / 275) ≤ ((313 : ℝ) / 2000))
  exact hmono.trans cosh_b1565_ub

private lemma sech5_pt_85_ge : (6794 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_85_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_85_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_86_le : cosh (87 : ℝ) / 110 ≤ (132949606 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((87 : ℝ) / 110) (by norm_num) (by norm_num : ((87 : ℝ) / 110) ≤ ((791 : ℝ) / 1000))
  exact hmono.trans cosh_b7910_ub

private lemma cosh5_v_86_le : cosh (87 : ℝ) / 550 ≤ (101258745 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((87 : ℝ) / 550) (by norm_num) (by norm_num : ((87 : ℝ) / 550) ≤ ((317 : ℝ) / 2000))
  exact hmono.trans cosh_b1585_ub

private lemma sech5_pt_86_ge : (6752 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (87 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_86_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_86_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_87_le : cosh (4 : ℝ) / 5 ≤ (133743495 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((4 : ℝ) / 5) (by norm_num) (by norm_num : ((4 : ℝ) / 5) ≤ ((4 : ℝ) / 5))
  exact hmono.trans cosh_b8000_ub

private lemma cosh5_v_87_le : cosh (4 : ℝ) / 25 ≤ (101282733 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((4 : ℝ) / 25) (by norm_num) (by norm_num : ((4 : ℝ) / 25) ≤ ((4 : ℝ) / 25))
  exact hmono.trans cosh_b1600_ub

private lemma sech5_pt_87_ge : (6711 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (4 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_87_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_87_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_88_le : cosh (89 : ℝ) / 110 ≤ (134593244 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((89 : ℝ) / 110) (by norm_num) (by norm_num : ((89 : ℝ) / 110) ≤ ((1619 : ℝ) / 2000))
  exact hmono.trans cosh_b8095_ub

private lemma cosh5_v_88_le : cosh (89 : ℝ) / 550 ≤ (101315073 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((89 : ℝ) / 550) (by norm_num) (by norm_num : ((89 : ℝ) / 550) ≤ ((81 : ℝ) / 500))
  exact hmono.trans cosh_b1620_ub

private lemma sech5_pt_88_ge : (6666 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (89 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_88_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_88_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_89_le : cosh (9 : ℝ) / 11 ≤ (135409472 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 11) (by norm_num) (by norm_num : ((9 : ℝ) / 11) ≤ ((1637 : ℝ) / 2000))
  exact hmono.trans cosh_b8185_ub

private lemma cosh5_v_89_le : cosh (9 : ℝ) / 55 ≤ (101347817 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 55) (by norm_num) (by norm_num : ((9 : ℝ) / 55) ≤ ((41 : ℝ) / 250))
  exact hmono.trans cosh_b1640_ub

private lemma sech5_pt_89_ge : (6624 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_89_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_89_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_90_le : cosh (91 : ℝ) / 110 ≤ (136236669 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((91 : ℝ) / 110) (by norm_num) (by norm_num : ((91 : ℝ) / 110) ≤ ((331 : ℝ) / 400))
  exact hmono.trans cosh_b8275_ub

private lemma cosh5_v_90_le : cosh (91 : ℝ) / 550 ≤ (101372642 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((91 : ℝ) / 550) (by norm_num) (by norm_num : ((91 : ℝ) / 550) ≤ ((331 : ℝ) / 2000))
  exact hmono.trans cosh_b1655_ub

private lemma sech5_pt_90_ge : (6582 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (91 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_90_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_90_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_91_le : cosh (46 : ℝ) / 55 ≤ (137074902 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((46 : ℝ) / 55) (by norm_num) (by norm_num : ((46 : ℝ) / 55) ≤ ((1673 : ℝ) / 2000))
  exact hmono.trans cosh_b8365_ub

private lemma cosh5_v_91_le : cosh (46 : ℝ) / 275 ≤ (101406096 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((46 : ℝ) / 275) (by norm_num) (by norm_num : ((46 : ℝ) / 275) ≤ ((67 : ℝ) / 400))
  exact hmono.trans cosh_b1675_ub

private lemma sech5_pt_91_ge : (6540 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (46 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_91_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_91_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_92_le : cosh (93 : ℝ) / 110 ≤ (137924237 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((93 : ℝ) / 110) (by norm_num) (by norm_num : ((93 : ℝ) / 110) ≤ ((1691 : ℝ) / 2000))
  exact hmono.trans cosh_b8455_ub

private lemma cosh5_v_92_le : cosh (93 : ℝ) / 550 ≤ (101439956 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((93 : ℝ) / 550) (by norm_num) (by norm_num : ((93 : ℝ) / 550) ≤ ((339 : ℝ) / 2000))
  exact hmono.trans cosh_b1695_ub

private lemma sech5_pt_92_ge : (6497 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (93 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_92_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_92_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_93_le : cosh (47 : ℝ) / 55 ≤ (138832879 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((47 : ℝ) / 55) (by norm_num) (by norm_num : ((47 : ℝ) / 55) ≤ ((171 : ℝ) / 200))
  exact hmono.trans cosh_b8550_ub

private lemma cosh5_v_93_le : cosh (47 : ℝ) / 275 ≤ (101465617 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((47 : ℝ) / 275) (by norm_num) (by norm_num : ((47 : ℝ) / 275) ≤ ((171 : ℝ) / 1000))
  exact hmono.trans cosh_b1710_ub

private lemma sech5_pt_93_ge : (6453 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_93_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_93_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_94_le : cosh (19 : ℝ) / 22 ≤ (139705255 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((19 : ℝ) / 22) (by norm_num) (by norm_num : ((19 : ℝ) / 22) ≤ ((108 : ℝ) / 125))
  exact hmono.trans cosh_b8640_ub

private lemma cosh5_v_94_le : cosh (19 : ℝ) / 110 ≤ (101500186 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((19 : ℝ) / 110) (by norm_num) (by norm_num : ((19 : ℝ) / 110) ≤ ((173 : ℝ) / 1000))
  exact hmono.trans cosh_b1730_ub

private lemma sech5_pt_94_ge : (6411 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_94_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_94_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_95_le : cosh (48 : ℝ) / 55 ≤ (140588946 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((48 : ℝ) / 55) (by norm_num) (by norm_num : ((48 : ℝ) / 55) ≤ ((873 : ℝ) / 1000))
  exact hmono.trans cosh_b8730_ub

private lemma cosh5_v_95_le : cosh (48 : ℝ) / 275 ≤ (101535162 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((48 : ℝ) / 275) (by norm_num) (by norm_num : ((48 : ℝ) / 275) ≤ ((7 : ℝ) / 40))
  exact hmono.trans cosh_b1750_ub

private lemma sech5_pt_95_ge : (6368 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (48 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_95_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_95_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_96_le : cosh (97 : ℝ) / 110 ≤ (141484026 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((97 : ℝ) / 110) (by norm_num) (by norm_num : ((97 : ℝ) / 110) ≤ ((441 : ℝ) / 500))
  exact hmono.trans cosh_b8820_ub

private lemma cosh5_v_96_le : cosh (97 : ℝ) / 550 ≤ (101561661 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((97 : ℝ) / 550) (by norm_num) (by norm_num : ((97 : ℝ) / 550) ≤ ((353 : ℝ) / 2000))
  exact hmono.trans cosh_b1765_ub

private lemma sech5_pt_96_ge : (6326 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (97 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_96_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_96_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_97_le : cosh (49 : ℝ) / 55 ≤ (142390566 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((49 : ℝ) / 55) (by norm_num) (by norm_num : ((49 : ℝ) / 55) ≤ ((891 : ℝ) / 1000))
  exact hmono.trans cosh_b8910_ub

private lemma cosh5_v_97_le : cosh (49 : ℝ) / 275 ≤ (101597348 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((49 : ℝ) / 275) (by norm_num) (by norm_num : ((49 : ℝ) / 275) ≤ ((357 : ℝ) / 2000))
  exact hmono.trans cosh_b1785_ub

private lemma sech5_pt_97_ge : (6284 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_97_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_97_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_98_le : cosh (9 : ℝ) / 10 ≤ (143308639 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 10) (by norm_num) (by norm_num : ((9 : ℝ) / 10) ≤ ((9 : ℝ) / 10))
  exact hmono.trans cosh_b9000_ub

private lemma cosh5_v_98_le : cosh (9 : ℝ) / 50 ≤ (101624379 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 50) (by norm_num) (by norm_num : ((9 : ℝ) / 50) ≤ ((9 : ℝ) / 50))
  exact hmono.trans cosh_b1800_ub

private lemma sech5_pt_98_ge : (6242 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_98_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_98_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_99_le : cosh (10 : ℝ) / 11 ≤ (144290311 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((10 : ℝ) / 11) (by norm_num) (by norm_num : ((10 : ℝ) / 11) ≤ ((1819 : ℝ) / 2000))
  exact hmono.trans cosh_b9095_ub

private lemma cosh5_v_99_le : cosh (2 : ℝ) / 11 ≤ (101660777 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((2 : ℝ) / 11) (by norm_num) (by norm_num : ((2 : ℝ) / 11) ≤ ((91 : ℝ) / 500))
  exact hmono.trans cosh_b1820_ub

private lemma sech5_pt_99_ge : (6197 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (10 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_99_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_99_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma sech5_batch_1_ge : (360703 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (51 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (26 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (53 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 2 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (28 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (57 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (59 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (6 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (61 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (63 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (32 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (67 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (34 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (69 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (71 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (36 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (73 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (15 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (38 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (79 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (8 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (81 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (83 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (42 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (87 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (4 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (89 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (91 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (46 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (93 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (48 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (97 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (10 : ℝ) / 11 := by
  linarith [sech5_pt_50_ge, sech5_pt_51_ge, sech5_pt_52_ge, sech5_pt_53_ge, sech5_pt_54_ge, sech5_pt_55_ge, sech5_pt_56_ge, sech5_pt_57_ge, sech5_pt_58_ge, sech5_pt_59_ge, sech5_pt_60_ge, sech5_pt_61_ge, sech5_pt_62_ge, sech5_pt_63_ge, sech5_pt_64_ge, sech5_pt_65_ge, sech5_pt_66_ge, sech5_pt_67_ge, sech5_pt_68_ge, sech5_pt_69_ge, sech5_pt_70_ge, sech5_pt_71_ge, sech5_pt_72_ge, sech5_pt_73_ge, sech5_pt_74_ge, sech5_pt_75_ge, sech5_pt_76_ge, sech5_pt_77_ge, sech5_pt_78_ge, sech5_pt_79_ge, sech5_pt_80_ge, sech5_pt_81_ge, sech5_pt_82_ge, sech5_pt_83_ge, sech5_pt_84_ge, sech5_pt_85_ge, sech5_pt_86_ge, sech5_pt_87_ge, sech5_pt_88_ge, sech5_pt_89_ge, sech5_pt_90_ge, sech5_pt_91_ge, sech5_pt_92_ge, sech5_pt_93_ge, sech5_pt_94_ge, sech5_pt_95_ge, sech5_pt_96_ge, sech5_pt_97_ge, sech5_pt_98_ge, sech5_pt_99_ge]

private lemma cosh5_u_100_le : cosh (101 : ℝ) / 110 ≤ (145232328 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((101 : ℝ) / 110) (by norm_num) (by norm_num : ((101 : ℝ) / 110) ≤ ((1837 : ℝ) / 2000))
  exact hmono.trans cosh_b9185_ub

private lemma cosh5_v_100_le : cosh (101 : ℝ) / 550 ≤ (101697582 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((101 : ℝ) / 550) (by norm_num) (by norm_num : ((101 : ℝ) / 550) ≤ ((23 : ℝ) / 125))
  exact hmono.trans cosh_b1840_ub

private lemma sech5_pt_100_ge : (6155 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (101 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_100_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_100_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_101_le : cosh (51 : ℝ) / 55 ≤ (146186108 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((51 : ℝ) / 55) (by norm_num) (by norm_num : ((51 : ℝ) / 55) ≤ ((371 : ℝ) / 400))
  exact hmono.trans cosh_b9275_ub

private lemma cosh5_v_101_le : cosh (51 : ℝ) / 275 ≤ (101725452 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((51 : ℝ) / 275) (by norm_num) (by norm_num : ((51 : ℝ) / 275) ≤ ((371 : ℝ) / 2000))
  exact hmono.trans cosh_b1855_ub

private lemma sech5_pt_101_ge : (6113 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (51 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_101_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_101_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_102_le : cosh (103 : ℝ) / 110 ≤ (147151729 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((103 : ℝ) / 110) (by norm_num) (by norm_num : ((103 : ℝ) / 110) ≤ ((1873 : ℝ) / 2000))
  exact hmono.trans cosh_b9365_ub

private lemma cosh5_v_102_le : cosh (103 : ℝ) / 550 ≤ (101762969 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((103 : ℝ) / 550) (by norm_num) (by norm_num : ((103 : ℝ) / 550) ≤ ((3 : ℝ) / 16))
  exact hmono.trans cosh_b1875_ub

private lemma sech5_pt_102_ge : (6070 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (103 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_102_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_102_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_103_le : cosh (52 : ℝ) / 55 ≤ (148129270 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((52 : ℝ) / 55) (by norm_num) (by norm_num : ((52 : ℝ) / 55) ≤ ((1891 : ℝ) / 2000))
  exact hmono.trans cosh_b9455_ub

private lemma cosh5_v_103_le : cosh (52 : ℝ) / 275 ≤ (101800893 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((52 : ℝ) / 275) (by norm_num) (by norm_num : ((52 : ℝ) / 275) ≤ ((379 : ℝ) / 2000))
  exact hmono.trans cosh_b1895_ub

private lemma sech5_pt_103_ge : (6028 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (52 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_103_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_103_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_104_le : cosh (21 : ℝ) / 22 ≤ (149174137 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((21 : ℝ) / 22) (by norm_num) (by norm_num : ((21 : ℝ) / 22) ≤ ((191 : ℝ) / 200))
  exact hmono.trans cosh_b9550_ub

private lemma cosh5_v_104_le : cosh (21 : ℝ) / 110 ≤ (101829603 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((21 : ℝ) / 110) (by norm_num) (by norm_num : ((21 : ℝ) / 110) ≤ ((191 : ℝ) / 1000))
  exact hmono.trans cosh_b1910_ub

private lemma sech5_pt_104_ge : (5984 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_104_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_104_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_105_le : cosh (53 : ℝ) / 55 ≤ (150176428 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((53 : ℝ) / 55) (by norm_num) (by norm_num : ((53 : ℝ) / 55) ≤ ((241 : ℝ) / 250))
  exact hmono.trans cosh_b9640_ub

private lemma cosh5_v_105_le : cosh (53 : ℝ) / 275 ≤ (101868239 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((53 : ℝ) / 275) (by norm_num) (by norm_num : ((53 : ℝ) / 275) ≤ ((193 : ℝ) / 1000))
  exact hmono.trans cosh_b1930_ub

private lemma sech5_pt_105_ge : (5942 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (53 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_105_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_105_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_106_le : cosh (107 : ℝ) / 110 ≤ (151190884 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((107 : ℝ) / 110) (by norm_num) (by norm_num : ((107 : ℝ) / 110) ≤ ((973 : ℝ) / 1000))
  exact hmono.trans cosh_b9730_ub

private lemma cosh5_v_106_le : cosh (107 : ℝ) / 550 ≤ (101907283 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((107 : ℝ) / 550) (by norm_num) (by norm_num : ((107 : ℝ) / 550) ≤ ((39 : ℝ) / 200))
  exact hmono.trans cosh_b1950_ub

private lemma sech5_pt_106_ge : (5900 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (107 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_106_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_106_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_107_le : cosh (54 : ℝ) / 55 ≤ (152217586 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((54 : ℝ) / 55) (by norm_num) (by norm_num : ((54 : ℝ) / 55) ≤ ((491 : ℝ) / 500))
  exact hmono.trans cosh_b9820_ub

private lemma cosh5_v_107_le : cosh (54 : ℝ) / 275 ≤ (101936833 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((54 : ℝ) / 275) (by norm_num) (by norm_num : ((54 : ℝ) / 275) ≤ ((393 : ℝ) / 2000))
  exact hmono.trans cosh_b1965_ub

private lemma sech5_pt_107_ge : (5858 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (54 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_107_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_107_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_108_le : cosh (109 : ℝ) / 110 ≤ (153256618 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((109 : ℝ) / 110) (by norm_num) (by norm_num : ((109 : ℝ) / 110) ≤ ((991 : ℝ) / 1000))
  exact hmono.trans cosh_b9910_ub

private lemma cosh5_v_108_le : cosh (109 : ℝ) / 550 ≤ (101976590 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((109 : ℝ) / 550) (by norm_num) (by norm_num : ((109 : ℝ) / 550) ≤ ((397 : ℝ) / 2000))
  exact hmono.trans cosh_b1985_ub

private lemma sech5_pt_108_ge : (5816 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (109 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_108_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_108_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_109_le : cosh (1 : ℝ) / 1 ≤ (154308064 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 1) (by norm_num) (by norm_num : ((1 : ℝ) / 1) ≤ ((1 : ℝ) / 1))
  exact hmono.trans cosh_b10000_ub

private lemma cosh5_v_109_le : cosh (1 : ℝ) / 5 ≤ (102006676 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 5) (by norm_num) (by norm_num : ((1 : ℝ) / 5) ≤ ((1 : ℝ) / 5))
  exact hmono.trans cosh_b2000_ub

private lemma sech5_pt_109_ge : (5775 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 1 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_109_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_109_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_110_le : cosh (111 : ℝ) / 110 ≤ (155431485 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((111 : ℝ) / 110) (by norm_num) (by norm_num : ((111 : ℝ) / 110) ≤ ((2019 : ℝ) / 2000))
  exact hmono.trans cosh_b10095_ub

private lemma cosh5_v_110_le : cosh (111 : ℝ) / 550 ≤ (102047147 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((111 : ℝ) / 550) (by norm_num) (by norm_num : ((111 : ℝ) / 550) ≤ ((101 : ℝ) / 500))
  exact hmono.trans cosh_b2020_ub

private lemma sech5_pt_110_ge : (5731 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (111 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_110_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_110_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_111_le : cosh (56 : ℝ) / 55 ≤ (156508717 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((56 : ℝ) / 55) (by norm_num) (by norm_num : ((56 : ℝ) / 55) ≤ ((2037 : ℝ) / 2000))
  exact hmono.trans cosh_b10185_ub

private lemma cosh5_v_111_le : cosh (56 : ℝ) / 275 ≤ (102088027 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((56 : ℝ) / 275) (by norm_num) (by norm_num : ((56 : ℝ) / 275) ≤ ((51 : ℝ) / 250))
  exact hmono.trans cosh_b2040_ub

private lemma sech5_pt_111_ge : (5689 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (56 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_111_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_111_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_112_le : cosh (113 : ℝ) / 110 ≤ (157598626 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((113 : ℝ) / 110) (by norm_num) (by norm_num : ((113 : ℝ) / 110) ≤ ((411 : ℝ) / 400))
  exact hmono.trans cosh_b10275_ub

private lemma cosh5_v_112_le : cosh (113 : ℝ) / 550 ≤ (102118954 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((113 : ℝ) / 550) (by norm_num) (by norm_num : ((113 : ℝ) / 550) ≤ ((411 : ℝ) / 2000))
  exact hmono.trans cosh_b2055_ub

private lemma sech5_pt_112_ge : (5648 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (113 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_112_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_112_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_113_le : cosh (57 : ℝ) / 55 ≤ (158701301 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((57 : ℝ) / 55) (by norm_num) (by norm_num : ((57 : ℝ) / 55) ≤ ((2073 : ℝ) / 2000))
  exact hmono.trans cosh_b10365_ub

private lemma cosh5_v_113_le : cosh (57 : ℝ) / 275 ≤ (102160548 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((57 : ℝ) / 275) (by norm_num) (by norm_num : ((57 : ℝ) / 275) ≤ ((83 : ℝ) / 400))
  exact hmono.trans cosh_b2075_ub

private lemma sech5_pt_113_ge : (5607 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (57 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_113_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_113_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_114_le : cosh (23 : ℝ) / 22 ≤ (159816830 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((23 : ℝ) / 22) (by norm_num) (by norm_num : ((23 : ℝ) / 22) ≤ ((2091 : ℝ) / 2000))
  exact hmono.trans cosh_b10455_ub

private lemma cosh5_v_114_le : cosh (23 : ℝ) / 110 ≤ (102202551 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((23 : ℝ) / 110) (by norm_num) (by norm_num : ((23 : ℝ) / 110) ≤ ((419 : ℝ) / 2000))
  exact hmono.trans cosh_b2095_ub

private lemma sech5_pt_114_ge : (5565 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_114_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_114_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_115_le : cosh (58 : ℝ) / 55 ≤ (161008380 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((58 : ℝ) / 55) (by norm_num) (by norm_num : ((58 : ℝ) / 55) ≤ ((211 : ℝ) / 200))
  exact hmono.trans cosh_b10550_ub

private lemma cosh5_v_115_le : cosh (58 : ℝ) / 275 ≤ (102234322 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((58 : ℝ) / 275) (by norm_num) (by norm_num : ((58 : ℝ) / 275) ≤ ((211 : ℝ) / 1000))
  exact hmono.trans cosh_b2110_ub

private lemma sech5_pt_115_ge : (5522 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (58 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_115_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_115_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_116_le : cosh (117 : ℝ) / 110 ≤ (162150618 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((117 : ℝ) / 110) (by norm_num) (by norm_num : ((117 : ℝ) / 110) ≤ ((133 : ℝ) / 125))
  exact hmono.trans cosh_b10640_ub

private lemma cosh5_v_116_le : cosh (117 : ℝ) / 550 ≤ (102277040 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((117 : ℝ) / 550) (by norm_num) (by norm_num : ((117 : ℝ) / 550) ≤ ((213 : ℝ) / 1000))
  exact hmono.trans cosh_b2130_ub

private lemma sech5_pt_116_ge : (5481 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (117 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_116_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_116_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_117_le : cosh (59 : ℝ) / 55 ≤ (163305991 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((59 : ℝ) / 55) (by norm_num) (by norm_num : ((59 : ℝ) / 55) ≤ ((1073 : ℝ) / 1000))
  exact hmono.trans cosh_b10730_ub

private lemma cosh5_v_117_le : cosh (59 : ℝ) / 275 ≤ (102320167 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((59 : ℝ) / 275) (by norm_num) (by norm_num : ((59 : ℝ) / 275) ≤ ((43 : ℝ) / 200))
  exact hmono.trans cosh_b2150_ub

private lemma sech5_pt_117_ge : (5440 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (59 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_117_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_117_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_118_le : cosh (119 : ℝ) / 110 ≤ (164474591 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((119 : ℝ) / 110) (by norm_num) (by norm_num : ((119 : ℝ) / 110) ≤ ((541 : ℝ) / 500))
  exact hmono.trans cosh_b10820_ub

private lemma cosh5_v_118_le : cosh (119 : ℝ) / 550 ≤ (102352782 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((119 : ℝ) / 550) (by norm_num) (by norm_num : ((119 : ℝ) / 550) ≤ ((433 : ℝ) / 2000))
  exact hmono.trans cosh_b2165_ub

private lemma sech5_pt_118_ge : (5400 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (119 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_118_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_118_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_119_le : cosh (12 : ℝ) / 11 ≤ (165656514 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((12 : ℝ) / 11) (by norm_num) (by norm_num : ((12 : ℝ) / 11) ≤ ((1091 : ℝ) / 1000))
  exact hmono.trans cosh_b10910_ub

private lemma cosh5_v_119_le : cosh (12 : ℝ) / 55 ≤ (102396625 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((12 : ℝ) / 55) (by norm_num) (by norm_num : ((12 : ℝ) / 55) ≤ ((437 : ℝ) / 2000))
  exact hmono.trans cosh_b2185_ub

private lemma sech5_pt_119_ge : (5359 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (12 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_119_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_119_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_120_le : cosh (11 : ℝ) / 10 ≤ (166851856 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((11 : ℝ) / 10) (by norm_num) (by norm_num : ((11 : ℝ) / 10) ≤ ((11 : ℝ) / 10))
  exact hmono.trans cosh_b11000_ub

private lemma cosh5_v_120_le : cosh (11 : ℝ) / 50 ≤ (102429777 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((11 : ℝ) / 50) (by norm_num) (by norm_num : ((11 : ℝ) / 50) ≤ ((11 : ℝ) / 50))
  exact hmono.trans cosh_b2200_ub

private lemma sech5_pt_120_ge : (5319 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (11 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_120_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_120_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_121_le : cosh (61 : ℝ) / 55 ≤ (168128269 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((61 : ℝ) / 55) (by norm_num) (by norm_num : ((61 : ℝ) / 55) ≤ ((2219 : ℝ) / 2000))
  exact hmono.trans cosh_b11095_ub

private lemma cosh5_v_121_le : cosh (61 : ℝ) / 275 ≤ (102474338 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((61 : ℝ) / 275) (by norm_num) (by norm_num : ((61 : ℝ) / 275) ≤ ((111 : ℝ) / 500))
  exact hmono.trans cosh_b2220_ub

private lemma sech5_pt_121_ge : (5276 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (61 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_121_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_121_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_122_le : cosh (123 : ℝ) / 110 ≤ (169351498 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((123 : ℝ) / 110) (by norm_num) (by norm_num : ((123 : ℝ) / 110) ≤ ((2237 : ℝ) / 2000))
  exact hmono.trans cosh_b11185_ub

private lemma cosh5_v_122_le : cosh (123 : ℝ) / 550 ≤ (102519308 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((123 : ℝ) / 550) (by norm_num) (by norm_num : ((123 : ℝ) / 550) ≤ ((28 : ℝ) / 125))
  exact hmono.trans cosh_b2240_ub

private lemma sech5_pt_122_ge : (5236 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (123 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_122_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_122_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_123_le : cosh (62 : ℝ) / 55 ≤ (170588444 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((62 : ℝ) / 55) (by norm_num) (by norm_num : ((62 : ℝ) / 55) ≤ ((451 : ℝ) / 400))
  exact hmono.trans cosh_b11275_ub

private lemma cosh5_v_123_le : cosh (62 : ℝ) / 275 ≤ (102553305 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((62 : ℝ) / 275) (by norm_num) (by norm_num : ((62 : ℝ) / 275) ≤ ((451 : ℝ) / 2000))
  exact hmono.trans cosh_b2255_ub

private lemma sech5_pt_123_ge : (5196 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (62 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_123_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_123_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_124_le : cosh (25 : ℝ) / 22 ≤ (171839208 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((25 : ℝ) / 22) (by norm_num) (by norm_num : ((25 : ℝ) / 22) ≤ ((2273 : ℝ) / 2000))
  exact hmono.trans cosh_b11365_ub

private lemma cosh5_v_124_le : cosh (5 : ℝ) / 22 ≤ (102598994 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((5 : ℝ) / 22) (by norm_num) (by norm_num : ((5 : ℝ) / 22) ≤ ((91 : ℝ) / 400))
  exact hmono.trans cosh_b2275_ub

private lemma sech5_pt_124_ge : (5156 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (25 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_124_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_124_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_125_le : cosh (63 : ℝ) / 55 ≤ (173103891 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((63 : ℝ) / 55) (by norm_num) (by norm_num : ((63 : ℝ) / 55) ≤ ((2291 : ℝ) / 2000))
  exact hmono.trans cosh_b11455_ub

private lemma cosh5_v_125_le : cosh (63 : ℝ) / 275 ≤ (102645092 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((63 : ℝ) / 275) (by norm_num) (by norm_num : ((63 : ℝ) / 275) ≤ ((459 : ℝ) / 2000))
  exact hmono.trans cosh_b2295_ub

private lemma sech5_pt_125_ge : (5116 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (63 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_125_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_125_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_126_le : cosh (127 : ℝ) / 110 ≤ (174454048 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((127 : ℝ) / 110) (by norm_num) (by norm_num : ((127 : ℝ) / 110) ≤ ((231 : ℝ) / 200))
  exact hmono.trans cosh_b11550_ub

private lemma cosh5_v_126_le : cosh (127 : ℝ) / 550 ≤ (102679936 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((127 : ℝ) / 550) (by norm_num) (by norm_num : ((127 : ℝ) / 550) ≤ ((231 : ℝ) / 1000))
  exact hmono.trans cosh_b2310_ub

private lemma sech5_pt_126_ge : (5075 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (127 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_126_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_126_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_127_le : cosh (64 : ℝ) / 55 ≤ (175747666 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((64 : ℝ) / 55) (by norm_num) (by norm_num : ((64 : ℝ) / 55) ≤ ((291 : ℝ) / 250))
  exact hmono.trans cosh_b11640_ub

private lemma cosh5_v_127_le : cosh (64 : ℝ) / 275 ≤ (102726753 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((64 : ℝ) / 275) (by norm_num) (by norm_num : ((64 : ℝ) / 275) ≤ ((233 : ℝ) / 1000))
  exact hmono.trans cosh_b2330_ub

private lemma sech5_pt_127_ge : (5035 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (64 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_127_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_127_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_128_le : cosh (129 : ℝ) / 110 ≤ (177055519 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((129 : ℝ) / 110) (by norm_num) (by norm_num : ((129 : ℝ) / 110) ≤ ((1173 : ℝ) / 1000))
  exact hmono.trans cosh_b11730_ub

private lemma cosh5_v_128_le : cosh (129 : ℝ) / 550 ≤ (102773981 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((129 : ℝ) / 550) (by norm_num) (by norm_num : ((129 : ℝ) / 550) ≤ ((47 : ℝ) / 200))
  exact hmono.trans cosh_b2350_ub

private lemma sech5_pt_128_ge : (4995 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (129 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_128_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_128_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_129_le : cosh (13 : ℝ) / 11 ≤ (178377713 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((13 : ℝ) / 11) (by norm_num) (by norm_num : ((13 : ℝ) / 11) ≤ ((591 : ℝ) / 500))
  exact hmono.trans cosh_b11820_ub

private lemma cosh5_v_129_le : cosh (13 : ℝ) / 55 ≤ (102809672 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((13 : ℝ) / 55) (by norm_num) (by norm_num : ((13 : ℝ) / 55) ≤ ((473 : ℝ) / 2000))
  exact hmono.trans cosh_b2365_ub

private lemma sech5_pt_129_ge : (4957 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_129_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_129_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_130_le : cosh (131 : ℝ) / 110 ≤ (179714357 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((131 : ℝ) / 110) (by norm_num) (by norm_num : ((131 : ℝ) / 110) ≤ ((1191 : ℝ) / 1000))
  exact hmono.trans cosh_b11910_ub

private lemma cosh5_v_130_le : cosh (131 : ℝ) / 550 ≤ (102857620 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((131 : ℝ) / 550) (by norm_num) (by norm_num : ((131 : ℝ) / 550) ≤ ((477 : ℝ) / 2000))
  exact hmono.trans cosh_b2385_ub

private lemma sech5_pt_130_ge : (4917 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (131 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_130_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_130_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_131_le : cosh (6 : ℝ) / 5 ≤ (181065557 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((6 : ℝ) / 5) (by norm_num) (by norm_num : ((6 : ℝ) / 5) ≤ ((6 : ℝ) / 5))
  exact hmono.trans cosh_b12000_ub

private lemma cosh5_v_131_le : cosh (6 : ℝ) / 25 ≤ (102893851 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((6 : ℝ) / 25) (by norm_num) (by norm_num : ((6 : ℝ) / 25) ≤ ((6 : ℝ) / 25))
  exact hmono.trans cosh_b2400_ub

private lemma sech5_pt_131_ge : (4879 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (6 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_131_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_131_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_132_le : cosh (133 : ℝ) / 110 ≤ (182507738 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((133 : ℝ) / 110) (by norm_num) (by norm_num : ((133 : ℝ) / 110) ≤ ((2419 : ℝ) / 2000))
  exact hmono.trans cosh_b12095_ub

private lemma cosh5_v_132_le : cosh (133 : ℝ) / 550 ≤ (102942519 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((133 : ℝ) / 550) (by norm_num) (by norm_num : ((133 : ℝ) / 550) ≤ ((121 : ℝ) / 500))
  exact hmono.trans cosh_b2420_ub

private lemma sech5_pt_132_ge : (4838 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (133 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_132_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_132_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_133_le : cosh (67 : ℝ) / 55 ≤ (183889206 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((67 : ℝ) / 55) (by norm_num) (by norm_num : ((67 : ℝ) / 55) ≤ ((2437 : ℝ) / 2000))
  exact hmono.trans cosh_b12185_ub

private lemma cosh5_v_133_le : cosh (67 : ℝ) / 275 ≤ (102991599 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((67 : ℝ) / 275) (by norm_num) (by norm_num : ((67 : ℝ) / 275) ≤ ((61 : ℝ) / 250))
  exact hmono.trans cosh_b2440_ub

private lemma sech5_pt_133_ge : (4800 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (67 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_133_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_133_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_134_le : cosh (27 : ℝ) / 22 ≤ (185285569 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((27 : ℝ) / 22) (by norm_num) (by norm_num : ((27 : ℝ) / 22) ≤ ((491 : ℝ) / 400))
  exact hmono.trans cosh_b12275_ub

private lemma cosh5_v_134_le : cosh (27 : ℝ) / 110 ≤ (103028679 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((27 : ℝ) / 110) (by norm_num) (by norm_num : ((27 : ℝ) / 110) ≤ ((491 : ℝ) / 2000))
  exact hmono.trans cosh_b2455_ub

private lemma sech5_pt_134_ge : (4762 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_134_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_134_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_135_le : cosh (68 : ℝ) / 55 ≤ (186696940 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((68 : ℝ) / 55) (by norm_num) (by norm_num : ((68 : ℝ) / 55) ≤ ((2473 : ℝ) / 2000))
  exact hmono.trans cosh_b12365_ub

private lemma cosh5_v_135_le : cosh (68 : ℝ) / 275 ≤ (103078480 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((68 : ℝ) / 275) (by norm_num) (by norm_num : ((68 : ℝ) / 275) ≤ ((99 : ℝ) / 400))
  exact hmono.trans cosh_b2475_ub

private lemma sech5_pt_135_ge : (4723 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (68 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_135_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_135_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_136_le : cosh (137 : ℝ) / 110 ≤ (188123434 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((137 : ℝ) / 110) (by norm_num) (by norm_num : ((137 : ℝ) / 110) ≤ ((2491 : ℝ) / 2000))
  exact hmono.trans cosh_b12455_ub

private lemma cosh5_v_136_le : cosh (137 : ℝ) / 550 ≤ (103128693 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((137 : ℝ) / 550) (by norm_num) (by norm_num : ((137 : ℝ) / 550) ≤ ((499 : ℝ) / 2000))
  exact hmono.trans cosh_b2495_ub

private lemma sech5_pt_136_ge : (4685 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (137 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_136_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_136_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_137_le : cosh (69 : ℝ) / 55 ≤ (189645712 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((69 : ℝ) / 55) (by norm_num) (by norm_num : ((69 : ℝ) / 55) ≤ ((251 : ℝ) / 200))
  exact hmono.trans cosh_b12550_ub

private lemma cosh5_v_137_le : cosh (69 : ℝ) / 275 ≤ (103166623 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((69 : ℝ) / 275) (by norm_num) (by norm_num : ((69 : ℝ) / 275) ≤ ((251 : ℝ) / 1000))
  exact hmono.trans cosh_b2510_ub

private lemma sech5_pt_137_ge : (4646 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (69 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_137_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_137_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_138_le : cosh (139 : ℝ) / 110 ≤ (191103655 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((139 : ℝ) / 110) (by norm_num) (by norm_num : ((139 : ℝ) / 110) ≤ ((158 : ℝ) / 125))
  exact hmono.trans cosh_b12640_ub

private lemma cosh5_v_138_le : cosh (139 : ℝ) / 550 ≤ (103217558 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((139 : ℝ) / 550) (by norm_num) (by norm_num : ((139 : ℝ) / 550) ≤ ((253 : ℝ) / 1000))
  exact hmono.trans cosh_b2530_ub

private lemma sech5_pt_138_ge : (4608 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (139 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_138_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_138_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_139_le : cosh (14 : ℝ) / 11 ≤ (192577078 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((14 : ℝ) / 11) (by norm_num) (by norm_num : ((14 : ℝ) / 11) ≤ ((1273 : ℝ) / 1000))
  exact hmono.trans cosh_b12730_ub

private lemma cosh5_v_139_le : cosh (14 : ℝ) / 55 ≤ (103268906 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((14 : ℝ) / 55) (by norm_num) (by norm_num : ((14 : ℝ) / 55) ≤ ((51 : ℝ) / 200))
  exact hmono.trans cosh_b2550_ub

private lemma sech5_pt_139_ge : (4571 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (14 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_139_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_139_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_140_le : cosh (141 : ℝ) / 110 ≤ (194066100 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((141 : ℝ) / 110) (by norm_num) (by norm_num : ((141 : ℝ) / 110) ≤ ((641 : ℝ) / 500))
  exact hmono.trans cosh_b12820_ub

private lemma cosh5_v_140_le : cosh (141 : ℝ) / 550 ≤ (103307689 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((141 : ℝ) / 550) (by norm_num) (by norm_num : ((141 : ℝ) / 550) ≤ ((513 : ℝ) / 2000))
  exact hmono.trans cosh_b2565_ub

private lemma sech5_pt_140_ge : (4534 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (141 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_140_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_140_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_141_le : cosh (71 : ℝ) / 55 ≤ (195570841 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((71 : ℝ) / 55) (by norm_num) (by norm_num : ((71 : ℝ) / 55) ≤ ((1291 : ℝ) / 1000))
  exact hmono.trans cosh_b12910_ub

private lemma cosh5_v_141_le : cosh (71 : ℝ) / 275 ≤ (103359760 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((71 : ℝ) / 275) (by norm_num) (by norm_num : ((71 : ℝ) / 275) ≤ ((517 : ℝ) / 2000))
  exact hmono.trans cosh_b2585_ub

private lemma sech5_pt_141_ge : (4497 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (71 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_141_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_141_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_142_le : cosh (13 : ℝ) / 10 ≤ (197091424 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((13 : ℝ) / 10) (by norm_num) (by norm_num : ((13 : ℝ) / 10) ≤ ((13 : ℝ) / 10))
  exact hmono.trans cosh_b13000_ub

private lemma cosh5_v_142_le : cosh (13 : ℝ) / 50 ≤ (103399084 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((13 : ℝ) / 50) (by norm_num) (by norm_num : ((13 : ℝ) / 50) ≤ ((13 : ℝ) / 50))
  exact hmono.trans cosh_b2600_ub

private lemma sech5_pt_142_ge : (4460 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_142_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_142_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_143_le : cosh (72 : ℝ) / 55 ≤ (198713805 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((72 : ℝ) / 55) (by norm_num) (by norm_num : ((72 : ℝ) / 55) ≤ ((2619 : ℝ) / 2000))
  exact hmono.trans cosh_b13095_ub

private lemma cosh5_v_143_le : cosh (72 : ℝ) / 275 ≤ (103451879 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((72 : ℝ) / 275) (by norm_num) (by norm_num : ((72 : ℝ) / 275) ≤ ((131 : ℝ) / 500))
  exact hmono.trans cosh_b2620_ub

private lemma sech5_pt_143_ge : (4422 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (72 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_143_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_143_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_144_le : cosh (29 : ℝ) / 22 ≤ (200267339 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((29 : ℝ) / 22) (by norm_num) (by norm_num : ((29 : ℝ) / 22) ≤ ((2637 : ℝ) / 2000))
  exact hmono.trans cosh_b13185_ub

private lemma cosh5_v_144_le : cosh (29 : ℝ) / 110 ≤ (103505087 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((29 : ℝ) / 110) (by norm_num) (by norm_num : ((29 : ℝ) / 110) ≤ ((33 : ℝ) / 125))
  exact hmono.trans cosh_b2640_ub

private lemma sech5_pt_144_ge : (4385 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_144_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_144_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_145_le : cosh (73 : ℝ) / 55 ≤ (201837094 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((73 : ℝ) / 55) (by norm_num) (by norm_num : ((73 : ℝ) / 55) ≤ ((531 : ℝ) / 400))
  exact hmono.trans cosh_b13275_ub

private lemma cosh5_v_145_le : cosh (73 : ℝ) / 275 ≤ (103545265 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((73 : ℝ) / 275) (by norm_num) (by norm_num : ((73 : ℝ) / 275) ≤ ((531 : ℝ) / 2000))
  exact hmono.trans cosh_b2655_ub

private lemma sech5_pt_145_ge : (4349 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (73 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_145_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_145_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_146_le : cosh (147 : ℝ) / 110 ≤ (203423198 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((147 : ℝ) / 110) (by norm_num) (by norm_num : ((147 : ℝ) / 110) ≤ ((2673 : ℝ) / 2000))
  exact hmono.trans cosh_b13365_ub

private lemma cosh5_v_146_le : cosh (147 : ℝ) / 550 ≤ (103599199 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((147 : ℝ) / 550) (by norm_num) (by norm_num : ((147 : ℝ) / 550) ≤ ((107 : ℝ) / 400))
  exact hmono.trans cosh_b2675_ub

private lemma sech5_pt_146_ge : (4313 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (147 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_146_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_146_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_147_le : cosh (74 : ℝ) / 55 ≤ (205025780 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((74 : ℝ) / 55) (by norm_num) (by norm_num : ((74 : ℝ) / 55) ≤ ((2691 : ℝ) / 2000))
  exact hmono.trans cosh_b13455_ub

private lemma cosh5_v_147_le : cosh (74 : ℝ) / 275 ≤ (103653546 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((74 : ℝ) / 275) (by norm_num) (by norm_num : ((74 : ℝ) / 275) ≤ ((539 : ℝ) / 2000))
  exact hmono.trans cosh_b2695_ub

private lemma sech5_pt_147_ge : (4277 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (74 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_147_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_147_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_148_le : cosh (149 : ℝ) / 110 ≤ (206735413 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((149 : ℝ) / 110) (by norm_num) (by norm_num : ((149 : ℝ) / 110) ≤ ((271 : ℝ) / 200))
  exact hmono.trans cosh_b13550_ub

private lemma cosh5_v_148_le : cosh (149 : ℝ) / 550 ≤ (103694579 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((149 : ℝ) / 550) (by norm_num) (by norm_num : ((149 : ℝ) / 550) ≤ ((271 : ℝ) / 1000))
  exact hmono.trans cosh_b2710_ub

private lemma sech5_pt_148_ge : (4240 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (149 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_148_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_148_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_149_le : cosh (15 : ℝ) / 11 ≤ (208372274 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((15 : ℝ) / 11) (by norm_num) (by norm_num : ((15 : ℝ) / 11) ≤ ((341 : ℝ) / 250))
  exact hmono.trans cosh_b13640_ub

private lemma cosh5_v_149_le : cosh (3 : ℝ) / 11 ≤ (103749652 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 11) (by norm_num) (by norm_num : ((3 : ℝ) / 11) ≤ ((273 : ℝ) / 1000))
  exact hmono.trans cosh_b2730_ub

private lemma sech5_pt_149_ge : (4205 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (15 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_149_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_149_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma sech5_batch_2_ge : (257581 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (101 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (51 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (103 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (52 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (53 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (107 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (54 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (109 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 1 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (111 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (56 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (113 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (57 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (58 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (117 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (59 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (119 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (12 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (11 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (61 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (123 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (62 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (25 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (63 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (127 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (64 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (129 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (131 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (6 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (133 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (67 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (68 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (137 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (69 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (139 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (14 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (141 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (71 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (72 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (73 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (147 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (74 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (149 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (15 : ℝ) / 11 := by
  linarith [sech5_pt_100_ge, sech5_pt_101_ge, sech5_pt_102_ge, sech5_pt_103_ge, sech5_pt_104_ge, sech5_pt_105_ge, sech5_pt_106_ge, sech5_pt_107_ge, sech5_pt_108_ge, sech5_pt_109_ge, sech5_pt_110_ge, sech5_pt_111_ge, sech5_pt_112_ge, sech5_pt_113_ge, sech5_pt_114_ge, sech5_pt_115_ge, sech5_pt_116_ge, sech5_pt_117_ge, sech5_pt_118_ge, sech5_pt_119_ge, sech5_pt_120_ge, sech5_pt_121_ge, sech5_pt_122_ge, sech5_pt_123_ge, sech5_pt_124_ge, sech5_pt_125_ge, sech5_pt_126_ge, sech5_pt_127_ge, sech5_pt_128_ge, sech5_pt_129_ge, sech5_pt_130_ge, sech5_pt_131_ge, sech5_pt_132_ge, sech5_pt_133_ge, sech5_pt_134_ge, sech5_pt_135_ge, sech5_pt_136_ge, sech5_pt_137_ge, sech5_pt_138_ge, sech5_pt_139_ge, sech5_pt_140_ge, sech5_pt_141_ge, sech5_pt_142_ge, sech5_pt_143_ge, sech5_pt_144_ge, sech5_pt_145_ge, sech5_pt_146_ge, sech5_pt_147_ge, sech5_pt_148_ge, sech5_pt_149_ge]

private lemma cosh5_u_150_le : cosh (151 : ℝ) / 110 ≤ (210026013 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((151 : ℝ) / 110) (by norm_num) (by norm_num : ((151 : ℝ) / 110) ≤ ((1373 : ℝ) / 1000))
  exact hmono.trans cosh_b13730_ub

private lemma cosh5_v_150_le : cosh (151 : ℝ) / 550 ≤ (103805140 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((151 : ℝ) / 550) (by norm_num) (by norm_num : ((151 : ℝ) / 550) ≤ ((11 : ℝ) / 40))
  exact hmono.trans cosh_b2750_ub

private lemma sech5_pt_150_ge : (4169 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (151 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_150_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_150_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_151_le : cosh (76 : ℝ) / 55 ≤ (211696765 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((76 : ℝ) / 55) (by norm_num) (by norm_num : ((76 : ℝ) / 55) ≤ ((691 : ℝ) / 500))
  exact hmono.trans cosh_b13820_ub

private lemma cosh5_v_151_le : cosh (76 : ℝ) / 275 ≤ (103847029 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((76 : ℝ) / 275) (by norm_num) (by norm_num : ((76 : ℝ) / 275) ≤ ((553 : ℝ) / 2000))
  exact hmono.trans cosh_b2765_ub

private lemma sech5_pt_151_ge : (4135 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (76 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_151_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_151_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_152_le : cosh (153 : ℝ) / 110 ≤ (213384664 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((153 : ℝ) / 110) (by norm_num) (by norm_num : ((153 : ℝ) / 110) ≤ ((1391 : ℝ) / 1000))
  exact hmono.trans cosh_b13910_ub

private lemma cosh5_v_152_le : cosh (153 : ℝ) / 550 ≤ (103903244 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((153 : ℝ) / 550) (by norm_num) (by norm_num : ((153 : ℝ) / 550) ≤ ((557 : ℝ) / 2000))
  exact hmono.trans cosh_b2785_ub

private lemma sech5_pt_152_ge : (4100 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (153 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_152_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_152_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_153_le : cosh (7 : ℝ) / 5 ≤ (215089847 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 5) (by norm_num) (by norm_num : ((7 : ℝ) / 5) ≤ ((7 : ℝ) / 5))
  exact hmono.trans cosh_b14000_ub

private lemma cosh5_v_153_le : cosh (7 : ℝ) / 25 ≤ (103945678 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 25) (by norm_num) (by norm_num : ((7 : ℝ) / 25) ≤ ((7 : ℝ) / 25))
  exact hmono.trans cosh_b2800_ub

private lemma sech5_pt_153_ge : (4066 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_153_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_153_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_154_le : cosh (31 : ℝ) / 22 ≤ (216908667 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((31 : ℝ) / 22) (by norm_num) (by norm_num : ((31 : ℝ) / 22) ≤ ((2819 : ℝ) / 2000))
  exact hmono.trans cosh_b14095_ub

private lemma cosh5_v_154_le : cosh (31 : ℝ) / 110 ≤ (104002621 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((31 : ℝ) / 110) (by norm_num) (by norm_num : ((31 : ℝ) / 110) ≤ ((141 : ℝ) / 500))
  exact hmono.trans cosh_b2820_ub

private lemma sech5_pt_154_ge : (4029 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_154_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_154_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_155_le : cosh (78 : ℝ) / 55 ≤ (218649814 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((78 : ℝ) / 55) (by norm_num) (by norm_num : ((78 : ℝ) / 55) ≤ ((2837 : ℝ) / 2000))
  exact hmono.trans cosh_b14185_ub

private lemma cosh5_v_155_le : cosh (78 : ℝ) / 275 ≤ (104059979 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((78 : ℝ) / 275) (by norm_num) (by norm_num : ((78 : ℝ) / 275) ≤ ((71 : ℝ) / 250))
  exact hmono.trans cosh_b2840_ub

private lemma sech5_pt_155_ge : (3995 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (78 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_155_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_155_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_156_le : cosh (157 : ℝ) / 110 ≤ (220408672 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((157 : ℝ) / 110) (by norm_num) (by norm_num : ((157 : ℝ) / 110) ≤ ((571 : ℝ) / 400))
  exact hmono.trans cosh_b14275_ub

private lemma cosh5_v_156_le : cosh (157 : ℝ) / 550 ≤ (104103271 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((157 : ℝ) / 550) (by norm_num) (by norm_num : ((157 : ℝ) / 550) ≤ ((571 : ℝ) / 2000))
  exact hmono.trans cosh_b2855_ub

private lemma sech5_pt_156_ge : (3961 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (157 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_156_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_156_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_157_le : cosh (79 : ℝ) / 55 ≤ (222185384 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((79 : ℝ) / 55) (by norm_num) (by norm_num : ((79 : ℝ) / 55) ≤ ((2873 : ℝ) / 2000))
  exact hmono.trans cosh_b14365_ub

private lemma cosh5_v_157_le : cosh (79 : ℝ) / 275 ≤ (104161358 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((79 : ℝ) / 275) (by norm_num) (by norm_num : ((79 : ℝ) / 275) ≤ ((23 : ℝ) / 80))
  exact hmono.trans cosh_b2875_ub

private lemma sech5_pt_157_ge : (3928 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (79 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_157_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_157_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_158_le : cosh (159 : ℝ) / 110 ≤ (223980092 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((159 : ℝ) / 110) (by norm_num) (by norm_num : ((159 : ℝ) / 110) ≤ ((2891 : ℝ) / 2000))
  exact hmono.trans cosh_b14455_ub

private lemma cosh5_v_158_le : cosh (159 : ℝ) / 550 ≤ (104219862 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((159 : ℝ) / 550) (by norm_num) (by norm_num : ((159 : ℝ) / 550) ≤ ((579 : ℝ) / 2000))
  exact hmono.trans cosh_b2895_ub

private lemma sech5_pt_158_ge : (3894 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (159 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_158_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_158_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_159_le : cosh (16 : ℝ) / 11 ≤ (225894192 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((16 : ℝ) / 11) (by norm_num) (by norm_num : ((16 : ℝ) / 11) ≤ ((291 : ℝ) / 200))
  exact hmono.trans cosh_b14550_ub

private lemma cosh5_v_159_le : cosh (16 : ℝ) / 55 ≤ (104264014 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((16 : ℝ) / 55) (by norm_num) (by norm_num : ((16 : ℝ) / 55) ≤ ((291 : ℝ) / 1000))
  exact hmono.trans cosh_b2910_ub

private lemma sech5_pt_159_ge : (3859 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (16 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_159_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_159_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_160_le : cosh (161 : ℝ) / 110 ≤ (227726353 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((161 : ℝ) / 110) (by norm_num) (by norm_num : ((161 : ℝ) / 110) ≤ ((183 : ℝ) / 125))
  exact hmono.trans cosh_b14640_ub

private lemma cosh5_v_160_le : cosh (161 : ℝ) / 550 ≤ (104323247 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((161 : ℝ) / 550) (by norm_num) (by norm_num : ((161 : ℝ) / 550) ≤ ((293 : ℝ) / 1000))
  exact hmono.trans cosh_b2930_ub

private lemma sech5_pt_160_ge : (3826 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (161 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_160_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_160_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_161_le : cosh (81 : ℝ) / 55 ≤ (229576959 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((81 : ℝ) / 55) (by norm_num) (by norm_num : ((81 : ℝ) / 55) ≤ ((1473 : ℝ) / 1000))
  exact hmono.trans cosh_b14730_ub

private lemma cosh5_v_161_le : cosh (81 : ℝ) / 275 ≤ (104382898 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((81 : ℝ) / 275) (by norm_num) (by norm_num : ((81 : ℝ) / 275) ≤ ((59 : ℝ) / 200))
  exact hmono.trans cosh_b2950_ub

private lemma sech5_pt_161_ge : (3793 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (81 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_161_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_161_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_162_le : cosh (163 : ℝ) / 110 ≤ (231446162 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((163 : ℝ) / 110) (by norm_num) (by norm_num : ((163 : ℝ) / 110) ≤ ((741 : ℝ) / 500))
  exact hmono.trans cosh_b14820_ub

private lemma cosh5_v_162_le : cosh (163 : ℝ) / 550 ≤ (104427910 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((163 : ℝ) / 550) (by norm_num) (by norm_num : ((163 : ℝ) / 550) ≤ ((593 : ℝ) / 2000))
  exact hmono.trans cosh_b2965_ub

private lemma sech5_pt_162_ge : (3761 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (163 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_162_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_162_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_163_le : cosh (82 : ℝ) / 55 ≤ (233334112 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((82 : ℝ) / 55) (by norm_num) (by norm_num : ((82 : ℝ) / 55) ≤ ((1491 : ℝ) / 1000))
  exact hmono.trans cosh_b14910_ub

private lemma cosh5_v_163_le : cosh (82 : ℝ) / 275 ≤ (104488291 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((82 : ℝ) / 275) (by norm_num) (by norm_num : ((82 : ℝ) / 275) ≤ ((597 : ℝ) / 2000))
  exact hmono.trans cosh_b2985_ub

private lemma sech5_pt_163_ge : (3728 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (82 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_163_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_163_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_164_le : cosh (3 : ℝ) / 2 ≤ (235240962 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 2) (by norm_num) (by norm_num : ((3 : ℝ) / 2) ≤ ((3 : ℝ) / 2))
  exact hmono.trans cosh_b15000_ub

private lemma cosh5_v_164_le : cosh (3 : ℝ) / 10 ≤ (104533852 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 10) (by norm_num) (by norm_num : ((3 : ℝ) / 10) ≤ ((3 : ℝ) / 10))
  exact hmono.trans cosh_b3000_ub

private lemma sech5_pt_164_ge : (3696 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 2 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_164_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_164_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_165_le : cosh (83 : ℝ) / 55 ≤ (237274423 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((83 : ℝ) / 55) (by norm_num) (by norm_num : ((83 : ℝ) / 55) ≤ ((3019 : ℝ) / 2000))
  exact hmono.trans cosh_b15095_ub

private lemma cosh5_v_165_le : cosh (83 : ℝ) / 275 ≤ (104594965 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((83 : ℝ) / 275) (by norm_num) (by norm_num : ((83 : ℝ) / 275) ≤ ((151 : ℝ) / 500))
  exact hmono.trans cosh_b3020_ub

private lemma sech5_pt_165_ge : (3663 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (83 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_165_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_165_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_166_le : cosh (167 : ℝ) / 110 ≤ (239220610 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((167 : ℝ) / 110) (by norm_num) (by norm_num : ((167 : ℝ) / 110) ≤ ((3037 : ℝ) / 2000))
  exact hmono.trans cosh_b15185_ub

private lemma cosh5_v_166_le : cosh (167 : ℝ) / 550 ≤ (104656497 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((167 : ℝ) / 550) (by norm_num) (by norm_num : ((167 : ℝ) / 550) ≤ ((38 : ℝ) / 125))
  exact hmono.trans cosh_b3040_ub

private lemma sech5_pt_166_ge : (3631 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (167 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_166_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_166_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_167_le : cosh (84 : ℝ) / 55 ≤ (241186175 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((84 : ℝ) / 55) (by norm_num) (by norm_num : ((84 : ℝ) / 55) ≤ ((611 : ℝ) / 400))
  exact hmono.trans cosh_b15275_ub

private lemma cosh5_v_167_le : cosh (84 : ℝ) / 275 ≤ (104702920 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((84 : ℝ) / 275) (by norm_num) (by norm_num : ((84 : ℝ) / 275) ≤ ((611 : ℝ) / 2000))
  exact hmono.trans cosh_b3055_ub

private lemma sech5_pt_167_ge : (3599 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (84 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_167_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_167_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_168_le : cosh (169 : ℝ) / 110 ≤ (243171275 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((169 : ℝ) / 110) (by norm_num) (by norm_num : ((169 : ℝ) / 110) ≤ ((3073 : ℝ) / 2000))
  exact hmono.trans cosh_b15365_ub

private lemma cosh5_v_168_le : cosh (169 : ℝ) / 550 ≤ (104765184 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((169 : ℝ) / 550) (by norm_num) (by norm_num : ((169 : ℝ) / 550) ≤ ((123 : ℝ) / 400))
  exact hmono.trans cosh_b3075_ub

private lemma sech5_pt_168_ge : (3568 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (169 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_168_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_168_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_169_le : cosh (17 : ℝ) / 11 ≤ (245176073 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((17 : ℝ) / 11) (by norm_num) (by norm_num : ((17 : ℝ) / 11) ≤ ((3091 : ℝ) / 2000))
  exact hmono.trans cosh_b15455_ub

private lemma cosh5_v_169_le : cosh (17 : ℝ) / 55 ≤ (104827868 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((17 : ℝ) / 55) (by norm_num) (by norm_num : ((17 : ℝ) / 55) ≤ ((619 : ℝ) / 2000))
  exact hmono.trans cosh_b3095_ub

private lemma sech5_pt_169_ge : (3537 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_169_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_169_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_170_le : cosh (171 : ℝ) / 110 ≤ (247313796 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((171 : ℝ) / 110) (by norm_num) (by norm_num : ((171 : ℝ) / 110) ≤ ((311 : ℝ) / 200))
  exact hmono.trans cosh_b15550_ub

private lemma cosh5_v_170_le : cosh (171 : ℝ) / 550 ≤ (104875155 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((171 : ℝ) / 550) (by norm_num) (by norm_num : ((171 : ℝ) / 550) ≤ ((311 : ℝ) / 1000))
  exact hmono.trans cosh_b3110_ub

private lemma sech5_pt_170_ge : (3504 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (171 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_170_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_170_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_171_le : cosh (86 : ℝ) / 55 ≤ (249359593 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((86 : ℝ) / 55) (by norm_num) (by norm_num : ((86 : ℝ) / 55) ≤ ((391 : ℝ) / 250))
  exact hmono.trans cosh_b15640_ub

private lemma cosh5_v_171_le : cosh (86 : ℝ) / 275 ≤ (104938573 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((86 : ℝ) / 275) (by norm_num) (by norm_num : ((86 : ℝ) / 275) ≤ ((313 : ℝ) / 1000))
  exact hmono.trans cosh_b3130_ub

private lemma sech5_pt_171_ge : (3474 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (86 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_171_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_171_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_172_le : cosh (173 : ℝ) / 110 ≤ (251425589 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((173 : ℝ) / 110) (by norm_num) (by norm_num : ((173 : ℝ) / 110) ≤ ((1573 : ℝ) / 1000))
  exact hmono.trans cosh_b15730_ub

private lemma cosh5_v_172_le : cosh (173 : ℝ) / 550 ≤ (105002410 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((173 : ℝ) / 550) (by norm_num) (by norm_num : ((173 : ℝ) / 550) ≤ ((63 : ℝ) / 200))
  exact hmono.trans cosh_b3150_ub

private lemma sech5_pt_172_ge : (3443 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (173 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_172_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_172_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_173_le : cosh (87 : ℝ) / 55 ≤ (253511950 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((87 : ℝ) / 55) (by norm_num) (by norm_num : ((87 : ℝ) / 55) ≤ ((791 : ℝ) / 500))
  exact hmono.trans cosh_b15820_ub

private lemma cosh5_v_173_le : cosh (87 : ℝ) / 275 ≤ (105050563 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((87 : ℝ) / 275) (by norm_num) (by norm_num : ((87 : ℝ) / 275) ≤ ((633 : ℝ) / 2000))
  exact hmono.trans cosh_b3165_ub

private lemma sech5_pt_173_ge : (3413 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (87 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_173_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_173_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_174_le : cosh (35 : ℝ) / 22 ≤ (255618846 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((35 : ℝ) / 22) (by norm_num) (by norm_num : ((35 : ℝ) / 22) ≤ ((1591 : ℝ) / 1000))
  exact hmono.trans cosh_b15910_ub

private lemma cosh5_v_174_le : cosh (7 : ℝ) / 22 ≤ (105115135 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 22) (by norm_num) (by norm_num : ((7 : ℝ) / 22) ≤ ((637 : ℝ) / 2000))
  exact hmono.trans cosh_b3185_ub

private lemma sech5_pt_174_ge : (3383 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (35 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_174_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_174_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_175_le : cosh (8 : ℝ) / 5 ≤ (257746448 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((8 : ℝ) / 5) (by norm_num) (by norm_num : ((8 : ℝ) / 5) ≤ ((8 : ℝ) / 5))
  exact hmono.trans cosh_b16000_ub

private lemma cosh5_v_175_le : cosh (8 : ℝ) / 25 ≤ (105163841 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((8 : ℝ) / 25) (by norm_num) (by norm_num : ((8 : ℝ) / 25) ≤ ((8 : ℝ) / 25))
  exact hmono.trans cosh_b3200_ub

private lemma sech5_pt_175_ge : (3353 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (8 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_175_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_175_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_176_le : cosh (177 : ℝ) / 110 ≤ (260014902 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((177 : ℝ) / 110) (by norm_num) (by norm_num : ((177 : ℝ) / 110) ≤ ((3219 : ℝ) / 2000))
  exact hmono.trans cosh_b16095_ub

private lemma cosh5_v_176_le : cosh (177 : ℝ) / 550 ≤ (105229149 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((177 : ℝ) / 550) (by norm_num) (by norm_num : ((177 : ℝ) / 550) ≤ ((161 : ℝ) / 500))
  exact hmono.trans cosh_b3220_ub

private lemma sech5_pt_176_ge : (3322 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (177 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_176_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_176_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_177_le : cosh (89 : ℝ) / 55 ≤ (262185607 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((89 : ℝ) / 55) (by norm_num) (by norm_num : ((89 : ℝ) / 55) ≤ ((3237 : ℝ) / 2000))
  exact hmono.trans cosh_b16185_ub

private lemma cosh5_v_177_le : cosh (89 : ℝ) / 275 ≤ (105294878 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((89 : ℝ) / 275) (by norm_num) (by norm_num : ((89 : ℝ) / 275) ≤ ((81 : ℝ) / 250))
  exact hmono.trans cosh_b3240_ub

private lemma sech5_pt_177_ge : (3292 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (89 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_177_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_177_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_178_le : cosh (179 : ℝ) / 110 ≤ (264377549 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((179 : ℝ) / 110) (by norm_num) (by norm_num : ((179 : ℝ) / 110) ≤ ((651 : ℝ) / 400))
  exact hmono.trans cosh_b16275_ub

private lemma cosh5_v_178_le : cosh (179 : ℝ) / 550 ≤ (105344451 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((179 : ℝ) / 550) (by norm_num) (by norm_num : ((179 : ℝ) / 550) ≤ ((651 : ℝ) / 2000))
  exact hmono.trans cosh_b3255_ub

private lemma sech5_pt_178_ge : (3264 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (179 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_178_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_178_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_179_le : cosh (18 : ℝ) / 11 ≤ (266590906 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((18 : ℝ) / 11) (by norm_num) (by norm_num : ((18 : ℝ) / 11) ≤ ((3273 : ℝ) / 2000))
  exact hmono.trans cosh_b16365_ub

private lemma cosh5_v_179_le : cosh (18 : ℝ) / 55 ≤ (105410918 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((18 : ℝ) / 55) (by norm_num) (by norm_num : ((18 : ℝ) / 55) ≤ ((131 : ℝ) / 400))
  exact hmono.trans cosh_b3275_ub

private lemma sech5_pt_179_ge : (3235 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (18 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_179_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_179_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_180_le : cosh (181 : ℝ) / 110 ≤ (268825858 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((181 : ℝ) / 110) (by norm_num) (by norm_num : ((181 : ℝ) / 110) ≤ ((3291 : ℝ) / 2000))
  exact hmono.trans cosh_b16455_ub

private lemma cosh5_v_180_le : cosh (181 : ℝ) / 550 ≤ (105477806 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((181 : ℝ) / 550) (by norm_num) (by norm_num : ((181 : ℝ) / 550) ≤ ((659 : ℝ) / 2000))
  exact hmono.trans cosh_b3295_ub

private lemma sech5_pt_180_ge : (3206 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (181 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_180_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_180_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_181_le : cosh (91 : ℝ) / 55 ≤ (271208599 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((91 : ℝ) / 55) (by norm_num) (by norm_num : ((91 : ℝ) / 55) ≤ ((331 : ℝ) / 200))
  exact hmono.trans cosh_b16550_ub

private lemma cosh5_v_181_le : cosh (91 : ℝ) / 275 ≤ (105528249 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((91 : ℝ) / 275) (by norm_num) (by norm_num : ((91 : ℝ) / 275) ≤ ((331 : ℝ) / 1000))
  exact hmono.trans cosh_b3310_ub

private lemma sech5_pt_181_ge : (3176 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (91 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_181_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_181_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_182_le : cosh (183 : ℝ) / 110 ≤ (273488509 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((183 : ℝ) / 110) (by norm_num) (by norm_num : ((183 : ℝ) / 110) ≤ ((208 : ℝ) / 125))
  exact hmono.trans cosh_b16640_ub

private lemma cosh5_v_182_le : cosh (183 : ℝ) / 550 ≤ (105595875 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((183 : ℝ) / 550) (by norm_num) (by norm_num : ((183 : ℝ) / 550) ≤ ((333 : ℝ) / 1000))
  exact hmono.trans cosh_b3330_ub

private lemma sech5_pt_182_ge : (3147 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (183 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_182_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_182_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_183_le : cosh (92 : ℝ) / 55 ≤ (275790570 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((92 : ℝ) / 55) (by norm_num) (by norm_num : ((92 : ℝ) / 55) ≤ ((1673 : ℝ) / 1000))
  exact hmono.trans cosh_b16730_ub

private lemma cosh5_v_183_le : cosh (92 : ℝ) / 275 ≤ (105663924 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((92 : ℝ) / 275) (by norm_num) (by norm_num : ((92 : ℝ) / 275) ≤ ((67 : ℝ) / 200))
  exact hmono.trans cosh_b3350_ub

private lemma sech5_pt_183_ge : (3119 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (92 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_183_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_183_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_184_le : cosh (37 : ℝ) / 22 ≤ (278114972 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((37 : ℝ) / 22) (by norm_num) (by norm_num : ((37 : ℝ) / 22) ≤ ((841 : ℝ) / 500))
  exact hmono.trans cosh_b16820_ub

private lemma cosh5_v_184_le : cosh (37 : ℝ) / 110 ≤ (105715238 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((37 : ℝ) / 110) (by norm_num) (by norm_num : ((37 : ℝ) / 110) ≤ ((673 : ℝ) / 2000))
  exact hmono.trans cosh_b3365_ub

private lemma sech5_pt_184_ge : (3092 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_184_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_184_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_185_le : cosh (93 : ℝ) / 55 ≤ (280461900 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((93 : ℝ) / 55) (by norm_num) (by norm_num : ((93 : ℝ) / 55) ≤ ((1691 : ℝ) / 1000))
  exact hmono.trans cosh_b16910_ub

private lemma cosh5_v_185_le : cosh (93 : ℝ) / 275 ≤ (105784027 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((93 : ℝ) / 275) (by norm_num) (by norm_num : ((93 : ℝ) / 275) ≤ ((677 : ℝ) / 2000))
  exact hmono.trans cosh_b3385_ub

private lemma sech5_pt_185_ge : (3064 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (93 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_185_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_185_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_186_le : cosh (17 : ℝ) / 10 ≤ (282831546 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((17 : ℝ) / 10) (by norm_num) (by norm_num : ((17 : ℝ) / 10) ≤ ((17 : ℝ) / 10))
  exact hmono.trans cosh_b17000_ub

private lemma cosh5_v_186_le : cosh (17 : ℝ) / 50 ≤ (105835896 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((17 : ℝ) / 50) (by norm_num) (by norm_num : ((17 : ℝ) / 50) ≤ ((17 : ℝ) / 50))
  exact hmono.trans cosh_b3400_ub

private lemma sech5_pt_186_ge : (3037 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_186_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_186_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_187_le : cosh (94 : ℝ) / 55 ≤ (285357697 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((94 : ℝ) / 55) (by norm_num) (by norm_num : ((94 : ℝ) / 55) ≤ ((3419 : ℝ) / 2000))
  exact hmono.trans cosh_b17095_ub

private lemma cosh5_v_187_le : cosh (94 : ℝ) / 275 ≤ (105905426 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((94 : ℝ) / 275) (by norm_num) (by norm_num : ((94 : ℝ) / 275) ≤ ((171 : ℝ) / 500))
  exact hmono.trans cosh_b3420_ub

private lemma sech5_pt_187_ge : (3008 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (94 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_187_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_187_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_188_le : cosh (189 : ℝ) / 110 ≤ (287774645 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((189 : ℝ) / 110) (by norm_num) (by norm_num : ((189 : ℝ) / 110) ≤ ((3437 : ℝ) / 2000))
  exact hmono.trans cosh_b17185_ub

private lemma cosh5_v_188_le : cosh (189 : ℝ) / 550 ≤ (105975379 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((189 : ℝ) / 550) (by norm_num) (by norm_num : ((189 : ℝ) / 550) ≤ ((43 : ℝ) / 125))
  exact hmono.trans cosh_b3440_ub

private lemma sech5_pt_188_ge : (2980 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (189 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_188_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_188_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_189_le : cosh (19 : ℝ) / 11 ≤ (290214904 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((19 : ℝ) / 11) (by norm_num) (by norm_num : ((19 : ℝ) / 11) ≤ ((691 : ℝ) / 400))
  exact hmono.trans cosh_b17275_ub

private lemma cosh5_v_189_le : cosh (19 : ℝ) / 55 ≤ (106028122 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((19 : ℝ) / 55) (by norm_num) (by norm_num : ((19 : ℝ) / 55) ≤ ((691 : ℝ) / 2000))
  exact hmono.trans cosh_b3455_ub

private lemma sech5_pt_189_ge : (2954 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_189_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_189_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_190_le : cosh (191 : ℝ) / 110 ≤ (292678669 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((191 : ℝ) / 110) (by norm_num) (by norm_num : ((191 : ℝ) / 110) ≤ ((3473 : ℝ) / 2000))
  exact hmono.trans cosh_b17365_ub

private lemma cosh5_v_190_le : cosh (191 : ℝ) / 550 ≤ (106098817 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((191 : ℝ) / 550) (by norm_num) (by norm_num : ((191 : ℝ) / 550) ≤ ((139 : ℝ) / 400))
  exact hmono.trans cosh_b3475_ub

private lemma sech5_pt_190_ge : (2927 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (191 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_190_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_190_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_191_le : cosh (96 : ℝ) / 55 ≤ (295166142 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((96 : ℝ) / 55) (by norm_num) (by norm_num : ((96 : ℝ) / 55) ≤ ((3491 : ℝ) / 2000))
  exact hmono.trans cosh_b17455_ub

private lemma cosh5_v_191_le : cosh (96 : ℝ) / 275 ≤ (106169936 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((96 : ℝ) / 275) (by norm_num) (by norm_num : ((96 : ℝ) / 275) ≤ ((699 : ℝ) / 2000))
  exact hmono.trans cosh_b3495_ub

private lemma sech5_pt_191_ge : (2900 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (96 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_191_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_191_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_192_le : cosh (193 : ℝ) / 110 ≤ (297817750 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((193 : ℝ) / 110) (by norm_num) (by norm_num : ((193 : ℝ) / 110) ≤ ((351 : ℝ) / 200))
  exact hmono.trans cosh_b17550_ub

private lemma cosh5_v_192_le : cosh (193 : ℝ) / 550 ≤ (106223554 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((193 : ℝ) / 550) (by norm_num) (by norm_num : ((193 : ℝ) / 550) ≤ ((351 : ℝ) / 1000))
  exact hmono.trans cosh_b3510_ub

private lemma sech5_pt_192_ge : (2873 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (193 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_192_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_192_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_193_le : cosh (97 : ℝ) / 55 ≤ (300354589 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((97 : ℝ) / 55) (by norm_num) (by norm_num : ((97 : ℝ) / 55) ≤ ((441 : ℝ) / 250))
  exact hmono.trans cosh_b17640_ub

private lemma cosh5_v_193_le : cosh (97 : ℝ) / 275 ≤ (106295417 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((97 : ℝ) / 275) (by norm_num) (by norm_num : ((97 : ℝ) / 275) ≤ ((353 : ℝ) / 1000))
  exact hmono.trans cosh_b3530_ub

private lemma sech5_pt_193_ge : (2847 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (97 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_193_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_193_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_194_le : cosh (39 : ℝ) / 22 ≤ (302915757 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((39 : ℝ) / 22) (by norm_num) (by norm_num : ((39 : ℝ) / 22) ≤ ((1773 : ℝ) / 1000))
  exact hmono.trans cosh_b17730_ub

private lemma cosh5_v_194_le : cosh (39 : ℝ) / 110 ≤ (106367705 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((39 : ℝ) / 110) (by norm_num) (by norm_num : ((39 : ℝ) / 110) ≤ ((71 : ℝ) / 200))
  exact hmono.trans cosh_b3550_ub

private lemma sech5_pt_194_ge : (2821 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_194_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_194_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_195_le : cosh (98 : ℝ) / 55 ≤ (305501461 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((98 : ℝ) / 55) (by norm_num) (by norm_num : ((98 : ℝ) / 55) ≤ ((891 : ℝ) / 500))
  exact hmono.trans cosh_b17820_ub

private lemma cosh5_v_195_le : cosh (98 : ℝ) / 275 ≤ (106422201 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((98 : ℝ) / 275) (by norm_num) (by norm_num : ((98 : ℝ) / 275) ≤ ((713 : ℝ) / 2000))
  exact hmono.trans cosh_b3565_ub

private lemma sech5_pt_195_ge : (2796 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (98 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_195_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_195_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_196_le : cosh (197 : ℝ) / 110 ≤ (308111911 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((197 : ℝ) / 110) (by norm_num) (by norm_num : ((197 : ℝ) / 110) ≤ ((1791 : ℝ) / 1000))
  exact hmono.trans cosh_b17910_ub

private lemma cosh5_v_196_le : cosh (197 : ℝ) / 550 ≤ (106495233 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((197 : ℝ) / 550) (by norm_num) (by norm_num : ((197 : ℝ) / 550) ≤ ((717 : ℝ) / 2000))
  exact hmono.trans cosh_b3585_ub

private lemma sech5_pt_196_ge : (2770 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (197 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_196_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_196_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_197_le : cosh (9 : ℝ) / 5 ≤ (310747318 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 5) (by norm_num) (by norm_num : ((9 : ℝ) / 5) ≤ ((9 : ℝ) / 5))
  exact hmono.trans cosh_b18000_ub

private lemma cosh5_v_197_le : cosh (9 : ℝ) / 25 ≤ (106550288 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 25) (by norm_num) (by norm_num : ((9 : ℝ) / 25) ≤ ((9 : ℝ) / 25))
  exact hmono.trans cosh_b3600_ub

private lemma sech5_pt_197_ge : (2745 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_197_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_197_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_198_le : cosh (199 : ℝ) / 110 ≤ (313556448 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((199 : ℝ) / 110) (by norm_num) (by norm_num : ((199 : ℝ) / 110) ≤ ((3619 : ℝ) / 2000))
  exact hmono.trans cosh_b18095_ub

private lemma cosh5_v_198_le : cosh (199 : ℝ) / 550 ≤ (106624066 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((199 : ℝ) / 550) (by norm_num) (by norm_num : ((199 : ℝ) / 550) ≤ ((181 : ℝ) / 500))
  exact hmono.trans cosh_b3620_ub

private lemma sech5_pt_198_ge : (2719 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (199 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_198_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_198_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_199_le : cosh (20 : ℝ) / 11 ≤ (316243829 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((20 : ℝ) / 11) (by norm_num) (by norm_num : ((20 : ℝ) / 11) ≤ ((3637 : ℝ) / 2000))
  exact hmono.trans cosh_b18185_ub

private lemma cosh5_v_199_le : cosh (4 : ℝ) / 11 ≤ (106698271 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((4 : ℝ) / 11) (by norm_num) (by norm_num : ((4 : ℝ) / 11) ≤ ((91 : ℝ) / 250))
  exact hmono.trans cosh_b3640_ub

private lemma sech5_pt_199_ge : (2694 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (20 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_199_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_199_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma sech5_batch_3_ge : (169519 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (151 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (76 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (153 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (78 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (157 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (79 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (159 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (16 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (161 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (81 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (163 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (82 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 2 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (83 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (167 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (84 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (169 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (171 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (86 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (173 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (87 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (35 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (8 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (177 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (89 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (179 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (18 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (181 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (91 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (183 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (92 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (93 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (94 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (189 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (191 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (96 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (193 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (97 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (98 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (197 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (199 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (20 : ℝ) / 11 := by
  linarith [sech5_pt_150_ge, sech5_pt_151_ge, sech5_pt_152_ge, sech5_pt_153_ge, sech5_pt_154_ge, sech5_pt_155_ge, sech5_pt_156_ge, sech5_pt_157_ge, sech5_pt_158_ge, sech5_pt_159_ge, sech5_pt_160_ge, sech5_pt_161_ge, sech5_pt_162_ge, sech5_pt_163_ge, sech5_pt_164_ge, sech5_pt_165_ge, sech5_pt_166_ge, sech5_pt_167_ge, sech5_pt_168_ge, sech5_pt_169_ge, sech5_pt_170_ge, sech5_pt_171_ge, sech5_pt_172_ge, sech5_pt_173_ge, sech5_pt_174_ge, sech5_pt_175_ge, sech5_pt_176_ge, sech5_pt_177_ge, sech5_pt_178_ge, sech5_pt_179_ge, sech5_pt_180_ge, sech5_pt_181_ge, sech5_pt_182_ge, sech5_pt_183_ge, sech5_pt_184_ge, sech5_pt_185_ge, sech5_pt_186_ge, sech5_pt_187_ge, sech5_pt_188_ge, sech5_pt_189_ge, sech5_pt_190_ge, sech5_pt_191_ge, sech5_pt_192_ge, sech5_pt_193_ge, sech5_pt_194_ge, sech5_pt_195_ge, sech5_pt_196_ge, sech5_pt_197_ge, sech5_pt_198_ge, sech5_pt_199_ge]

private lemma cosh5_u_200_le : cosh (201 : ℝ) / 110 ≤ (318956826 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((201 : ℝ) / 110) (by norm_num) (by norm_num : ((201 : ℝ) / 110) ≤ ((731 : ℝ) / 400))
  exact hmono.trans cosh_b18275_ub

private lemma cosh5_v_200_le : cosh (201 : ℝ) / 550 ≤ (106754205 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((201 : ℝ) / 550) (by norm_num) (by norm_num : ((201 : ℝ) / 550) ≤ ((731 : ℝ) / 2000))
  exact hmono.trans cosh_b3655_ub

private lemma sech5_pt_200_ge : (2669 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (201 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_200_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_200_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_201_le : cosh (101 : ℝ) / 55 ≤ (321695658 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((101 : ℝ) / 55) (by norm_num) (by norm_num : ((101 : ℝ) / 55) ≤ ((3673 : ℝ) / 2000))
  exact hmono.trans cosh_b18365_ub

private lemma cosh5_v_201_le : cosh (101 : ℝ) / 275 ≤ (106829157 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((101 : ℝ) / 275) (by norm_num) (by norm_num : ((101 : ℝ) / 275) ≤ ((147 : ℝ) / 400))
  exact hmono.trans cosh_b3675_ub

private lemma sech5_pt_201_ge : (2645 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (101 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_201_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_201_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_202_le : cosh (203 : ℝ) / 110 ≤ (324460548 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((203 : ℝ) / 110) (by norm_num) (by norm_num : ((203 : ℝ) / 110) ≤ ((3691 : ℝ) / 2000))
  exact hmono.trans cosh_b18455_ub

private lemma cosh5_v_202_le : cosh (203 : ℝ) / 550 ≤ (106904536 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((203 : ℝ) / 550) (by norm_num) (by norm_num : ((203 : ℝ) / 550) ≤ ((739 : ℝ) / 2000))
  exact hmono.trans cosh_b3695_ub

private lemma sech5_pt_202_ge : (2620 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (203 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_202_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_202_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_203_le : cosh (102 : ℝ) / 55 ≤ (327407560 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((102 : ℝ) / 55) (by norm_num) (by norm_num : ((102 : ℝ) / 55) ≤ ((371 : ℝ) / 200))
  exact hmono.trans cosh_b18550_ub

private lemma cosh5_v_203_le : cosh (102 : ℝ) / 275 ≤ (106961351 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((102 : ℝ) / 275) (by norm_num) (by norm_num : ((102 : ℝ) / 275) ≤ ((371 : ℝ) / 1000))
  exact hmono.trans cosh_b3710_ub

private lemma sech5_pt_203_ge : (2595 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (102 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_203_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_203_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_204_le : cosh (41 : ℝ) / 22 ≤ (330226719 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((41 : ℝ) / 22) (by norm_num) (by norm_num : ((41 : ℝ) / 22) ≤ ((233 : ℝ) / 125))
  exact hmono.trans cosh_b18640_ub

private lemma cosh5_v_204_le : cosh (41 : ℝ) / 110 ≤ (107037479 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((41 : ℝ) / 110) (by norm_num) (by norm_num : ((41 : ℝ) / 110) ≤ ((373 : ℝ) / 1000))
  exact hmono.trans cosh_b3730_ub

private lemma sech5_pt_204_ge : (2571 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_204_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_204_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_205_le : cosh (103 : ℝ) / 55 ≤ (333072625 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((103 : ℝ) / 55) (by norm_num) (by norm_num : ((103 : ℝ) / 55) ≤ ((1873 : ℝ) / 1000))
  exact hmono.trans cosh_b18730_ub

private lemma cosh5_v_205_le : cosh (103 : ℝ) / 275 ≤ (107114035 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((103 : ℝ) / 275) (by norm_num) (by norm_num : ((103 : ℝ) / 275) ≤ ((3 : ℝ) / 8))
  exact hmono.trans cosh_b3750_ub

private lemma sech5_pt_205_ge : (2548 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (103 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_205_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_205_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_206_le : cosh (207 : ℝ) / 110 ≤ (335945511 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((207 : ℝ) / 110) (by norm_num) (by norm_num : ((207 : ℝ) / 110) ≤ ((941 : ℝ) / 500))
  exact hmono.trans cosh_b18820_ub

private lemma cosh5_v_206_le : cosh (207 : ℝ) / 550 ≤ (107171733 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((207 : ℝ) / 550) (by norm_num) (by norm_num : ((207 : ℝ) / 550) ≤ ((753 : ℝ) / 2000))
  exact hmono.trans cosh_b3765_ub

private lemma sech5_pt_206_ge : (2524 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (207 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_206_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_206_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_207_le : cosh (104 : ℝ) / 55 ≤ (338845609 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((104 : ℝ) / 55) (by norm_num) (by norm_num : ((104 : ℝ) / 55) ≤ ((1891 : ℝ) / 1000))
  exact hmono.trans cosh_b18910_ub

private lemma cosh5_v_207_le : cosh (104 : ℝ) / 275 ≤ (107249039 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((104 : ℝ) / 275) (by norm_num) (by norm_num : ((104 : ℝ) / 275) ≤ ((757 : ℝ) / 2000))
  exact hmono.trans cosh_b3785_ub

private lemma sech5_pt_207_ge : (2501 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (104 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_207_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_207_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_208_le : cosh (19 : ℝ) / 10 ≤ (341773154 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((19 : ℝ) / 10) (by norm_num) (by norm_num : ((19 : ℝ) / 10) ≤ ((19 : ℝ) / 10))
  exact hmono.trans cosh_b19000_ub

private lemma cosh5_v_208_le : cosh (19 : ℝ) / 50 ≤ (107307300 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((19 : ℝ) / 50) (by norm_num) (by norm_num : ((19 : ℝ) / 50) ≤ ((19 : ℝ) / 50))
  exact hmono.trans cosh_b3800_ub

private lemma sech5_pt_208_ge : (2478 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_208_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_208_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_209_le : cosh (21 : ℝ) / 11 ≤ (344893378 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((21 : ℝ) / 11) (by norm_num) (by norm_num : ((21 : ℝ) / 11) ≤ ((3819 : ℝ) / 2000))
  exact hmono.trans cosh_b19095_ub

private lemma cosh5_v_209_le : cosh (21 : ℝ) / 55 ≤ (107385357 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((21 : ℝ) / 55) (by norm_num) (by norm_num : ((21 : ℝ) / 55) ≤ ((191 : ℝ) / 500))
  exact hmono.trans cosh_b3820_ub

private lemma sech5_pt_209_ge : (2454 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_209_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_209_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_210_le : cosh (211 : ℝ) / 110 ≤ (347878087 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((211 : ℝ) / 110) (by norm_num) (by norm_num : ((211 : ℝ) / 110) ≤ ((3837 : ℝ) / 2000))
  exact hmono.trans cosh_b19185_ub

private lemma cosh5_v_210_le : cosh (211 : ℝ) / 550 ≤ (107463844 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((211 : ℝ) / 550) (by norm_num) (by norm_num : ((211 : ℝ) / 550) ≤ ((48 : ℝ) / 125))
  exact hmono.trans cosh_b3840_ub

private lemma sech5_pt_210_ge : (2431 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (211 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_210_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_210_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_211_le : cosh (106 : ℝ) / 55 ≤ (350890976 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((106 : ℝ) / 55) (by norm_num) (by norm_num : ((106 : ℝ) / 55) ≤ ((771 : ℝ) / 400))
  exact hmono.trans cosh_b19275_ub

private lemma cosh5_v_211_le : cosh (106 : ℝ) / 275 ≤ (107522991 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((106 : ℝ) / 275) (by norm_num) (by norm_num : ((106 : ℝ) / 275) ≤ ((771 : ℝ) / 2000))
  exact hmono.trans cosh_b3855_ub

private lemma sech5_pt_211_ge : (2409 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (106 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_211_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_211_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_212_le : cosh (213 : ℝ) / 110 ≤ (353932286 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((213 : ℝ) / 110) (by norm_num) (by norm_num : ((213 : ℝ) / 110) ≤ ((3873 : ℝ) / 2000))
  exact hmono.trans cosh_b19365_ub

private lemma cosh5_v_212_le : cosh (213 : ℝ) / 550 ≤ (107602230 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((213 : ℝ) / 550) (by norm_num) (by norm_num : ((213 : ℝ) / 550) ≤ ((31 : ℝ) / 80))
  exact hmono.trans cosh_b3875_ub

private lemma sech5_pt_212_ge : (2387 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (213 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_212_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_212_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_213_le : cosh (107 : ℝ) / 55 ≤ (357002265 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((107 : ℝ) / 55) (by norm_num) (by norm_num : ((107 : ℝ) / 55) ≤ ((3891 : ℝ) / 2000))
  exact hmono.trans cosh_b19455_ub

private lemma cosh5_v_213_le : cosh (107 : ℝ) / 275 ≤ (107681899 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((107 : ℝ) / 275) (by norm_num) (by norm_num : ((107 : ℝ) / 275) ≤ ((779 : ℝ) / 2000))
  exact hmono.trans cosh_b3895_ub

private lemma sech5_pt_213_ge : (2364 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (107 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_213_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_213_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_214_le : cosh (43 : ℝ) / 22 ≤ (360274176 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((43 : ℝ) / 22) (by norm_num) (by norm_num : ((43 : ℝ) / 22) ≤ ((391 : ℝ) / 200))
  exact hmono.trans cosh_b19550_ub

private lemma cosh5_v_214_le : cosh (43 : ℝ) / 110 ≤ (107741934 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((43 : ℝ) / 110) (by norm_num) (by norm_num : ((43 : ℝ) / 110) ≤ ((391 : ℝ) / 1000))
  exact hmono.trans cosh_b3910_ub

private lemma sech5_pt_214_ge : (2342 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_214_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_214_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_215_le : cosh (108 : ℝ) / 55 ≤ (363403868 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((108 : ℝ) / 55) (by norm_num) (by norm_num : ((108 : ℝ) / 55) ≤ ((491 : ℝ) / 250))
  exact hmono.trans cosh_b19640_ub

private lemma cosh5_v_215_le : cosh (108 : ℝ) / 275 ≤ (107822357 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((108 : ℝ) / 275) (by norm_num) (by norm_num : ((108 : ℝ) / 275) ≤ ((393 : ℝ) / 1000))
  exact hmono.trans cosh_b3930_ub

private lemma sech5_pt_215_ge : (2320 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (108 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_215_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_215_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_216_le : cosh (217 : ℝ) / 110 ≤ (366562997 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((217 : ℝ) / 110) (by norm_num) (by norm_num : ((217 : ℝ) / 110) ≤ ((1973 : ℝ) / 1000))
  exact hmono.trans cosh_b19730_ub

private lemma cosh5_v_216_le : cosh (217 : ℝ) / 550 ≤ (107903212 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((217 : ℝ) / 550) (by norm_num) (by norm_num : ((217 : ℝ) / 550) ≤ ((79 : ℝ) / 200))
  exact hmono.trans cosh_b3950_ub

private lemma sech5_pt_216_ge : (2298 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (217 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_216_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_216_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_217_le : cosh (109 : ℝ) / 55 ≤ (369751818 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((109 : ℝ) / 55) (by norm_num) (by norm_num : ((109 : ℝ) / 55) ≤ ((991 : ℝ) / 500))
  exact hmono.trans cosh_b19820_ub

private lemma cosh5_v_217_le : cosh (109 : ℝ) / 275 ≤ (107964136 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((109 : ℝ) / 275) (by norm_num) (by norm_num : ((109 : ℝ) / 275) ≤ ((793 : ℝ) / 2000))
  exact hmono.trans cosh_b3965_ub

private lemma sech5_pt_217_ge : (2277 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (109 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_217_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_217_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_218_le : cosh (219 : ℝ) / 110 ≤ (372970588 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((219 : ℝ) / 110) (by norm_num) (by norm_num : ((219 : ℝ) / 110) ≤ ((1991 : ℝ) / 1000))
  exact hmono.trans cosh_b19910_ub

private lemma cosh5_v_218_le : cosh (219 : ℝ) / 550 ≤ (108045746 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((219 : ℝ) / 550) (by norm_num) (by norm_num : ((219 : ℝ) / 550) ≤ ((797 : ℝ) / 2000))
  exact hmono.trans cosh_b3985_ub

private lemma sech5_pt_218_ge : (2255 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (219 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_218_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_218_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_219_le : cosh (2 : ℝ) / 1 ≤ (376219570 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((2 : ℝ) / 1) (by norm_num) (by norm_num : ((2 : ℝ) / 1) ≤ ((2 : ℝ) / 1))
  exact hmono.trans cosh_b20000_ub

private lemma cosh5_v_219_le : cosh (2 : ℝ) / 5 ≤ (108107238 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((2 : ℝ) / 5) (by norm_num) (by norm_num : ((2 : ℝ) / 5) ≤ ((2 : ℝ) / 5))
  exact hmono.trans cosh_b4000_ub

private lemma sech5_pt_219_ge : (2235 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (2 : ℝ) / 1 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_219_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_219_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_220_le : cosh (221 : ℝ) / 110 ≤ (379682116 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((221 : ℝ) / 110) (by norm_num) (by norm_num : ((221 : ℝ) / 110) ≤ ((4019 : ℝ) / 2000))
  exact hmono.trans cosh_b20095_ub

private lemma cosh5_v_220_le : cosh (221 : ℝ) / 550 ≤ (108189604 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((221 : ℝ) / 550) (by norm_num) (by norm_num : ((221 : ℝ) / 550) ≤ ((201 : ℝ) / 500))
  exact hmono.trans cosh_b4020_ub

private lemma sech5_pt_220_ge : (2213 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (221 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_220_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_220_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_221_le : cosh (111 : ℝ) / 55 ≤ (382994027 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((111 : ℝ) / 55) (by norm_num) (by norm_num : ((111 : ℝ) / 55) ≤ ((4037 : ℝ) / 2000))
  exact hmono.trans cosh_b20185_ub

private lemma cosh5_v_221_le : cosh (111 : ℝ) / 275 ≤ (108272404 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((111 : ℝ) / 275) (by norm_num) (by norm_num : ((111 : ℝ) / 275) ≤ ((101 : ℝ) / 250))
  exact hmono.trans cosh_b4040_ub

private lemma sech5_pt_221_ge : (2192 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (111 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_221_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_221_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_222_le : cosh (223 : ℝ) / 110 ≤ (386336960 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((223 : ℝ) / 110) (by norm_num) (by norm_num : ((223 : ℝ) / 110) ≤ ((811 : ℝ) / 400))
  exact hmono.trans cosh_b20275_ub

private lemma cosh5_v_222_le : cosh (223 : ℝ) / 550 ≤ (108334788 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((223 : ℝ) / 550) (by norm_num) (by norm_num : ((223 : ℝ) / 550) ≤ ((811 : ℝ) / 2000))
  exact hmono.trans cosh_b4055_ub

private lemma sech5_pt_222_ge : (2172 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (223 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_222_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_222_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_223_le : cosh (112 : ℝ) / 55 ≤ (389711187 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((112 : ℝ) / 55) (by norm_num) (by norm_num : ((112 : ℝ) / 55) ≤ ((4073 : ℝ) / 2000))
  exact hmono.trans cosh_b20365_ub

private lemma cosh5_v_223_le : cosh (112 : ℝ) / 275 ≤ (108418345 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((112 : ℝ) / 275) (by norm_num) (by norm_num : ((112 : ℝ) / 275) ≤ ((163 : ℝ) / 400))
  exact hmono.trans cosh_b4075_ub

private lemma sech5_pt_223_ge : (2151 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (112 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_223_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_223_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_224_le : cosh (45 : ℝ) / 22 ≤ (393116980 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((45 : ℝ) / 22) (by norm_num) (by norm_num : ((45 : ℝ) / 22) ≤ ((4091 : ℝ) / 2000))
  exact hmono.trans cosh_b20455_ub

private lemma cosh5_v_224_le : cosh (9 : ℝ) / 22 ≤ (108502337 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 22) (by norm_num) (by norm_num : ((9 : ℝ) / 22) ≤ ((819 : ℝ) / 2000))
  exact hmono.trans cosh_b4095_ub

private lemma sech5_pt_224_ge : (2131 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (45 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_224_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_224_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_225_le : cosh (113 : ℝ) / 55 ≤ (396746536 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((113 : ℝ) / 55) (by norm_num) (by norm_num : ((113 : ℝ) / 55) ≤ ((411 : ℝ) / 200))
  exact hmono.trans cosh_b20550_ub

private lemma cosh5_v_225_le : cosh (113 : ℝ) / 275 ≤ (108565615 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((113 : ℝ) / 275) (by norm_num) (by norm_num : ((113 : ℝ) / 275) ≤ ((411 : ℝ) / 1000))
  exact hmono.trans cosh_b4110_ub

private lemma sech5_pt_225_ge : (2110 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (113 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_225_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_225_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_226_le : cosh (227 : ℝ) / 110 ≤ (400218086 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((227 : ℝ) / 110) (by norm_num) (by norm_num : ((227 : ℝ) / 110) ≤ ((258 : ℝ) / 125))
  exact hmono.trans cosh_b20640_ub

private lemma cosh5_v_226_le : cosh (227 : ℝ) / 550 ≤ (108650366 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((227 : ℝ) / 550) (by norm_num) (by norm_num : ((227 : ℝ) / 550) ≤ ((413 : ℝ) / 1000))
  exact hmono.trans cosh_b4130_ub

private lemma sech5_pt_226_ge : (2090 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (227 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_226_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_226_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_227_le : cosh (114 : ℝ) / 55 ≤ (403722054 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((114 : ℝ) / 55) (by norm_num) (by norm_num : ((114 : ℝ) / 55) ≤ ((2073 : ℝ) / 1000))
  exact hmono.trans cosh_b20730_ub

private lemma cosh5_v_227_le : cosh (114 : ℝ) / 275 ≤ (108735552 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((114 : ℝ) / 275) (by norm_num) (by norm_num : ((114 : ℝ) / 275) ≤ ((83 : ℝ) / 200))
  exact hmono.trans cosh_b4150_ub

private lemma sech5_pt_227_ge : (2070 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (114 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_227_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_227_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_228_le : cosh (229 : ℝ) / 110 ≤ (407258724 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((229 : ℝ) / 110) (by norm_num) (by norm_num : ((229 : ℝ) / 110) ≤ ((1041 : ℝ) / 500))
  exact hmono.trans cosh_b20820_ub

private lemma cosh5_v_228_le : cosh (229 : ℝ) / 550 ≤ (108799726 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((229 : ℝ) / 550) (by norm_num) (by norm_num : ((229 : ℝ) / 550) ≤ ((833 : ℝ) / 2000))
  exact hmono.trans cosh_b4165_ub

private lemma sech5_pt_228_ge : (2051 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (229 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_228_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_228_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_229_le : cosh (23 : ℝ) / 11 ≤ (410828382 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((23 : ℝ) / 11) (by norm_num) (by norm_num : ((23 : ℝ) / 11) ≤ ((2091 : ℝ) / 1000))
  exact hmono.trans cosh_b20910_ub

private lemma cosh5_v_229_le : cosh (23 : ℝ) / 55 ≤ (108885673 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((23 : ℝ) / 55) (by norm_num) (by norm_num : ((23 : ℝ) / 55) ≤ ((837 : ℝ) / 2000))
  exact hmono.trans cosh_b4185_ub

private lemma sech5_pt_229_ge : (2032 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_229_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_229_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_230_le : cosh (21 : ℝ) / 10 ≤ (414431318 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((21 : ℝ) / 10) (by norm_num) (by norm_num : ((21 : ℝ) / 10) ≤ ((21 : ℝ) / 10))
  exact hmono.trans cosh_b21000_ub

private lemma cosh5_v_230_le : cosh (21 : ℝ) / 50 ≤ (108950419 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((21 : ℝ) / 50) (by norm_num) (by norm_num : ((21 : ℝ) / 50) ≤ ((21 : ℝ) / 50))
  exact hmono.trans cosh_b4200_ub

private lemma sech5_pt_230_ge : (2013 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_230_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_230_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_231_le : cosh (116 : ℝ) / 55 ≤ (418270840 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((116 : ℝ) / 55) (by norm_num) (by norm_num : ((116 : ℝ) / 55) ≤ ((4219 : ℝ) / 2000))
  exact hmono.trans cosh_b21095_ub

private lemma cosh5_v_231_le : cosh (116 : ℝ) / 275 ≤ (109037129 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((116 : ℝ) / 275) (by norm_num) (by norm_num : ((116 : ℝ) / 275) ≤ ((211 : ℝ) / 500))
  exact hmono.trans cosh_b4220_ub

private lemma sech5_pt_231_ge : (1993 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (116 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_231_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_231_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_232_le : cosh (233 : ℝ) / 110 ≤ (421943099 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((233 : ℝ) / 110) (by norm_num) (by norm_num : ((233 : ℝ) / 110) ≤ ((4237 : ℝ) / 2000))
  exact hmono.trans cosh_b21185_ub

private lemma cosh5_v_232_le : cosh (233 : ℝ) / 550 ≤ (109124274 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((233 : ℝ) / 550) (by norm_num) (by norm_num : ((233 : ℝ) / 550) ≤ ((53 : ℝ) / 125))
  exact hmono.trans cosh_b4240_ub

private lemma sech5_pt_232_ge : (1974 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (233 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_232_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_232_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_233_le : cosh (117 : ℝ) / 55 ≤ (425649534 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((117 : ℝ) / 55) (by norm_num) (by norm_num : ((117 : ℝ) / 55) ≤ ((851 : ℝ) / 400))
  exact hmono.trans cosh_b21275_ub

private lemma cosh5_v_233_le : cosh (117 : ℝ) / 275 ≤ (109189920 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((117 : ℝ) / 275) (by norm_num) (by norm_num : ((117 : ℝ) / 275) ≤ ((851 : ℝ) / 2000))
  exact hmono.trans cosh_b4255_ub

private lemma sech5_pt_233_ge : (1956 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (117 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_233_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_233_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_234_le : cosh (47 : ℝ) / 22 ≤ (429390448 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((47 : ℝ) / 22) (by norm_num) (by norm_num : ((47 : ℝ) / 22) ≤ ((4273 : ℝ) / 2000))
  exact hmono.trans cosh_b21365_ub

private lemma cosh5_v_234_le : cosh (47 : ℝ) / 110 ≤ (109277830 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((47 : ℝ) / 110) (by norm_num) (by norm_num : ((47 : ℝ) / 110) ≤ ((171 : ℝ) / 400))
  exact hmono.trans cosh_b4275_ub

private lemma sech5_pt_234_ge : (1937 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_234_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_234_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_235_le : cosh (118 : ℝ) / 55 ≤ (433166143 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((118 : ℝ) / 55) (by norm_num) (by norm_num : ((118 : ℝ) / 55) ≤ ((4291 : ℝ) / 2000))
  exact hmono.trans cosh_b21455_ub

private lemma cosh5_v_235_le : cosh (118 : ℝ) / 275 ≤ (109366176 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((118 : ℝ) / 275) (by norm_num) (by norm_num : ((118 : ℝ) / 275) ≤ ((859 : ℝ) / 2000))
  exact hmono.trans cosh_b4295_ub

private lemma sech5_pt_235_ge : (1918 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (118 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_235_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_235_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_236_le : cosh (237 : ℝ) / 110 ≤ (437189669 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((237 : ℝ) / 110) (by norm_num) (by norm_num : ((237 : ℝ) / 110) ≤ ((431 : ℝ) / 200))
  exact hmono.trans cosh_b21550_ub

private lemma cosh5_v_236_le : cosh (237 : ℝ) / 550 ≤ (109432724 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((237 : ℝ) / 550) (by norm_num) (by norm_num : ((237 : ℝ) / 550) ≤ ((431 : ℝ) / 1000))
  exact hmono.trans cosh_b4310_ub

private lemma sech5_pt_236_ge : (1900 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (237 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_236_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_236_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_237_le : cosh (119 : ℝ) / 55 ≤ (441037821 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((119 : ℝ) / 55) (by norm_num) (by norm_num : ((119 : ℝ) / 55) ≤ ((541 : ℝ) / 250))
  exact hmono.trans cosh_b21640_ub

private lemma cosh5_v_237_le : cosh (119 : ℝ) / 275 ≤ (109521836 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((119 : ℝ) / 275) (by norm_num) (by norm_num : ((119 : ℝ) / 275) ≤ ((433 : ℝ) / 1000))
  exact hmono.trans cosh_b4330_ub

private lemma sech5_pt_237_ge : (1882 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (119 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_237_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_237_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_238_le : cosh (239 : ℝ) / 110 ≤ (444921698 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((239 : ℝ) / 110) (by norm_num) (by norm_num : ((239 : ℝ) / 110) ≤ ((2173 : ℝ) / 1000))
  exact hmono.trans cosh_b21730_ub

private lemma cosh5_v_238_le : cosh (239 : ℝ) / 550 ≤ (109611387 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((239 : ℝ) / 550) (by norm_num) (by norm_num : ((239 : ℝ) / 550) ≤ ((87 : ℝ) / 200))
  exact hmono.trans cosh_b4350_ub

private lemma sech5_pt_238_ge : (1864 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (239 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_238_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_238_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_239_le : cosh (24 : ℝ) / 11 ≤ (448841613 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((24 : ℝ) / 11) (by norm_num) (by norm_num : ((24 : ℝ) / 11) ≤ ((1091 : ℝ) / 500))
  exact hmono.trans cosh_b21820_ub

private lemma cosh5_v_239_le : cosh (24 : ℝ) / 55 ≤ (109678838 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((24 : ℝ) / 55) (by norm_num) (by norm_num : ((24 : ℝ) / 55) ≤ ((873 : ℝ) / 2000))
  exact hmono.trans cosh_b4365_ub

private lemma sech5_pt_239_ge : (1846 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (24 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_239_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_239_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_240_le : cosh (241 : ℝ) / 110 ≤ (452797885 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((241 : ℝ) / 110) (by norm_num) (by norm_num : ((241 : ℝ) / 110) ≤ ((2191 : ℝ) / 1000))
  exact hmono.trans cosh_b21910_ub

private lemma cosh5_v_240_le : cosh (241 : ℝ) / 550 ≤ (109769156 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((241 : ℝ) / 550) (by norm_num) (by norm_num : ((241 : ℝ) / 550) ≤ ((877 : ℝ) / 2000))
  exact hmono.trans cosh_b4385_ub

private lemma sech5_pt_240_ge : (1829 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (241 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_240_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_240_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_241_le : cosh (11 : ℝ) / 5 ≤ (456790833 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((11 : ℝ) / 5) (by norm_num) (by norm_num : ((11 : ℝ) / 5) ≤ ((11 : ℝ) / 5))
  exact hmono.trans cosh_b22000_ub

private lemma cosh5_v_241_le : cosh (11 : ℝ) / 25 ≤ (109837182 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((11 : ℝ) / 25) (by norm_num) (by norm_num : ((11 : ℝ) / 25) ≤ ((11 : ℝ) / 25))
  exact hmono.trans cosh_b4400_ub

private lemma sech5_pt_241_ge : (1811 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (11 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_241_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_241_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_242_le : cosh (243 : ℝ) / 110 ≤ (461045760 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((243 : ℝ) / 110) (by norm_num) (by norm_num : ((243 : ℝ) / 110) ≤ ((4419 : ℝ) / 2000))
  exact hmono.trans cosh_b22095_ub

private lemma cosh5_v_242_le : cosh (243 : ℝ) / 550 ≤ (109928269 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((243 : ℝ) / 550) (by norm_num) (by norm_num : ((243 : ℝ) / 550) ≤ ((221 : ℝ) / 500))
  exact hmono.trans cosh_b4420_ub

private lemma sech5_pt_242_ge : (1793 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (243 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_242_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_242_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_243_le : cosh (122 : ℝ) / 55 ≤ (465115119 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((122 : ℝ) / 55) (by norm_num) (by norm_num : ((122 : ℝ) / 55) ≤ ((4437 : ℝ) / 2000))
  exact hmono.trans cosh_b22185_ub

private lemma cosh5_v_243_le : cosh (122 : ℝ) / 275 ≤ (110019796 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((122 : ℝ) / 275) (by norm_num) (by norm_num : ((122 : ℝ) / 275) ≤ ((111 : ℝ) / 250))
  exact hmono.trans cosh_b4440_ub

private lemma sech5_pt_243_ge : (1776 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (122 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_243_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_243_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_244_le : cosh (49 : ℝ) / 22 ≤ (469222152 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((49 : ℝ) / 22) (by norm_num) (by norm_num : ((49 : ℝ) / 22) ≤ ((891 : ℝ) / 400))
  exact hmono.trans cosh_b22275_ub

private lemma cosh5_v_244_le : cosh (49 : ℝ) / 110 ≤ (110088730 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((49 : ℝ) / 110) (by norm_num) (by norm_num : ((49 : ℝ) / 110) ≤ ((891 : ℝ) / 2000))
  exact hmono.trans cosh_b4455_ub

private lemma sech5_pt_244_ge : (1759 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_244_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_244_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_245_le : cosh (123 : ℝ) / 55 ≤ (473367193 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((123 : ℝ) / 55) (by norm_num) (by norm_num : ((123 : ℝ) / 55) ≤ ((4473 : ℝ) / 2000))
  exact hmono.trans cosh_b22365_ub

private lemma cosh5_v_245_le : cosh (123 : ℝ) / 275 ≤ (110181026 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((123 : ℝ) / 275) (by norm_num) (by norm_num : ((123 : ℝ) / 275) ≤ ((179 : ℝ) / 400))
  exact hmono.trans cosh_b4475_ub

private lemma sech5_pt_245_ge : (1743 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (123 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_245_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_245_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_246_le : cosh (247 : ℝ) / 110 ≤ (477550577 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((247 : ℝ) / 110) (by norm_num) (by norm_num : ((247 : ℝ) / 110) ≤ ((4491 : ℝ) / 2000))
  exact hmono.trans cosh_b22455_ub

private lemma cosh5_v_246_le : cosh (247 : ℝ) / 550 ≤ (110273764 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((247 : ℝ) / 550) (by norm_num) (by norm_num : ((247 : ℝ) / 550) ≤ ((899 : ℝ) / 2000))
  exact hmono.trans cosh_b4495_ub

private lemma sech5_pt_246_ge : (1726 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (247 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_246_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_246_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_247_le : cosh (124 : ℝ) / 55 ≤ (482008343 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((124 : ℝ) / 55) (by norm_num) (by norm_num : ((124 : ℝ) / 55) ≤ ((451 : ℝ) / 200))
  exact hmono.trans cosh_b22550_ub

private lemma cosh5_v_247_le : cosh (124 : ℝ) / 275 ≤ (110343607 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((124 : ℝ) / 275) (by norm_num) (by norm_num : ((124 : ℝ) / 275) ≤ ((451 : ℝ) / 1000))
  exact hmono.trans cosh_b4510_ub

private lemma sech5_pt_247_ge : (1709 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (124 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_247_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_247_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_248_le : cosh (249 : ℝ) / 110 ≤ (486271611 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((249 : ℝ) / 110) (by norm_num) (by norm_num : ((249 : ℝ) / 110) ≤ ((283 : ℝ) / 125))
  exact hmono.trans cosh_b22640_ub

private lemma cosh5_v_248_le : cosh (249 : ℝ) / 550 ≤ (110437117 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((249 : ℝ) / 550) (by norm_num) (by norm_num : ((249 : ℝ) / 550) ≤ ((453 : ℝ) / 1000))
  exact hmono.trans cosh_b4530_ub

private lemma sech5_pt_248_ge : (1692 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (249 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_248_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_248_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_249_le : cosh (25 : ℝ) / 11 ≤ (490574267 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((25 : ℝ) / 11) (by norm_num) (by norm_num : ((25 : ℝ) / 11) ≤ ((2273 : ℝ) / 1000))
  exact hmono.trans cosh_b22730_ub

private lemma cosh5_v_249_le : cosh (5 : ℝ) / 11 ≤ (110531068 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((5 : ℝ) / 11) (by norm_num) (by norm_num : ((5 : ℝ) / 11) ≤ ((91 : ℝ) / 200))
  exact hmono.trans cosh_b4550_ub

private lemma sech5_pt_249_ge : (1676 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (25 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_249_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_249_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma sech5_batch_4_ge : (106955 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (201 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (101 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (203 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (102 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (103 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (207 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (104 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (211 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (106 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (213 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (107 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (108 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (217 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (109 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (219 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (2 : ℝ) / 1 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (221 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (111 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (223 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (112 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (45 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (113 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (227 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (114 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (229 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (116 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (233 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (117 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (118 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (237 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (119 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (239 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (24 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (241 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (11 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (243 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (122 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (123 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (247 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (124 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (249 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (25 : ℝ) / 11 := by
  linarith [sech5_pt_200_ge, sech5_pt_201_ge, sech5_pt_202_ge, sech5_pt_203_ge, sech5_pt_204_ge, sech5_pt_205_ge, sech5_pt_206_ge, sech5_pt_207_ge, sech5_pt_208_ge, sech5_pt_209_ge, sech5_pt_210_ge, sech5_pt_211_ge, sech5_pt_212_ge, sech5_pt_213_ge, sech5_pt_214_ge, sech5_pt_215_ge, sech5_pt_216_ge, sech5_pt_217_ge, sech5_pt_218_ge, sech5_pt_219_ge, sech5_pt_220_ge, sech5_pt_221_ge, sech5_pt_222_ge, sech5_pt_223_ge, sech5_pt_224_ge, sech5_pt_225_ge, sech5_pt_226_ge, sech5_pt_227_ge, sech5_pt_228_ge, sech5_pt_229_ge, sech5_pt_230_ge, sech5_pt_231_ge, sech5_pt_232_ge, sech5_pt_233_ge, sech5_pt_234_ge, sech5_pt_235_ge, sech5_pt_236_ge, sech5_pt_237_ge, sech5_pt_238_ge, sech5_pt_239_ge, sech5_pt_240_ge, sech5_pt_241_ge, sech5_pt_242_ge, sech5_pt_243_ge, sech5_pt_244_ge, sech5_pt_245_ge, sech5_pt_246_ge, sech5_pt_247_ge, sech5_pt_248_ge, sech5_pt_249_ge]

private lemma cosh5_u_250_le : cosh (251 : ℝ) / 110 ≤ (494916659 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((251 : ℝ) / 110) (by norm_num) (by norm_num : ((251 : ℝ) / 110) ≤ ((1141 : ℝ) / 500))
  exact hmono.trans cosh_b22820_ub

private lemma cosh5_v_250_le : cosh (251 : ℝ) / 550 ≤ (110601822 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((251 : ℝ) / 550) (by norm_num) (by norm_num : ((251 : ℝ) / 550) ≤ ((913 : ℝ) / 2000))
  exact hmono.trans cosh_b4565_ub

private lemma sech5_pt_250_ge : (1660 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (251 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_250_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_250_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_251_le : cosh (126 : ℝ) / 55 ≤ (499299141 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((126 : ℝ) / 55) (by norm_num) (by norm_num : ((126 : ℝ) / 55) ≤ ((2291 : ℝ) / 1000))
  exact hmono.trans cosh_b22910_ub

private lemma cosh5_v_251_le : cosh (126 : ℝ) / 275 ≤ (110696547 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((126 : ℝ) / 275) (by norm_num) (by norm_num : ((126 : ℝ) / 275) ≤ ((917 : ℝ) / 2000))
  exact hmono.trans cosh_b4585_ub

private lemma sech5_pt_251_ge : (1644 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (126 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_251_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_251_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_252_le : cosh (23 : ℝ) / 10 ≤ (503722065 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((23 : ℝ) / 10) (by norm_num) (by norm_num : ((23 : ℝ) / 10) ≤ ((23 : ℝ) / 10))
  exact hmono.trans cosh_b23000_ub

private lemma cosh5_v_252_le : cosh (23 : ℝ) / 50 ≤ (110767882 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((23 : ℝ) / 50) (by norm_num) (by norm_num : ((23 : ℝ) / 50) ≤ ((23 : ℝ) / 50))
  exact hmono.trans cosh_b4600_ub

private lemma sech5_pt_252_ge : (1629 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_252_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_252_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_253_le : cosh (127 : ℝ) / 55 ≤ (508434980 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((127 : ℝ) / 55) (by norm_num) (by norm_num : ((127 : ℝ) / 55) ≤ ((4619 : ℝ) / 2000))
  exact hmono.trans cosh_b23095_ub

private lemma cosh5_v_253_le : cosh (127 : ℝ) / 275 ≤ (110863383 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((127 : ℝ) / 275) (by norm_num) (by norm_num : ((127 : ℝ) / 275) ≤ ((231 : ℝ) / 500))
  exact hmono.trans cosh_b4620_ub

private lemma sech5_pt_253_ge : (1612 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (127 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_253_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_253_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_254_le : cosh (51 : ℝ) / 22 ≤ (512942168 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((51 : ℝ) / 22) (by norm_num) (by norm_num : ((51 : ℝ) / 22) ≤ ((4637 : ℝ) / 2000))
  exact hmono.trans cosh_b23185_ub

private lemma cosh5_v_254_le : cosh (51 : ℝ) / 110 ≤ (110959327 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((51 : ℝ) / 110) (by norm_num) (by norm_num : ((51 : ℝ) / 110) ≤ ((58 : ℝ) / 125))
  exact hmono.trans cosh_b4640_ub

private lemma sech5_pt_254_ge : (1597 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (51 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_254_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_254_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_255_le : cosh (128 : ℝ) / 55 ≤ (517490904 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((128 : ℝ) / 55) (by norm_num) (by norm_num : ((128 : ℝ) / 55) ≤ ((931 : ℝ) / 400))
  exact hmono.trans cosh_b23275_ub

private lemma cosh5_v_255_le : cosh (128 : ℝ) / 275 ≤ (111031576 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((128 : ℝ) / 275) (by norm_num) (by norm_num : ((128 : ℝ) / 275) ≤ ((931 : ℝ) / 2000))
  exact hmono.trans cosh_b4655_ub

private lemma sech5_pt_255_ge : (1582 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (128 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_255_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_255_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_256_le : cosh (257 : ℝ) / 110 ≤ (522081557 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((257 : ℝ) / 110) (by norm_num) (by norm_num : ((257 : ℝ) / 110) ≤ ((4673 : ℝ) / 2000))
  exact hmono.trans cosh_b23365_ub

private lemma cosh5_v_256_le : cosh (257 : ℝ) / 550 ≤ (111128297 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((257 : ℝ) / 550) (by norm_num) (by norm_num : ((257 : ℝ) / 550) ≤ ((187 : ℝ) / 400))
  exact hmono.trans cosh_b4675_ub

private lemma sech5_pt_256_ge : (1566 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (257 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_256_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_256_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_257_le : cosh (129 : ℝ) / 55 ≤ (526714498 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((129 : ℝ) / 55) (by norm_num) (by norm_num : ((129 : ℝ) / 55) ≤ ((4691 : ℝ) / 2000))
  exact hmono.trans cosh_b23455_ub

private lemma cosh5_v_257_le : cosh (129 : ℝ) / 275 ≤ (111225463 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((129 : ℝ) / 275) (by norm_num) (by norm_num : ((129 : ℝ) / 275) ≤ ((939 : ℝ) / 2000))
  exact hmono.trans cosh_b4695_ub

private lemma sech5_pt_257_ge : (1551 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (129 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_257_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_257_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_258_le : cosh (259 : ℝ) / 110 ≤ (531651119 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((259 : ℝ) / 110) (by norm_num) (by norm_num : ((259 : ℝ) / 110) ≤ ((471 : ℝ) / 200))
  exact hmono.trans cosh_b23550_ub

private lemma cosh5_v_258_le : cosh (259 : ℝ) / 550 ≤ (111298629 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((259 : ℝ) / 550) (by norm_num) (by norm_num : ((259 : ℝ) / 550) ≤ ((471 : ℝ) / 1000))
  exact hmono.trans cosh_b4710_ub

private lemma sech5_pt_258_ge : (1536 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (259 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_258_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_258_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_259_le : cosh (26 : ℝ) / 11 ≤ (536372170 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((26 : ℝ) / 11) (by norm_num) (by norm_num : ((26 : ℝ) / 11) ≤ ((591 : ℝ) / 250))
  exact hmono.trans cosh_b23640_ub

private lemma cosh5_v_259_le : cosh (26 : ℝ) / 55 ≤ (111396573 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((26 : ℝ) / 55) (by norm_num) (by norm_num : ((26 : ℝ) / 55) ≤ ((473 : ℝ) / 1000))
  exact hmono.trans cosh_b4730_ub

private lemma sech5_pt_259_ge : (1521 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (26 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_259_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_259_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_260_le : cosh (261 : ℝ) / 110 ≤ (541136668 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((261 : ℝ) / 110) (by norm_num) (by norm_num : ((261 : ℝ) / 110) ≤ ((2373 : ℝ) / 1000))
  exact hmono.trans cosh_b23730_ub

private lemma cosh5_v_260_le : cosh (261 : ℝ) / 550 ≤ (111494963 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((261 : ℝ) / 550) (by norm_num) (by norm_num : ((261 : ℝ) / 550) ≤ ((19 : ℝ) / 40))
  exact hmono.trans cosh_b4750_ub

private lemma sech5_pt_260_ge : (1506 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (261 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_260_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_260_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_261_le : cosh (131 : ℝ) / 55 ≤ (545944998 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((131 : ℝ) / 55) (by norm_num) (by norm_num : ((131 : ℝ) / 55) ≤ ((1191 : ℝ) / 500))
  exact hmono.trans cosh_b23820_ub

private lemma cosh5_v_261_le : cosh (131 : ℝ) / 275 ≤ (111569048 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((131 : ℝ) / 275) (by norm_num) (by norm_num : ((131 : ℝ) / 275) ≤ ((953 : ℝ) / 2000))
  exact hmono.trans cosh_b4765_ub

private lemma sech5_pt_261_ge : (1492 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (131 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_261_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_261_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_262_le : cosh (263 : ℝ) / 110 ≤ (550797550 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((263 : ℝ) / 110) (by norm_num) (by norm_num : ((263 : ℝ) / 110) ≤ ((2391 : ℝ) / 1000))
  exact hmono.trans cosh_b23910_ub

private lemma cosh5_v_262_le : cosh (263 : ℝ) / 550 ≤ (111668219 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((263 : ℝ) / 550) (by norm_num) (by norm_num : ((263 : ℝ) / 550) ≤ ((957 : ℝ) / 2000))
  exact hmono.trans cosh_b4785_ub

private lemma sech5_pt_262_ge : (1478 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (263 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_262_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_262_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_263_le : cosh (12 : ℝ) / 5 ≤ (555694717 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((12 : ℝ) / 5) (by norm_num) (by norm_num : ((12 : ℝ) / 5) ≤ ((12 : ℝ) / 5))
  exact hmono.trans cosh_b24000_ub

private lemma cosh5_v_263_le : cosh (12 : ℝ) / 25 ≤ (111742890 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((12 : ℝ) / 25) (by norm_num) (by norm_num : ((12 : ℝ) / 25) ≤ ((12 : ℝ) / 25))
  exact hmono.trans cosh_b4800_ub

private lemma sech5_pt_263_ge : (1464 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (12 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_263_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_263_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_264_le : cosh (53 : ℝ) / 22 ≤ (560912789 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((53 : ℝ) / 22) (by norm_num) (by norm_num : ((53 : ℝ) / 22) ≤ ((4819 : ℝ) / 2000))
  exact hmono.trans cosh_b24095_ub

private lemma cosh5_v_264_le : cosh (53 : ℝ) / 110 ≤ (111842843 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((53 : ℝ) / 110) (by norm_num) (by norm_num : ((53 : ℝ) / 110) ≤ ((241 : ℝ) / 500))
  exact hmono.trans cosh_b4820_ub

private lemma sech5_pt_264_ge : (1449 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (53 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_264_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_264_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_265_le : cosh (133 : ℝ) / 55 ≤ (565902914 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((133 : ℝ) / 55) (by norm_num) (by norm_num : ((133 : ℝ) / 55) ≤ ((4837 : ℝ) / 2000))
  exact hmono.trans cosh_b24185_ub

private lemma cosh5_v_265_le : cosh (133 : ℝ) / 275 ≤ (111943243 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((133 : ℝ) / 275) (by norm_num) (by norm_num : ((133 : ℝ) / 275) ≤ ((121 : ℝ) / 250))
  exact hmono.trans cosh_b4840_ub

private lemma sech5_pt_265_ge : (1435 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (133 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_265_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_265_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_266_le : cosh (267 : ℝ) / 110 ≤ (570938878 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((267 : ℝ) / 110) (by norm_num) (by norm_num : ((267 : ℝ) / 110) ≤ ((971 : ℝ) / 400))
  exact hmono.trans cosh_b24275_ub

private lemma cosh5_v_266_le : cosh (267 : ℝ) / 550 ≤ (112018837 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((267 : ℝ) / 550) (by norm_num) (by norm_num : ((267 : ℝ) / 550) ≤ ((971 : ℝ) / 2000))
  exact hmono.trans cosh_b4855_ub

private lemma sech5_pt_266_ge : (1421 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (267 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_266_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_266_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_267_le : cosh (134 : ℝ) / 55 ≤ (576021087 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((134 : ℝ) / 55) (by norm_num) (by norm_num : ((134 : ℝ) / 55) ≤ ((4873 : ℝ) / 2000))
  exact hmono.trans cosh_b24365_ub

private lemma cosh5_v_267_le : cosh (134 : ℝ) / 275 ≤ (112120021 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((134 : ℝ) / 275) (by norm_num) (by norm_num : ((134 : ℝ) / 275) ≤ ((39 : ℝ) / 80))
  exact hmono.trans cosh_b4875_ub

private lemma sech5_pt_267_ge : (1407 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (134 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_267_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_267_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_268_le : cosh (269 : ℝ) / 110 ≤ (581149955 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((269 : ℝ) / 110) (by norm_num) (by norm_num : ((269 : ℝ) / 110) ≤ ((4891 : ℝ) / 2000))
  exact hmono.trans cosh_b24455_ub

private lemma cosh5_v_268_le : cosh (269 : ℝ) / 550 ≤ (112221653 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((269 : ℝ) / 550) (by norm_num) (by norm_num : ((269 : ℝ) / 550) ≤ ((979 : ℝ) / 2000))
  exact hmono.trans cosh_b4895_ub

private lemma sech5_pt_268_ge : (1393 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (269 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_268_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_268_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_269_le : cosh (27 : ℝ) / 11 ≤ (586614838 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((27 : ℝ) / 11) (by norm_num) (by norm_num : ((27 : ℝ) / 11) ≤ ((491 : ℝ) / 200))
  exact hmono.trans cosh_b24550_ub

private lemma cosh5_v_269_le : cosh (27 : ℝ) / 55 ≤ (112298172 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((27 : ℝ) / 55) (by norm_num) (by norm_num : ((27 : ℝ) / 55) ≤ ((491 : ℝ) / 1000))
  exact hmono.trans cosh_b4910_ub

private lemma sech5_pt_269_ge : (1380 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_269_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_269_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_270_le : cosh (271 : ℝ) / 110 ≤ (591840923 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((271 : ℝ) / 110) (by norm_num) (by norm_num : ((271 : ℝ) / 110) ≤ ((308 : ℝ) / 125))
  exact hmono.trans cosh_b24640_ub

private lemma cosh5_v_270_le : cosh (271 : ℝ) / 550 ≤ (112400590 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((271 : ℝ) / 550) (by norm_num) (by norm_num : ((271 : ℝ) / 550) ≤ ((493 : ℝ) / 1000))
  exact hmono.trans cosh_b4930_ub

private lemma sech5_pt_270_ge : (1366 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (271 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_270_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_270_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_271_le : cosh (136 : ℝ) / 55 ≤ (597114947 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((136 : ℝ) / 55) (by norm_num) (by norm_num : ((136 : ℝ) / 55) ≤ ((2473 : ℝ) / 1000))
  exact hmono.trans cosh_b24730_ub

private lemma cosh5_v_271_le : cosh (136 : ℝ) / 275 ≤ (112503458 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((136 : ℝ) / 275) (by norm_num) (by norm_num : ((136 : ℝ) / 275) ≤ ((99 : ℝ) / 200))
  exact hmono.trans cosh_b4950_ub

private lemma sech5_pt_271_ge : (1353 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (136 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_271_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_271_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_272_le : cosh (273 : ℝ) / 110 ≤ (602437338 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((273 : ℝ) / 110) (by norm_num) (by norm_num : ((273 : ℝ) / 110) ≤ ((1241 : ℝ) / 500))
  exact hmono.trans cosh_b24820_ub

private lemma cosh5_v_272_le : cosh (273 : ℝ) / 550 ≤ (112580904 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((273 : ℝ) / 550) (by norm_num) (by norm_num : ((273 : ℝ) / 550) ≤ ((993 : ℝ) / 2000))
  exact hmono.trans cosh_b4965_ub

private lemma sech5_pt_272_ge : (1340 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (273 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_272_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_272_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_273_le : cosh (137 : ℝ) / 55 ≤ (607808527 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((137 : ℝ) / 55) (by norm_num) (by norm_num : ((137 : ℝ) / 55) ≤ ((2491 : ℝ) / 1000))
  exact hmono.trans cosh_b24910_ub

private lemma cosh5_v_273_le : cosh (137 : ℝ) / 275 ≤ (112684560 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((137 : ℝ) / 275) (by norm_num) (by norm_num : ((137 : ℝ) / 275) ≤ ((997 : ℝ) / 2000))
  exact hmono.trans cosh_b4985_ub

private lemma sech5_pt_273_ge : (1327 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (137 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_273_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_273_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_274_le : cosh (5 : ℝ) / 2 ≤ (613228948 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((5 : ℝ) / 2) (by norm_num) (by norm_num : ((5 : ℝ) / 2) ≤ ((5 : ℝ) / 2))
  exact hmono.trans cosh_b25000_ub

private lemma cosh5_v_274_le : cosh (1 : ℝ) / 2 ≤ (112762597 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 2) (by norm_num) (by norm_num : ((1 : ℝ) / 2) ≤ ((1 : ℝ) / 2))
  exact hmono.trans cosh_b5000_ub

private lemma sech5_pt_274_ge : (1314 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (5 : ℝ) / 2 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_274_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_274_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_275_le : cosh (138 : ℝ) / 55 ≤ (619004401 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((138 : ℝ) / 55) (by norm_num) (by norm_num : ((138 : ℝ) / 55) ≤ ((5019 : ℝ) / 2000))
  exact hmono.trans cosh_b25095_ub

private lemma cosh5_v_275_le : cosh (138 : ℝ) / 275 ≤ (112867042 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((138 : ℝ) / 275) (by norm_num) (by norm_num : ((138 : ℝ) / 275) ≤ ((251 : ℝ) / 500))
  exact hmono.trans cosh_b5020_ub

private lemma sech5_pt_275_ge : (1301 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (138 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_275_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_275_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_276_le : cosh (277 : ℝ) / 110 ≤ (624527407 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((277 : ℝ) / 110) (by norm_num) (by norm_num : ((277 : ℝ) / 110) ≤ ((5037 : ℝ) / 2000))
  exact hmono.trans cosh_b25185_ub

private lemma cosh5_v_276_le : cosh (277 : ℝ) / 550 ≤ (112971938 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((277 : ℝ) / 550) (by norm_num) (by norm_num : ((277 : ℝ) / 550) ≤ ((63 : ℝ) / 125))
  exact hmono.trans cosh_b5040_ub

private lemma sech5_pt_276_ge : (1288 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (277 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_276_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_276_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_277_le : cosh (139 : ℝ) / 55 ≤ (630101000 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((139 : ℝ) / 55) (by norm_num) (by norm_num : ((139 : ℝ) / 55) ≤ ((1011 : ℝ) / 400))
  exact hmono.trans cosh_b25275_ub

private lemma cosh5_v_277_le : cosh (139 : ℝ) / 275 ≤ (113050906 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((139 : ℝ) / 275) (by norm_num) (by norm_num : ((139 : ℝ) / 275) ≤ ((1011 : ℝ) / 2000))
  exact hmono.trans cosh_b5055_ub

private lemma sech5_pt_277_ge : (1276 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (139 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_277_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_277_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_278_le : cosh (279 : ℝ) / 110 ≤ (635725631 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((279 : ℝ) / 110) (by norm_num) (by norm_num : ((279 : ℝ) / 110) ≤ ((5073 : ℝ) / 2000))
  exact hmono.trans cosh_b25365_ub

private lemma cosh5_v_278_le : cosh (279 : ℝ) / 550 ≤ (113156594 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((279 : ℝ) / 550) (by norm_num) (by norm_num : ((279 : ℝ) / 550) ≤ ((203 : ℝ) / 400))
  exact hmono.trans cosh_b5075_ub

private lemma sech5_pt_278_ge : (1263 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (279 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_278_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_278_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_279_le : cosh (28 : ℝ) / 11 ≤ (641401756 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((28 : ℝ) / 11) (by norm_num) (by norm_num : ((28 : ℝ) / 11) ≤ ((5091 : ℝ) / 2000))
  exact hmono.trans cosh_b25455_ub

private lemma cosh5_v_279_le : cosh (28 : ℝ) / 55 ≤ (113262733 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((28 : ℝ) / 55) (by norm_num) (by norm_num : ((28 : ℝ) / 55) ≤ ((1019 : ℝ) / 2000))
  exact hmono.trans cosh_b5095_ub

private lemma sech5_pt_279_ge : (1251 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (28 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_279_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_279_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_280_le : cosh (281 : ℝ) / 110 ≤ (647449595 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((281 : ℝ) / 110) (by norm_num) (by norm_num : ((281 : ℝ) / 110) ≤ ((511 : ℝ) / 200))
  exact hmono.trans cosh_b25550_ub

private lemma cosh5_v_280_le : cosh (281 : ℝ) / 550 ≤ (113342636 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((281 : ℝ) / 550) (by norm_num) (by norm_num : ((281 : ℝ) / 550) ≤ ((511 : ℝ) / 1000))
  exact hmono.trans cosh_b5110_ub

private lemma sech5_pt_280_ge : (1238 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (281 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_280_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_280_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_281_le : cosh (141 : ℝ) / 55 ≤ (653233018 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((141 : ℝ) / 55) (by norm_num) (by norm_num : ((141 : ℝ) / 55) ≤ ((641 : ℝ) / 250))
  exact hmono.trans cosh_b25640_ub

private lemma cosh5_v_281_le : cosh (141 : ℝ) / 275 ≤ (113449569 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((141 : ℝ) / 275) (by norm_num) (by norm_num : ((141 : ℝ) / 275) ≤ ((513 : ℝ) / 1000))
  exact hmono.trans cosh_b5130_ub

private lemma sech5_pt_281_ge : (1226 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (141 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_281_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_281_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_282_le : cosh (283 : ℝ) / 110 ≤ (659069353 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((283 : ℝ) / 110) (by norm_num) (by norm_num : ((283 : ℝ) / 110) ≤ ((2573 : ℝ) / 1000))
  exact hmono.trans cosh_b25730_ub

private lemma cosh5_v_282_le : cosh (283 : ℝ) / 550 ≤ (113556955 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((283 : ℝ) / 550) (by norm_num) (by norm_num : ((283 : ℝ) / 550) ≤ ((103 : ℝ) / 200))
  exact hmono.trans cosh_b5150_ub

private lemma sech5_pt_282_ge : (1214 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (283 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_282_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_282_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_283_le : cosh (142 : ℝ) / 55 ≤ (664959073 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((142 : ℝ) / 55) (by norm_num) (by norm_num : ((142 : ℝ) / 55) ≤ ((1291 : ℝ) / 500))
  exact hmono.trans cosh_b25820_ub

private lemma cosh5_v_283_le : cosh (142 : ℝ) / 275 ≤ (113637793 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((142 : ℝ) / 275) (by norm_num) (by norm_num : ((142 : ℝ) / 275) ≤ ((1033 : ℝ) / 2000))
  exact hmono.trans cosh_b5165_ub

private lemma sech5_pt_283_ge : (1203 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (142 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_283_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_283_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_284_le : cosh (57 : ℝ) / 22 ≤ (670902655 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((57 : ℝ) / 22) (by norm_num) (by norm_num : ((57 : ℝ) / 22) ≤ ((2591 : ℝ) / 1000))
  exact hmono.trans cosh_b25910_ub

private lemma cosh5_v_284_le : cosh (57 : ℝ) / 110 ≤ (113745975 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((57 : ℝ) / 110) (by norm_num) (by norm_num : ((57 : ℝ) / 110) ≤ ((1037 : ℝ) / 2000))
  exact hmono.trans cosh_b5185_ub

private lemma sech5_pt_284_ge : (1191 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (57 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_284_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_284_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_285_le : cosh (13 : ℝ) / 5 ≤ (676900581 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((13 : ℝ) / 5) (by norm_num) (by norm_num : ((13 : ℝ) / 5) ≤ ((13 : ℝ) / 5))
  exact hmono.trans cosh_b26000_ub

private lemma cosh5_v_285_le : cosh (13 : ℝ) / 25 ≤ (113827410 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((13 : ℝ) / 25) (by norm_num) (by norm_num : ((13 : ℝ) / 25) ≤ ((13 : ℝ) / 25))
  exact hmono.trans cosh_b5200_ub

private lemma sech5_pt_285_ge : (1179 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_285_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_285_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_286_le : cosh (287 : ℝ) / 110 ≤ (683291218 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((287 : ℝ) / 110) (by norm_num) (by norm_num : ((287 : ℝ) / 110) ≤ ((5219 : ℝ) / 2000))
  exact hmono.trans cosh_b26095_ub

private lemma cosh5_v_286_le : cosh (287 : ℝ) / 550 ≤ (113936389 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((287 : ℝ) / 550) (by norm_num) (by norm_num : ((287 : ℝ) / 550) ≤ ((261 : ℝ) / 500))
  exact hmono.trans cosh_b5220_ub

private lemma sech5_pt_286_ge : (1167 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (287 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_286_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_286_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_287_le : cosh (144 : ℝ) / 55 ≤ (689402380 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((144 : ℝ) / 55) (by norm_num) (by norm_num : ((144 : ℝ) / 55) ≤ ((5237 : ℝ) / 2000))
  exact hmono.trans cosh_b26185_ub

private lemma cosh5_v_287_le : cosh (144 : ℝ) / 275 ≤ (114045823 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((144 : ℝ) / 275) (by norm_num) (by norm_num : ((144 : ℝ) / 275) ≤ ((131 : ℝ) / 250))
  exact hmono.trans cosh_b5240_ub

private lemma sech5_pt_287_ge : (1156 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (144 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_287_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_287_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_288_le : cosh (289 : ℝ) / 110 ≤ (695569385 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((289 : ℝ) / 110) (by norm_num) (by norm_num : ((289 : ℝ) / 110) ≤ ((1051 : ℝ) / 400))
  exact hmono.trans cosh_b26275_ub

private lemma cosh5_v_288_le : cosh (289 : ℝ) / 550 ≤ (114128198 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((289 : ℝ) / 550) (by norm_num) (by norm_num : ((289 : ℝ) / 550) ≤ ((1051 : ℝ) / 2000))
  exact hmono.trans cosh_b5255_ub

private lemma sech5_pt_288_ge : (1145 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (289 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_288_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_288_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_289_le : cosh (29 : ℝ) / 11 ≤ (701792730 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((29 : ℝ) / 11) (by norm_num) (by norm_num : ((29 : ℝ) / 11) ≤ ((5273 : ℝ) / 2000))
  exact hmono.trans cosh_b26365_ub

private lemma cosh5_v_289_le : cosh (29 : ℝ) / 55 ≤ (114238431 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((29 : ℝ) / 55) (by norm_num) (by norm_num : ((29 : ℝ) / 55) ≤ ((211 : ℝ) / 400))
  exact hmono.trans cosh_b5275_ub

private lemma sech5_pt_289_ge : (1133 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_289_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_289_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_290_le : cosh (291 : ℝ) / 110 ≤ (708072922 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((291 : ℝ) / 110) (by norm_num) (by norm_num : ((291 : ℝ) / 110) ≤ ((5291 : ℝ) / 2000))
  exact hmono.trans cosh_b26455_ub

private lemma cosh5_v_290_le : cosh (291 : ℝ) / 550 ≤ (114349121 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((291 : ℝ) / 550) (by norm_num) (by norm_num : ((291 : ℝ) / 550) ≤ ((1059 : ℝ) / 2000))
  exact hmono.trans cosh_b5295_ub

private lemma sech5_pt_290_ge : (1122 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (291 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_290_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_290_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_291_le : cosh (146 : ℝ) / 55 ≤ (714764245 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((146 : ℝ) / 55) (by norm_num) (by norm_num : ((146 : ℝ) / 55) ≤ ((531 : ℝ) / 200))
  exact hmono.trans cosh_b26550_ub

private lemma cosh5_v_291_le : cosh (146 : ℝ) / 275 ≤ (114432438 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((146 : ℝ) / 275) (by norm_num) (by norm_num : ((146 : ℝ) / 275) ≤ ((531 : ℝ) / 1000))
  exact hmono.trans cosh_b5310_ub

private lemma sech5_pt_291_ge : (1111 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (146 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_291_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_291_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_292_le : cosh (293 : ℝ) / 110 ≤ (721162889 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((293 : ℝ) / 110) (by norm_num) (by norm_num : ((293 : ℝ) / 110) ≤ ((333 : ℝ) / 125))
  exact hmono.trans cosh_b26640_ub

private lemma cosh5_v_292_le : cosh (293 : ℝ) / 550 ≤ (114543928 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((293 : ℝ) / 550) (by norm_num) (by norm_num : ((293 : ℝ) / 550) ≤ ((533 : ℝ) / 1000))
  exact hmono.trans cosh_b5330_ub

private lemma sech5_pt_292_ge : (1100 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (293 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_292_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_292_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_293_le : cosh (147 : ℝ) / 55 ≤ (727619947 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((147 : ℝ) / 55) (by norm_num) (by norm_num : ((147 : ℝ) / 55) ≤ ((2673 : ℝ) / 1000))
  exact hmono.trans cosh_b26730_ub

private lemma cosh5_v_293_le : cosh (147 : ℝ) / 275 ≤ (114655877 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((147 : ℝ) / 275) (by norm_num) (by norm_num : ((147 : ℝ) / 275) ≤ ((107 : ℝ) / 200))
  exact hmono.trans cosh_b5350_ub

private lemma sech5_pt_293_ge : (1089 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (147 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_293_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_293_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_294_le : cosh (59 : ℝ) / 22 ≤ (734135942 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((59 : ℝ) / 22) (by norm_num) (by norm_num : ((59 : ℝ) / 22) ≤ ((1341 : ℝ) / 500))
  exact hmono.trans cosh_b26820_ub

private lemma cosh5_v_294_le : cosh (59 : ℝ) / 110 ≤ (114740140 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((59 : ℝ) / 110) (by norm_num) (by norm_num : ((59 : ℝ) / 110) ≤ ((1073 : ℝ) / 2000))
  exact hmono.trans cosh_b5365_ub

private lemma sech5_pt_294_ge : (1079 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (59 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_294_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_294_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_295_le : cosh (148 : ℝ) / 55 ≤ (740711403 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((148 : ℝ) / 55) (by norm_num) (by norm_num : ((148 : ℝ) / 55) ≤ ((2691 : ℝ) / 1000))
  exact hmono.trans cosh_b26910_ub

private lemma cosh5_v_295_le : cosh (148 : ℝ) / 275 ≤ (114852891 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((148 : ℝ) / 275) (by norm_num) (by norm_num : ((148 : ℝ) / 275) ≤ ((1077 : ℝ) / 2000))
  exact hmono.trans cosh_b5385_ub

private lemma sech5_pt_295_ge : (1068 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (148 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_295_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_295_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_296_le : cosh (27 : ℝ) / 10 ≤ (747346862 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((27 : ℝ) / 10) (by norm_num) (by norm_num : ((27 : ℝ) / 10) ≤ ((27 : ℝ) / 10))
  exact hmono.trans cosh_b27000_ub

private lemma cosh5_v_296_le : cosh (27 : ℝ) / 50 ≤ (114937756 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((27 : ℝ) / 50) (by norm_num) (by norm_num : ((27 : ℝ) / 50) ≤ ((27 : ℝ) / 50))
  exact hmono.trans cosh_b5400_ub

private lemma sech5_pt_296_ge : (1058 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_296_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_296_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_297_le : cosh (149 : ℝ) / 55 ≤ (754416642 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((149 : ℝ) / 55) (by norm_num) (by norm_num : ((149 : ℝ) / 55) ≤ ((5419 : ℝ) / 2000))
  exact hmono.trans cosh_b27095_ub

private lemma cosh5_v_297_le : cosh (149 : ℝ) / 275 ≤ (115051312 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((149 : ℝ) / 275) (by norm_num) (by norm_num : ((149 : ℝ) / 275) ≤ ((271 : ℝ) / 500))
  exact hmono.trans cosh_b5420_ub

private lemma sech5_pt_297_ge : (1047 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (149 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_297_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_297_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_298_le : cosh (299 : ℝ) / 110 ≤ (761177124 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((299 : ℝ) / 110) (by norm_num) (by norm_num : ((299 : ℝ) / 110) ≤ ((5437 : ℝ) / 2000))
  exact hmono.trans cosh_b27185_ub

private lemma cosh5_v_298_le : cosh (299 : ℝ) / 550 ≤ (115165328 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((299 : ℝ) / 550) (by norm_num) (by norm_num : ((299 : ℝ) / 550) ≤ ((68 : ℝ) / 125))
  exact hmono.trans cosh_b5440_ub

private lemma sech5_pt_298_ge : (1037 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (299 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_298_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_298_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_299_le : cosh (30 : ℝ) / 11 ≤ (767999261 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((30 : ℝ) / 11) (by norm_num) (by norm_num : ((30 : ℝ) / 11) ≤ ((1091 : ℝ) / 400))
  exact hmono.trans cosh_b27275_ub

private lemma cosh5_v_299_le : cosh (6 : ℝ) / 11 ≤ (115251142 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((6 : ℝ) / 11) (by norm_num) (by norm_num : ((6 : ℝ) / 11) ≤ ((1091 : ℝ) / 2000))
  exact hmono.trans cosh_b5455_ub

private lemma sech5_pt_299_ge : (1027 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (30 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_299_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_299_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma sech5_batch_5_ge : (66015 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (251 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (126 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (127 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (51 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (128 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (257 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (129 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (259 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (26 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (261 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (131 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (263 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (12 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (53 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (133 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (267 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (134 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (269 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (271 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (136 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (273 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (137 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (5 : ℝ) / 2 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (138 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (277 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (139 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (279 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (28 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (281 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (141 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (283 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (142 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (57 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (287 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (144 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (289 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (291 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (146 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (293 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (147 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (59 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (148 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (149 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (299 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (30 : ℝ) / 11 := by
  linarith [sech5_pt_250_ge, sech5_pt_251_ge, sech5_pt_252_ge, sech5_pt_253_ge, sech5_pt_254_ge, sech5_pt_255_ge, sech5_pt_256_ge, sech5_pt_257_ge, sech5_pt_258_ge, sech5_pt_259_ge, sech5_pt_260_ge, sech5_pt_261_ge, sech5_pt_262_ge, sech5_pt_263_ge, sech5_pt_264_ge, sech5_pt_265_ge, sech5_pt_266_ge, sech5_pt_267_ge, sech5_pt_268_ge, sech5_pt_269_ge, sech5_pt_270_ge, sech5_pt_271_ge, sech5_pt_272_ge, sech5_pt_273_ge, sech5_pt_274_ge, sech5_pt_275_ge, sech5_pt_276_ge, sech5_pt_277_ge, sech5_pt_278_ge, sech5_pt_279_ge, sech5_pt_280_ge, sech5_pt_281_ge, sech5_pt_282_ge, sech5_pt_283_ge, sech5_pt_284_ge, sech5_pt_285_ge, sech5_pt_286_ge, sech5_pt_287_ge, sech5_pt_288_ge, sech5_pt_289_ge, sech5_pt_290_ge, sech5_pt_291_ge, sech5_pt_292_ge, sech5_pt_293_ge, sech5_pt_294_ge, sech5_pt_295_ge, sech5_pt_296_ge, sech5_pt_297_ge, sech5_pt_298_ge, sech5_pt_299_ge]

private lemma cosh5_u_300_le : cosh (301 : ℝ) / 110 ≤ (774883607 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((301 : ℝ) / 110) (by norm_num) (by norm_num : ((301 : ℝ) / 110) ≤ ((5473 : ℝ) / 2000))
  exact hmono.trans cosh_b27365_ub

private lemma cosh5_v_300_le : cosh (301 : ℝ) / 550 ≤ (115365965 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((301 : ℝ) / 550) (by norm_num) (by norm_num : ((301 : ℝ) / 550) ≤ ((219 : ℝ) / 400))
  exact hmono.trans cosh_b5475_ub

private lemma sech5_pt_300_ge : (1016 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (301 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_300_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_300_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_301_le : cosh (151 : ℝ) / 55 ≤ (781830719 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((151 : ℝ) / 55) (by norm_num) (by norm_num : ((151 : ℝ) / 55) ≤ ((5491 : ℝ) / 2000))
  exact hmono.trans cosh_b27455_ub

private lemma cosh5_v_301_le : cosh (151 : ℝ) / 275 ≤ (115481249 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((151 : ℝ) / 275) (by norm_num) (by norm_num : ((151 : ℝ) / 275) ≤ ((1099 : ℝ) / 2000))
  exact hmono.trans cosh_b5495_ub

private lemma sech5_pt_301_ge : (1006 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (151 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_301_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_301_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_302_le : cosh (303 : ℝ) / 110 ≤ (789232497 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((303 : ℝ) / 110) (by norm_num) (by norm_num : ((303 : ℝ) / 110) ≤ ((551 : ℝ) / 200))
  exact hmono.trans cosh_b27550_ub

private lemma cosh5_v_302_le : cosh (303 : ℝ) / 550 ≤ (115568015 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((303 : ℝ) / 550) (by norm_num) (by norm_num : ((303 : ℝ) / 550) ≤ ((551 : ℝ) / 1000))
  exact hmono.trans cosh_b5510_ub

private lemma sech5_pt_302_ge : (996 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (303 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_302_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_302_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_303_le : cosh (152 : ℝ) / 55 ≤ (796310400 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((152 : ℝ) / 55) (by norm_num) (by norm_num : ((152 : ℝ) / 55) ≤ ((691 : ℝ) / 250))
  exact hmono.trans cosh_b27640_ub

private lemma cosh5_v_303_le : cosh (152 : ℝ) / 275 ≤ (115684107 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((152 : ℝ) / 275) (by norm_num) (by norm_num : ((152 : ℝ) / 275) ≤ ((553 : ℝ) / 1000))
  exact hmono.trans cosh_b5530_ub

private lemma sech5_pt_303_ge : (986 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (152 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_303_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_303_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_304_le : cosh (61 : ℝ) / 22 ≤ (803452805 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((61 : ℝ) / 22) (by norm_num) (by norm_num : ((61 : ℝ) / 22) ≤ ((2773 : ℝ) / 1000))
  exact hmono.trans cosh_b27730_ub

private lemma cosh5_v_304_le : cosh (61 : ℝ) / 110 ≤ (115800663 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((61 : ℝ) / 110) (by norm_num) (by norm_num : ((61 : ℝ) / 110) ≤ ((111 : ℝ) / 200))
  exact hmono.trans cosh_b5550_ub

private lemma sech5_pt_304_ge : (977 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (61 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_304_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_304_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_305_le : cosh (153 : ℝ) / 55 ≤ (810660291 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((153 : ℝ) / 55) (by norm_num) (by norm_num : ((153 : ℝ) / 55) ≤ ((1391 : ℝ) / 500))
  exact hmono.trans cosh_b27820_ub

private lemma cosh5_v_305_le : cosh (153 : ℝ) / 275 ≤ (115888383 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((153 : ℝ) / 275) (by norm_num) (by norm_num : ((153 : ℝ) / 275) ≤ ((1113 : ℝ) / 2000))
  exact hmono.trans cosh_b5565_ub

private lemma sech5_pt_305_ge : (967 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (153 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_305_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_305_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_306_le : cosh (307 : ℝ) / 110 ≤ (817933440 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((307 : ℝ) / 110) (by norm_num) (by norm_num : ((307 : ℝ) / 110) ≤ ((2791 : ℝ) / 1000))
  exact hmono.trans cosh_b27910_ub

private lemma cosh5_v_306_le : cosh (307 : ℝ) / 550 ≤ (116005750 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((307 : ℝ) / 550) (by norm_num) (by norm_num : ((307 : ℝ) / 550) ≤ ((1117 : ℝ) / 2000))
  exact hmono.trans cosh_b5585_ub

private lemma sech5_pt_306_ge : (958 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (307 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_306_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_306_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_307_le : cosh (14 : ℝ) / 5 ≤ (825272842 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((14 : ℝ) / 5) (by norm_num) (by norm_num : ((14 : ℝ) / 5) ≤ ((14 : ℝ) / 5))
  exact hmono.trans cosh_b28000_ub

private lemma cosh5_v_307_le : cosh (14 : ℝ) / 25 ≤ (116094079 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((14 : ℝ) / 25) (by norm_num) (by norm_num : ((14 : ℝ) / 25) ≤ ((14 : ℝ) / 25))
  exact hmono.trans cosh_b5600_ub

private lemma sech5_pt_307_ge : (948 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (14 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_307_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_307_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_308_le : cosh (309 : ℝ) / 110 ≤ (833092522 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((309 : ℝ) / 110) (by norm_num) (by norm_num : ((309 : ℝ) / 110) ≤ ((5619 : ℝ) / 2000))
  exact hmono.trans cosh_b28095_ub

private lemma cosh5_v_308_le : cosh (309 : ℝ) / 550 ≤ (116212257 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((309 : ℝ) / 550) (by norm_num) (by norm_num : ((309 : ℝ) / 550) ≤ ((281 : ℝ) / 500))
  exact hmono.trans cosh_b5620_ub

private lemma sech5_pt_308_ge : (938 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (309 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_308_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_308_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_309_le : cosh (31 : ℝ) / 11 ≤ (840569984 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((31 : ℝ) / 11) (by norm_num) (by norm_num : ((31 : ℝ) / 11) ≤ ((5637 : ℝ) / 2000))
  exact hmono.trans cosh_b28185_ub

private lemma cosh5_v_309_le : cosh (31 : ℝ) / 55 ≤ (116330901 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((31 : ℝ) / 55) (by norm_num) (by norm_num : ((31 : ℝ) / 55) ≤ ((141 : ℝ) / 250))
  exact hmono.trans cosh_b5640_ub

private lemma sech5_pt_309_ge : (929 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_309_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_309_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_310_le : cosh (311 : ℝ) / 110 ≤ (848115533 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((311 : ℝ) / 110) (by norm_num) (by norm_num : ((311 : ℝ) / 110) ≤ ((1131 : ℝ) / 400))
  exact hmono.trans cosh_b28275_ub

private lemma cosh5_v_310_le : cosh (311 : ℝ) / 550 ≤ (116420189 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((311 : ℝ) / 550) (by norm_num) (by norm_num : ((311 : ℝ) / 550) ≤ ((1131 : ℝ) / 2000))
  exact hmono.trans cosh_b5655_ub

private lemma sech5_pt_310_ge : (920 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (311 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_310_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_310_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_311_le : cosh (156 : ℝ) / 55 ≤ (855729780 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((156 : ℝ) / 55) (by norm_num) (by norm_num : ((156 : ℝ) / 55) ≤ ((5673 : ℝ) / 2000))
  exact hmono.trans cosh_b28365_ub

private lemma cosh5_v_311_le : cosh (156 : ℝ) / 275 ≤ (116539647 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((156 : ℝ) / 275) (by norm_num) (by norm_num : ((156 : ℝ) / 275) ≤ ((227 : ℝ) / 400))
  exact hmono.trans cosh_b5675_ub

private lemma sech5_pt_311_ge : (911 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (156 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_311_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_311_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_312_le : cosh (313 : ℝ) / 110 ≤ (863413341 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((313 : ℝ) / 110) (by norm_num) (by norm_num : ((313 : ℝ) / 110) ≤ ((5691 : ℝ) / 2000))
  exact hmono.trans cosh_b28455_ub

private lemma cosh5_v_312_le : cosh (313 : ℝ) / 550 ≤ (116659571 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((313 : ℝ) / 550) (by norm_num) (by norm_num : ((313 : ℝ) / 550) ≤ ((1139 : ℝ) / 2000))
  exact hmono.trans cosh_b5695_ub

private lemma sech5_pt_312_ge : (902 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (313 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_312_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_312_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_313_le : cosh (157 : ℝ) / 55 ≤ (871599652 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((157 : ℝ) / 55) (by norm_num) (by norm_num : ((157 : ℝ) / 55) ≤ ((571 : ℝ) / 200))
  exact hmono.trans cosh_b28550_ub

private lemma cosh5_v_313_le : cosh (157 : ℝ) / 275 ≤ (116749820 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((157 : ℝ) / 275) (by norm_num) (by norm_num : ((157 : ℝ) / 275) ≤ ((571 : ℝ) / 1000))
  exact hmono.trans cosh_b5710_ub

private lemma sech5_pt_313_ge : (893 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (157 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_313_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_313_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_314_le : cosh (63 : ℝ) / 22 ≤ (879427654 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((63 : ℝ) / 22) (by norm_num) (by norm_num : ((63 : ℝ) / 22) ≤ ((358 : ℝ) / 125))
  exact hmono.trans cosh_b28640_ub

private lemma cosh5_v_314_le : cosh (63 : ℝ) / 110 ≤ (116870562 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((63 : ℝ) / 110) (by norm_num) (by norm_num : ((63 : ℝ) / 110) ≤ ((573 : ℝ) / 1000))
  exact hmono.trans cosh_b5730_ub

private lemma sech5_pt_314_ge : (884 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (63 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_314_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_314_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_315_le : cosh (158 : ℝ) / 55 ≤ (887326890 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((158 : ℝ) / 55) (by norm_num) (by norm_num : ((158 : ℝ) / 55) ≤ ((2873 : ℝ) / 1000))
  exact hmono.trans cosh_b28730_ub

private lemma cosh5_v_315_le : cosh (158 : ℝ) / 275 ≤ (116991770 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((158 : ℝ) / 275) (by norm_num) (by norm_num : ((158 : ℝ) / 275) ≤ ((23 : ℝ) / 40))
  exact hmono.trans cosh_b5750_ub

private lemma sech5_pt_315_ge : (875 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (158 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_315_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_315_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_316_le : cosh (317 : ℝ) / 110 ≤ (895298000 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((317 : ℝ) / 110) (by norm_num) (by norm_num : ((317 : ℝ) / 110) ≤ ((1441 : ℝ) / 500))
  exact hmono.trans cosh_b28820_ub

private lemma cosh5_v_316_le : cosh (317 : ℝ) / 550 ≤ (117082984 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((317 : ℝ) / 550) (by norm_num) (by norm_num : ((317 : ℝ) / 550) ≤ ((1153 : ℝ) / 2000))
  exact hmono.trans cosh_b5765_ub

private lemma sech5_pt_316_ge : (867 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (317 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_316_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_316_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_317_le : cosh (159 : ℝ) / 55 ≤ (903341629 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((159 : ℝ) / 55) (by norm_num) (by norm_num : ((159 : ℝ) / 55) ≤ ((2891 : ℝ) / 1000))
  exact hmono.trans cosh_b28910_ub

private lemma cosh5_v_317_le : cosh (159 : ℝ) / 275 ≤ (117205012 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((159 : ℝ) / 275) (by norm_num) (by norm_num : ((159 : ℝ) / 275) ≤ ((1157 : ℝ) / 2000))
  exact hmono.trans cosh_b5785_ub

private lemma sech5_pt_317_ge : (858 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (159 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_317_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_317_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_318_le : cosh (29 : ℝ) / 10 ≤ (911458430 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((29 : ℝ) / 10) (by norm_num) (by norm_num : ((29 : ℝ) / 10) ≤ ((29 : ℝ) / 10))
  exact hmono.trans cosh_b29000_ub

private lemma cosh5_v_318_le : cosh (29 : ℝ) / 50 ≤ (117296840 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((29 : ℝ) / 50) (by norm_num) (by norm_num : ((29 : ℝ) / 50) ≤ ((29 : ℝ) / 50))
  exact hmono.trans cosh_b5800_ub

private lemma sech5_pt_318_ge : (850 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_318_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_318_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_319_le : cosh (32 : ℝ) / 11 ≤ (920106272 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((32 : ℝ) / 11) (by norm_num) (by norm_num : ((32 : ℝ) / 11) ≤ ((5819 : ℝ) / 2000))
  exact hmono.trans cosh_b29095_ub

private lemma cosh5_v_319_le : cosh (32 : ℝ) / 55 ≤ (117419689 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((32 : ℝ) / 55) (by norm_num) (by norm_num : ((32 : ℝ) / 55) ≤ ((291 : ℝ) / 500))
  exact hmono.trans cosh_b5820_ub

private lemma sech5_pt_319_ge : (841 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (32 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_319_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_319_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_320_le : cosh (321 : ℝ) / 110 ≤ (928375552 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((321 : ℝ) / 110) (by norm_num) (by norm_num : ((321 : ℝ) / 110) ≤ ((5837 : ℝ) / 2000))
  exact hmono.trans cosh_b29185_ub

private lemma cosh5_v_320_le : cosh (321 : ℝ) / 550 ≤ (117543007 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((321 : ℝ) / 550) (by norm_num) (by norm_num : ((321 : ℝ) / 550) ≤ ((73 : ℝ) / 125))
  exact hmono.trans cosh_b5840_ub

private lemma sech5_pt_320_ge : (833 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (321 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_320_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_320_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_321_le : cosh (161 : ℝ) / 55 ≤ (936720030 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((161 : ℝ) / 55) (by norm_num) (by norm_num : ((161 : ℝ) / 55) ≤ ((1171 : ℝ) / 400))
  exact hmono.trans cosh_b29275_ub

private lemma cosh5_v_321_le : cosh (161 : ℝ) / 275 ≤ (117635805 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((161 : ℝ) / 275) (by norm_num) (by norm_num : ((161 : ℝ) / 275) ≤ ((1171 : ℝ) / 2000))
  exact hmono.trans cosh_b5855_ub

private lemma sech5_pt_321_ge : (825 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (161 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_321_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_321_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_322_le : cosh (323 : ℝ) / 110 ≤ (945140383 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((323 : ℝ) / 110) (by norm_num) (by norm_num : ((323 : ℝ) / 110) ≤ ((5873 : ℝ) / 2000))
  exact hmono.trans cosh_b29365_ub

private lemma cosh5_v_322_le : cosh (323 : ℝ) / 550 ≤ (117759946 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((323 : ℝ) / 550) (by norm_num) (by norm_num : ((323 : ℝ) / 550) ≤ ((47 : ℝ) / 80))
  exact hmono.trans cosh_b5875_ub

private lemma sech5_pt_322_ge : (816 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (323 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_322_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_322_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_323_le : cosh (162 : ℝ) / 55 ≤ (953637293 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((162 : ℝ) / 55) (by norm_num) (by norm_num : ((162 : ℝ) / 55) ≤ ((5891 : ℝ) / 2000))
  exact hmono.trans cosh_b29455_ub

private lemma cosh5_v_323_le : cosh (162 : ℝ) / 275 ≤ (117884559 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((162 : ℝ) / 275) (by norm_num) (by norm_num : ((162 : ℝ) / 275) ≤ ((1179 : ℝ) / 2000))
  exact hmono.trans cosh_b5895_ub

private lemma sech5_pt_323_ge : (808 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (162 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_323_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_323_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_324_le : cosh (65 : ℝ) / 22 ≤ (962690070 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((65 : ℝ) / 22) (by norm_num) (by norm_num : ((65 : ℝ) / 22) ≤ ((591 : ℝ) / 200))
  exact hmono.trans cosh_b29550_ub

private lemma cosh5_v_324_le : cosh (13 : ℝ) / 22 ≤ (117978328 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((13 : ℝ) / 22) (by norm_num) (by norm_num : ((13 : ℝ) / 22) ≤ ((591 : ℝ) / 1000))
  exact hmono.trans cosh_b5910_ub

private lemma sech5_pt_324_ge : (800 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (65 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_324_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_324_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_325_le : cosh (163 : ℝ) / 55 ≤ (971346515 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((163 : ℝ) / 55) (by norm_num) (by norm_num : ((163 : ℝ) / 55) ≤ ((741 : ℝ) / 250))
  exact hmono.trans cosh_b29640_ub

private lemma cosh5_v_325_le : cosh (163 : ℝ) / 275 ≤ (118103766 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((163 : ℝ) / 275) (by norm_num) (by norm_num : ((163 : ℝ) / 275) ≤ ((593 : ℝ) / 1000))
  exact hmono.trans cosh_b5930_ub

private lemma sech5_pt_325_ge : (792 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (163 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_325_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_325_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_326_le : cosh (327 : ℝ) / 110 ≤ (980081640 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((327 : ℝ) / 110) (by norm_num) (by norm_num : ((327 : ℝ) / 110) ≤ ((2973 : ℝ) / 1000))
  exact hmono.trans cosh_b29730_ub

private lemma cosh5_v_326_le : cosh (327 : ℝ) / 550 ≤ (118229676 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((327 : ℝ) / 550) (by norm_num) (by norm_num : ((327 : ℝ) / 550) ≤ ((119 : ℝ) / 200))
  exact hmono.trans cosh_b5950_ub

private lemma sech5_pt_326_ge : (784 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (327 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_326_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_326_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_327_le : cosh (164 : ℝ) / 55 ≤ (988896152 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((164 : ℝ) / 55) (by norm_num) (by norm_num : ((164 : ℝ) / 55) ≤ ((1491 : ℝ) / 500))
  exact hmono.trans cosh_b29820_ub

private lemma cosh5_v_327_le : cosh (164 : ℝ) / 275 ≤ (118324419 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((164 : ℝ) / 275) (by norm_num) (by norm_num : ((164 : ℝ) / 275) ≤ ((1193 : ℝ) / 2000))
  exact hmono.trans cosh_b5965_ub

private lemma sech5_pt_327_ge : (776 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (164 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_327_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_327_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_328_le : cosh (329 : ℝ) / 110 ≤ (997790765 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((329 : ℝ) / 110) (by norm_num) (by norm_num : ((329 : ℝ) / 110) ≤ ((2991 : ℝ) / 1000))
  exact hmono.trans cosh_b29910_ub

private lemma cosh5_v_328_le : cosh (329 : ℝ) / 550 ≤ (118451158 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((329 : ℝ) / 550) (by norm_num) (by norm_num : ((329 : ℝ) / 550) ≤ ((1197 : ℝ) / 2000))
  exact hmono.trans cosh_b5985_ub

private lemma sech5_pt_328_ge : (769 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (329 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_328_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_328_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_329_le : cosh (3 : ℝ) / 1 ≤ (1006766200 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 1) (by norm_num) (by norm_num : ((3 : ℝ) / 1) ≤ ((3 : ℝ) / 1))
  exact hmono.trans cosh_b30000_ub

private lemma cosh5_v_329_le : cosh (3 : ℝ) / 5 ≤ (118546522 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((3 : ℝ) / 5) (by norm_num) (by norm_num : ((3 : ℝ) / 5) ≤ ((3 : ℝ) / 5))
  exact hmono.trans cosh_b6000_ub

private lemma sech5_pt_329_ge : (761 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 1 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_329_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_329_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_330_le : cosh (331 : ℝ) / 110 ≤ (1016328755 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((331 : ℝ) / 110) (by norm_num) (by norm_num : ((331 : ℝ) / 110) ≤ ((6019 : ℝ) / 2000))
  exact hmono.trans cosh_b30095_ub

private lemma cosh5_v_330_le : cosh (331 : ℝ) / 550 ≤ (118674090 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((331 : ℝ) / 550) (by norm_num) (by norm_num : ((331 : ℝ) / 550) ≤ ((301 : ℝ) / 500))
  exact hmono.trans cosh_b6020_ub

private lemma sech5_pt_330_ge : (753 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (331 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_330_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_330_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_331_le : cosh (166 : ℝ) / 55 ≤ (1025472614 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((166 : ℝ) / 55) (by norm_num) (by norm_num : ((166 : ℝ) / 55) ≤ ((6037 : ℝ) / 2000))
  exact hmono.trans cosh_b30185_ub

private lemma cosh5_v_331_le : cosh (166 : ℝ) / 275 ≤ (118802133 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((166 : ℝ) / 275) (by norm_num) (by norm_num : ((166 : ℝ) / 275) ≤ ((151 : ℝ) / 250))
  exact hmono.trans cosh_b6040_ub

private lemma sech5_pt_331_ge : (746 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (166 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_331_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_331_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_332_le : cosh (333 : ℝ) / 110 ≤ (1034699536 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((333 : ℝ) / 110) (by norm_num) (by norm_num : ((333 : ℝ) / 110) ≤ ((1211 : ℝ) / 400))
  exact hmono.trans cosh_b30275_ub

private lemma cosh5_v_332_le : cosh (333 : ℝ) / 550 ≤ (118898477 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((333 : ℝ) / 550) (by norm_num) (by norm_num : ((333 : ℝ) / 550) ≤ ((1211 : ℝ) / 2000))
  exact hmono.trans cosh_b6055_ub

private lemma sech5_pt_332_ge : (738 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (333 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_332_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_332_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_333_le : cosh (167 : ℝ) / 55 ≤ (1044010270 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((167 : ℝ) / 55) (by norm_num) (by norm_num : ((167 : ℝ) / 55) ≤ ((6073 : ℝ) / 2000))
  exact hmono.trans cosh_b30365_ub

private lemma cosh5_v_333_le : cosh (167 : ℝ) / 275 ≤ (119027351 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((167 : ℝ) / 275) (by norm_num) (by norm_num : ((167 : ℝ) / 275) ≤ ((243 : ℝ) / 400))
  exact hmono.trans cosh_b6075_ub

private lemma sech5_pt_333_ge : (731 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (167 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_333_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_333_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_334_le : cosh (67 : ℝ) / 22 ≤ (1053405569 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((67 : ℝ) / 22) (by norm_num) (by norm_num : ((67 : ℝ) / 22) ≤ ((6091 : ℝ) / 2000))
  exact hmono.trans cosh_b30455_ub

private lemma cosh5_v_334_le : cosh (67 : ℝ) / 110 ≤ (119156702 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((67 : ℝ) / 110) (by norm_num) (by norm_num : ((67 : ℝ) / 110) ≤ ((1219 : ℝ) / 2000))
  exact hmono.trans cosh_b6095_ub

private lemma sech5_pt_334_ge : (724 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (67 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_334_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_334_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_335_le : cosh (168 : ℝ) / 55 ≤ (1063415413 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((168 : ℝ) / 55) (by norm_num) (by norm_num : ((168 : ℝ) / 55) ≤ ((611 : ℝ) / 200))
  exact hmono.trans cosh_b30550_ub

private lemma cosh5_v_335_le : cosh (168 : ℝ) / 275 ≤ (119254028 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((168 : ℝ) / 275) (by norm_num) (by norm_num : ((168 : ℝ) / 275) ≤ ((611 : ℝ) / 1000))
  exact hmono.trans cosh_b6110_ub

private lemma sech5_pt_335_ge : (716 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (168 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_335_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_335_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_336_le : cosh (337 : ℝ) / 110 ≤ (1072986938 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((337 : ℝ) / 110) (by norm_num) (by norm_num : ((337 : ℝ) / 110) ≤ ((383 : ℝ) / 125))
  exact hmono.trans cosh_b30640_ub

private lemma cosh5_v_336_le : cosh (337 : ℝ) / 550 ≤ (119384213 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((337 : ℝ) / 550) (by norm_num) (by norm_num : ((337 : ℝ) / 550) ≤ ((613 : ℝ) / 1000))
  exact hmono.trans cosh_b6130_ub

private lemma sech5_pt_336_ge : (709 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (337 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_336_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_336_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_337_le : cosh (169 : ℝ) / 55 ≤ (1082645376 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((169 : ℝ) / 55) (by norm_num) (by norm_num : ((169 : ℝ) / 55) ≤ ((3073 : ℝ) / 1000))
  exact hmono.trans cosh_b30730_ub

private lemma cosh5_v_337_le : cosh (169 : ℝ) / 275 ≤ (119514875 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((169 : ℝ) / 275) (by norm_num) (by norm_num : ((169 : ℝ) / 275) ≤ ((123 : ℝ) / 200))
  exact hmono.trans cosh_b6150_ub

private lemma sech5_pt_337_ge : (702 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (169 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_337_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_337_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_338_le : cosh (339 : ℝ) / 110 ≤ (1092391509 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((339 : ℝ) / 110) (by norm_num) (by norm_num : ((339 : ℝ) / 110) ≤ ((1541 : ℝ) / 500))
  exact hmono.trans cosh_b30820_ub

private lemma cosh5_v_338_le : cosh (339 : ℝ) / 550 ≤ (119613186 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((339 : ℝ) / 550) (by norm_num) (by norm_num : ((339 : ℝ) / 550) ≤ ((1233 : ℝ) / 2000))
  exact hmono.trans cosh_b6165_ub

private lemma sech5_pt_338_ge : (695 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (339 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_338_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_338_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_339_le : cosh (34 : ℝ) / 11 ≤ (1102226127 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((34 : ℝ) / 11) (by norm_num) (by norm_num : ((34 : ℝ) / 11) ≤ ((3091 : ℝ) / 1000))
  exact hmono.trans cosh_b30910_ub

private lemma cosh5_v_339_le : cosh (34 : ℝ) / 55 ≤ (119744685 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((34 : ℝ) / 55) (by norm_num) (by norm_num : ((34 : ℝ) / 55) ≤ ((1237 : ℝ) / 2000))
  exact hmono.trans cosh_b6185_ub

private lemma sech5_pt_339_ge : (688 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (34 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_339_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_339_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_340_le : cosh (31 : ℝ) / 10 ≤ (1112150025 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((31 : ℝ) / 10) (by norm_num) (by norm_num : ((31 : ℝ) / 10) ≤ ((31 : ℝ) / 10))
  exact hmono.trans cosh_b31000_ub

private lemma cosh5_v_340_le : cosh (31 : ℝ) / 50 ≤ (119843624 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((31 : ℝ) / 50) (by norm_num) (by norm_num : ((31 : ℝ) / 50) ≤ ((31 : ℝ) / 50))
  exact hmono.trans cosh_b6200_ub

private lemma sech5_pt_340_ge : (682 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_340_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_340_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_341_le : cosh (171 : ℝ) / 55 ≤ (1122722998 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((171 : ℝ) / 55) (by norm_num) (by norm_num : ((171 : ℝ) / 55) ≤ ((6219 : ℝ) / 2000))
  exact hmono.trans cosh_b31095_ub

private lemma cosh5_v_341_le : cosh (171 : ℝ) / 275 ≤ (119975963 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((171 : ℝ) / 275) (by norm_num) (by norm_num : ((171 : ℝ) / 275) ≤ ((311 : ℝ) / 500))
  exact hmono.trans cosh_b6220_ub

private lemma sech5_pt_341_ge : (674 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (171 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_341_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_341_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_342_le : cosh (343 : ℝ) / 110 ≤ (1132832950 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((343 : ℝ) / 110) (by norm_num) (by norm_num : ((343 : ℝ) / 110) ≤ ((6237 : ℝ) / 2000))
  exact hmono.trans cosh_b31185_ub

private lemma cosh5_v_342_le : cosh (343 : ℝ) / 550 ≤ (120108781 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((343 : ℝ) / 550) (by norm_num) (by norm_num : ((343 : ℝ) / 550) ≤ ((78 : ℝ) / 125))
  exact hmono.trans cosh_b6240_ub

private lemma sech5_pt_342_ge : (668 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (343 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_342_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_342_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_343_le : cosh (172 : ℝ) / 55 ≤ (1143034663 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((172 : ℝ) / 55) (by norm_num) (by norm_num : ((172 : ℝ) / 55) ≤ ((1251 : ℝ) / 400))
  exact hmono.trans cosh_b31275_ub

private lemma cosh5_v_343_le : cosh (172 : ℝ) / 275 ≤ (120208709 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((172 : ℝ) / 275) (by norm_num) (by norm_num : ((172 : ℝ) / 275) ≤ ((1251 : ℝ) / 2000))
  exact hmono.trans cosh_b6255_ub

private lemma sech5_pt_343_ge : (661 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (172 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_343_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_343_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_344_le : cosh (69 : ℝ) / 22 ≤ (1153328962 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((69 : ℝ) / 22) (by norm_num) (by norm_num : ((69 : ℝ) / 22) ≤ ((6273 : ℝ) / 2000))
  exact hmono.trans cosh_b31365_ub

private lemma cosh5_v_344_le : cosh (69 : ℝ) / 110 ≤ (120342369 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((69 : ℝ) / 110) (by norm_num) (by norm_num : ((69 : ℝ) / 110) ≤ ((251 : ℝ) / 400))
  exact hmono.trans cosh_b6275_ub

private lemma sech5_pt_344_ge : (654 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (69 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_344_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_344_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_345_le : cosh (173 : ℝ) / 55 ≤ (1163716681 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((173 : ℝ) / 55) (by norm_num) (by norm_num : ((173 : ℝ) / 55) ≤ ((6291 : ℝ) / 2000))
  exact hmono.trans cosh_b31455_ub

private lemma cosh5_v_345_le : cosh (173 : ℝ) / 275 ≤ (120476509 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((173 : ℝ) / 275) (by norm_num) (by norm_num : ((173 : ℝ) / 275) ≤ ((1259 : ℝ) / 2000))
  exact hmono.trans cosh_b6295_ub

private lemma sech5_pt_345_ge : (648 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (173 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_345_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_345_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_346_le : cosh (347 : ℝ) / 110 ≤ (1174783775 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((347 : ℝ) / 110) (by norm_num) (by norm_num : ((347 : ℝ) / 110) ≤ ((631 : ℝ) / 200))
  exact hmono.trans cosh_b31550_ub

private lemma cosh5_v_346_le : cosh (347 : ℝ) / 550 ≤ (120577431 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((347 : ℝ) / 550) (by norm_num) (by norm_num : ((347 : ℝ) / 550) ≤ ((631 : ℝ) / 1000))
  exact hmono.trans cosh_b6310_ub

private lemma sech5_pt_346_ge : (641 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (347 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_346_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_346_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_347_le : cosh (174 : ℝ) / 55 ≤ (1185366176 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((174 : ℝ) / 55) (by norm_num) (by norm_num : ((174 : ℝ) / 55) ≤ ((791 : ℝ) / 250))
  exact hmono.trans cosh_b31640_ub

private lemma cosh5_v_347_le : cosh (174 : ℝ) / 275 ≤ (120712415 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((174 : ℝ) / 275) (by norm_num) (by norm_num : ((174 : ℝ) / 275) ≤ ((633 : ℝ) / 1000))
  exact hmono.trans cosh_b6330_ub

private lemma sech5_pt_347_ge : (635 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (174 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_347_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_347_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_348_le : cosh (349 : ℝ) / 110 ≤ (1196044592 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((349 : ℝ) / 110) (by norm_num) (by norm_num : ((349 : ℝ) / 110) ≤ ((3173 : ℝ) / 1000))
  exact hmono.trans cosh_b31730_ub

private lemma cosh5_v_348_le : cosh (349 : ℝ) / 550 ≤ (120847882 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((349 : ℝ) / 550) (by norm_num) (by norm_num : ((349 : ℝ) / 550) ≤ ((127 : ℝ) / 200))
  exact hmono.trans cosh_b6350_ub

private lemma sech5_pt_348_ge : (628 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (349 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_348_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_348_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_349_le : cosh (35 : ℝ) / 11 ≤ (1206819888 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((35 : ℝ) / 11) (by norm_num) (by norm_num : ((35 : ℝ) / 11) ≤ ((1591 : ℝ) / 500))
  exact hmono.trans cosh_b31820_ub

private lemma cosh5_v_349_le : cosh (7 : ℝ) / 11 ≤ (120949799 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 11) (by norm_num) (by norm_num : ((7 : ℝ) / 11) ≤ ((1273 : ℝ) / 2000))
  exact hmono.trans cosh_b6365_ub

private lemma sech5_pt_349_ge : (622 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (35 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_349_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_349_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma sech5_batch_6_ge : (40230 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (301 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (151 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (303 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (152 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (61 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (153 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (307 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (14 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (309 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (311 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (156 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (313 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (157 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (63 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (158 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (317 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (159 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (32 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (321 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (161 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (323 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (162 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (65 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (163 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (327 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (164 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (329 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 1 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (331 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (166 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (333 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (167 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (67 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (168 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (337 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (169 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (339 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (34 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (171 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (343 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (172 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (69 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (173 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (347 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (174 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (349 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (35 : ℝ) / 11 := by
  linarith [sech5_pt_300_ge, sech5_pt_301_ge, sech5_pt_302_ge, sech5_pt_303_ge, sech5_pt_304_ge, sech5_pt_305_ge, sech5_pt_306_ge, sech5_pt_307_ge, sech5_pt_308_ge, sech5_pt_309_ge, sech5_pt_310_ge, sech5_pt_311_ge, sech5_pt_312_ge, sech5_pt_313_ge, sech5_pt_314_ge, sech5_pt_315_ge, sech5_pt_316_ge, sech5_pt_317_ge, sech5_pt_318_ge, sech5_pt_319_ge, sech5_pt_320_ge, sech5_pt_321_ge, sech5_pt_322_ge, sech5_pt_323_ge, sech5_pt_324_ge, sech5_pt_325_ge, sech5_pt_326_ge, sech5_pt_327_ge, sech5_pt_328_ge, sech5_pt_329_ge, sech5_pt_330_ge, sech5_pt_331_ge, sech5_pt_332_ge, sech5_pt_333_ge, sech5_pt_334_ge, sech5_pt_335_ge, sech5_pt_336_ge, sech5_pt_337_ge, sech5_pt_338_ge, sech5_pt_339_ge, sech5_pt_340_ge, sech5_pt_341_ge, sech5_pt_342_ge, sech5_pt_343_ge, sech5_pt_344_ge, sech5_pt_345_ge, sech5_pt_346_ge, sech5_pt_347_ge, sech5_pt_348_ge, sech5_pt_349_ge]

private lemma cosh5_u_350_le : cosh (351 : ℝ) / 110 ≤ (1217692937 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((351 : ℝ) / 110) (by norm_num) (by norm_num : ((351 : ℝ) / 110) ≤ ((3191 : ℝ) / 1000))
  exact hmono.trans cosh_b31910_ub

private lemma cosh5_v_350_le : cosh (351 : ℝ) / 550 ≤ (121086113 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((351 : ℝ) / 550) (by norm_num) (by norm_num : ((351 : ℝ) / 550) ≤ ((1277 : ℝ) / 2000))
  exact hmono.trans cosh_b6385_ub

private lemma sech5_pt_350_ge : (616 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (351 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_350_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_350_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_351_le : cosh (16 : ℝ) / 5 ≤ (1228664621 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((16 : ℝ) / 5) (by norm_num) (by norm_num : ((16 : ℝ) / 5) ≤ ((16 : ℝ) / 5))
  exact hmono.trans cosh_b32000_ub

private lemma cosh5_v_351_le : cosh (16 : ℝ) / 25 ≤ (121188666 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((16 : ℝ) / 25) (by norm_num) (by norm_num : ((16 : ℝ) / 25) ≤ ((16 : ℝ) / 25))
  exact hmono.trans cosh_b6400_ub

private lemma sech5_pt_351_ge : (610 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (16 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_351_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_351_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_352_le : cosh (353 : ℝ) / 110 ≤ (1240353829 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((353 : ℝ) / 110) (by norm_num) (by norm_num : ((353 : ℝ) / 110) ≤ ((6419 : ℝ) / 2000))
  exact hmono.trans cosh_b32095_ub

private lemma cosh5_v_352_le : cosh (353 : ℝ) / 550 ≤ (121325827 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((353 : ℝ) / 550) (by norm_num) (by norm_num : ((353 : ℝ) / 550) ≤ ((321 : ℝ) / 500))
  exact hmono.trans cosh_b6420_ub

private lemma sech5_pt_352_ge : (604 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (353 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_352_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_352_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_353_le : cosh (177 : ℝ) / 55 ≤ (1251531059 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((177 : ℝ) / 55) (by norm_num) (by norm_num : ((177 : ℝ) / 55) ≤ ((6437 : ℝ) / 2000))
  exact hmono.trans cosh_b32185_ub

private lemma cosh5_v_353_le : cosh (177 : ℝ) / 275 ≤ (121463474 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((177 : ℝ) / 275) (by norm_num) (by norm_num : ((177 : ℝ) / 275) ≤ ((161 : ℝ) / 250))
  exact hmono.trans cosh_b6440_ub

private lemma sech5_pt_353_ge : (598 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (177 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_353_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_353_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_354_le : cosh (71 : ℝ) / 22 ≤ (1262809664 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((71 : ℝ) / 22) (by norm_num) (by norm_num : ((71 : ℝ) / 22) ≤ ((1291 : ℝ) / 400))
  exact hmono.trans cosh_b32275_ub

private lemma cosh5_v_354_le : cosh (71 : ℝ) / 110 ≤ (121567027 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((71 : ℝ) / 110) (by norm_num) (by norm_num : ((71 : ℝ) / 110) ≤ ((1291 : ℝ) / 2000))
  exact hmono.trans cosh_b6455_ub

private lemma sech5_pt_354_ge : (592 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (71 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_354_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_354_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_355_le : cosh (178 : ℝ) / 55 ≤ (1274190558 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((178 : ℝ) / 55) (by norm_num) (by norm_num : ((178 : ℝ) / 55) ≤ ((6473 : ℝ) / 2000))
  exact hmono.trans cosh_b32365_ub

private lemma cosh5_v_355_le : cosh (178 : ℝ) / 275 ≤ (121705525 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((178 : ℝ) / 275) (by norm_num) (by norm_num : ((178 : ℝ) / 275) ≤ ((259 : ℝ) / 400))
  exact hmono.trans cosh_b6475_ub

private lemma sech5_pt_355_ge : (586 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (178 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_355_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_355_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_356_le : cosh (357 : ℝ) / 110 ≤ (1285674661 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((357 : ℝ) / 110) (by norm_num) (by norm_num : ((357 : ℝ) / 110) ≤ ((6491 : ℝ) / 2000))
  exact hmono.trans cosh_b32455_ub

private lemma cosh5_v_356_le : cosh (357 : ℝ) / 550 ≤ (121844509 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((357 : ℝ) / 550) (by norm_num) (by norm_num : ((357 : ℝ) / 550) ≤ ((1299 : ℝ) / 2000))
  exact hmono.trans cosh_b6495_ub

private lemma sech5_pt_356_ge : (580 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (357 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_356_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_356_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_357_le : cosh (179 : ℝ) / 55 ≤ (1297909768 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((179 : ℝ) / 55) (by norm_num) (by norm_num : ((179 : ℝ) / 55) ≤ ((651 : ℝ) / 200))
  exact hmono.trans cosh_b32550_ub

private lemma cosh5_v_357_le : cosh (179 : ℝ) / 275 ≤ (121949066 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((179 : ℝ) / 275) (by norm_num) (by norm_num : ((179 : ℝ) / 275) ≤ ((651 : ℝ) / 1000))
  exact hmono.trans cosh_b6510_ub

private lemma sech5_pt_357_ge : (574 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (179 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_357_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_357_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_358_le : cosh (359 : ℝ) / 110 ≤ (1309608956 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((359 : ℝ) / 110) (by norm_num) (by norm_num : ((359 : ℝ) / 110) ≤ ((408 : ℝ) / 125))
  exact hmono.trans cosh_b32640_ub

private lemma cosh5_v_358_le : cosh (359 : ℝ) / 550 ≤ (122088904 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((359 : ℝ) / 550) (by norm_num) (by norm_num : ((359 : ℝ) / 550) ≤ ((653 : ℝ) / 1000))
  exact hmono.trans cosh_b6530_ub

private lemma sech5_pt_358_ge : (568 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (359 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_358_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_358_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_359_le : cosh (36 : ℝ) / 11 ≤ (1321414223 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((36 : ℝ) / 11) (by norm_num) (by norm_num : ((36 : ℝ) / 11) ≤ ((3273 : ℝ) / 1000))
  exact hmono.trans cosh_b32730_ub

private lemma cosh5_v_359_le : cosh (36 : ℝ) / 55 ≤ (122229229 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((36 : ℝ) / 55) (by norm_num) (by norm_num : ((36 : ℝ) / 55) ≤ ((131 : ℝ) / 200))
  exact hmono.trans cosh_b6550_ub

private lemma sech5_pt_359_ge : (562 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (36 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_359_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_359_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_360_le : cosh (361 : ℝ) / 110 ≤ (1333326526 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((361 : ℝ) / 110) (by norm_num) (by norm_num : ((361 : ℝ) / 110) ≤ ((1641 : ℝ) / 500))
  exact hmono.trans cosh_b32820_ub

private lemma cosh5_v_360_le : cosh (361 : ℝ) / 550 ≤ (122334795 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((361 : ℝ) / 550) (by norm_num) (by norm_num : ((361 : ℝ) / 550) ≤ ((1313 : ℝ) / 2000))
  exact hmono.trans cosh_b6565_ub

private lemma sech5_pt_360_ge : (557 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (361 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_360_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_360_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_361_le : cosh (181 : ℝ) / 55 ≤ (1345346828 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((181 : ℝ) / 55) (by norm_num) (by norm_num : ((181 : ℝ) / 55) ≤ ((3291 : ℝ) / 1000))
  exact hmono.trans cosh_b32910_ub

private lemma cosh5_v_361_le : cosh (181 : ℝ) / 275 ≤ (122475976 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((181 : ℝ) / 275) (by norm_num) (by norm_num : ((181 : ℝ) / 275) ≤ ((1317 : ℝ) / 2000))
  exact hmono.trans cosh_b6585_ub

private lemma sech5_pt_361_ge : (551 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (181 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_361_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_361_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_362_le : cosh (33 : ℝ) / 10 ≤ (1357476105 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((33 : ℝ) / 10) (by norm_num) (by norm_num : ((33 : ℝ) / 10) ≤ ((33 : ℝ) / 10))
  exact hmono.trans cosh_b33000_ub

private lemma cosh5_v_362_le : cosh (33 : ℝ) / 50 ≤ (122582184 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((33 : ℝ) / 50) (by norm_num) (by norm_num : ((33 : ℝ) / 50) ≤ ((33 : ℝ) / 50))
  exact hmono.trans cosh_b6600_ub

private lemma sech5_pt_362_ge : (546 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (33 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_362_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_362_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_363_le : cosh (182 : ℝ) / 55 ≤ (1370398539 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((182 : ℝ) / 55) (by norm_num) (by norm_num : ((182 : ℝ) / 55) ≤ ((6619 : ℝ) / 2000))
  exact hmono.trans cosh_b33095_ub

private lemma cosh5_v_363_le : cosh (182 : ℝ) / 275 ≤ (122724223 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((182 : ℝ) / 275) (by norm_num) (by norm_num : ((182 : ℝ) / 275) ≤ ((331 : ℝ) / 500))
  exact hmono.trans cosh_b6620_ub

private lemma sech5_pt_363_ge : (540 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (182 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_363_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_363_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_364_le : cosh (73 : ℝ) / 22 ≤ (1382754912 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((73 : ℝ) / 22) (by norm_num) (by norm_num : ((73 : ℝ) / 22) ≤ ((6637 : ℝ) / 2000))
  exact hmono.trans cosh_b33185_ub

private lemma cosh5_v_364_le : cosh (73 : ℝ) / 110 ≤ (122866754 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((73 : ℝ) / 110) (by norm_num) (by norm_num : ((73 : ℝ) / 110) ≤ ((83 : ℝ) / 125))
  exact hmono.trans cosh_b6640_ub

private lemma sech5_pt_364_ge : (535 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (73 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_364_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_364_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_365_le : cosh (183 : ℝ) / 55 ≤ (1395223290 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((183 : ℝ) / 55) (by norm_num) (by norm_num : ((183 : ℝ) / 55) ≤ ((1331 : ℝ) / 400))
  exact hmono.trans cosh_b33275_ub

private lemma cosh5_v_365_le : cosh (183 : ℝ) / 275 ≤ (122973974 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((183 : ℝ) / 275) (by norm_num) (by norm_num : ((183 : ℝ) / 275) ≤ ((1331 : ℝ) / 2000))
  exact hmono.trans cosh_b6655_ub

private lemma sech5_pt_365_ge : (529 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (183 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_365_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_365_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_366_le : cosh (367 : ℝ) / 110 ≤ (1407804681 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((367 : ℝ) / 110) (by norm_num) (by norm_num : ((367 : ℝ) / 110) ≤ ((6673 : ℝ) / 2000))
  exact hmono.trans cosh_b33365_ub

private lemma cosh5_v_366_le : cosh (367 : ℝ) / 550 ≤ (123117364 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((367 : ℝ) / 550) (by norm_num) (by norm_num : ((367 : ℝ) / 550) ≤ ((267 : ℝ) / 400))
  exact hmono.trans cosh_b6675_ub

private lemma sech5_pt_366_ge : (524 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (367 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_366_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_366_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_367_le : cosh (184 : ℝ) / 55 ≤ (1420500105 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((184 : ℝ) / 55) (by norm_num) (by norm_num : ((184 : ℝ) / 55) ≤ ((6691 : ℝ) / 2000))
  exact hmono.trans cosh_b33455_ub

private lemma cosh5_v_367_le : cosh (184 : ℝ) / 275 ≤ (123261248 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((184 : ℝ) / 275) (by norm_num) (by norm_num : ((184 : ℝ) / 275) ≤ ((1339 : ℝ) / 2000))
  exact hmono.trans cosh_b6695_ub

private lemma sech5_pt_367_ge : (519 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (184 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_367_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_367_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_368_le : cosh (369 : ℝ) / 110 ≤ (1434025679 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((369 : ℝ) / 110) (by norm_num) (by norm_num : ((369 : ℝ) / 110) ≤ ((671 : ℝ) / 200))
  exact hmono.trans cosh_b33550_ub

private lemma cosh5_v_368_le : cosh (369 : ℝ) / 550 ≤ (123369484 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((369 : ℝ) / 550) (by norm_num) (by norm_num : ((369 : ℝ) / 550) ≤ ((671 : ℝ) / 1000))
  exact hmono.trans cosh_b6710_ub

private lemma sech5_pt_368_ge : (513 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (369 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_368_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_368_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_369_le : cosh (37 : ℝ) / 11 ≤ (1446958743 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((37 : ℝ) / 11) (by norm_num) (by norm_num : ((37 : ℝ) / 11) ≤ ((841 : ℝ) / 250))
  exact hmono.trans cosh_b33640_ub

private lemma cosh5_v_369_le : cosh (37 : ℝ) / 55 ≤ (123514230 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((37 : ℝ) / 55) (by norm_num) (by norm_num : ((37 : ℝ) / 55) ≤ ((673 : ℝ) / 1000))
  exact hmono.trans cosh_b6730_ub

private lemma sech5_pt_369_ge : (508 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_369_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_369_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_370_le : cosh (371 : ℝ) / 110 ≤ (1460009013 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((371 : ℝ) / 110) (by norm_num) (by norm_num : ((371 : ℝ) / 110) ≤ ((3373 : ℝ) / 1000))
  exact hmono.trans cosh_b33730_ub

private lemma cosh5_v_370_le : cosh (371 : ℝ) / 550 ≤ (123659470 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((371 : ℝ) / 550) (by norm_num) (by norm_num : ((371 : ℝ) / 550) ≤ ((27 : ℝ) / 40))
  exact hmono.trans cosh_b6750_ub

private lemma sech5_pt_370_ge : (503 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (371 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_370_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_370_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_371_le : cosh (186 : ℝ) / 55 ≤ (1473177544 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((186 : ℝ) / 55) (by norm_num) (by norm_num : ((186 : ℝ) / 55) ≤ ((1691 : ℝ) / 500))
  exact hmono.trans cosh_b33820_ub

private lemma cosh5_v_371_le : cosh (186 : ℝ) / 275 ≤ (123768725 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((186 : ℝ) / 275) (by norm_num) (by norm_num : ((186 : ℝ) / 275) ≤ ((1353 : ℝ) / 2000))
  exact hmono.trans cosh_b6765_ub

private lemma sech5_pt_371_ge : (498 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (186 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_371_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_371_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_372_le : cosh (373 : ℝ) / 110 ≤ (1486465403 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((373 : ℝ) / 110) (by norm_num) (by norm_num : ((373 : ℝ) / 110) ≤ ((3391 : ℝ) / 1000))
  exact hmono.trans cosh_b33910_ub

private lemma cosh5_v_372_le : cosh (373 : ℝ) / 550 ≤ (123914832 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((373 : ℝ) / 550) (by norm_num) (by norm_num : ((373 : ℝ) / 550) ≤ ((1357 : ℝ) / 2000))
  exact hmono.trans cosh_b6785_ub

private lemma sech5_pt_372_ge : (493 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (373 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_372_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_372_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_373_le : cosh (17 : ℝ) / 5 ≤ (1499873666 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((17 : ℝ) / 5) (by norm_num) (by norm_num : ((17 : ℝ) / 5) ≤ ((17 : ℝ) / 5))
  exact hmono.trans cosh_b34000_ub

private lemma cosh5_v_373_le : cosh (17 : ℝ) / 25 ≤ (124024737 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((17 : ℝ) / 25) (by norm_num) (by norm_num : ((17 : ℝ) / 25) ≤ ((17 : ℝ) / 25))
  exact hmono.trans cosh_b6800_ub

private lemma sech5_pt_373_ge : (488 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_373_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_373_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_374_le : cosh (75 : ℝ) / 22 ≤ (1514158658 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((75 : ℝ) / 22) (by norm_num) (by norm_num : ((75 : ℝ) / 22) ≤ ((6819 : ℝ) / 2000))
  exact hmono.trans cosh_b34095_ub

private lemma cosh5_v_374_le : cosh (15 : ℝ) / 22 ≤ (124171711 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((15 : ℝ) / 22) (by norm_num) (by norm_num : ((15 : ℝ) / 22) ≤ ((341 : ℝ) / 500))
  exact hmono.trans cosh_b6820_ub

private lemma sech5_pt_374_ge : (483 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (75 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_374_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_374_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_375_le : cosh (188 : ℝ) / 55 ≤ (1527817841 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((188 : ℝ) / 55) (by norm_num) (by norm_num : ((188 : ℝ) / 55) ≤ ((6837 : ℝ) / 2000))
  exact hmono.trans cosh_b34185_ub

private lemma cosh5_v_375_le : cosh (188 : ℝ) / 275 ≤ (124319182 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((188 : ℝ) / 275) (by norm_num) (by norm_num : ((188 : ℝ) / 275) ≤ ((171 : ℝ) / 250))
  exact hmono.trans cosh_b6840_ub

private lemma sech5_pt_375_ge : (478 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (188 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_375_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_375_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_376_le : cosh (377 : ℝ) / 110 ≤ (1541600779 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((377 : ℝ) / 110) (by norm_num) (by norm_num : ((377 : ℝ) / 110) ≤ ((1371 : ℝ) / 400))
  exact hmono.trans cosh_b34275_ub

private lemma cosh5_v_376_le : cosh (377 : ℝ) / 550 ≤ (124430111 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((377 : ℝ) / 550) (by norm_num) (by norm_num : ((377 : ℝ) / 550) ≤ ((1371 : ℝ) / 2000))
  exact hmono.trans cosh_b6855_ub

private lemma sech5_pt_376_ge : (473 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (377 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_376_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_376_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_377_le : cosh (189 : ℝ) / 55 ≤ (1555508587 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((189 : ℝ) / 55) (by norm_num) (by norm_num : ((189 : ℝ) / 55) ≤ ((6873 : ℝ) / 2000))
  exact hmono.trans cosh_b34365_ub

private lemma cosh5_v_377_le : cosh (189 : ℝ) / 275 ≤ (124578453 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((189 : ℝ) / 275) (by norm_num) (by norm_num : ((189 : ℝ) / 275) ≤ ((11 : ℝ) / 16))
  exact hmono.trans cosh_b6875_ub

private lemma sech5_pt_377_ge : (469 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (189 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_377_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_377_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_378_le : cosh (379 : ℝ) / 110 ≤ (1569542392 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((379 : ℝ) / 110) (by norm_num) (by norm_num : ((379 : ℝ) / 110) ≤ ((6891 : ℝ) / 2000))
  exact hmono.trans cosh_b34455_ub

private lemma cosh5_v_378_le : cosh (379 : ℝ) / 550 ≤ (124727293 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((379 : ℝ) / 550) (by norm_num) (by norm_num : ((379 : ℝ) / 550) ≤ ((1379 : ℝ) / 2000))
  exact hmono.trans cosh_b6895_ub

private lemma sech5_pt_378_ge : (464 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (379 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_378_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_378_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_379_le : cosh (38 : ℝ) / 11 ≤ (1584493800 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((38 : ℝ) / 11) (by norm_num) (by norm_num : ((38 : ℝ) / 11) ≤ ((691 : ℝ) / 200))
  exact hmono.trans cosh_b34550_ub

private lemma cosh5_v_379_le : cosh (38 : ℝ) / 55 ≤ (124839250 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((38 : ℝ) / 55) (by norm_num) (by norm_num : ((38 : ℝ) / 55) ≤ ((691 : ℝ) / 1000))
  exact hmono.trans cosh_b6910_ub

private lemma sech5_pt_379_ge : (459 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (38 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_379_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_379_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_380_le : cosh (381 : ℝ) / 110 ≤ (1598790180 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((381 : ℝ) / 110) (by norm_num) (by norm_num : ((381 : ℝ) / 110) ≤ ((433 : ℝ) / 125))
  exact hmono.trans cosh_b34640_ub

private lemma cosh5_v_380_le : cosh (381 : ℝ) / 550 ≤ (124988963 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((381 : ℝ) / 550) (by norm_num) (by norm_num : ((381 : ℝ) / 550) ≤ ((693 : ℝ) / 1000))
  exact hmono.trans cosh_b6930_ub

private lemma sech5_pt_380_ge : (454 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (381 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_380_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_380_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_381_le : cosh (191 : ℝ) / 55 ≤ (1613216063 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((191 : ℝ) / 55) (by norm_num) (by norm_num : ((191 : ℝ) / 55) ≤ ((3473 : ℝ) / 1000))
  exact hmono.trans cosh_b34730_ub

private lemma cosh5_v_381_le : cosh (191 : ℝ) / 275 ≤ (125139177 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((191 : ℝ) / 275) (by norm_num) (by norm_num : ((191 : ℝ) / 275) ≤ ((139 : ℝ) / 200))
  exact hmono.trans cosh_b6950_ub

private lemma sech5_pt_381_ge : (450 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (191 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_381_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_381_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_382_le : cosh (383 : ℝ) / 110 ≤ (1627772618 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((383 : ℝ) / 110) (by norm_num) (by norm_num : ((383 : ℝ) / 110) ≤ ((1741 : ℝ) / 500))
  exact hmono.trans cosh_b34820_ub

private lemma cosh5_v_382_le : cosh (383 : ℝ) / 550 ≤ (125252165 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((383 : ℝ) / 550) (by norm_num) (by norm_num : ((383 : ℝ) / 550) ≤ ((1393 : ℝ) / 2000))
  exact hmono.trans cosh_b6965_ub

private lemma sech5_pt_382_ge : (445 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (383 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_382_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_382_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_383_le : cosh (192 : ℝ) / 55 ≤ (1642461022 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((192 : ℝ) / 55) (by norm_num) (by norm_num : ((192 : ℝ) / 55) ≤ ((3491 : ℝ) / 1000))
  exact hmono.trans cosh_b34910_ub

private lemma cosh5_v_383_le : cosh (192 : ℝ) / 275 ≤ (125403255 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((192 : ℝ) / 275) (by norm_num) (by norm_num : ((192 : ℝ) / 275) ≤ ((1397 : ℝ) / 2000))
  exact hmono.trans cosh_b6985_ub

private lemma sech5_pt_383_ge : (441 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (192 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_383_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_383_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_384_le : cosh (7 : ℝ) / 2 ≤ (1657282468 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 2) (by norm_num) (by norm_num : ((7 : ℝ) / 2) ≤ ((7 : ℝ) / 2))
  exact hmono.trans cosh_b35000_ub

private lemma cosh5_v_384_le : cosh (7 : ℝ) / 10 ≤ (125516901 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((7 : ℝ) / 10) (by norm_num) (by norm_num : ((7 : ℝ) / 10) ≤ ((7 : ℝ) / 10))
  exact hmono.trans cosh_b7000_ub

private lemma sech5_pt_384_ge : (437 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 2 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_384_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_384_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_385_le : cosh (193 : ℝ) / 55 ≤ (1673072985 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((193 : ℝ) / 55) (by norm_num) (by norm_num : ((193 : ℝ) / 55) ≤ ((7019 : ℝ) / 2000))
  exact hmono.trans cosh_b35095_ub

private lemma cosh5_v_385_le : cosh (193 : ℝ) / 275 ≤ (125668869 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((193 : ℝ) / 275) (by norm_num) (by norm_num : ((193 : ℝ) / 275) ≤ ((351 : ℝ) / 500))
  exact hmono.trans cosh_b7020_ub

private lemma sech5_pt_385_ge : (432 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (193 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_385_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_385_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_386_le : cosh (387 : ℝ) / 110 ≤ (1688171684 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((387 : ℝ) / 110) (by norm_num) (by norm_num : ((387 : ℝ) / 110) ≤ ((7037 : ℝ) / 2000))
  exact hmono.trans cosh_b35185_ub

private lemma cosh5_v_386_le : cosh (387 : ℝ) / 550 ≤ (125821339 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((387 : ℝ) / 550) (by norm_num) (by norm_num : ((387 : ℝ) / 550) ≤ ((88 : ℝ) / 125))
  exact hmono.trans cosh_b7040_ub

private lemma sech5_pt_386_ge : (427 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (387 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_386_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_386_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_387_le : cosh (194 : ℝ) / 55 ≤ (1703407126 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((194 : ℝ) / 55) (by norm_num) (by norm_num : ((194 : ℝ) / 55) ≤ ((1411 : ℝ) / 400))
  exact hmono.trans cosh_b35275_ub

private lemma cosh5_v_387_le : cosh (194 : ℝ) / 275 ≤ (125936023 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((194 : ℝ) / 275) (by norm_num) (by norm_num : ((194 : ℝ) / 275) ≤ ((1411 : ℝ) / 2000))
  exact hmono.trans cosh_b7055_ub

private lemma sech5_pt_387_ge : (423 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (194 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_387_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_387_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_388_le : cosh (389 : ℝ) / 110 ≤ (1718780545 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((389 : ℝ) / 110) (by norm_num) (by norm_num : ((389 : ℝ) / 110) ≤ ((7073 : ℝ) / 2000))
  exact hmono.trans cosh_b35365_ub

private lemma cosh5_v_388_le : cosh (389 : ℝ) / 550 ≤ (126089374 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((389 : ℝ) / 550) (by norm_num) (by norm_num : ((389 : ℝ) / 550) ≤ ((283 : ℝ) / 400))
  exact hmono.trans cosh_b7075_ub

private lemma sech5_pt_388_ge : (419 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (389 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_388_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_388_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_389_le : cosh (39 : ℝ) / 11 ≤ (1734293186 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((39 : ℝ) / 11) (by norm_num) (by norm_num : ((39 : ℝ) / 11) ≤ ((7091 : ℝ) / 2000))
  exact hmono.trans cosh_b35455_ub

private lemma cosh5_v_389_le : cosh (39 : ℝ) / 55 ≤ (126243230 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((39 : ℝ) / 55) (by norm_num) (by norm_num : ((39 : ℝ) / 55) ≤ ((1419 : ℝ) / 2000))
  exact hmono.trans cosh_b7095_ub

private lemma sech5_pt_389_ge : (415 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_389_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_389_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_390_le : cosh (391 : ℝ) / 110 ≤ (1750820068 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((391 : ℝ) / 110) (by norm_num) (by norm_num : ((391 : ℝ) / 110) ≤ ((711 : ℝ) / 200))
  exact hmono.trans cosh_b35550_ub

private lemma cosh5_v_390_le : cosh (391 : ℝ) / 550 ≤ (126358954 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((391 : ℝ) / 550) (by norm_num) (by norm_num : ((391 : ℝ) / 550) ≤ ((711 : ℝ) / 1000))
  exact hmono.trans cosh_b7110_ub

private lemma sech5_pt_390_ge : (410 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (391 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_390_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_390_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_391_le : cosh (196 : ℝ) / 55 ≤ (1766622846 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((196 : ℝ) / 55) (by norm_num) (by norm_num : ((196 : ℝ) / 55) ≤ ((891 : ℝ) / 250))
  exact hmono.trans cosh_b35640_ub

private lemma cosh5_v_391_le : cosh (196 : ℝ) / 275 ≤ (126513694 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((196 : ℝ) / 275) (by norm_num) (by norm_num : ((196 : ℝ) / 275) ≤ ((713 : ℝ) / 1000))
  exact hmono.trans cosh_b7130_ub

private lemma sech5_pt_391_ge : (406 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (196 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_391_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_391_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_392_le : cosh (393 : ℝ) / 110 ≤ (1782568722 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((393 : ℝ) / 110) (by norm_num) (by norm_num : ((393 : ℝ) / 110) ≤ ((3573 : ℝ) / 1000))
  exact hmono.trans cosh_b35730_ub

private lemma cosh5_v_392_le : cosh (393 : ℝ) / 550 ≤ (126668940 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((393 : ℝ) / 550) (by norm_num) (by norm_num : ((393 : ℝ) / 550) ≤ ((143 : ℝ) / 200))
  exact hmono.trans cosh_b7150_ub

private lemma sech5_pt_392_ge : (402 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (393 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_392_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_392_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_393_le : cosh (197 : ℝ) / 55 ≤ (1798658987 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((197 : ℝ) / 55) (by norm_num) (by norm_num : ((197 : ℝ) / 55) ≤ ((1791 : ℝ) / 500))
  exact hmono.trans cosh_b35820_ub

private lemma cosh5_v_393_le : cosh (197 : ℝ) / 275 ≤ (126785707 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((197 : ℝ) / 275) (by norm_num) (by norm_num : ((197 : ℝ) / 275) ≤ ((1433 : ℝ) / 2000))
  exact hmono.trans cosh_b7165_ub

private lemma sech5_pt_393_ge : (398 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (197 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_393_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_393_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_394_le : cosh (79 : ℝ) / 22 ≤ (1814894944 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((79 : ℝ) / 22) (by norm_num) (by norm_num : ((79 : ℝ) / 22) ≤ ((3591 : ℝ) / 1000))
  exact hmono.trans cosh_b35910_ub

private lemma cosh5_v_394_le : cosh (79 : ℝ) / 110 ≤ (126941841 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((79 : ℝ) / 110) (by norm_num) (by norm_num : ((79 : ℝ) / 110) ≤ ((1437 : ℝ) / 2000))
  exact hmono.trans cosh_b7185_ub

private lemma sech5_pt_394_ge : (394 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (79 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_394_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_394_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_395_le : cosh (18 : ℝ) / 5 ≤ (1831277909 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((18 : ℝ) / 5) (by norm_num) (by norm_num : ((18 : ℝ) / 5) ≤ ((18 : ℝ) / 5))
  exact hmono.trans cosh_b36000_ub

private lemma cosh5_v_395_le : cosh (18 : ℝ) / 25 ≤ (127059274 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((18 : ℝ) / 25) (by norm_num) (by norm_num : ((18 : ℝ) / 25) ≤ ((18 : ℝ) / 25))
  exact hmono.trans cosh_b7200_ub

private lemma sech5_pt_395_ge : (390 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (18 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_395_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_395_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_396_le : cosh (397 : ℝ) / 110 ≤ (1848731990 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((397 : ℝ) / 110) (by norm_num) (by norm_num : ((397 : ℝ) / 110) ≤ ((7219 : ℝ) / 2000))
  exact hmono.trans cosh_b36095_ub

private lemma cosh5_v_396_le : cosh (397 : ℝ) / 550 ≤ (127216296 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((397 : ℝ) / 550) (by norm_num) (by norm_num : ((397 : ℝ) / 550) ≤ ((361 : ℝ) / 500))
  exact hmono.trans cosh_b7220_ub

private lemma sech5_pt_396_ge : (386 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (397 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_396_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_396_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_397_le : cosh (199 : ℝ) / 55 ≤ (1865421317 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((199 : ℝ) / 55) (by norm_num) (by norm_num : ((199 : ℝ) / 55) ≤ ((7237 : ℝ) / 2000))
  exact hmono.trans cosh_b36185_ub

private lemma cosh5_v_397_le : cosh (199 : ℝ) / 275 ≤ (127373827 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((199 : ℝ) / 275) (by norm_num) (by norm_num : ((199 : ℝ) / 275) ≤ ((181 : ℝ) / 250))
  exact hmono.trans cosh_b7240_ub

private lemma sech5_pt_397_ge : (382 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (199 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_397_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_397_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_398_le : cosh (399 : ℝ) / 110 ≤ (1882261745 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((399 : ℝ) / 110) (by norm_num) (by norm_num : ((399 : ℝ) / 110) ≤ ((1451 : ℝ) / 400))
  exact hmono.trans cosh_b36275_ub

private lemma cosh5_v_398_le : cosh (399 : ℝ) / 550 ≤ (127492310 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((399 : ℝ) / 550) (by norm_num) (by norm_num : ((399 : ℝ) / 550) ≤ ((1451 : ℝ) / 2000))
  exact hmono.trans cosh_b7255_ub

private lemma sech5_pt_398_ge : (378 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (399 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_398_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_398_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_399_le : cosh (40 : ℝ) / 11 ≤ (1899254637 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((40 : ℝ) / 11) (by norm_num) (by norm_num : ((40 : ℝ) / 11) ≤ ((7273 : ℝ) / 2000))
  exact hmono.trans cosh_b36365_ub

private lemma cosh5_v_399_le : cosh (8 : ℝ) / 11 ≤ (127650733 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((8 : ℝ) / 11) (by norm_num) (by norm_num : ((8 : ℝ) / 11) ≤ ((291 : ℝ) / 400))
  exact hmono.trans cosh_b7275_ub

private lemma sech5_pt_399_ge : (374 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (40 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_399_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_399_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma sech5_batch_7_ge : (24309 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (351 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (16 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (353 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (177 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (71 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (178 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (357 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (179 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (359 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (36 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (361 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (181 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (33 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (182 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (73 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (183 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (367 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (184 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (369 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (371 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (186 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (373 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (75 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (188 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (377 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (189 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (379 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (38 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (381 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (191 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (383 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (192 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 2 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (193 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (387 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (194 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (389 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (391 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (196 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (393 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (197 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (79 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (18 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (397 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (199 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (399 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (40 : ℝ) / 11 := by
  linarith [sech5_pt_350_ge, sech5_pt_351_ge, sech5_pt_352_ge, sech5_pt_353_ge, sech5_pt_354_ge, sech5_pt_355_ge, sech5_pt_356_ge, sech5_pt_357_ge, sech5_pt_358_ge, sech5_pt_359_ge, sech5_pt_360_ge, sech5_pt_361_ge, sech5_pt_362_ge, sech5_pt_363_ge, sech5_pt_364_ge, sech5_pt_365_ge, sech5_pt_366_ge, sech5_pt_367_ge, sech5_pt_368_ge, sech5_pt_369_ge, sech5_pt_370_ge, sech5_pt_371_ge, sech5_pt_372_ge, sech5_pt_373_ge, sech5_pt_374_ge, sech5_pt_375_ge, sech5_pt_376_ge, sech5_pt_377_ge, sech5_pt_378_ge, sech5_pt_379_ge, sech5_pt_380_ge, sech5_pt_381_ge, sech5_pt_382_ge, sech5_pt_383_ge, sech5_pt_384_ge, sech5_pt_385_ge, sech5_pt_386_ge, sech5_pt_387_ge, sech5_pt_388_ge, sech5_pt_389_ge, sech5_pt_390_ge, sech5_pt_391_ge, sech5_pt_392_ge, sech5_pt_393_ge, sech5_pt_394_ge, sech5_pt_395_ge, sech5_pt_396_ge, sech5_pt_397_ge, sech5_pt_398_ge, sech5_pt_399_ge]

private lemma cosh5_u_400_le : cosh (401 : ℝ) / 110 ≤ (1916401369 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((401 : ℝ) / 110) (by norm_num) (by norm_num : ((401 : ℝ) / 110) ≤ ((7291 : ℝ) / 2000))
  exact hmono.trans cosh_b36455_ub

private lemma cosh5_v_400_le : cosh (401 : ℝ) / 550 ≤ (127809667 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((401 : ℝ) / 550) (by norm_num) (by norm_num : ((401 : ℝ) / 550) ≤ ((1459 : ℝ) / 2000))
  exact hmono.trans cosh_b7295_ub

private lemma sech5_pt_400_ge : (371 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (401 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_400_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_400_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_401_le : cosh (201 : ℝ) / 55 ≤ (1934669131 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((201 : ℝ) / 55) (by norm_num) (by norm_num : ((201 : ℝ) / 55) ≤ ((731 : ℝ) / 200))
  exact hmono.trans cosh_b36550_ub

private lemma cosh5_v_401_le : cosh (201 : ℝ) / 275 ≤ (127929203 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((201 : ℝ) / 275) (by norm_num) (by norm_num : ((201 : ℝ) / 275) ≤ ((731 : ℝ) / 1000))
  exact hmono.trans cosh_b7310_ub

private lemma sech5_pt_401_ge : (367 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (201 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_401_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_401_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_402_le : cosh (403 : ℝ) / 110 ≤ (1952136467 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((403 : ℝ) / 110) (by norm_num) (by norm_num : ((403 : ℝ) / 110) ≤ ((458 : ℝ) / 125))
  exact hmono.trans cosh_b36640_ub

private lemma cosh5_v_402_le : cosh (403 : ℝ) / 550 ≤ (128089032 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((403 : ℝ) / 550) (by norm_num) (by norm_num : ((403 : ℝ) / 550) ≤ ((733 : ℝ) / 1000))
  exact hmono.trans cosh_b7330_ub

private lemma sech5_pt_402_ge : (363 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (403 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_402_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_402_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_403_le : cosh (202 : ℝ) / 55 ≤ (1969761928 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((202 : ℝ) / 55) (by norm_num) (by norm_num : ((202 : ℝ) / 55) ≤ ((3673 : ℝ) / 1000))
  exact hmono.trans cosh_b36730_ub

private lemma cosh5_v_403_le : cosh (202 : ℝ) / 275 ≤ (128249373 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((202 : ℝ) / 275) (by norm_num) (by norm_num : ((202 : ℝ) / 275) ≤ ((147 : ℝ) / 200))
  exact hmono.trans cosh_b7350_ub

private lemma sech5_pt_403_ge : (359 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (202 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_403_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_403_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_404_le : cosh (81 : ℝ) / 22 ≤ (1987546940 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((81 : ℝ) / 22) (by norm_num) (by norm_num : ((81 : ℝ) / 22) ≤ ((1841 : ℝ) / 500))
  exact hmono.trans cosh_b36820_ub

private lemma cosh5_v_404_le : cosh (81 : ℝ) / 110 ≤ (128369966 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((81 : ℝ) / 110) (by norm_num) (by norm_num : ((81 : ℝ) / 110) ≤ ((1473 : ℝ) / 2000))
  exact hmono.trans cosh_b7365_ub

private lemma sech5_pt_404_ge : (356 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (81 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_404_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_404_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_405_le : cosh (203 : ℝ) / 55 ≤ (2005492944 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((203 : ℝ) / 55) (by norm_num) (by norm_num : ((203 : ℝ) / 55) ≤ ((3691 : ℝ) / 1000))
  exact hmono.trans cosh_b36910_ub

private lemma cosh5_v_405_le : cosh (203 : ℝ) / 275 ≤ (128531205 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((203 : ℝ) / 275) (by norm_num) (by norm_num : ((203 : ℝ) / 275) ≤ ((1477 : ℝ) / 2000))
  exact hmono.trans cosh_b7385_ub

private lemma sech5_pt_405_ge : (352 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (203 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_405_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_405_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_406_le : cosh (37 : ℝ) / 10 ≤ (2023601395 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((37 : ℝ) / 10) (by norm_num) (by norm_num : ((37 : ℝ) / 10) ≤ ((37 : ℝ) / 10))
  exact hmono.trans cosh_b37000_ub

private lemma cosh5_v_406_le : cosh (37 : ℝ) / 50 ≤ (128652472 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((37 : ℝ) / 50) (by norm_num) (by norm_num : ((37 : ℝ) / 50) ≤ ((37 : ℝ) / 50))
  exact hmono.trans cosh_b7400_ub

private lemma sech5_pt_406_ge : (349 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_406_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_406_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_407_le : cosh (204 : ℝ) / 55 ≤ (2042893725 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((204 : ℝ) / 55) (by norm_num) (by norm_num : ((204 : ℝ) / 55) ≤ ((7419 : ℝ) / 2000))
  exact hmono.trans cosh_b37095_ub

private lemma cosh5_v_407_le : cosh (204 : ℝ) / 275 ≤ (128814612 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((204 : ℝ) / 275) (by norm_num) (by norm_num : ((204 : ℝ) / 275) ≤ ((371 : ℝ) / 500))
  exact hmono.trans cosh_b7420_ub

private lemma sech5_pt_407_ge : (345 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (204 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_407_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_407_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_408_le : cosh (409 : ℝ) / 110 ≤ (2061340714 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((409 : ℝ) / 110) (by norm_num) (by norm_num : ((409 : ℝ) / 110) ≤ ((7437 : ℝ) / 2000))
  exact hmono.trans cosh_b37185_ub

private lemma cosh5_v_408_le : cosh (409 : ℝ) / 550 ≤ (128977266 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((409 : ℝ) / 550) (by norm_num) (by norm_num : ((409 : ℝ) / 550) ≤ ((93 : ℝ) / 125))
  exact hmono.trans cosh_b7440_ub

private lemma sech5_pt_408_ge : (341 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (409 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_408_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_408_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_409_le : cosh (41 : ℝ) / 11 ≤ (2079954672 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((41 : ℝ) / 11) (by norm_num) (by norm_num : ((41 : ℝ) / 11) ≤ ((1491 : ℝ) / 400))
  exact hmono.trans cosh_b37275_ub

private lemma cosh5_v_409_le : cosh (41 : ℝ) / 55 ≤ (129099596 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((41 : ℝ) / 55) (by norm_num) (by norm_num : ((41 : ℝ) / 55) ≤ ((1491 : ℝ) / 2000))
  exact hmono.trans cosh_b7455_ub

private lemma sech5_pt_409_ge : (338 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_409_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_409_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_410_le : cosh (411 : ℝ) / 110 ≤ (2098737107 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((411 : ℝ) / 110) (by norm_num) (by norm_num : ((411 : ℝ) / 110) ≤ ((7473 : ℝ) / 2000))
  exact hmono.trans cosh_b37365_ub

private lemma cosh5_v_410_le : cosh (411 : ℝ) / 550 ≤ (129263154 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((411 : ℝ) / 550) (by norm_num) (by norm_num : ((411 : ℝ) / 550) ≤ ((299 : ℝ) / 400))
  exact hmono.trans cosh_b7475_ub

private lemma sech5_pt_410_ge : (335 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (411 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_410_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_410_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_411_le : cosh (206 : ℝ) / 55 ≤ (2117689542 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((206 : ℝ) / 55) (by norm_num) (by norm_num : ((206 : ℝ) / 55) ≤ ((7491 : ℝ) / 2000))
  exact hmono.trans cosh_b37455_ub

private lemma cosh5_v_411_le : cosh (206 : ℝ) / 275 ≤ (129427229 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((206 : ℝ) / 275) (by norm_num) (by norm_num : ((206 : ℝ) / 275) ≤ ((1499 : ℝ) / 2000))
  exact hmono.trans cosh_b7495_ub

private lemma sech5_pt_411_ge : (331 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (206 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_411_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_411_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_412_le : cosh (413 : ℝ) / 110 ≤ (2137881014 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((413 : ℝ) / 110) (by norm_num) (by norm_num : ((413 : ℝ) / 110) ≤ ((751 : ℝ) / 200))
  exact hmono.trans cosh_b37550_ub

private lemma cosh5_v_412_le : cosh (413 : ℝ) / 550 ≤ (129550625 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((413 : ℝ) / 550) (by norm_num) (by norm_num : ((413 : ℝ) / 550) ≤ ((751 : ℝ) / 1000))
  exact hmono.trans cosh_b7510_ub

private lemma sech5_pt_412_ge : (328 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (413 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_412_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_412_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_413_le : cosh (207 : ℝ) / 55 ≤ (2157187727 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((207 : ℝ) / 55) (by norm_num) (by norm_num : ((207 : ℝ) / 55) ≤ ((941 : ℝ) / 250))
  exact hmono.trans cosh_b37640_ub

private lemma cosh5_v_413_le : cosh (207 : ℝ) / 275 ≤ (129715607 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((207 : ℝ) / 275) (by norm_num) (by norm_num : ((207 : ℝ) / 275) ≤ ((753 : ℝ) / 1000))
  exact hmono.trans cosh_b7530_ub

private lemma sech5_pt_413_ge : (324 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (207 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_413_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_413_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_414_le : cosh (83 : ℝ) / 22 ≤ (2176669173 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((83 : ℝ) / 22) (by norm_num) (by norm_num : ((83 : ℝ) / 22) ≤ ((3773 : ℝ) / 1000))
  exact hmono.trans cosh_b37730_ub

private lemma cosh5_v_414_le : cosh (83 : ℝ) / 110 ≤ (129881107 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((83 : ℝ) / 110) (by norm_num) (by norm_num : ((83 : ℝ) / 110) ≤ ((151 : ℝ) / 200))
  exact hmono.trans cosh_b7550_ub

private lemma sech5_pt_414_ge : (321 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (83 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_414_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_414_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_415_le : cosh (208 : ℝ) / 55 ≤ (2196326931 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((208 : ℝ) / 55) (by norm_num) (by norm_num : ((208 : ℝ) / 55) ≤ ((1891 : ℝ) / 500))
  exact hmono.trans cosh_b37820_ub

private lemma cosh5_v_415_le : cosh (208 : ℝ) / 275 ≤ (130005574 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((208 : ℝ) / 275) (by norm_num) (by norm_num : ((208 : ℝ) / 275) ≤ ((1513 : ℝ) / 2000))
  exact hmono.trans cosh_b7565_ub

private lemma sech5_pt_415_ge : (318 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (208 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_415_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_415_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_416_le : cosh (417 : ℝ) / 110 ≤ (2216162592 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((417 : ℝ) / 110) (by norm_num) (by norm_num : ((417 : ℝ) / 110) ≤ ((3791 : ℝ) / 1000))
  exact hmono.trans cosh_b37910_ub

private lemma cosh5_v_416_le : cosh (417 : ℝ) / 550 ≤ (130171984 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((417 : ℝ) / 550) (by norm_num) (by norm_num : ((417 : ℝ) / 550) ≤ ((1517 : ℝ) / 2000))
  exact hmono.trans cosh_b7585_ub

private lemma sech5_pt_416_ge : (315 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (417 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_416_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_416_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_417_le : cosh (19 : ℝ) / 5 ≤ (2236177764 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((19 : ℝ) / 5) (by norm_num) (by norm_num : ((19 : ℝ) / 5) ≤ ((19 : ℝ) / 5))
  exact hmono.trans cosh_b38000_ub

private lemma cosh5_v_417_le : cosh (19 : ℝ) / 25 ≤ (130297133 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((19 : ℝ) / 25) (by norm_num) (by norm_num : ((19 : ℝ) / 25) ≤ ((19 : ℝ) / 25))
  exact hmono.trans cosh_b7600_ub

private lemma sech5_pt_417_ge : (312 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_417_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_417_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_418_le : cosh (419 : ℝ) / 110 ≤ (2257501428 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((419 : ℝ) / 110) (by norm_num) (by norm_num : ((419 : ℝ) / 110) ≤ ((7619 : ℝ) / 2000))
  exact hmono.trans cosh_b38095_ub

private lemma cosh5_v_418_le : cosh (419 : ℝ) / 550 ≤ (130464455 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((419 : ℝ) / 550) (by norm_num) (by norm_num : ((419 : ℝ) / 550) ≤ ((381 : ℝ) / 500))
  exact hmono.trans cosh_b7620_ub

private lemma sech5_pt_418_ge : (308 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (419 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_418_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_418_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_419_le : cosh (42 : ℝ) / 11 ≤ (2277890701 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((42 : ℝ) / 11) (by norm_num) (by norm_num : ((42 : ℝ) / 11) ≤ ((7637 : ℝ) / 2000))
  exact hmono.trans cosh_b38185_ub

private lemma cosh5_v_419_le : cosh (42 : ℝ) / 55 ≤ (130632298 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((42 : ℝ) / 55) (by norm_num) (by norm_num : ((42 : ℝ) / 55) ≤ ((191 : ℝ) / 250))
  exact hmono.trans cosh_b7640_ub

private lemma sech5_pt_419_ge : (305 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (42 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_419_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_419_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_420_le : cosh (421 : ℝ) / 110 ≤ (2298464484 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((421 : ℝ) / 110) (by norm_num) (by norm_num : ((421 : ℝ) / 110) ≤ ((1531 : ℝ) / 400))
  exact hmono.trans cosh_b38275_ub

private lemma cosh5_v_420_le : cosh (421 : ℝ) / 550 ≤ (130758524 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((421 : ℝ) / 550) (by norm_num) (by norm_num : ((421 : ℝ) / 550) ≤ ((1531 : ℝ) / 2000))
  exact hmono.trans cosh_b7655_ub

private lemma sech5_pt_420_ge : (302 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (421 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_420_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_420_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_421_le : cosh (211 : ℝ) / 55 ≤ (2319224444 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((211 : ℝ) / 55) (by norm_num) (by norm_num : ((211 : ℝ) / 55) ≤ ((7673 : ℝ) / 2000))
  exact hmono.trans cosh_b38365_ub

private lemma cosh5_v_421_le : cosh (211 : ℝ) / 275 ≤ (130927282 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((211 : ℝ) / 275) (by norm_num) (by norm_num : ((211 : ℝ) / 275) ≤ ((307 : ℝ) / 400))
  exact hmono.trans cosh_b7675_ub

private lemma sech5_pt_421_ge : (299 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (211 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_421_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_421_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_422_le : cosh (423 : ℝ) / 110 ≤ (2340172263 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((423 : ℝ) / 110) (by norm_num) (by norm_num : ((423 : ℝ) / 110) ≤ ((7691 : ℝ) / 2000))
  exact hmono.trans cosh_b38455_ub

private lemma cosh5_v_422_le : cosh (423 : ℝ) / 550 ≤ (131096564 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((423 : ℝ) / 550) (by norm_num) (by norm_num : ((423 : ℝ) / 550) ≤ ((1539 : ℝ) / 2000))
  exact hmono.trans cosh_b7695_ub

private lemma sech5_pt_422_ge : (296 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (423 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_422_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_422_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_423_le : cosh (212 : ℝ) / 55 ≤ (2362489528 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((212 : ℝ) / 55) (by norm_num) (by norm_num : ((212 : ℝ) / 55) ≤ ((771 : ℝ) / 200))
  exact hmono.trans cosh_b38550_ub

private lemma cosh5_v_423_le : cosh (212 : ℝ) / 275 ≤ (131223870 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((212 : ℝ) / 275) (by norm_num) (by norm_num : ((212 : ℝ) / 275) ≤ ((771 : ℝ) / 1000))
  exact hmono.trans cosh_b7710_ub

private lemma sech5_pt_423_ge : (293 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (212 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_423_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_423_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_424_le : cosh (85 : ℝ) / 22 ≤ (2383828845 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((85 : ℝ) / 22) (by norm_num) (by norm_num : ((85 : ℝ) / 22) ≤ ((483 : ℝ) / 125))
  exact hmono.trans cosh_b38640_ub

private lemma cosh5_v_424_le : cosh (17 : ℝ) / 22 ≤ (131394070 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((17 : ℝ) / 22) (by norm_num) (by norm_num : ((17 : ℝ) / 22) ≤ ((773 : ℝ) / 1000))
  exact hmono.trans cosh_b7730_ub

private lemma sech5_pt_424_ge : (290 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (85 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_424_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_424_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_425_le : cosh (213 : ℝ) / 55 ≤ (2405361255 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((213 : ℝ) / 55) (by norm_num) (by norm_num : ((213 : ℝ) / 55) ≤ ((3873 : ℝ) / 1000))
  exact hmono.trans cosh_b38730_ub

private lemma cosh5_v_425_le : cosh (213 : ℝ) / 275 ≤ (131564796 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((213 : ℝ) / 275) (by norm_num) (by norm_num : ((213 : ℝ) / 275) ≤ ((31 : ℝ) / 40))
  exact hmono.trans cosh_b7750_ub

private lemma sech5_pt_425_ge : (287 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (213 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_425_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_425_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_426_le : cosh (427 : ℝ) / 110 ≤ (2427088499 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((427 : ℝ) / 110) (by norm_num) (by norm_num : ((427 : ℝ) / 110) ≤ ((1941 : ℝ) / 500))
  exact hmono.trans cosh_b38820_ub

private lemma cosh5_v_426_le : cosh (427 : ℝ) / 550 ≤ (131693186 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((427 : ℝ) / 550) (by norm_num) (by norm_num : ((427 : ℝ) / 550) ≤ ((1553 : ℝ) / 2000))
  exact hmono.trans cosh_b7765_ub

private lemma sech5_pt_426_ge : (284 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (427 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_426_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_426_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_427_le : cosh (214 : ℝ) / 55 ≤ (2449012340 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((214 : ℝ) / 55) (by norm_num) (by norm_num : ((214 : ℝ) / 55) ≤ ((3891 : ℝ) / 1000))
  exact hmono.trans cosh_b38910_ub

private lemma cosh5_v_427_le : cosh (214 : ℝ) / 275 ≤ (131864833 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((214 : ℝ) / 275) (by norm_num) (by norm_num : ((214 : ℝ) / 275) ≤ ((1557 : ℝ) / 2000))
  exact hmono.trans cosh_b7785_ub

private lemma sech5_pt_427_ge : (281 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (214 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_427_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_427_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_428_le : cosh (39 : ℝ) / 10 ≤ (2471134551 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((39 : ℝ) / 10) (by norm_num) (by norm_num : ((39 : ℝ) / 10) ≤ ((39 : ℝ) / 10))
  exact hmono.trans cosh_b39000_ub

private lemma cosh5_v_428_le : cosh (39 : ℝ) / 50 ≤ (131993914 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((39 : ℝ) / 50) (by norm_num) (by norm_num : ((39 : ℝ) / 50) ≤ ((39 : ℝ) / 50))
  exact hmono.trans cosh_b7800_ub

private lemma sech5_pt_428_ge : (278 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_428_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_428_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_429_le : cosh (43 : ℝ) / 11 ≤ (2494702963 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((43 : ℝ) / 11) (by norm_num) (by norm_num : ((43 : ℝ) / 11) ≤ ((7819 : ℝ) / 2000))
  exact hmono.trans cosh_b39095_ub

private lemma cosh5_v_429_le : cosh (43 : ℝ) / 55 ≤ (132166485 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((43 : ℝ) / 55) (by norm_num) (by norm_num : ((43 : ℝ) / 55) ≤ ((391 : ℝ) / 500))
  exact hmono.trans cosh_b7820_ub

private lemma sech5_pt_429_ge : (275 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_429_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_429_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_430_le : cosh (431 : ℝ) / 110 ≤ (2517238584 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((431 : ℝ) / 110) (by norm_num) (by norm_num : ((431 : ℝ) / 110) ≤ ((7837 : ℝ) / 2000))
  exact hmono.trans cosh_b39185_ub

private lemma cosh5_v_430_le : cosh (431 : ℝ) / 550 ≤ (132339584 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((431 : ℝ) / 550) (by norm_num) (by norm_num : ((431 : ℝ) / 550) ≤ ((98 : ℝ) / 125))
  exact hmono.trans cosh_b7840_ub

private lemma sech5_pt_430_ge : (272 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (431 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_430_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_430_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_431_le : cosh (216 : ℝ) / 55 ≤ (2539978102 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((216 : ℝ) / 55) (by norm_num) (by norm_num : ((216 : ℝ) / 55) ≤ ((1571 : ℝ) / 400))
  exact hmono.trans cosh_b39275_ub

private lemma cosh5_v_431_le : cosh (216 : ℝ) / 275 ≤ (132469756 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((216 : ℝ) / 275) (by norm_num) (by norm_num : ((216 : ℝ) / 275) ≤ ((1571 : ℝ) / 2000))
  exact hmono.trans cosh_b7855_ub

private lemma sech5_pt_431_ge : (270 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (216 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_431_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_431_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_432_le : cosh (433 : ℝ) / 110 ≤ (2562923359 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((433 : ℝ) / 110) (by norm_num) (by norm_num : ((433 : ℝ) / 110) ≤ ((7873 : ℝ) / 2000))
  exact hmono.trans cosh_b39365_ub

private lemma cosh5_v_432_le : cosh (433 : ℝ) / 550 ≤ (132643783 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((433 : ℝ) / 550) (by norm_num) (by norm_num : ((433 : ℝ) / 550) ≤ ((63 : ℝ) / 80))
  exact hmono.trans cosh_b7875_ub

private lemma sech5_pt_432_ge : (267 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (433 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_432_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_432_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_433_le : cosh (217 : ℝ) / 55 ≤ (2586076215 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((217 : ℝ) / 55) (by norm_num) (by norm_num : ((217 : ℝ) / 55) ≤ ((7891 : ℝ) / 2000))
  exact hmono.trans cosh_b39455_ub

private lemma cosh5_v_433_le : cosh (217 : ℝ) / 275 ≤ (132818339 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((217 : ℝ) / 275) (by norm_num) (by norm_num : ((217 : ℝ) / 275) ≤ ((1579 : ℝ) / 2000))
  exact hmono.trans cosh_b7895_ub

private lemma sech5_pt_433_ge : (264 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (217 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_433_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_433_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_434_le : cosh (87 : ℝ) / 22 ≤ (2610742631 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((87 : ℝ) / 22) (by norm_num) (by norm_num : ((87 : ℝ) / 22) ≤ ((791 : ℝ) / 200))
  exact hmono.trans cosh_b39550_ub

private lemma cosh5_v_434_le : cosh (87 : ℝ) / 110 ≤ (132949606 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((87 : ℝ) / 110) (by norm_num) (by norm_num : ((87 : ℝ) / 110) ≤ ((791 : ℝ) / 1000))
  exact hmono.trans cosh_b7910_ub

private lemma sech5_pt_434_ge : (261 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (87 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_434_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_434_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_435_le : cosh (218 : ℝ) / 55 ≤ (2634328125 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((218 : ℝ) / 55) (by norm_num) (by norm_num : ((218 : ℝ) / 55) ≤ ((991 : ℝ) / 250))
  exact hmono.trans cosh_b39640_ub

private lemma cosh5_v_435_le : cosh (218 : ℝ) / 275 ≤ (133125093 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((218 : ℝ) / 275) (by norm_num) (by norm_num : ((218 : ℝ) / 275) ≤ ((793 : ℝ) / 1000))
  exact hmono.trans cosh_b7930_ub

private lemma sech5_pt_435_ge : (259 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (218 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_435_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_435_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_436_le : cosh (437 : ℝ) / 110 ≤ (2658127000 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((437 : ℝ) / 110) (by norm_num) (by norm_num : ((437 : ℝ) / 110) ≤ ((3973 : ℝ) / 1000))
  exact hmono.trans cosh_b39730_ub

private lemma cosh5_v_436_le : cosh (437 : ℝ) / 550 ≤ (133301112 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((437 : ℝ) / 550) (by norm_num) (by norm_num : ((437 : ℝ) / 550) ≤ ((159 : ℝ) / 200))
  exact hmono.trans cosh_b7950_ub

private lemma sech5_pt_436_ge : (256 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (437 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_436_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_436_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_437_le : cosh (219 : ℝ) / 55 ≤ (2682141186 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((219 : ℝ) / 55) (by norm_num) (by norm_num : ((219 : ℝ) / 55) ≤ ((1991 : ℝ) / 500))
  exact hmono.trans cosh_b39820_ub

private lemma cosh5_v_437_le : cosh (219 : ℝ) / 275 ≤ (133433477 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((219 : ℝ) / 275) (by norm_num) (by norm_num : ((219 : ℝ) / 275) ≤ ((1593 : ℝ) / 2000))
  exact hmono.trans cosh_b7965_ub

private lemma sech5_pt_437_ge : (254 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (219 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_437_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_437_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_438_le : cosh (439 : ℝ) / 110 ≤ (2706372626 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((439 : ℝ) / 110) (by norm_num) (by norm_num : ((439 : ℝ) / 110) ≤ ((3991 : ℝ) / 1000))
  exact hmono.trans cosh_b39910_ub

private lemma cosh5_v_438_le : cosh (439 : ℝ) / 550 ≤ (133610430 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((439 : ℝ) / 550) (by norm_num) (by norm_num : ((439 : ℝ) / 550) ≤ ((1597 : ℝ) / 2000))
  exact hmono.trans cosh_b7985_ub

private lemma sech5_pt_438_ge : (251 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (439 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_438_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_438_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_439_le : cosh (4 : ℝ) / 1 ≤ (2730823284 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((4 : ℝ) / 1) (by norm_num) (by norm_num : ((4 : ℝ) / 1) ≤ ((4 : ℝ) / 1))
  exact hmono.trans cosh_b40000_ub

private lemma cosh5_v_439_le : cosh (4 : ℝ) / 5 ≤ (133743495 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((4 : ℝ) / 5) (by norm_num) (by norm_num : ((4 : ℝ) / 5) ≤ ((4 : ℝ) / 5))
  exact hmono.trans cosh_b8000_ub

private lemma sech5_pt_439_ge : (248 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (4 : ℝ) / 1 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_439_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_439_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_440_le : cosh (441 : ℝ) / 110 ≤ (2756872325 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((441 : ℝ) / 110) (by norm_num) (by norm_num : ((441 : ℝ) / 110) ≤ ((8019 : ℝ) / 2000))
  exact hmono.trans cosh_b40095_ub

private lemma cosh5_v_440_le : cosh (441 : ℝ) / 550 ≤ (133921384 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((441 : ℝ) / 550) (by norm_num) (by norm_num : ((441 : ℝ) / 550) ≤ ((401 : ℝ) / 500))
  exact hmono.trans cosh_b8020_ub

private lemma sech5_pt_440_ge : (246 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (441 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_440_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_440_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_441_le : cosh (221 : ℝ) / 55 ≤ (2781779836 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((221 : ℝ) / 55) (by norm_num) (by norm_num : ((221 : ℝ) / 55) ≤ ((8037 : ℝ) / 2000))
  exact hmono.trans cosh_b40185_ub

private lemma cosh5_v_441_le : cosh (221 : ℝ) / 275 ≤ (134099808 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((221 : ℝ) / 275) (by norm_num) (by norm_num : ((221 : ℝ) / 275) ≤ ((201 : ℝ) / 250))
  exact hmono.trans cosh_b8040_ub

private lemma sech5_pt_441_ge : (243 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (221 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_441_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_441_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_442_le : cosh (443 : ℝ) / 110 ≤ (2806912673 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((443 : ℝ) / 110) (by norm_num) (by norm_num : ((443 : ℝ) / 110) ≤ ((1611 : ℝ) / 400))
  exact hmono.trans cosh_b40275_ub

private lemma cosh5_v_442_le : cosh (443 : ℝ) / 550 ≤ (134233979 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((443 : ℝ) / 550) (by norm_num) (by norm_num : ((443 : ℝ) / 550) ≤ ((1611 : ℝ) / 2000))
  exact hmono.trans cosh_b8055_ub

private lemma sech5_pt_442_ge : (241 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (443 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_442_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_442_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_443_le : cosh (222 : ℝ) / 55 ≤ (2832272872 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((222 : ℝ) / 55) (by norm_num) (by norm_num : ((222 : ℝ) / 55) ≤ ((8073 : ℝ) / 2000))
  exact hmono.trans cosh_b40365_ub

private lemma cosh5_v_443_le : cosh (222 : ℝ) / 275 ≤ (134413342 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((222 : ℝ) / 275) (by norm_num) (by norm_num : ((222 : ℝ) / 275) ≤ ((323 : ℝ) / 400))
  exact hmono.trans cosh_b8075_ub

private lemma sech5_pt_443_ge : (238 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (222 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_443_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_443_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_444_le : cosh (89 : ℝ) / 22 ≤ (2857862486 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((89 : ℝ) / 22) (by norm_num) (by norm_num : ((89 : ℝ) / 22) ≤ ((8091 : ℝ) / 2000))
  exact hmono.trans cosh_b40455_ub

private lemma cosh5_v_444_le : cosh (89 : ℝ) / 110 ≤ (134593244 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((89 : ℝ) / 110) (by norm_num) (by norm_num : ((89 : ℝ) / 110) ≤ ((1619 : ℝ) / 2000))
  exact hmono.trans cosh_b8095_ub

private lemma sech5_pt_444_ge : (236 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (89 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_444_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_444_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_445_le : cosh (223 : ℝ) / 55 ≤ (2885124924 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((223 : ℝ) / 55) (by norm_num) (by norm_num : ((223 : ℝ) / 55) ≤ ((811 : ℝ) / 200))
  exact hmono.trans cosh_b40550_ub

private lemma cosh5_v_445_le : cosh (223 : ℝ) / 275 ≤ (134728523 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((223 : ℝ) / 275) (by norm_num) (by norm_num : ((223 : ℝ) / 275) ≤ ((811 : ℝ) / 1000))
  exact hmono.trans cosh_b8110_ub

private lemma sech5_pt_445_ge : (233 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (223 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_445_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_445_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_446_le : cosh (447 : ℝ) / 110 ≤ (2911192645 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((447 : ℝ) / 110) (by norm_num) (by norm_num : ((447 : ℝ) / 110) ≤ ((508 : ℝ) / 125))
  exact hmono.trans cosh_b40640_ub

private lemma cosh5_v_446_le : cosh (447 : ℝ) / 550 ≤ (134909367 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((447 : ℝ) / 550) (by norm_num) (by norm_num : ((447 : ℝ) / 550) ≤ ((813 : ℝ) / 1000))
  exact hmono.trans cosh_b8130_ub

private lemma sech5_pt_446_ge : (231 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (447 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_446_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_446_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_447_le : cosh (224 : ℝ) / 55 ≤ (2937496175 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((224 : ℝ) / 55) (by norm_num) (by norm_num : ((224 : ℝ) / 55) ≤ ((4073 : ℝ) / 1000))
  exact hmono.trans cosh_b40730_ub

private lemma cosh5_v_447_le : cosh (224 : ℝ) / 275 ≤ (135090750 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((224 : ℝ) / 275) (by norm_num) (by norm_num : ((224 : ℝ) / 275) ≤ ((163 : ℝ) / 200))
  exact hmono.trans cosh_b8150_ub

private lemma sech5_pt_447_ge : (229 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (224 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_447_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_447_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_448_le : cosh (449 : ℝ) / 110 ≤ (2964037643 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((449 : ℝ) / 110) (by norm_num) (by norm_num : ((449 : ℝ) / 110) ≤ ((2041 : ℝ) / 500))
  exact hmono.trans cosh_b40820_ub

private lemma cosh5_v_448_le : cosh (449 : ℝ) / 550 ≤ (135227143 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((449 : ℝ) / 550) (by norm_num) (by norm_num : ((449 : ℝ) / 550) ≤ ((1633 : ℝ) / 2000))
  exact hmono.trans cosh_b8165_ub

private lemma sech5_pt_448_ge : (226 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (449 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_448_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_448_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_449_le : cosh (45 : ℝ) / 11 ≤ (2990819199 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((45 : ℝ) / 11) (by norm_num) (by norm_num : ((45 : ℝ) / 11) ≤ ((4091 : ℝ) / 1000))
  exact hmono.trans cosh_b40910_ub

private lemma cosh5_v_449_le : cosh (9 : ℝ) / 11 ≤ (135409472 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 11) (by norm_num) (by norm_num : ((9 : ℝ) / 11) ≤ ((1637 : ℝ) / 2000))
  exact hmono.trans cosh_b8185_ub

private lemma sech5_pt_449_ge : (224 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (45 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_449_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_449_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma sech5_batch_8_ge : (14595 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (401 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (201 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (403 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (202 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (81 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (203 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (204 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (409 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (411 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (206 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (413 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (207 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (83 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (208 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (417 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (419 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (42 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (421 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (211 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (423 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (212 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (85 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (213 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (427 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (214 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (431 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (216 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (433 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (217 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (87 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (218 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (437 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (219 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (439 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (4 : ℝ) / 1 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (441 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (221 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (443 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (222 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (89 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (223 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (447 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (224 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (449 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (45 : ℝ) / 11 := by
  linarith [sech5_pt_400_ge, sech5_pt_401_ge, sech5_pt_402_ge, sech5_pt_403_ge, sech5_pt_404_ge, sech5_pt_405_ge, sech5_pt_406_ge, sech5_pt_407_ge, sech5_pt_408_ge, sech5_pt_409_ge, sech5_pt_410_ge, sech5_pt_411_ge, sech5_pt_412_ge, sech5_pt_413_ge, sech5_pt_414_ge, sech5_pt_415_ge, sech5_pt_416_ge, sech5_pt_417_ge, sech5_pt_418_ge, sech5_pt_419_ge, sech5_pt_420_ge, sech5_pt_421_ge, sech5_pt_422_ge, sech5_pt_423_ge, sech5_pt_424_ge, sech5_pt_425_ge, sech5_pt_426_ge, sech5_pt_427_ge, sech5_pt_428_ge, sech5_pt_429_ge, sech5_pt_430_ge, sech5_pt_431_ge, sech5_pt_432_ge, sech5_pt_433_ge, sech5_pt_434_ge, sech5_pt_435_ge, sech5_pt_436_ge, sech5_pt_437_ge, sech5_pt_438_ge, sech5_pt_439_ge, sech5_pt_440_ge, sech5_pt_441_ge, sech5_pt_442_ge, sech5_pt_443_ge, sech5_pt_444_ge, sech5_pt_445_ge, sech5_pt_446_ge, sech5_pt_447_ge, sech5_pt_448_ge, sech5_pt_449_ge]

private lemma cosh5_u_450_le : cosh (41 : ℝ) / 10 ≤ (3017843014 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((41 : ℝ) / 10) (by norm_num) (by norm_num : ((41 : ℝ) / 10) ≤ ((41 : ℝ) / 10))
  exact hmono.trans cosh_b41000_ub

private lemma cosh5_v_450_le : cosh (41 : ℝ) / 50 ≤ (135546575 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((41 : ℝ) / 50) (by norm_num) (by norm_num : ((41 : ℝ) / 50) ≤ ((41 : ℝ) / 50))
  exact hmono.trans cosh_b8200_ub

private lemma sech5_pt_450_ge : (222 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_450_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_450_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_451_le : cosh (226 : ℝ) / 55 ≤ (3046633391 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((226 : ℝ) / 55) (by norm_num) (by norm_num : ((226 : ℝ) / 55) ≤ ((8219 : ℝ) / 2000))
  exact hmono.trans cosh_b41095_ub

private lemma cosh5_v_451_le : cosh (226 : ℝ) / 275 ≤ (135729853 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((226 : ℝ) / 275) (by norm_num) (by norm_num : ((226 : ℝ) / 275) ≤ ((411 : ℝ) / 500))
  exact hmono.trans cosh_b8220_ub

private lemma sech5_pt_451_ge : (219 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (226 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_451_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_451_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_452_le : cosh (453 : ℝ) / 110 ≤ (3074162077 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((453 : ℝ) / 110) (by norm_num) (by norm_num : ((453 : ℝ) / 110) ≤ ((8237 : ℝ) / 2000))
  exact hmono.trans cosh_b41185_ub

private lemma cosh5_v_452_le : cosh (453 : ℝ) / 550 ≤ (135913674 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((453 : ℝ) / 550) (by norm_num) (by norm_num : ((453 : ℝ) / 550) ≤ ((103 : ℝ) / 125))
  exact hmono.trans cosh_b8240_ub

private lemma sech5_pt_452_ge : (217 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (453 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_452_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_452_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_453_le : cosh (227 : ℝ) / 55 ≤ (3101939771 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((227 : ℝ) / 55) (by norm_num) (by norm_num : ((227 : ℝ) / 55) ≤ ((1651 : ℝ) / 400))
  exact hmono.trans cosh_b41275_ub

private lemma cosh5_v_453_le : cosh (227 : ℝ) / 275 ≤ (136051897 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((227 : ℝ) / 275) (by norm_num) (by norm_num : ((227 : ℝ) / 275) ≤ ((1651 : ℝ) / 2000))
  exact hmono.trans cosh_b8255_ub

private lemma sech5_pt_453_ge : (215 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (227 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_453_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_453_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_454_le : cosh (91 : ℝ) / 22 ≤ (3129968724 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((91 : ℝ) / 22) (by norm_num) (by norm_num : ((91 : ℝ) / 22) ≤ ((8273 : ℝ) / 2000))
  exact hmono.trans cosh_b41365_ub

private lemma cosh5_v_454_le : cosh (91 : ℝ) / 110 ≤ (136236669 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((91 : ℝ) / 110) (by norm_num) (by norm_num : ((91 : ℝ) / 110) ≤ ((331 : ℝ) / 400))
  exact hmono.trans cosh_b8275_ub

private lemma sech5_pt_454_ge : (213 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (91 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_454_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_454_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_455_le : cosh (228 : ℝ) / 55 ≤ (3158251206 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((228 : ℝ) / 55) (by norm_num) (by norm_num : ((228 : ℝ) / 55) ≤ ((8291 : ℝ) / 2000))
  exact hmono.trans cosh_b41455_ub

private lemma cosh5_v_455_le : cosh (228 : ℝ) / 275 ≤ (136421987 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((228 : ℝ) / 275) (by norm_num) (by norm_num : ((228 : ℝ) / 275) ≤ ((1659 : ℝ) / 2000))
  exact hmono.trans cosh_b8295_ub

private lemma sech5_pt_455_ge : (210 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (228 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_455_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_455_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_456_le : cosh (457 : ℝ) / 110 ≤ (3188382517 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((457 : ℝ) / 110) (by norm_num) (by norm_num : ((457 : ℝ) / 110) ≤ ((831 : ℝ) / 200))
  exact hmono.trans cosh_b41550_ub

private lemma cosh5_v_456_le : cosh (457 : ℝ) / 550 ≤ (136561334 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((457 : ℝ) / 550) (by norm_num) (by norm_num : ((457 : ℝ) / 550) ≤ ((831 : ℝ) / 1000))
  exact hmono.trans cosh_b8310_ub

private lemma sech5_pt_456_ge : (208 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (457 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_456_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_456_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_457_le : cosh (229 : ℝ) / 55 ≤ (3217193360 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((229 : ℝ) / 55) (by norm_num) (by norm_num : ((229 : ℝ) / 55) ≤ ((1041 : ℝ) / 250))
  exact hmono.trans cosh_b41640_ub

private lemma cosh5_v_457_le : cosh (229 : ℝ) / 275 ≤ (136747607 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((229 : ℝ) / 275) (by norm_num) (by norm_num : ((229 : ℝ) / 275) ≤ ((833 : ℝ) / 1000))
  exact hmono.trans cosh_b8330_ub

private lemma sech5_pt_457_ge : (206 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (229 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_457_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_457_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_458_le : cosh (459 : ℝ) / 110 ≤ (3246264798 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((459 : ℝ) / 110) (by norm_num) (by norm_num : ((459 : ℝ) / 110) ≤ ((4173 : ℝ) / 1000))
  exact hmono.trans cosh_b41730_ub

private lemma cosh5_v_458_le : cosh (459 : ℝ) / 550 ≤ (136934427 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((459 : ℝ) / 550) (by norm_num) (by norm_num : ((459 : ℝ) / 550) ≤ ((167 : ℝ) / 200))
  exact hmono.trans cosh_b8350_ub

private lemma sech5_pt_458_ge : (204 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (459 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_458_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_458_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_459_le : cosh (46 : ℝ) / 11 ≤ (3275599185 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((46 : ℝ) / 11) (by norm_num) (by norm_num : ((46 : ℝ) / 11) ≤ ((2091 : ℝ) / 500))
  exact hmono.trans cosh_b41820_ub

private lemma cosh5_v_459_le : cosh (46 : ℝ) / 55 ≤ (137074902 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((46 : ℝ) / 55) (by norm_num) (by norm_num : ((46 : ℝ) / 55) ≤ ((1673 : ℝ) / 2000))
  exact hmono.trans cosh_b8365_ub

private lemma sech5_pt_459_ge : (202 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (46 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_459_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_459_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_460_le : cosh (461 : ℝ) / 110 ≤ (3305198896 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((461 : ℝ) / 110) (by norm_num) (by norm_num : ((461 : ℝ) / 110) ≤ ((4191 : ℝ) / 1000))
  exact hmono.trans cosh_b41910_ub

private lemma cosh5_v_460_le : cosh (461 : ℝ) / 550 ≤ (137262681 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((461 : ℝ) / 550) (by norm_num) (by norm_num : ((461 : ℝ) / 550) ≤ ((1677 : ℝ) / 2000))
  exact hmono.trans cosh_b8385_ub

private lemma sech5_pt_460_ge : (200 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (461 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_460_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_460_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_461_le : cosh (21 : ℝ) / 5 ≤ (3335066331 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((21 : ℝ) / 5) (by norm_num) (by norm_num : ((21 : ℝ) / 5) ≤ ((21 : ℝ) / 5))
  exact hmono.trans cosh_b42000_ub

private lemma cosh5_v_461_le : cosh (21 : ℝ) / 25 ≤ (137403876 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((21 : ℝ) / 25) (by norm_num) (by norm_num : ((21 : ℝ) / 25) ≤ ((21 : ℝ) / 25))
  exact hmono.trans cosh_b8400_ub

private lemma sech5_pt_461_ge : (198 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_461_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_461_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_462_le : cosh (463 : ℝ) / 110 ≤ (3366886188 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((463 : ℝ) / 110) (by norm_num) (by norm_num : ((463 : ℝ) / 110) ≤ ((8419 : ℝ) / 2000))
  exact hmono.trans cosh_b42095_ub

private lemma cosh5_v_462_le : cosh (463 : ℝ) / 550 ≤ (137592616 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((463 : ℝ) / 550) (by norm_num) (by norm_num : ((463 : ℝ) / 550) ≤ ((421 : ℝ) / 500))
  exact hmono.trans cosh_b8420_ub

private lemma sech5_pt_462_ge : (196 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (463 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_462_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_462_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_463_le : cosh (232 : ℝ) / 55 ≤ (3397311564 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((232 : ℝ) / 55) (by norm_num) (by norm_num : ((232 : ℝ) / 55) ≤ ((8437 : ℝ) / 2000))
  exact hmono.trans cosh_b42185_ub

private lemma cosh5_v_463_le : cosh (232 : ℝ) / 275 ≤ (137781907 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((232 : ℝ) / 275) (by norm_num) (by norm_num : ((232 : ℝ) / 275) ≤ ((211 : ℝ) / 250))
  exact hmono.trans cosh_b8440_ub

private lemma sech5_pt_463_ge : (194 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (232 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_463_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_463_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_464_le : cosh (93 : ℝ) / 22 ≤ (3428012124 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((93 : ℝ) / 22) (by norm_num) (by norm_num : ((93 : ℝ) / 22) ≤ ((1691 : ℝ) / 400))
  exact hmono.trans cosh_b42275_ub

private lemma cosh5_v_464_le : cosh (93 : ℝ) / 110 ≤ (137924237 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((93 : ℝ) / 110) (by norm_num) (by norm_num : ((93 : ℝ) / 110) ≤ ((1691 : ℝ) / 2000))
  exact hmono.trans cosh_b8455_ub

private lemma sech5_pt_464_ge : (192 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (93 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_464_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_464_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_465_le : cosh (233 : ℝ) / 55 ≤ (3458990355 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((233 : ℝ) / 55) (by norm_num) (by norm_num : ((233 : ℝ) / 55) ≤ ((8473 : ℝ) / 2000))
  exact hmono.trans cosh_b42365_ub

private lemma cosh5_v_465_le : cosh (233 : ℝ) / 275 ≤ (138114493 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((233 : ℝ) / 275) (by norm_num) (by norm_num : ((233 : ℝ) / 275) ≤ ((339 : ℝ) / 400))
  exact hmono.trans cosh_b8475_ub

private lemma sech5_pt_465_ge : (190 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (233 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_465_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_465_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_466_le : cosh (467 : ℝ) / 110 ≤ (3490248766 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((467 : ℝ) / 110) (by norm_num) (by norm_num : ((467 : ℝ) / 110) ≤ ((8491 : ℝ) / 2000))
  exact hmono.trans cosh_b42455_ub

private lemma cosh5_v_466_le : cosh (467 : ℝ) / 550 ≤ (138305301 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((467 : ℝ) / 550) (by norm_num) (by norm_num : ((467 : ℝ) / 550) ≤ ((1699 : ℝ) / 2000))
  exact hmono.trans cosh_b8495_ub

private lemma sech5_pt_466_ge : (188 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (467 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_466_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_466_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_467_le : cosh (234 : ℝ) / 55 ≤ (3523550514 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((234 : ℝ) / 55) (by norm_num) (by norm_num : ((234 : ℝ) / 55) ≤ ((851 : ℝ) / 200))
  exact hmono.trans cosh_b42550_ub

private lemma cosh5_v_467_le : cosh (234 : ℝ) / 275 ≤ (138448770 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((234 : ℝ) / 275) (by norm_num) (by norm_num : ((234 : ℝ) / 275) ≤ ((851 : ℝ) / 1000))
  exact hmono.trans cosh_b8510_ub

private lemma sech5_pt_467_ge : (186 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (234 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_467_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_467_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_468_le : cosh (469 : ℝ) / 110 ≤ (3555392828 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((469 : ℝ) / 110) (by norm_num) (by norm_num : ((469 : ℝ) / 110) ≤ ((533 : ℝ) / 125))
  exact hmono.trans cosh_b42640_ub

private lemma cosh5_v_468_le : cosh (469 : ℝ) / 550 ≤ (138640548 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((469 : ℝ) / 550) (by norm_num) (by norm_num : ((469 : ℝ) / 550) ≤ ((853 : ℝ) / 1000))
  exact hmono.trans cosh_b8530_ub

private lemma sech5_pt_468_ge : (184 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (469 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_468_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_468_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_469_le : cosh (47 : ℝ) / 11 ≤ (3587523130 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((47 : ℝ) / 11) (by norm_num) (by norm_num : ((47 : ℝ) / 11) ≤ ((4273 : ℝ) / 1000))
  exact hmono.trans cosh_b42730_ub

private lemma cosh5_v_469_le : cosh (47 : ℝ) / 55 ≤ (138832879 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((47 : ℝ) / 55) (by norm_num) (by norm_num : ((47 : ℝ) / 55) ≤ ((171 : ℝ) / 200))
  exact hmono.trans cosh_b8550_ub

private lemma sech5_pt_469_ge : (182 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_469_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_469_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_470_le : cosh (471 : ℝ) / 110 ≤ (3619944024 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((471 : ℝ) / 110) (by norm_num) (by norm_num : ((471 : ℝ) / 110) ≤ ((2141 : ℝ) / 500))
  exact hmono.trans cosh_b42820_ub

private lemma cosh5_v_470_le : cosh (471 : ℝ) / 550 ≤ (138977492 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((471 : ℝ) / 550) (by norm_num) (by norm_num : ((471 : ℝ) / 550) ≤ ((1713 : ℝ) / 2000))
  exact hmono.trans cosh_b8565_ub

private lemma sech5_pt_470_ge : (180 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (471 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_470_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_470_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_471_le : cosh (236 : ℝ) / 55 ≤ (3652658135 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((236 : ℝ) / 55) (by norm_num) (by norm_num : ((236 : ℝ) / 55) ≤ ((4291 : ℝ) / 1000))
  exact hmono.trans cosh_b42910_ub

private lemma cosh5_v_471_le : cosh (236 : ℝ) / 275 ≤ (139170796 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((236 : ℝ) / 275) (by norm_num) (by norm_num : ((236 : ℝ) / 275) ≤ ((1717 : ℝ) / 2000))
  exact hmono.trans cosh_b8585_ub

private lemma sech5_pt_471_ge : (178 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (236 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_471_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_471_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_472_le : cosh (43 : ℝ) / 10 ≤ (3685668113 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((43 : ℝ) / 10) (by norm_num) (by norm_num : ((43 : ℝ) / 10) ≤ ((43 : ℝ) / 10))
  exact hmono.trans cosh_b43000_ub

private lemma cosh5_v_472_le : cosh (43 : ℝ) / 50 ≤ (139316139 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((43 : ℝ) / 50) (by norm_num) (by norm_num : ((43 : ℝ) / 50) ≤ ((43 : ℝ) / 50))
  exact hmono.trans cosh_b8600_ub

private lemma sech5_pt_472_ge : (177 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_472_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_472_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_473_le : cosh (237 : ℝ) / 55 ≤ (3720835914 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((237 : ℝ) / 55) (by norm_num) (by norm_num : ((237 : ℝ) / 55) ≤ ((8619 : ℝ) / 2000))
  exact hmono.trans cosh_b43095_ub

private lemma cosh5_v_473_le : cosh (237 : ℝ) / 275 ≤ (139510418 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((237 : ℝ) / 275) (by norm_num) (by norm_num : ((237 : ℝ) / 275) ≤ ((431 : ℝ) / 500))
  exact hmono.trans cosh_b8620_ub

private lemma sech5_pt_473_ge : (175 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (237 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_473_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_473_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_474_le : cosh (95 : ℝ) / 22 ≤ (3754462488 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((95 : ℝ) / 22) (by norm_num) (by norm_num : ((95 : ℝ) / 22) ≤ ((8637 : ℝ) / 2000))
  exact hmono.trans cosh_b43185_ub

private lemma cosh5_v_474_le : cosh (19 : ℝ) / 22 ≤ (139705255 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((19 : ℝ) / 22) (by norm_num) (by norm_num : ((19 : ℝ) / 22) ≤ ((108 : ℝ) / 125))
  exact hmono.trans cosh_b8640_ub

private lemma sech5_pt_474_ge : (173 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (95 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_474_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_474_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_475_le : cosh (238 : ℝ) / 55 ≤ (3788393175 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((238 : ℝ) / 55) (by norm_num) (by norm_num : ((238 : ℝ) / 55) ≤ ((1731 : ℝ) / 400))
  exact hmono.trans cosh_b43275_ub

private lemma cosh5_v_475_le : cosh (238 : ℝ) / 275 ≤ (139851749 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((238 : ℝ) / 275) (by norm_num) (by norm_num : ((238 : ℝ) / 275) ≤ ((1731 : ℝ) / 2000))
  exact hmono.trans cosh_b8655_ub

private lemma sech5_pt_475_ge : (171 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (238 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_475_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_475_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_476_le : cosh (477 : ℝ) / 110 ≤ (3822630724 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((477 : ℝ) / 110) (by norm_num) (by norm_num : ((477 : ℝ) / 110) ≤ ((8673 : ℝ) / 2000))
  exact hmono.trans cosh_b43365_ub

private lemma cosh5_v_476_le : cosh (477 : ℝ) / 550 ≤ (140047564 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((477 : ℝ) / 550) (by norm_num) (by norm_num : ((477 : ℝ) / 550) ≤ ((347 : ℝ) / 400))
  exact hmono.trans cosh_b8675_ub

private lemma sech5_pt_476_ge : (169 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (477 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_476_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_476_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_477_le : cosh (239 : ℝ) / 55 ≤ (3857177909 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((239 : ℝ) / 55) (by norm_num) (by norm_num : ((239 : ℝ) / 55) ≤ ((8691 : ℝ) / 2000))
  exact hmono.trans cosh_b43455_ub

private lemma cosh5_v_477_le : cosh (239 : ℝ) / 275 ≤ (140243939 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((239 : ℝ) / 275) (by norm_num) (by norm_num : ((239 : ℝ) / 275) ≤ ((1739 : ℝ) / 2000))
  exact hmono.trans cosh_b8695_ub

private lemma sech5_pt_477_ge : (168 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (239 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_477_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_477_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_478_le : cosh (479 : ℝ) / 110 ≤ (3893983389 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((479 : ℝ) / 110) (by norm_num) (by norm_num : ((479 : ℝ) / 110) ≤ ((871 : ℝ) / 200))
  exact hmono.trans cosh_b43550_ub

private lemma cosh5_v_478_le : cosh (479 : ℝ) / 550 ≤ (140391589 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((479 : ℝ) / 550) (by norm_num) (by norm_num : ((479 : ℝ) / 550) ≤ ((871 : ℝ) / 1000))
  exact hmono.trans cosh_b8710_ub

private lemma sech5_pt_478_ge : (166 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (479 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_478_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_478_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_479_le : cosh (48 : ℝ) / 11 ≤ (3929175862 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((48 : ℝ) / 11) (by norm_num) (by norm_num : ((48 : ℝ) / 11) ≤ ((1091 : ℝ) / 250))
  exact hmono.trans cosh_b43640_ub

private lemma cosh5_v_479_le : cosh (48 : ℝ) / 55 ≤ (140588946 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((48 : ℝ) / 55) (by norm_num) (by norm_num : ((48 : ℝ) / 55) ≤ ((873 : ℝ) / 1000))
  exact hmono.trans cosh_b8730_ub

private lemma sech5_pt_479_ge : (164 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (48 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_479_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_479_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_480_le : cosh (481 : ℝ) / 110 ≤ (3964686600 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((481 : ℝ) / 110) (by norm_num) (by norm_num : ((481 : ℝ) / 110) ≤ ((4373 : ℝ) / 1000))
  exact hmono.trans cosh_b43730_ub

private lemma cosh5_v_480_le : cosh (481 : ℝ) / 550 ≤ (140786866 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((481 : ℝ) / 550) (by norm_num) (by norm_num : ((481 : ℝ) / 550) ≤ ((7 : ℝ) / 8))
  exact hmono.trans cosh_b8750_ub

private lemma sech5_pt_480_ge : (162 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (481 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_480_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_480_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_481_le : cosh (241 : ℝ) / 55 ≤ (4000518480 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((241 : ℝ) / 55) (by norm_num) (by norm_num : ((241 : ℝ) / 55) ≤ ((2191 : ℝ) / 500))
  exact hmono.trans cosh_b43820_ub

private lemma cosh5_v_481_le : cosh (241 : ℝ) / 275 ≤ (140935676 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((241 : ℝ) / 275) (by norm_num) (by norm_num : ((241 : ℝ) / 275) ≤ ((1753 : ℝ) / 2000))
  exact hmono.trans cosh_b8765_ub

private lemma sech5_pt_481_ge : (161 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (241 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_481_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_481_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_482_le : cosh (483 : ℝ) / 110 ≤ (4036674404 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((483 : ℝ) / 110) (by norm_num) (by norm_num : ((483 : ℝ) / 110) ≤ ((4391 : ℝ) / 1000))
  exact hmono.trans cosh_b43910_ub

private lemma cosh5_v_482_le : cosh (483 : ℝ) / 550 ≤ (141134582 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((483 : ℝ) / 550) (by norm_num) (by norm_num : ((483 : ℝ) / 550) ≤ ((1757 : ℝ) / 2000))
  exact hmono.trans cosh_b8785_ub

private lemma sech5_pt_482_ge : (159 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (483 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_482_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_482_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_483_le : cosh (22 : ℝ) / 5 ≤ (4073157301 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((22 : ℝ) / 5) (by norm_num) (by norm_num : ((22 : ℝ) / 5) ≤ ((22 : ℝ) / 5))
  exact hmono.trans cosh_b44000_ub

private lemma cosh5_v_483_le : cosh (22 : ℝ) / 25 ≤ (141284131 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((22 : ℝ) / 25) (by norm_num) (by norm_num : ((22 : ℝ) / 25) ≤ ((22 : ℝ) / 25))
  exact hmono.trans cosh_b8800_ub

private lemma sech5_pt_483_ge : (157 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (22 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_483_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_483_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_484_le : cosh (97 : ℝ) / 22 ≤ (4112025016 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((97 : ℝ) / 22) (by norm_num) (by norm_num : ((97 : ℝ) / 22) ≤ ((8819 : ℝ) / 2000))
  exact hmono.trans cosh_b44095_ub

private lemma cosh5_v_484_le : cosh (97 : ℝ) / 110 ≤ (141484026 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((97 : ℝ) / 110) (by norm_num) (by norm_num : ((97 : ℝ) / 110) ≤ ((441 : ℝ) / 500))
  exact hmono.trans cosh_b8820_ub

private lemma sech5_pt_484_ge : (156 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (97 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_484_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_484_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_485_le : cosh (243 : ℝ) / 55 ≤ (4149189334 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((243 : ℝ) / 55) (by norm_num) (by norm_num : ((243 : ℝ) / 55) ≤ ((8837 : ℝ) / 2000))
  exact hmono.trans cosh_b44185_ub

private lemma cosh5_v_485_le : cosh (243 : ℝ) / 275 ≤ (141684486 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((243 : ℝ) / 275) (by norm_num) (by norm_num : ((243 : ℝ) / 275) ≤ ((221 : ℝ) / 250))
  exact hmono.trans cosh_b8840_ub

private lemma sech5_pt_485_ge : (154 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (243 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_485_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_485_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_486_le : cosh (487 : ℝ) / 110 ≤ (4186689738 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((487 : ℝ) / 110) (by norm_num) (by norm_num : ((487 : ℝ) / 110) ≤ ((1771 : ℝ) / 400))
  exact hmono.trans cosh_b44275_ub

private lemma cosh5_v_486_le : cosh (487 : ℝ) / 550 ≤ (141835203 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((487 : ℝ) / 550) (by norm_num) (by norm_num : ((487 : ℝ) / 550) ≤ ((1771 : ℝ) / 2000))
  exact hmono.trans cosh_b8855_ub

private lemma sech5_pt_486_ge : (153 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (487 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_486_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_486_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_487_le : cosh (244 : ℝ) / 55 ≤ (4224529266 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((244 : ℝ) / 55) (by norm_num) (by norm_num : ((244 : ℝ) / 55) ≤ ((8873 : ℝ) / 2000))
  exact hmono.trans cosh_b44365_ub

private lemma cosh5_v_487_le : cosh (244 : ℝ) / 275 ≤ (142036656 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((244 : ℝ) / 275) (by norm_num) (by norm_num : ((244 : ℝ) / 275) ≤ ((71 : ℝ) / 80))
  exact hmono.trans cosh_b8875_ub

private lemma sech5_pt_487_ge : (151 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (244 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_487_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_487_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_488_le : cosh (489 : ℝ) / 110 ≤ (4262710984 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((489 : ℝ) / 110) (by norm_num) (by norm_num : ((489 : ℝ) / 110) ≤ ((8891 : ℝ) / 2000))
  exact hmono.trans cosh_b44455_ub

private lemma cosh5_v_488_le : cosh (489 : ℝ) / 550 ≤ (142238677 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((489 : ℝ) / 550) (by norm_num) (by norm_num : ((489 : ℝ) / 550) ≤ ((1779 : ℝ) / 2000))
  exact hmono.trans cosh_b8895_ub

private lemma sech5_pt_488_ge : (149 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (489 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_488_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_488_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_489_le : cosh (49 : ℝ) / 11 ≤ (4303388559 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((49 : ℝ) / 11) (by norm_num) (by norm_num : ((49 : ℝ) / 11) ≤ ((891 : ℝ) / 200))
  exact hmono.trans cosh_b44550_ub

private lemma cosh5_v_489_le : cosh (49 : ℝ) / 55 ≤ (142390566 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((49 : ℝ) / 55) (by norm_num) (by norm_num : ((49 : ℝ) / 55) ≤ ((891 : ℝ) / 1000))
  exact hmono.trans cosh_b8910_ub

private lemma sech5_pt_489_ge : (148 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_489_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_489_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_490_le : cosh (491 : ℝ) / 110 ≤ (4342283409 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((491 : ℝ) / 110) (by norm_num) (by norm_num : ((491 : ℝ) / 110) ≤ ((558 : ℝ) / 125))
  exact hmono.trans cosh_b44640_ub

private lemma cosh5_v_490_le : cosh (491 : ℝ) / 550 ≤ (142593583 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((491 : ℝ) / 550) (by norm_num) (by norm_num : ((491 : ℝ) / 550) ≤ ((893 : ℝ) / 1000))
  exact hmono.trans cosh_b8930_ub

private lemma sech5_pt_490_ge : (146 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (491 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_490_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_490_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_491_le : cosh (246 : ℝ) / 55 ≤ (4381529986 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((246 : ℝ) / 55) (by norm_num) (by norm_num : ((246 : ℝ) / 55) ≤ ((4473 : ℝ) / 1000))
  exact hmono.trans cosh_b44730_ub

private lemma cosh5_v_491_le : cosh (246 : ℝ) / 275 ≤ (142797170 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((246 : ℝ) / 275) (by norm_num) (by norm_num : ((246 : ℝ) / 275) ≤ ((179 : ℝ) / 200))
  exact hmono.trans cosh_b8950_ub

private lemma sech5_pt_491_ge : (145 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (246 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_491_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_491_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_492_le : cosh (493 : ℝ) / 110 ≤ (4421131469 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((493 : ℝ) / 110) (by norm_num) (by norm_num : ((493 : ℝ) / 110) ≤ ((2241 : ℝ) / 500))
  exact hmono.trans cosh_b44820_ub

private lemma cosh5_v_492_le : cosh (493 : ℝ) / 550 ≤ (142950235 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((493 : ℝ) / 550) (by norm_num) (by norm_num : ((493 : ℝ) / 550) ≤ ((1793 : ℝ) / 2000))
  exact hmono.trans cosh_b8965_ub

private lemma sech5_pt_492_ge : (143 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (493 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_492_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_492_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_493_le : cosh (247 : ℝ) / 55 ≤ (4461091067 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((247 : ℝ) / 55) (by norm_num) (by norm_num : ((247 : ℝ) / 55) ≤ ((4491 : ℝ) / 1000))
  exact hmono.trans cosh_b44910_ub

private lemma cosh5_v_493_le : cosh (247 : ℝ) / 275 ≤ (143154823 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((247 : ℝ) / 275) (by norm_num) (by norm_num : ((247 : ℝ) / 275) ≤ ((1797 : ℝ) / 2000))
  exact hmono.trans cosh_b8985_ub

private lemma sech5_pt_493_ge : (142 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (247 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_493_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_493_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_494_le : cosh (9 : ℝ) / 2 ≤ (4501412015 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 2) (by norm_num) (by norm_num : ((9 : ℝ) / 2) ≤ ((9 : ℝ) / 2))
  exact hmono.trans cosh_b45000_ub

private lemma cosh5_v_494_le : cosh (9 : ℝ) / 10 ≤ (143308639 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((9 : ℝ) / 10) (by norm_num) (by norm_num : ((9 : ℝ) / 10) ≤ ((9 : ℝ) / 10))
  exact hmono.trans cosh_b9000_ub

private lemma sech5_pt_494_ge : (140 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 2 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_494_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_494_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_495_le : cosh (248 : ℝ) / 55 ≤ (4544368647 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((248 : ℝ) / 55) (by norm_num) (by norm_num : ((248 : ℝ) / 55) ≤ ((9019 : ℝ) / 2000))
  exact hmono.trans cosh_b45095_ub

private lemma cosh5_v_495_le : cosh (248 : ℝ) / 275 ≤ (143514229 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((248 : ℝ) / 275) (by norm_num) (by norm_num : ((248 : ℝ) / 275) ≤ ((451 : ℝ) / 500))
  exact hmono.trans cosh_b9020_ub

private lemma sech5_pt_495_ge : (139 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (248 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_495_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_495_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_496_le : cosh (497 : ℝ) / 110 ≤ (4585442661 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((497 : ℝ) / 110) (by norm_num) (by norm_num : ((497 : ℝ) / 110) ≤ ((9037 : ℝ) / 2000))
  exact hmono.trans cosh_b45185_ub

private lemma cosh5_v_496_le : cosh (497 : ℝ) / 550 ≤ (143720393 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((497 : ℝ) / 550) (by norm_num) (by norm_num : ((497 : ℝ) / 550) ≤ ((113 : ℝ) / 125))
  exact hmono.trans cosh_b9040_ub

private lemma sech5_pt_496_ge : (137 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (497 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_496_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_496_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_497_le : cosh (249 : ℝ) / 55 ≤ (4626888099 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((249 : ℝ) / 55) (by norm_num) (by norm_num : ((249 : ℝ) / 55) ≤ ((1811 : ℝ) / 400))
  exact hmono.trans cosh_b45275_ub

private lemma cosh5_v_497_le : cosh (249 : ℝ) / 275 ≤ (143875394 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((249 : ℝ) / 275) (by norm_num) (by norm_num : ((249 : ℝ) / 275) ≤ ((1811 : ℝ) / 2000))
  exact hmono.trans cosh_b9055_ub

private lemma sech5_pt_497_ge : (136 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (249 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_497_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_497_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_498_le : cosh (499 : ℝ) / 110 ≤ (4668708317 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((499 : ℝ) / 110) (by norm_num) (by norm_num : ((499 : ℝ) / 110) ≤ ((9073 : ℝ) / 2000))
  exact hmono.trans cosh_b45365_ub

private lemma cosh5_v_498_le : cosh (499 : ℝ) / 550 ≤ (144082564 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((499 : ℝ) / 550) (by norm_num) (by norm_num : ((499 : ℝ) / 550) ≤ ((363 : ℝ) / 400))
  exact hmono.trans cosh_b9075_ub

private lemma sech5_pt_498_ge : (135 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (499 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_498_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_498_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_499_le : cosh (50 : ℝ) / 11 ≤ (4710906703 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((50 : ℝ) / 11) (by norm_num) (by norm_num : ((50 : ℝ) / 11) ≤ ((9091 : ℝ) / 2000))
  exact hmono.trans cosh_b45455_ub

private lemma cosh5_v_499_le : cosh (10 : ℝ) / 11 ≤ (144290311 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((10 : ℝ) / 11) (by norm_num) (by norm_num : ((10 : ℝ) / 11) ≤ ((1819 : ℝ) / 2000))
  exact hmono.trans cosh_b9095_ub

private lemma sech5_pt_499_ge : (133 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (50 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_499_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_499_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma sech5_batch_9_ge : (8717 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (226 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (453 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (227 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (91 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (228 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (457 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (229 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (459 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (46 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (461 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (463 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (232 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (93 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (233 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (467 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (234 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (469 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (471 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (236 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (237 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (95 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (238 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (477 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (239 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (479 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (48 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (481 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (241 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (483 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (22 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (97 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (243 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (487 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (244 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (489 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (491 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (246 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (493 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (247 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 2 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (248 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (497 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (249 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (499 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (50 : ℝ) / 11 := by
  linarith [sech5_pt_450_ge, sech5_pt_451_ge, sech5_pt_452_ge, sech5_pt_453_ge, sech5_pt_454_ge, sech5_pt_455_ge, sech5_pt_456_ge, sech5_pt_457_ge, sech5_pt_458_ge, sech5_pt_459_ge, sech5_pt_460_ge, sech5_pt_461_ge, sech5_pt_462_ge, sech5_pt_463_ge, sech5_pt_464_ge, sech5_pt_465_ge, sech5_pt_466_ge, sech5_pt_467_ge, sech5_pt_468_ge, sech5_pt_469_ge, sech5_pt_470_ge, sech5_pt_471_ge, sech5_pt_472_ge, sech5_pt_473_ge, sech5_pt_474_ge, sech5_pt_475_ge, sech5_pt_476_ge, sech5_pt_477_ge, sech5_pt_478_ge, sech5_pt_479_ge, sech5_pt_480_ge, sech5_pt_481_ge, sech5_pt_482_ge, sech5_pt_483_ge, sech5_pt_484_ge, sech5_pt_485_ge, sech5_pt_486_ge, sech5_pt_487_ge, sech5_pt_488_ge, sech5_pt_489_ge, sech5_pt_490_ge, sech5_pt_491_ge, sech5_pt_492_ge, sech5_pt_493_ge, sech5_pt_494_ge, sech5_pt_495_ge, sech5_pt_496_ge, sech5_pt_497_ge, sech5_pt_498_ge, sech5_pt_499_ge]

private lemma cosh5_u_500_le : cosh (501 : ℝ) / 110 ≤ (4755863487 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((501 : ℝ) / 110) (by norm_num) (by norm_num : ((501 : ℝ) / 110) ≤ ((911 : ℝ) / 200))
  exact hmono.trans cosh_b45550_ub

private lemma cosh5_v_500_le : cosh (501 : ℝ) / 550 ≤ (144446500 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((501 : ℝ) / 550) (by norm_num) (by norm_num : ((501 : ℝ) / 550) ≤ ((911 : ℝ) / 1000))
  exact hmono.trans cosh_b9110_ub

private lemma sech5_pt_500_ge : (132 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (501 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_500_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_500_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_501_le : cosh (251 : ℝ) / 55 ≤ (4798849987 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((251 : ℝ) / 55) (by norm_num) (by norm_num : ((251 : ℝ) / 55) ≤ ((1141 : ℝ) / 250))
  exact hmono.trans cosh_b45640_ub

private lemma cosh5_v_501_le : cosh (251 : ℝ) / 275 ≤ (144655258 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((251 : ℝ) / 275) (by norm_num) (by norm_num : ((251 : ℝ) / 275) ≤ ((913 : ℝ) / 1000))
  exact hmono.trans cosh_b9130_ub

private lemma sech5_pt_501_ge : (130 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (251 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_501_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_501_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_502_le : cosh (503 : ℝ) / 110 ≤ (4842225196 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((503 : ℝ) / 110) (by norm_num) (by norm_num : ((503 : ℝ) / 110) ≤ ((4573 : ℝ) / 1000))
  exact hmono.trans cosh_b45730_ub

private lemma cosh5_v_502_le : cosh (503 : ℝ) / 550 ≤ (144864594 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((503 : ℝ) / 550) (by norm_num) (by norm_num : ((503 : ℝ) / 550) ≤ ((183 : ℝ) / 200))
  exact hmono.trans cosh_b9150_ub

private lemma sech5_pt_502_ge : (129 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (503 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_502_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_502_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_503_le : cosh (252 : ℝ) / 55 ≤ (4885992629 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((252 : ℝ) / 55) (by norm_num) (by norm_num : ((252 : ℝ) / 55) ≤ ((2291 : ℝ) / 500))
  exact hmono.trans cosh_b45820_ub

private lemma cosh5_v_503_le : cosh (252 : ℝ) / 275 ≤ (145021977 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((252 : ℝ) / 275) (by norm_num) (by norm_num : ((252 : ℝ) / 275) ≤ ((1833 : ℝ) / 2000))
  exact hmono.trans cosh_b9165_ub

private lemma sech5_pt_503_ge : (128 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (252 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_503_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_503_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_504_le : cosh (101 : ℝ) / 22 ≤ (4930155829 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((101 : ℝ) / 22) (by norm_num) (by norm_num : ((101 : ℝ) / 22) ≤ ((4591 : ℝ) / 1000))
  exact hmono.trans cosh_b45910_ub

private lemma cosh5_v_504_le : cosh (101 : ℝ) / 110 ≤ (145232328 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((101 : ℝ) / 110) (by norm_num) (by norm_num : ((101 : ℝ) / 110) ≤ ((1837 : ℝ) / 2000))
  exact hmono.trans cosh_b9185_ub

private lemma sech5_pt_504_ge : (126 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (101 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_504_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_504_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_505_le : cosh (23 : ℝ) / 5 ≤ (4974718374 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((23 : ℝ) / 5) (by norm_num) (by norm_num : ((23 : ℝ) / 5) ≤ ((23 : ℝ) / 5))
  exact hmono.trans cosh_b46000_ub

private lemma cosh5_v_505_le : cosh (23 : ℝ) / 25 ≤ (145390472 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((23 : ℝ) / 25) (by norm_num) (by norm_num : ((23 : ℝ) / 25) ≤ ((23 : ℝ) / 25))
  exact hmono.trans cosh_b9200_ub

private lemma sech5_pt_505_ge : (125 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_505_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_505_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_506_le : cosh (507 : ℝ) / 110 ≤ (5022193846 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((507 : ℝ) / 110) (by norm_num) (by norm_num : ((507 : ℝ) / 110) ≤ ((9219 : ℝ) / 2000))
  exact hmono.trans cosh_b46095_ub

private lemma cosh5_v_506_le : cosh (507 : ℝ) / 550 ≤ (145601840 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((507 : ℝ) / 550) (by norm_num) (by norm_num : ((507 : ℝ) / 550) ≤ ((461 : ℝ) / 500))
  exact hmono.trans cosh_b9220_ub

private lemma sech5_pt_506_ge : (124 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (507 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_506_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_506_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_507_le : cosh (254 : ℝ) / 55 ≤ (5067588640 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((254 : ℝ) / 55) (by norm_num) (by norm_num : ((254 : ℝ) / 55) ≤ ((9237 : ℝ) / 2000))
  exact hmono.trans cosh_b46185_ub

private lemma cosh5_v_507_le : cosh (254 : ℝ) / 275 ≤ (145813791 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((254 : ℝ) / 275) (by norm_num) (by norm_num : ((254 : ℝ) / 275) ≤ ((231 : ℝ) / 250))
  exact hmono.trans cosh_b9240_ub

private lemma sech5_pt_507_ge : (123 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (254 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_507_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_507_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_508_le : cosh (509 : ℝ) / 110 ≤ (5113393911 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((509 : ℝ) / 110) (by norm_num) (by norm_num : ((509 : ℝ) / 110) ≤ ((1851 : ℝ) / 400))
  exact hmono.trans cosh_b46275_ub

private lemma cosh5_v_508_le : cosh (509 : ℝ) / 550 ≤ (145973136 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((509 : ℝ) / 550) (by norm_num) (by norm_num : ((509 : ℝ) / 550) ≤ ((1851 : ℝ) / 2000))
  exact hmono.trans cosh_b9255_ub

private lemma sech5_pt_508_ge : (121 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (509 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_508_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_508_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_509_le : cosh (51 : ℝ) / 11 ≤ (5159613370 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((51 : ℝ) / 11) (by norm_num) (by norm_num : ((51 : ℝ) / 11) ≤ ((9273 : ℝ) / 2000))
  exact hmono.trans cosh_b46365_ub

private lemma cosh5_v_509_le : cosh (51 : ℝ) / 55 ≤ (146186108 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((51 : ℝ) / 55) (by norm_num) (by norm_num : ((51 : ℝ) / 55) ≤ ((371 : ℝ) / 400))
  exact hmono.trans cosh_b9275_ub

private lemma sech5_pt_509_ge : (120 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (51 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_509_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_509_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_510_le : cosh (511 : ℝ) / 110 ≤ (5206250761 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((511 : ℝ) / 110) (by norm_num) (by norm_num : ((511 : ℝ) / 110) ≤ ((9291 : ℝ) / 2000))
  exact hmono.trans cosh_b46455_ub

private lemma cosh5_v_510_le : cosh (511 : ℝ) / 550 ≤ (146399664 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((511 : ℝ) / 550) (by norm_num) (by norm_num : ((511 : ℝ) / 550) ≤ ((1859 : ℝ) / 2000))
  exact hmono.trans cosh_b9295_ub

private lemma sech5_pt_510_ge : (119 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (511 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_510_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_510_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_511_le : cosh (256 : ℝ) / 55 ≤ (5255936696 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((256 : ℝ) / 55) (by norm_num) (by norm_num : ((256 : ℝ) / 55) ≤ ((931 : ℝ) / 200))
  exact hmono.trans cosh_b46550_ub

private lemma cosh5_v_511_le : cosh (256 : ℝ) / 275 ≤ (146560216 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((256 : ℝ) / 275) (by norm_num) (by norm_num : ((256 : ℝ) / 275) ≤ ((931 : ℝ) / 1000))
  exact hmono.trans cosh_b9310_ub

private lemma sech5_pt_511_ge : (118 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (256 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_511_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_511_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_512_le : cosh (513 : ℝ) / 110 ≤ (5303445069 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((513 : ℝ) / 110) (by norm_num) (by norm_num : ((513 : ℝ) / 110) ≤ ((583 : ℝ) / 125))
  exact hmono.trans cosh_b46640_ub

private lemma cosh5_v_512_le : cosh (513 : ℝ) / 550 ≤ (146774798 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((513 : ℝ) / 550) (by norm_num) (by norm_num : ((513 : ℝ) / 550) ≤ ((933 : ℝ) / 1000))
  exact hmono.trans cosh_b9330_ub

private lemma sech5_pt_512_ge : (116 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (513 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_512_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_512_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_513_le : cosh (257 : ℝ) / 55 ≤ (5351383024 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((257 : ℝ) / 55) (by norm_num) (by norm_num : ((257 : ℝ) / 55) ≤ ((4673 : ℝ) / 1000))
  exact hmono.trans cosh_b46730_ub

private lemma cosh5_v_513_le : cosh (257 : ℝ) / 275 ≤ (146989967 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((257 : ℝ) / 275) (by norm_num) (by norm_num : ((257 : ℝ) / 275) ≤ ((187 : ℝ) / 200))
  exact hmono.trans cosh_b9350_ub

private lemma sech5_pt_513_ge : (115 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (257 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_513_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_513_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_514_le : cosh (103 : ℝ) / 22 ≤ (5399754444 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((103 : ℝ) / 22) (by norm_num) (by norm_num : ((103 : ℝ) / 22) ≤ ((2341 : ℝ) / 500))
  exact hmono.trans cosh_b46820_ub

private lemma cosh5_v_514_le : cosh (103 : ℝ) / 110 ≤ (147151729 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((103 : ℝ) / 110) (by norm_num) (by norm_num : ((103 : ℝ) / 110) ≤ ((1873 : ℝ) / 2000))
  exact hmono.trans cosh_b9365_ub

private lemma sech5_pt_514_ge : (114 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (103 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_514_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_514_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_515_le : cosh (258 : ℝ) / 55 ≤ (5448563247 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((258 : ℝ) / 55) (by norm_num) (by norm_num : ((258 : ℝ) / 55) ≤ ((4691 : ℝ) / 1000))
  exact hmono.trans cosh_b46910_ub

private lemma cosh5_v_515_le : cosh (258 : ℝ) / 275 ≤ (147367928 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((258 : ℝ) / 275) (by norm_num) (by norm_num : ((258 : ℝ) / 275) ≤ ((1877 : ℝ) / 2000))
  exact hmono.trans cosh_b9385_ub

private lemma sech5_pt_515_ge : (113 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (258 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_515_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_515_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_516_le : cosh (47 : ℝ) / 10 ≤ (5497813387 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((47 : ℝ) / 10) (by norm_num) (by norm_num : ((47 : ℝ) / 10) ≤ ((47 : ℝ) / 10))
  exact hmono.trans cosh_b47000_ub

private lemma cosh5_v_516_le : cosh (47 : ℝ) / 50 ≤ (147530463 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((47 : ℝ) / 50) (by norm_num) (by norm_num : ((47 : ℝ) / 50) ≤ ((47 : ℝ) / 50))
  exact hmono.trans cosh_b9400_ub

private lemma sech5_pt_516_ge : (112 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_516_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_516_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_517_le : cosh (259 : ℝ) / 55 ≤ (5550282850 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((259 : ℝ) / 55) (by norm_num) (by norm_num : ((259 : ℝ) / 55) ≤ ((9419 : ℝ) / 2000))
  exact hmono.trans cosh_b47095_ub

private lemma cosh5_v_517_le : cosh (259 : ℝ) / 275 ≤ (147747694 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((259 : ℝ) / 275) (by norm_num) (by norm_num : ((259 : ℝ) / 275) ≤ ((471 : ℝ) / 500))
  exact hmono.trans cosh_b9420_ub

private lemma sech5_pt_517_ge : (110 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (259 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_517_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_517_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_518_le : cosh (519 : ℝ) / 110 ≤ (5600452749 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((519 : ℝ) / 110) (by norm_num) (by norm_num : ((519 : ℝ) / 110) ≤ ((9437 : ℝ) / 2000))
  exact hmono.trans cosh_b47185_ub

private lemma cosh5_v_518_le : cosh (519 : ℝ) / 550 ≤ (147965515 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((519 : ℝ) / 550) (by norm_num) (by norm_num : ((519 : ℝ) / 550) ≤ ((118 : ℝ) / 125))
  exact hmono.trans cosh_b9440_ub

private lemma sech5_pt_518_ge : (109 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (519 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_518_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_518_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_519_le : cosh (52 : ℝ) / 11 ≤ (5651076289 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((52 : ℝ) / 11) (by norm_num) (by norm_num : ((52 : ℝ) / 11) ≤ ((1891 : ℝ) / 400))
  exact hmono.trans cosh_b47275_ub

private lemma cosh5_v_519_le : cosh (52 : ℝ) / 55 ≤ (148129270 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((52 : ℝ) / 55) (by norm_num) (by norm_num : ((52 : ℝ) / 55) ≤ ((1891 : ℝ) / 2000))
  exact hmono.trans cosh_b9455_ub

private lemma sech5_pt_519_ge : (108 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (52 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_519_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_519_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_520_le : cosh (521 : ℝ) / 110 ≤ (5702157568 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((521 : ℝ) / 110) (by norm_num) (by norm_num : ((521 : ℝ) / 110) ≤ ((9473 : ℝ) / 2000))
  exact hmono.trans cosh_b47365_ub

private lemma cosh5_v_520_le : cosh (521 : ℝ) / 550 ≤ (148348128 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((521 : ℝ) / 550) (by norm_num) (by norm_num : ((521 : ℝ) / 550) ≤ ((379 : ℝ) / 400))
  exact hmono.trans cosh_b9475_ub

private lemma sech5_pt_520_ge : (107 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (521 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_520_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_520_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_521_le : cosh (261 : ℝ) / 55 ≤ (5753700725 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((261 : ℝ) / 55) (by norm_num) (by norm_num : ((261 : ℝ) / 55) ≤ ((9491 : ℝ) / 2000))
  exact hmono.trans cosh_b47455_ub

private lemma cosh5_v_521_le : cosh (261 : ℝ) / 275 ≤ (148567579 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((261 : ℝ) / 275) (by norm_num) (by norm_num : ((261 : ℝ) / 275) ≤ ((1899 : ℝ) / 2000))
  exact hmono.trans cosh_b9495_ub

private lemma sech5_pt_521_ge : (106 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (261 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_521_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_521_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_522_le : cosh (523 : ℝ) / 110 ≤ (5808613086 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((523 : ℝ) / 110) (by norm_num) (by norm_num : ((523 : ℝ) / 110) ≤ ((951 : ℝ) / 200))
  exact hmono.trans cosh_b47550_ub

private lemma cosh5_v_522_le : cosh (523 : ℝ) / 550 ≤ (148732557 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((523 : ℝ) / 550) (by norm_num) (by norm_num : ((523 : ℝ) / 550) ≤ ((951 : ℝ) / 1000))
  exact hmono.trans cosh_b9510_ub

private lemma sech5_pt_522_ge : (105 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (523 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_522_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_522_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_523_le : cosh (262 : ℝ) / 55 ≤ (5861118812 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((262 : ℝ) / 55) (by norm_num) (by norm_num : ((262 : ℝ) / 55) ≤ ((1191 : ℝ) / 250))
  exact hmono.trans cosh_b47640_ub

private lemma cosh5_v_523_le : cosh (262 : ℝ) / 275 ≤ (148953049 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((262 : ℝ) / 275) (by norm_num) (by norm_num : ((262 : ℝ) / 275) ≤ ((953 : ℝ) / 1000))
  exact hmono.trans cosh_b9530_ub

private lemma sech5_pt_523_ge : (104 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (262 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_523_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_523_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_524_le : cosh (105 : ℝ) / 22 ≤ (5914099292 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((105 : ℝ) / 22) (by norm_num) (by norm_num : ((105 : ℝ) / 22) ≤ ((4773 : ℝ) / 1000))
  exact hmono.trans cosh_b47730_ub

private lemma cosh5_v_524_le : cosh (21 : ℝ) / 22 ≤ (149174137 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((21 : ℝ) / 22) (by norm_num) (by norm_num : ((21 : ℝ) / 22) ≤ ((191 : ℝ) / 200))
  exact hmono.trans cosh_b9550_ub

private lemma sech5_pt_524_ge : (103 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (105 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_524_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_524_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_525_le : cosh (263 : ℝ) / 55 ≤ (5967558817 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((263 : ℝ) / 55) (by norm_num) (by norm_num : ((263 : ℝ) / 55) ≤ ((2391 : ℝ) / 500))
  exact hmono.trans cosh_b47820_ub

private lemma cosh5_v_525_le : cosh (263 : ℝ) / 275 ≤ (149340344 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((263 : ℝ) / 275) (by norm_num) (by norm_num : ((263 : ℝ) / 275) ≤ ((1913 : ℝ) / 2000))
  exact hmono.trans cosh_b9565_ub

private lemma sech5_pt_525_ge : (102 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (263 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_525_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_525_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_526_le : cosh (527 : ℝ) / 110 ≤ (6021501718 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((527 : ℝ) / 110) (by norm_num) (by norm_num : ((527 : ℝ) / 110) ≤ ((4791 : ℝ) / 1000))
  exact hmono.trans cosh_b47910_ub

private lemma cosh5_v_526_le : cosh (527 : ℝ) / 550 ≤ (149562477 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((527 : ℝ) / 550) (by norm_num) (by norm_num : ((527 : ℝ) / 550) ≤ ((1917 : ℝ) / 2000))
  exact hmono.trans cosh_b9585_ub

private lemma sech5_pt_526_ge : (100 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (527 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_526_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_526_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_527_le : cosh (24 : ℝ) / 5 ≤ (6075932364 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((24 : ℝ) / 5) (by norm_num) (by norm_num : ((24 : ℝ) / 5) ≤ ((24 : ℝ) / 5))
  exact hmono.trans cosh_b48000_ub

private lemma cosh5_v_527_le : cosh (24 : ℝ) / 25 ≤ (149729468 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((24 : ℝ) / 25) (by norm_num) (by norm_num : ((24 : ℝ) / 25) ≤ ((24 : ℝ) / 25))
  exact hmono.trans cosh_b9600_ub

private lemma sech5_pt_527_ge : (99 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (24 : ℝ) / 5 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_527_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_527_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_528_le : cosh (529 : ℝ) / 110 ≤ (6133920950 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((529 : ℝ) / 110) (by norm_num) (by norm_num : ((529 : ℝ) / 110) ≤ ((9619 : ℝ) / 2000))
  exact hmono.trans cosh_b48095_ub

private lemma cosh5_v_528_le : cosh (529 : ℝ) / 550 ≤ (149952648 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((529 : ℝ) / 550) (by norm_num) (by norm_num : ((529 : ℝ) / 550) ≤ ((481 : ℝ) / 500))
  exact hmono.trans cosh_b9620_ub

private lemma sech5_pt_528_ge : (98 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (529 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_528_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_528_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_529_le : cosh (53 : ℝ) / 11 ≤ (6189368072 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((53 : ℝ) / 11) (by norm_num) (by norm_num : ((53 : ℝ) / 11) ≤ ((9637 : ℝ) / 2000))
  exact hmono.trans cosh_b48185_ub

private lemma cosh5_v_529_le : cosh (53 : ℝ) / 55 ≤ (150176428 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((53 : ℝ) / 55) (by norm_num) (by norm_num : ((53 : ℝ) / 55) ≤ ((241 : ℝ) / 250))
  exact hmono.trans cosh_b9640_ub

private lemma sech5_pt_529_ge : (97 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (53 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_529_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_529_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_530_le : cosh (531 : ℝ) / 110 ≤ (6245316537 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((531 : ℝ) / 110) (by norm_num) (by norm_num : ((531 : ℝ) / 110) ≤ ((1931 : ℝ) / 400))
  exact hmono.trans cosh_b48275_ub

private lemma cosh5_v_530_le : cosh (531 : ℝ) / 550 ≤ (150344657 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((531 : ℝ) / 550) (by norm_num) (by norm_num : ((531 : ℝ) / 550) ≤ ((1931 : ℝ) / 2000))
  exact hmono.trans cosh_b9655_ub

private lemma sech5_pt_530_ge : (96 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (531 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_530_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_530_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_531_le : cosh (266 : ℝ) / 55 ≤ (6301770875 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((266 : ℝ) / 55) (by norm_num) (by norm_num : ((266 : ℝ) / 55) ≤ ((9673 : ℝ) / 2000))
  exact hmono.trans cosh_b48365_ub

private lemma cosh5_v_531_le : cosh (266 : ℝ) / 275 ≤ (150569489 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((266 : ℝ) / 275) (by norm_num) (by norm_num : ((266 : ℝ) / 275) ≤ ((387 : ℝ) / 400))
  exact hmono.trans cosh_b9675_ub

private lemma sech5_pt_531_ge : (95 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (266 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_531_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_531_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_532_le : cosh (533 : ℝ) / 110 ≤ (6358735661 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((533 : ℝ) / 110) (by norm_num) (by norm_num : ((533 : ℝ) / 110) ≤ ((9691 : ℝ) / 2000))
  exact hmono.trans cosh_b48455_ub

private lemma cosh5_v_532_le : cosh (533 : ℝ) / 550 ≤ (150794923 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((533 : ℝ) / 550) (by norm_num) (by norm_num : ((533 : ℝ) / 550) ≤ ((1939 : ℝ) / 2000))
  exact hmono.trans cosh_b9695_ub

private lemma sech5_pt_532_ge : (94 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (533 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_532_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_532_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_533_le : cosh (267 : ℝ) / 55 ≤ (6419424028 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((267 : ℝ) / 55) (by norm_num) (by norm_num : ((267 : ℝ) / 55) ≤ ((971 : ℝ) / 200))
  exact hmono.trans cosh_b48550_ub

private lemma cosh5_v_533_le : cosh (267 : ℝ) / 275 ≤ (150964394 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((267 : ℝ) / 275) (by norm_num) (by norm_num : ((267 : ℝ) / 275) ≤ ((971 : ℝ) / 1000))
  exact hmono.trans cosh_b9710_ub

private lemma sech5_pt_533_ge : (93 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (267 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_533_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_533_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_534_le : cosh (107 : ℝ) / 22 ≤ (6477452602 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((107 : ℝ) / 22) (by norm_num) (by norm_num : ((107 : ℝ) / 22) ≤ ((608 : ℝ) / 125))
  exact hmono.trans cosh_b48640_ub

private lemma cosh5_v_534_le : cosh (107 : ℝ) / 110 ≤ (151190884 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((107 : ℝ) / 110) (by norm_num) (by norm_num : ((107 : ℝ) / 110) ≤ ((973 : ℝ) / 1000))
  exact hmono.trans cosh_b9730_ub

private lemma sech5_pt_534_ge : (92 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (107 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_534_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_534_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_535_le : cosh (268 : ℝ) / 55 ≤ (6536005853 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((268 : ℝ) / 55) (by norm_num) (by norm_num : ((268 : ℝ) / 55) ≤ ((4873 : ℝ) / 1000))
  exact hmono.trans cosh_b48730_ub

private lemma cosh5_v_535_le : cosh (268 : ℝ) / 275 ≤ (151417979 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((268 : ℝ) / 275) (by norm_num) (by norm_num : ((268 : ℝ) / 275) ≤ ((39 : ℝ) / 40))
  exact hmono.trans cosh_b9750_ub

private lemma sech5_pt_535_ge : (91 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (268 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_535_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_535_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_536_le : cosh (537 : ℝ) / 110 ≤ (6595088525 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((537 : ℝ) / 110) (by norm_num) (by norm_num : ((537 : ℝ) / 110) ≤ ((2441 : ℝ) / 500))
  exact hmono.trans cosh_b48820_ub

private lemma cosh5_v_536_le : cosh (537 : ℝ) / 550 ≤ (151588697 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((537 : ℝ) / 550) (by norm_num) (by norm_num : ((537 : ℝ) / 550) ≤ ((1953 : ℝ) / 2000))
  exact hmono.trans cosh_b9765_ub

private lemma sech5_pt_536_ge : (90 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (537 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_536_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_536_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_537_le : cosh (269 : ℝ) / 55 ≤ (6654705402 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((269 : ℝ) / 55) (by norm_num) (by norm_num : ((269 : ℝ) / 55) ≤ ((4891 : ℝ) / 1000))
  exact hmono.trans cosh_b48910_ub

private lemma cosh5_v_537_le : cosh (269 : ℝ) / 275 ≤ (151816853 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((269 : ℝ) / 275) (by norm_num) (by norm_num : ((269 : ℝ) / 275) ≤ ((1957 : ℝ) / 2000))
  exact hmono.trans cosh_b9785_ub

private lemma sech5_pt_537_ge : (89 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (269 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_537_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_537_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_538_le : cosh (49 : ℝ) / 10 ≤ (6714861314 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((49 : ℝ) / 10) (by norm_num) (by norm_num : ((49 : ℝ) / 10) ≤ ((49 : ℝ) / 10))
  exact hmono.trans cosh_b49000_ub

private lemma cosh5_v_538_le : cosh (49 : ℝ) / 50 ≤ (151988368 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((49 : ℝ) / 50) (by norm_num) (by norm_num : ((49 : ℝ) / 50) ≤ ((49 : ℝ) / 50))
  exact hmono.trans cosh_b9800_ub

private lemma sech5_pt_538_ge : (89 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 10 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_538_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_538_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_539_le : cosh (54 : ℝ) / 11 ≤ (6778949392 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((54 : ℝ) / 11) (by norm_num) (by norm_num : ((54 : ℝ) / 11) ≤ ((9819 : ℝ) / 2000))
  exact hmono.trans cosh_b49095_ub

private lemma cosh5_v_539_le : cosh (54 : ℝ) / 55 ≤ (152217586 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((54 : ℝ) / 55) (by norm_num) (by norm_num : ((54 : ℝ) / 55) ≤ ((491 : ℝ) / 500))
  exact hmono.trans cosh_b9820_ub

private lemma sech5_pt_539_ge : (88 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (54 : ℝ) / 11 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_539_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_539_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_540_le : cosh (541 : ℝ) / 110 ≤ (6840228671 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((541 : ℝ) / 110) (by norm_num) (by norm_num : ((541 : ℝ) / 110) ≤ ((9837 : ℝ) / 2000))
  exact hmono.trans cosh_b49185_ub

private lemma cosh5_v_540_le : cosh (541 : ℝ) / 550 ≤ (152447414 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((541 : ℝ) / 550) (by norm_num) (by norm_num : ((541 : ℝ) / 550) ≤ ((123 : ℝ) / 125))
  exact hmono.trans cosh_b9840_ub

private lemma sech5_pt_540_ge : (87 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (541 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_540_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_540_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_541_le : cosh (271 : ℝ) / 55 ≤ (6902062012 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((271 : ℝ) / 55) (by norm_num) (by norm_num : ((271 : ℝ) / 55) ≤ ((1971 : ℝ) / 400))
  exact hmono.trans cosh_b49275_ub

private lemma cosh5_v_541_le : cosh (271 : ℝ) / 275 ≤ (152620184 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((271 : ℝ) / 275) (by norm_num) (by norm_num : ((271 : ℝ) / 275) ≤ ((1971 : ℝ) / 2000))
  exact hmono.trans cosh_b9855_ub

private lemma sech5_pt_541_ge : (86 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (271 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_541_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_541_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_542_le : cosh (543 : ℝ) / 110 ≤ (6964454424 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((543 : ℝ) / 110) (by norm_num) (by norm_num : ((543 : ℝ) / 110) ≤ ((9873 : ℝ) / 2000))
  exact hmono.trans cosh_b49365_ub

private lemma cosh5_v_542_le : cosh (543 : ℝ) / 550 ≤ (152851080 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((543 : ℝ) / 550) (by norm_num) (by norm_num : ((543 : ℝ) / 550) ≤ ((79 : ℝ) / 80))
  exact hmono.trans cosh_b9875_ub

private lemma sech5_pt_542_ge : (85 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (543 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_542_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_542_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_543_le : cosh (272 : ℝ) / 55 ≤ (7027410960 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((272 : ℝ) / 55) (by norm_num) (by norm_num : ((272 : ℝ) / 55) ≤ ((9891 : ℝ) / 2000))
  exact hmono.trans cosh_b49455_ub

private lemma cosh5_v_543_le : cosh (272 : ℝ) / 275 ≤ (153082586 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((272 : ℝ) / 275) (by norm_num) (by norm_num : ((272 : ℝ) / 275) ≤ ((1979 : ℝ) / 2000))
  exact hmono.trans cosh_b9895_ub

private lemma sech5_pt_543_ge : (84 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (272 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_543_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_543_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_544_le : cosh (109 : ℝ) / 22 ≤ (7094482723 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((109 : ℝ) / 22) (by norm_num) (by norm_num : ((109 : ℝ) / 22) ≤ ((991 : ℝ) / 200))
  exact hmono.trans cosh_b49550_ub

private lemma cosh5_v_544_le : cosh (109 : ℝ) / 110 ≤ (153256618 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((109 : ℝ) / 110) (by norm_num) (by norm_num : ((109 : ℝ) / 110) ≤ ((991 : ℝ) / 1000))
  exact hmono.trans cosh_b9910_ub

private lemma sech5_pt_544_ge : (83 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (109 : ℝ) / 22 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_544_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_544_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_545_le : cosh (273 : ℝ) / 55 ≤ (7158614915 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((273 : ℝ) / 55) (by norm_num) (by norm_num : ((273 : ℝ) / 55) ≤ ((1241 : ℝ) / 250))
  exact hmono.trans cosh_b49640_ub

private lemma cosh5_v_545_le : cosh (273 : ℝ) / 275 ≤ (153489197 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((273 : ℝ) / 275) (by norm_num) (by norm_num : ((273 : ℝ) / 275) ≤ ((993 : ℝ) / 1000))
  exact hmono.trans cosh_b9930_ub

private lemma sech5_pt_545_ge : (82 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (273 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_545_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_545_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_546_le : cosh (547 : ℝ) / 110 ≤ (7223326958 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((547 : ℝ) / 110) (by norm_num) (by norm_num : ((547 : ℝ) / 110) ≤ ((4973 : ℝ) / 1000))
  exact hmono.trans cosh_b49730_ub

private lemma cosh5_v_546_le : cosh (547 : ℝ) / 550 ≤ (153722390 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((547 : ℝ) / 550) (by norm_num) (by norm_num : ((547 : ℝ) / 550) ≤ ((199 : ℝ) / 200))
  exact hmono.trans cosh_b9950_ub

private lemma sech5_pt_546_ge : (81 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (547 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_546_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_546_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_547_le : cosh (274 : ℝ) / 55 ≤ (7288624095 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((274 : ℝ) / 55) (by norm_num) (by norm_num : ((274 : ℝ) / 55) ≤ ((2491 : ℝ) / 500))
  exact hmono.trans cosh_b49820_ub

private lemma cosh5_v_547_le : cosh (274 : ℝ) / 275 ≤ (153897688 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((274 : ℝ) / 275) (by norm_num) (by norm_num : ((274 : ℝ) / 275) ≤ ((1993 : ℝ) / 2000))
  exact hmono.trans cosh_b9965_ub

private lemma sech5_pt_547_ge : (81 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (274 : ℝ) / 55 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_547_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_547_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_548_le : cosh (549 : ℝ) / 110 ≤ (7354511614 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((549 : ℝ) / 110) (by norm_num) (by norm_num : ((549 : ℝ) / 110) ≤ ((4991 : ℝ) / 1000))
  exact hmono.trans cosh_b49910_ub

private lemma cosh5_v_548_le : cosh (549 : ℝ) / 550 ≤ (154131957 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((549 : ℝ) / 550) (by norm_num) (by norm_num : ((549 : ℝ) / 550) ≤ ((1997 : ℝ) / 2000))
  exact hmono.trans cosh_b9985_ub

private lemma sech5_pt_548_ge : (80 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (549 : ℝ) / 110 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_548_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_548_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma cosh5_u_549_le : cosh (5 : ℝ) / 1 ≤ (7420994853 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((5 : ℝ) / 1) (by norm_num) (by norm_num : ((5 : ℝ) / 1) ≤ ((5 : ℝ) / 1))
  exact hmono.trans cosh_b50000_ub

private lemma cosh5_v_549_le : cosh (1 : ℝ) / 1 ≤ (154308064 : ℝ) / 100000000 := by
  have hmono := cosh_mono_Ici ((1 : ℝ) / 1) (by norm_num) (by norm_num : ((1 : ℝ) / 1) ≤ ((1 : ℝ) / 1))
  exact hmono.trans cosh_b10000_ub

private lemma sech5_pt_549_ge : (79 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (5 : ℝ) / 1 := by
  unfold sechProd; unfold sech
  have hc1 := sech_ge_of_cosh_le (by norm_num) (cosh5_u_549_le)
  have hc2 := sech_ge_of_cosh_le (by norm_num) (cosh5_v_549_le)
  have hprod := mul_le_mul hc1 hc2 (by norm_num) (by norm_num)
  norm_num at hprod ⊢; linarith

private lemma sech5_batch_10_ge : (5184 : ℝ) / 1000000 ≤ ((1 : ℝ) / 110 : ℝ) * sechProd 5 (501 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (251 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (503 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (252 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (101 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (507 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (254 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (509 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (51 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (511 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (256 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (513 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (257 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (103 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (258 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (259 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (519 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (52 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (521 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (261 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (523 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (262 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (105 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (263 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (527 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (24 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (529 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (53 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (531 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (266 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (533 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (267 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (107 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (268 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (537 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (269 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (54 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (541 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (271 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (543 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (272 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (109 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (273 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (547 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (274 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (549 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (5 : ℝ) / 1 := by
  linarith [sech5_pt_500_ge, sech5_pt_501_ge, sech5_pt_502_ge, sech5_pt_503_ge, sech5_pt_504_ge, sech5_pt_505_ge, sech5_pt_506_ge, sech5_pt_507_ge, sech5_pt_508_ge, sech5_pt_509_ge, sech5_pt_510_ge, sech5_pt_511_ge, sech5_pt_512_ge, sech5_pt_513_ge, sech5_pt_514_ge, sech5_pt_515_ge, sech5_pt_516_ge, sech5_pt_517_ge, sech5_pt_518_ge, sech5_pt_519_ge, sech5_pt_520_ge, sech5_pt_521_ge, sech5_pt_522_ge, sech5_pt_523_ge, sech5_pt_524_ge, sech5_pt_525_ge, sech5_pt_526_ge, sech5_pt_527_ge, sech5_pt_528_ge, sech5_pt_529_ge, sech5_pt_530_ge, sech5_pt_531_ge, sech5_pt_532_ge, sech5_pt_533_ge, sech5_pt_534_ge, sech5_pt_535_ge, sech5_pt_536_ge, sech5_pt_537_ge, sech5_pt_538_ge, sech5_pt_539_ge, sech5_pt_540_ge, sech5_pt_541_ge, sech5_pt_542_ge, sech5_pt_543_ge, sech5_pt_544_ge, sech5_pt_545_ge, sech5_pt_546_ge, sech5_pt_547_ge, sech5_pt_548_ge, sech5_pt_549_ge]

lemma sech5_halfline_meshSum_ge : (1492288 : ℝ) / 1000000 ≤ (((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (2 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (4 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (6 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (8 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (2 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (12 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (5 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (14 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (16 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (18 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (4 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (2 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (24 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (5 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (51 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (26 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (53 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 2 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (28 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (57 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (59 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (6 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (61 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (63 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (32 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (67 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (34 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (69 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (71 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (36 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (73 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (15 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (38 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (79 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (8 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (81 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (83 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (42 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (87 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (4 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (89 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (91 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (46 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (93 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (48 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (97 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (10 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (101 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (51 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (103 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (52 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (53 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (107 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (54 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (109 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (1 : ℝ) / 1 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (111 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (56 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (113 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (57 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (58 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (117 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (59 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (119 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (12 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (11 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (61 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (123 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (62 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (25 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (63 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (127 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (64 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (129 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (131 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (6 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (133 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (67 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (68 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (137 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (69 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (139 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (14 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (141 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (71 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (72 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (73 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (147 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (74 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (149 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (15 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (151 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (76 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (153 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (78 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (157 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (79 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (159 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (16 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (161 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (81 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (163 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (82 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 2 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (83 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (167 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (84 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (169 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (171 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (86 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (173 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (87 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (35 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (8 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (177 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (89 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (179 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (18 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (181 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (91 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (183 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (92 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (93 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (94 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (189 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (191 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (96 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (193 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (97 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (98 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (197 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (199 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (20 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (201 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (101 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (203 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (102 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (103 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (207 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (104 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (211 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (106 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (213 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (107 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (108 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (217 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (109 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (219 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (2 : ℝ) / 1 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (221 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (111 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (223 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (112 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (45 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (113 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (227 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (114 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (229 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (116 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (233 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (117 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (118 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (237 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (119 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (239 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (24 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (241 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (11 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (243 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (122 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (123 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (247 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (124 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (249 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (25 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (251 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (126 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (127 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (51 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (128 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (257 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (129 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (259 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (26 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (261 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (131 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (263 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (12 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (53 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (133 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (267 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (134 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (269 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (271 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (136 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (273 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (137 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (5 : ℝ) / 2 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (138 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (277 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (139 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (279 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (28 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (281 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (141 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (283 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (142 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (57 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (13 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (287 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (144 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (289 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (291 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (146 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (293 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (147 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (59 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (148 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (27 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (149 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (299 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (30 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (301 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (151 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (303 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (152 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (61 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (153 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (307 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (14 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (309 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (311 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (156 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (313 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (157 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (63 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (158 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (317 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (159 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (29 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (32 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (321 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (161 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (323 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (162 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (65 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (163 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (327 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (164 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (329 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (3 : ℝ) / 1 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (331 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (166 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (333 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (167 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (67 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (168 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (337 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (169 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (339 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (34 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (31 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (171 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (343 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (172 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (69 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (173 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (347 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (174 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (349 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (35 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (351 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (16 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (353 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (177 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (71 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (178 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (357 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (179 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (359 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (36 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (361 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (181 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (33 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (182 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (73 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (183 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (367 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (184 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (369 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (371 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (186 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (373 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (17 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (75 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (188 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (377 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (189 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (379 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (38 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (381 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (191 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (383 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (192 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (7 : ℝ) / 2 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (193 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (387 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (194 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (389 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (391 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (196 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (393 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (197 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (79 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (18 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (397 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (199 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (399 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (40 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (401 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (201 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (403 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (202 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (81 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (203 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (37 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (204 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (409 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (411 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (206 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (413 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (207 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (83 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (208 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (417 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (19 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (419 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (42 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (421 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (211 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (423 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (212 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (85 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (213 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (427 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (214 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (39 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (431 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (216 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (433 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (217 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (87 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (218 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (437 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (219 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (439 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (4 : ℝ) / 1 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (441 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (221 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (443 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (222 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (89 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (223 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (447 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (224 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (449 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (45 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (41 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (226 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (453 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (227 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (91 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (228 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (457 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (229 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (459 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (46 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (461 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (21 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (463 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (232 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (93 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (233 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (467 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (234 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (469 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (471 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (236 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (43 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (237 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (95 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (238 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (477 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (239 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (479 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (48 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (481 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (241 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (483 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (22 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (97 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (243 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (487 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (244 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (489 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (491 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (246 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (493 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (247 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (9 : ℝ) / 2 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (248 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (497 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (249 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (499 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (50 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (501 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (251 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (503 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (252 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (101 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (23 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (507 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (254 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (509 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (51 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (511 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (256 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (513 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (257 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (103 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (258 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (47 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (259 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (519 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (52 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (521 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (261 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (523 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (262 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (105 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (263 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (527 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (24 : ℝ) / 5 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (529 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (53 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (531 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (266 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (533 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (267 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (107 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (268 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (537 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (269 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (49 : ℝ) / 10 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (54 : ℝ) / 11 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (541 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (271 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (543 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (272 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (109 : ℝ) / 22 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (273 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (547 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (274 : ℝ) / 55 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (549 : ℝ) / 110 + ((1 : ℝ) / 110 : ℝ) * sechProd 5 (5 : ℝ) / 1) := by
  linarith [sech5_batch_0_ge, sech5_batch_1_ge, sech5_batch_2_ge, sech5_batch_3_ge, sech5_batch_4_ge, sech5_batch_5_ge, sech5_batch_6_ge, sech5_batch_7_ge, sech5_batch_8_ge, sech5_batch_9_ge, sech5_batch_10_ge]

end UgpLean.Substrate.PhiMDLFluctuationSpectrum
