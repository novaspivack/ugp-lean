import UgpLean.Substrate.SechOverlapIntegralBounds_bridge

/-!
# Sech overlap integral lower bounds (Riemann certification)

Route: `r·I(r) = ∫ sech(u/r)·sech(u) du`, restrict to a symmetric interval, lower-bound
by an antitone right-endpoint Riemann sum, certify the sum with mesh-generated bounds.

Mesh generators: `scripts/gen_sech5_cosh_bins.py`, `scripts/gen_sech5_mesh_proof.py`,
`scripts/gen_sech11_mesh_proof.py`. Helper lemmas: `SechOverlapIntegralBounds_cosh.lean`.
Certified mesh proofs: `SechOverlapIntegralBounds_r5mesh.lean`,
`SechOverlapIntegralBounds_r11cert.lean`. CatA integral bridge:
`SechOverlapIntegralBounds_bridge.lean`.
-/

namespace UgpLean.Substrate.PhiMDLFluctuationSpectrum

/-- **sech_overlap_at_five_ge_pi** (CatAL): `I(5) ≥ 0.95·π/5`. -/
theorem sech_overlap_at_five_ge_pi : (0.95 : ℝ) * Real.pi / 5 ≤ sech_overlap 5 :=
  sech_overlap_target_five_le_cert.trans sech_overlap_at_five_ge

/-- **sech_overlap_at_eleven_ge_pi** (CatAL): `I(11) ≥ 0.99·π/11`. -/
theorem sech_overlap_at_eleven_ge_pi : (0.99 : ℝ) * Real.pi / 11 ≤ sech_overlap 11 :=
  sech_overlap_target_eleven_le_cert.trans sech_overlap_at_eleven_ge

/-- **sech_overlap_at_five_ge_596_thousand** (CatAL): `I(5) ≥ 596/1000` from `596903/10⁶`. -/
theorem sech_overlap_at_five_ge_596_thousand : (596 : ℝ) / 1000 ≤ sech_overlap 5 :=
  le_trans (by norm_num) sech_overlap_at_five_ge

/-- **sech_overlap_at_eleven_ge_282_thousand** (CatAL): `I(11) ≥ 282/1000` from `282771/10⁶`. -/
theorem sech_overlap_at_eleven_ge_282_thousand : (282 : ℝ) / 1000 ≤ sech_overlap 11 :=
  le_trans (by norm_num) sech_overlap_at_eleven_ge

/-- Finite-`r` correction factor `5·I(5)/π` lower bound from certified `I(5)` and `π < 3141593/10⁶`. -/
theorem sech_overlap_five_ratio_ge : (2984515 : ℝ) / 3141593 ≤ 5 * sech_overlap 5 / Real.pi := by
  have hI5 : (2984515 : ℝ) / 1000000 ≤ 5 * sech_overlap 5 := by
    have h :=
      mul_le_mul_of_nonneg_left sech_overlap_at_five_ge (by norm_num : (0 : ℝ) ≤ 5)
    simpa [mul_div_assoc, show (5 : ℝ) * (596903 / 1000000) = 2984515 / 1000000 from by ring] using h
  have hπ := Real.pi_lt_d6
  have hposπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [le_div_iff₀ hposπ]
  have hπstep : (2984515 : ℝ) / 3141593 * Real.pi ≤ (2984515 : ℝ) / 1000000 := by
    have hπ' : Real.pi ≤ (3141593 : ℝ) / 1000000 := by
      have h := le_of_lt hπ
      simpa [show (3.141593 : ℝ) = (3141593 : ℝ) / 1000000 from by norm_num] using h
    calc
      (2984515 : ℝ) / 3141593 * Real.pi
          ≤ (2984515 : ℝ) / 3141593 * ((3141593 : ℝ) / 1000000) := by gcongr
      _ = (2984515 : ℝ) / 1000000 := by field_simp
  exact hπstep.trans hI5

/-- Finite-`r` correction factor `11·I(11)/π` lower bound from certified `I(11)` and `π < 3141593/10⁶`. -/
theorem sech_overlap_eleven_ratio_ge :
    (3110481 : ℝ) / 3141593 ≤ 11 * sech_overlap 11 / Real.pi := by
  have hI11 : (3110481 : ℝ) / 1000000 ≤ 11 * sech_overlap 11 := by
    have h :=
      mul_le_mul_of_nonneg_left sech_overlap_at_eleven_ge (by norm_num : (0 : ℝ) ≤ 11)
    simpa [mul_div_assoc, show (11 : ℝ) * (282771 / 1000000) = 3110481 / 1000000 from by ring] using h
  have hπ := Real.pi_lt_d6
  have hposπ : (0 : ℝ) < Real.pi := Real.pi_pos
  rw [le_div_iff₀ hposπ]
  have hπstep : (3110481 : ℝ) / 3141593 * Real.pi ≤ (3110481 : ℝ) / 1000000 := by
    have hπ' : Real.pi ≤ (3141593 : ℝ) / 1000000 := by
      have h := le_of_lt hπ
      simpa [show (3.141593 : ℝ) = (3141593 : ℝ) / 1000000 from by norm_num] using h
    calc
      (3110481 : ℝ) / 3141593 * Real.pi
          ≤ (3110481 : ℝ) / 3141593 * ((3141593 : ℝ) / 1000000) := by gcongr
      _ = (3110481 : ℝ) / 1000000 := by field_simp
  exact hπstep.trans hI11

end UgpLean.Substrate.PhiMDLFluctuationSpectrum
