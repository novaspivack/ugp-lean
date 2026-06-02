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

end UgpLean.Substrate.PhiMDLFluctuationSpectrum
