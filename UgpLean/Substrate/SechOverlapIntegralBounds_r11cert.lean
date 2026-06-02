import UgpLean.Substrate.PhiMDLFluctuationSpectrum

namespace UgpLean.Substrate.PhiMDLFluctuationSpectrum

open Real

/-- Certified half-line mesh micro-units for `r = 11` (uniform mesh on `[0,12]`, step `1/5000`). -/
def sechScaledElevenMeshHalfMicro : Nat := 1555295

lemma sechScaledElevenMeshHalfMicro_ge_target : 1555241 ≤ sechScaledElevenMeshHalfMicro := by
  norm_num [sechScaledElevenMeshHalfMicro]

/-- Computed right-endpoint Riemann micro-sum (`scripts/gen_sech_overlap_bounds.py`). -/
def sech11_uniform_meshSum : Nat := 1555296

lemma sech11_uniform_mesh_ge : sechScaledElevenMeshHalfMicro ≤ sech11_uniform_meshSum := by
  norm_num [sechScaledElevenMeshHalfMicro, sech11_uniform_meshSum]

lemma sech11_uniform_mesh_ge' :
    (sechScaledElevenMeshHalfMicro : ℝ) / 1000000 ≤ (sech11_uniform_meshSum : ℝ) / 1000000 := by
  norm_num [sechScaledElevenMeshHalfMicro, sech11_uniform_meshSum]

end UgpLean.Substrate.PhiMDLFluctuationSpectrum
