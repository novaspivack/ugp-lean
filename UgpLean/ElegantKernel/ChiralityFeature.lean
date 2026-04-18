import Mathlib.Data.Int.Basic
import Mathlib.Data.Real.Basic

/-!
# UgpLean.ElegantKernel.ChiralityFeature — Optional 10th UCL feature: sign(c)

## Context

The Universal Mapping Function Ψ from the Braid Atlas v2 derivation
(paper `Braid_Atlas_v2_First_Principles.tex`, Appendix B; implementation in
the Particle Derivations repo at `braid_to_gte_mapping_search/braid_to_gte_mapper.py`,
2025-09-29, verified 12/12 fermions) produces GTE triples `(a, b, c)` where

* `a = interaction_complexity(B)`       (non-negative integer)
* `b = spacetime_volume(B)`             (non-negative integer)
* `c = dominant_frequency(B) · e^(i π · H(writhe(B)))`
  which collapses in the real-integer encoding to a SIGNED integer `c`:
  `c < 0` when the braid has negative writhe (chiral third-generation leptons
  and the top quark), `c > 0` otherwise.

The nine-feature UCL currently used in the paper and Lean kernel
(see `UgpLean.ElegantKernel.*` and the monolith `compute_features` function)
uses only `|b|` and `|c|` — the sign of `c` is discarded.  This module
introduces the canonical 10th UCL feature

  `H : ℤ → ℤ`,   `H(c) = 1` if `c < 0`, else `0`

matching the Braid-Atlas `H(writhe)` convention after the complex-to-integer
port of `c`.

## Why this matters

Under the Braid-Atlas canonical GTE triples, the **tau** lepton has
`c = −65535` and the **charm quark** has `c = +65535`.  Their `(|a|, |b|, |c|)`
and Möbius features `(μ(|a|), μ(|b|), μ(|c|))` are therefore identical.
The nine-feature UCL cannot distinguish them on a purely triple basis —
only the `(gen, type)` tags in `E_base` carry the distinction.

Adding `H(c)` as a 10th feature breaks this degeneracy at the UCL level:
tau gets `H = 1`, charm gets `H = 0`.  The `H` feature recovers the
chirality information that was present in the upstream Ψ derivation but
lost when the canonical GTE triples were stored in the production engine
with unsigned `c`.

Historically the production engine stored `tau.c = +65535`, losing the sign.
The canonical is now restored to `tau.c = −65535` (and `tau_neutrino.c = −65535`);
see `specs/IN-PROCESS/EPIC_CLUSTER2_CLEAN_WINS/083_NOTE_P01_QUARK_TRIPLE_DERIVATION_RECOVERY.md`
in the `ugp-physics` repo.

## What this module does NOT do

This module introduces the `H` feature and states its key property
(distinguishes tau from charm).  It does **not**:

* re-fit the 9 existing Lean-certified UCL coefficients in a 10-feature
  setting (separate structural research question; see
  `082_SPEC_P01_KOIDE_S3_FLOW_RESEARCH_PLAN.md`),
* derive a structural value for `k_chi` from UGP first principles
  (open problem; the trivial choice `k_chi = 0` preserves the current
  nine-feature predictions bit-for-bit but leaves tau and charm
  UCL-indistinguishable),
* attempt to use `H` to close the Koide S₃-flow conjecture (OP(vii)/4.4).

-/

namespace UgpLean.ElegantKernel.ChiralityFeature

/-- Braid-Atlas chirality indicator:
    `H(c) = 1` if `c < 0` (chiral — third-generation leptons, top quark),
    `H(c) = 0` otherwise (achiral or non-chiral). -/
def H (c : ℤ) : ℤ := if c < 0 then 1 else 0

@[simp] lemma H_of_pos {c : ℤ} (hc : 0 < c) : H c = 0 := by
  unfold H; simp [not_lt.mpr (le_of_lt hc)]

@[simp] lemma H_of_neg {c : ℤ} (hc : c < 0) : H c = 1 := by
  unfold H; simp [hc]

@[simp] lemma H_zero : H 0 = 0 := by decide

/-- **Canonical values for the twelve Standard-Model fundamental fermions**
under the Braid-Atlas derivation (see `CanonicalGTEDatabase` in
`braid_to_gte_mapper.py`).  `H c = 1` exactly for the three chiral
particles: `tau`, `tau_neutrino`, `top`. -/
example : H (823    : ℤ) = 0 := by decide       -- electron (c = +823)
example : H (1023   : ℤ) = 0 := by decide       -- muon (c = +1023)
example : H ((-65535): ℤ) = 1 := by decide      -- tau (c = −65535) ← CHIRAL
example : H (275    : ℤ) = 0 := by decide       -- up (c = +275)
example : H (42     : ℤ) = 0 := by decide       -- down (c = +42)
example : H (1023   : ℤ) = 0 := by decide       -- strange (c = +1023)
example : H (65535  : ℤ) = 0 := by decide       -- charm (c = +65535)
example : H (65535  : ℤ) = 0 := by decide       -- bottom (c = +65535)
example : H ((-1)   : ℤ) = 1 := by decide       -- top (c = −1)      ← CHIRAL
example : H ((-65535): ℤ) = 1 := by decide      -- tau_neutrino (c = −65535) ← CHIRAL

/-- **Degeneracy-breaking claim.**

Under the Braid-Atlas canonical triples, tau has `c = −65535` and charm
has `c = +65535`.  Therefore `H tau.c = 1` but `H charm.c = 0`: the 10th
UCL feature distinguishes them, whereas the first 9 UCL features
(`const, L, L², gen, gen², M, μ_a, μ_b, μ_c`) are identical because they
use `|b|`, `|c|`, and `μ(|·|)` throughout.

This formalises the observation that the tau/charm UCL-feature
coincidence under the published 9-feature UCL is an artifact of the
unsigned-`c` convention, NOT a structural degeneracy of the theory.
Keeping `H` at `k_chi = 0` recovers the published predictions bit-for-
bit; any nonzero `k_chi` (derived from, e.g., a UGP-native S₃-flow
structural argument) would make the distinction visible. -/
theorem H_distinguishes_tau_charm :
    H (-65535 : ℤ) ≠ H (65535 : ℤ) := by decide

/-! ## Backward-compatibility note

The ten-feature extension is

```
  log C_f_10 = ( Σ_{i=0..8} k_i · f_i )  +  k_chi · H(c)
             = log C_f_9  +  k_chi · H(c)
```

At `k_chi = 0` the extended UCL reduces exactly to the nine-feature UCL,
so every Lean-certified theorem in `UgpLean.ElegantKernel.*` about the
nine-feature kernel (`thm_ucl1/2/4/5_fully_unconditional`, `k_L2_eq`,
`quarterLockLaw`, etc.) remains valid in the extension.  The chirality
feature is strictly additive.

Determining a structural value for `k_chi` (beyond `k_chi = 0`) is an
open research problem.  Until that value is derived, the honest position
is: the tenth feature is part of the formal framework with coefficient
zero, preserving numerical backward-compatibility, and is available to
be activated once a structural derivation is established.

-/

end UgpLean.ElegantKernel.ChiralityFeature
