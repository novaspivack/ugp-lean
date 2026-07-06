# PROPOSAL — Rule110 AlgebraicUniversality scope correction

**Status:** Proposal only — not committed to `rule110-lean`. For Nova review.

**Problem:** `rule110_turing_universal_algebraic` is literally `boolean_nand_complete` —
2-input NAND functional completeness (Sheffer 1913), not Turing universality.

**Corrected substrate universality:** `UgpLean/Universality/UWCARegisterUniversality.lean`
(`uwca_substrate_turing_universal`, one Minsky axiom).

---

## Before (`Rule110/AlgebraicUniversality.lean`)

```lean
theorem rule110_turing_universal_algebraic :
    ∀ (f : Bool → Bool → Bool),
      ∃ (circuit : Bool → Bool → Bool),
        ∀ (a b : Bool), circuit a b = f a b :=
  boolean_nand_complete
```

## After (proposed)

```lean
theorem rule110_center1_nand_functional_completeness :
    ∀ (f : Bool → Bool → Bool),
      ∃ (circuit : Bool → Bool → Bool),
        ∀ (a b : Bool), circuit a b = f a b :=
  boolean_nand_complete

abbrev rule110_turing_universal_algebraic := rule110_center1_nand_functional_completeness
```

See full proposed module header in this document's git history or the agent report.
