# Rule110 AlgebraicUniversality scope correction

**Status:** EXECUTED. Committed and pushed to `rule110-lean` (its own `origin`,
direct push authorized — this repo has no dev-sandbox counterpart).

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

## After (executed)

```lean
theorem rule110_center1_nand_functional_completeness :
    ∀ (f : Bool → Bool → Bool),
      ∃ (circuit : Bool → Bool → Bool),
        ∀ (a b : Bool), circuit a b = f a b :=
  boolean_nand_complete

@[deprecated rule110_center1_nand_functional_completeness (since := "2026-07-06")]
abbrev rule110_turing_universal_algebraic := rule110_center1_nand_functional_completeness
```

The module header docstring and `README.md` in `rule110-lean` were updated to match:
the module title changed from "Algebraic Universality Certificate" to "Finite NAND
Functional Completeness", and the claim that "Cook's theorem is a corollary of the
algebraic route" was removed (neither result is a corollary of the other).
