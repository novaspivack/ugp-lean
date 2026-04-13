import Mathlib
import UgpLean.Core.TripleDefs
import UgpLean.GTE.GTESimulation

/-!
# UgpLean.GTE.EntropyNonMonotone — Cumulative Shannon entropy drop (ML-9 companion)

**Meta-law ML-9** in `ugp_meta_laws.tex` (computational sketch and long-run statistics) predicts that
coarse Shannon entropy along a reversible GTE trajectory need not be monotone. This file proves a
**finite, strict** instance on the Lepton-seed recurrence at `n = 10` (`GTESimulation`): bins
`(Nat.log2 b, Nat.log2 c)`, and a drop in cumulative empirical entropy when extending an eight-step
prefix to nine steps.

Large-N empirical claims (e.g. `1.2 × 10⁶` steps in the paper) are not reproduced here; this is a
machine-checked witness compatible with ML-9.
-/

namespace UgpLean

/-- Coarse bin `(log₂ b, log₂ c)` along the simulated orbit. -/
def coarseMacro (t : Triple) : ℕ × ℕ :=
  (Nat.log2 t.b, Nat.log2 t.c)

/-- Macros for the first eight trajectory steps (indices `0 … 7`). -/
def macrosPrefix8 : List (ℕ × ℕ) :=
  [ (6, 9), (5, 9), (8, 9), (6, 9), (7, 9), (5, 9), (8, 9), (7, 9) ]

/-- Macro at trajectory index `8` (ninth configuration). -/
def macroAt8 : ℕ × ℕ := (7, 9)

-- Macro agreement: `macrosPrefix8_eq_map`, `macroAt8_eq` match `GTESimulation` (`gteAfterSteps`).

theorem macrosPrefix8_eq_map :
    (List.range 8).map (fun i : ℕ => coarseMacro (gteAfterSteps 10 i)) = macrosPrefix8 := by native_decide

theorem macroAt8_eq : coarseMacro (gteAfterSteps 10 8) = macroAt8 := by native_decide

noncomputable section

-- Hpred8: Shannon entropy (base 2) for the eight-step multiset (uniform on four macro bins).
def Hpred8 : ℝ :=
  let p : ℝ := 1 / 4;
  -4 * (p * Real.logb 2 p)

-- Hpred9: entropy for the nine-step multiset (counts 2,2,2,3 on four macro types).
def Hpred9 : ℝ :=
  let p2 : ℝ := 2 / 9;
  let p3 : ℝ := 1 / 3;
  -3 * (p2 * Real.logb 2 p2) - p3 * Real.logb 2 p3

theorem logb_one_div_four : Real.logb (2 : ℝ) (1 / 4 : ℝ) = -2 := by
  rw [show (1 / 4 : ℝ) = (2 : ℝ) ^ (-(2 : ℝ)) by norm_num]
  rw [Real.logb_rpow (by positivity : (0 : ℝ) < (2 : ℝ))]
  norm_num

theorem Hpred8_eq_two : Hpred8 = 2 := by
  dsimp [Hpred8]
  rw [logb_one_div_four]
  ring

theorem three_lt_two_rpow_eight_fifths : (3 : ℝ) < (2 : ℝ) ^ (8 / 5 : ℝ) := by
  have hs : ((2 : ℝ) ^ (8 / 5 : ℝ)) ^ (5 : ℕ) = (256 : ℝ) := by
    symm
    calc
      (256 : ℝ)
          = (2 : ℝ) ^ (8 : ℕ) := by norm_num
      _ = (2 : ℝ) ^ ((8 / 5 : ℝ) * (5 : ℝ)) := by norm_num
      _ = ((2 : ℝ) ^ (8 / 5 : ℝ)) ^ (5 : ℝ) := Real.rpow_mul (show (0 : ℝ) ≤ 2 by positivity) _ _
      _ = ((2 : ℝ) ^ (8 / 5 : ℝ)) ^ (5 : ℕ) := by norm_cast
  have h243 : (3 : ℝ) ^ (5 : ℕ) < ((2 : ℝ) ^ (8 / 5 : ℝ)) ^ (5 : ℕ) := by rw [hs]; norm_num
  exact (Odd.strictMono_pow (by decide : Odd (5 : ℕ))).lt_iff_lt.1 h243

theorem log2_three_lt_eight_fifths : Real.logb (2 : ℝ) 3 < (8 / 5 : ℝ) := by
  have hpow : (0 : ℝ) < (2 : ℝ) ^ (8 / 5 : ℝ) := Real.rpow_pos_of_pos (by positivity) _
  have hlog := (Real.log_lt_log_iff (by positivity) hpow).mpr three_lt_two_rpow_eight_fifths
  rw [Real.log_rpow (by positivity)] at hlog
  have hl2 : 0 < Real.log 2 := Real.log_pos (by norm_num : (1 : ℝ) < 2)
  rw [Real.logb, div_lt_iff₀ hl2]
  linarith [hlog]

theorem Hpred9_eq : Hpred9 = -(2 / 3 : ℝ) + (5 / 3 : ℝ) * Real.logb (2 : ℝ) 3 := by
  have h2pos : (0 : ℝ) < (2 : ℝ) := by positivity
  have h3pos : (0 : ℝ) < (3 : ℝ) := by positivity
  have h9 : (9 : ℝ) = 3 ^ (2 : ℕ) := by norm_num
  dsimp [Hpred9]
  have hlog22 : Real.logb (2 : ℝ) (2 / 9 : ℝ) = Real.logb (2 : ℝ) 2 - Real.logb (2 : ℝ) 9 := by
    rw [← Real.logb_div (by positivity : (2 : ℝ) ≠ 0) (by positivity : (9 : ℝ) ≠ 0)]
  have hlog9 : Real.logb (2 : ℝ) 9 = 2 * Real.logb (2 : ℝ) 3 := by
    rw [h9, Real.logb_pow (2 : ℝ) (3 : ℝ) 2]
    simp
  have hlog13 : Real.logb (2 : ℝ) (1 / 3 : ℝ) = -Real.logb (2 : ℝ) 3 := by
    rw [Real.logb_div one_ne_zero h3pos.ne']
    simp [Real.logb_one]
  have hb : Real.logb (2 : ℝ) 2 = 1 := by
    rw [Real.logb]
    field_simp [ne_of_gt (Real.log_pos (show (1 : ℝ) < 2 by norm_num))]
  rw [hlog22, hlog9, hlog13, hb]
  ring

theorem Hpred9_lt_two : Hpred9 < (2 : ℝ) := by
  rw [Hpred9_eq]
  linarith [log2_three_lt_eight_fifths]

theorem Hpred8_gt_Hpred9 : Hpred8 > Hpred9 := by
  rw [Hpred8_eq_two]
  linarith [Hpred9_lt_two]

end

-- Strict drop in cumulative coarse entropy from eight steps to nine (ML-9 finite witness).
theorem gte_entropy_prefix8_gt_prefix9 : Hpred8 > Hpred9 :=
  Hpred8_gt_Hpred9

end UgpLean
