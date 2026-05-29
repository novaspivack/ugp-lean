import Rule110

/-!
# Bridge to `rule110-lean` (Cook Rule 110 infrastructure)

The Cook cyclic-tag → Rule 110 simulation pipeline is formalized in the standalone
`rule110-lean` package (same Lean/Mathlib pins as this repo). Importing this module
forces Lake to compile `Rule110.*` alongside `UgpLean`, so background lemmas stay
binary-compatible as both evolve.

The Cook pipeline infrastructure now includes:
- Verified C-glider patterns (C1/C2/C3: 6-cell, period-7, from Cook 2004 Figure 4)
- Two-phase ether encoding (`gliders_to_tape_phased`, `cook_total_M`)
- Explicit M-value formula from Cook (2008) arXiv:0906.3248: M = 30·(2L+1) per CTS step
- Named collision axioms (`cook_cts_step_sim_ax`, `cook_cts_eval_sim_ax`) with concrete M witnesses
- `gte_embeds_in_rule110` is a theorem (zero sorry, one named axiom: `rule110_simulates_computable`)
-/

theorem cook_ether_one_period (i : ℕ) :
    Rule110.cookEther i = Rule110.cookEther (i + Rule110.etherPeriod) :=
  Rule110.ether_is_periodic i

theorem cook_ether_n_steps_shift {i n : ℕ} (hn : n ≤ i) :
    Rule110.infRule110Steps n Rule110.cookEther i =
      Rule110.cookEther (i + 4 * n) :=
  Rule110.infRule110Steps_cookEther_shift hn

theorem cook_cts_overlay_disjoint_cone_matches_ether_shift
    {cts : Rule110.CyclicTagSystem} {idx : ℕ} {w : List Bool}
    {cells : List (ℕ × Bool)} {i n : ℕ} (hn : n ≤ i)
    (hdisj : ∀ p ∈ cells, p.1 < i - n ∨ i + n < p.1) :
    Rule110.infRule110Steps n (Rule110.ctsTapeWithOverrides cts idx w cells) i =
      Rule110.cookEther (i + 4 * n) :=
  Rule110.ctsTapeWithOverrides_infRule110Steps_eq_shift_of_disjoint hn hdisj

/-- Cook (2008) M-value formula: Rule 110 steps per CTS step with appendant length L.
    M = 30*(2L+1) for L > 0; M = 30 for empty appendant.
    Source: Cook, "A Concrete View of Rule 110 Computation", EPTCS 1, 2009; arXiv:0906.3248 §1.4. -/
def cook_M (L : ℕ) : ℕ := Rule110.cook_M_for_appendant_len L

theorem cook_M_empty : cook_M 0 = 30 := rfl
theorem cook_M_nonempty (L : ℕ) (hL : 0 < L) : cook_M L = 30 * (2 * L + 1) :=
  Rule110.cook_M_nonempty L hL

/-- **cts_eval_deterministic** (CatAL): CTS evaluation is deterministic.
    A CTS is a deterministic computational system: given the same appendant set,
    step count, and initial word, the output is uniquely determined.
    The theorem states that any two equal-input evaluations produce the same result.

    The proof is immediate because `Rule110.CyclicTagSystem.cts_eval` is a function
    (deterministic by construction in Lean's type theory): functions are single-valued.

    LEAN-CERTIFIED (function equality, zero sorry). -/
theorem cts_eval_deterministic
    (cts : Rule110.CyclicTagSystem) (n : ℕ) (w : List Bool)
    (r1 r2 : List Bool)
    (h1 : cts.cts_eval n w = r1) (h2 : cts.cts_eval n w = r2) :
    r1 = r2 := by
  rw [← h1, ← h2]
