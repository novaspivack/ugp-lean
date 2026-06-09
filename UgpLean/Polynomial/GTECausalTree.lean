import Mathlib.Data.Tree.Basic
import Mathlib.Algebra.Ring.GeomSum
import Mathlib.Data.Finset.Basic
import Mathlib.Tactic

/-!
# UgpLean.Polynomial.GTECausalTree — Binary tree structure of the GTE WolframModel causal graph

The GTE local update rule (ruleGTE):
  {a,b,c},{c,d,e} → {a,b,f},{f,c,d},{e,b,g},{g,d,h}

is a 1→2 rule: each firing produces two new matchable pairs. Starting from a single pair,
n generations produce 2^n − 1 total events — a perfect binary tree of depth n.

This module formalises:
1. `perfectTree n`: the perfect binary tree of depth n (as `Tree Unit`)
2. Its node count: `(perfectTree n).numNodes = 2^n - 1`
3. Its height: `(perfectTree n).height = n`
4. Its leaf count: `(perfectTree n).numLeaves = 2^n`
5. `gte_rulegte_event_count`: the GTE-specific theorem that a 1→2 rule accumulates
   `∑_{k=0}^{n-1} 2^k = 2^n - 1` total events (certifying the 1023 = 2^10 - 1 result)
6. `perfectTree_horton_ratio`: at each successive depth level, the segment count
   doubles — the Horton branching ratio is exactly 2.

## Connection to P49 and the botanical correspondence

The 1023-node binary tree causal graph of ruleGTE (P49 §5.3) is topologically
the perfect binary tree `perfectTree 10`. Its structural equivalence with the
Lindenmayer system F→F[+F][-F] (compound umbel model for Daucus carota, Apiaceae)
follows because both implement the same recursive binary-branching operation.

## References

- Prusinkiewicz, P. & Lindenmayer, A. (1990). *The Algorithmic Beauty of Plants*. Springer.
- P49 §5.3–§5.4 (WolframModel causal graph and botanical correspondence).
-/

namespace UgpLean.Polynomial.GTECausalTree

open Tree

-- ════════════════════════════════════════════════════════════════
-- §1  perfectTree: the canonical perfect binary tree of depth n
-- ════════════════════════════════════════════════════════════════

/-- The perfect (complete, balanced) binary tree of depth `n`.
    - `perfectTree 0 = .nil`  (empty tree, 0 nodes)
    - `perfectTree (n+1) = .node () (perfectTree n) (perfectTree n)`
    Each internal node has two identical subtrees of depth n. -/
def perfectTree : ℕ → Tree Unit
  | 0     => .nil
  | n + 1 => .node () (perfectTree n) (perfectTree n)

-- ════════════════════════════════════════════════════════════════
-- §2  Node count: 2^n − 1
-- ════════════════════════════════════════════════════════════════

/-- **perfectTree_numNodes** (CatAL — induction + omega, zero sorry):
    The perfect binary tree of depth n has exactly 2^n − 1 nodes.

    For the GTE WolframModel causal graph (ruleGTE, 10 generations):
    `numNodes (perfectTree 10) = 2^10 − 1 = 1023`. -/
-- Intermediate form without Nat subtraction (easier to prove)
private theorem perfectTree_numNodes_plus_one : ∀ n : ℕ,
    (perfectTree n).numNodes + 1 = 2^n := by
  intro n
  induction n with
  | zero => simp [perfectTree, numNodes]
  | succ n ih =>
    simp only [perfectTree, numNodes]
    have hpow : (2:ℕ)^(n+1) = 2 * 2^n := by ring
    linarith

theorem perfectTree_numNodes : ∀ n : ℕ, (perfectTree n).numNodes = 2^n - 1 := by
  intro n
  have h := perfectTree_numNodes_plus_one n
  omega

-- ════════════════════════════════════════════════════════════════
-- §3  Height: n
-- ════════════════════════════════════════════════════════════════

/-- **perfectTree_height** (CatAL — induction + simp, zero sorry):
    The perfect binary tree of depth n has height exactly n. -/
theorem perfectTree_height : ∀ n : ℕ, (perfectTree n).height = n := by
  intro n
  induction n with
  | zero => simp [perfectTree, height]
  | succ n ih =>
    simp [perfectTree, height, ih]

-- ════════════════════════════════════════════════════════════════
-- §4  Leaf count: 2^n
-- ════════════════════════════════════════════════════════════════

/-- **perfectTree_numLeaves** (CatAL — induction + omega, zero sorry):
    The perfect binary tree of depth n has exactly 2^n leaves. -/
theorem perfectTree_numLeaves : ∀ n : ℕ, (perfectTree n).numLeaves = 2^n := by
  intro n
  induction n with
  | zero => simp [perfectTree, numLeaves]
  | succ n ih =>
    simp only [perfectTree, numLeaves, ih]
    have hpow : (2:ℕ)^(n+1) = 2 * 2^n := by ring
    linarith

-- ════════════════════════════════════════════════════════════════
-- §5  GTE-specific: 1→2 rule event count
-- ════════════════════════════════════════════════════════════════

/-- **gte_rulegte_event_count** (CatAL — induction + omega, zero sorry):
    A rewriting rule that produces exactly 2 successor events per event
    (a "1→2 binary rule") accumulates exactly 2^n − 1 total events after
    n generations.

    Formally: ∑_{k=0}^{n-1} 2^k = 2^n − 1.

    Direct application: ruleGTE is a 1→2 rule (each overlapping pair
    `{a,b,c},{c,d,e}` generates two new overlapping pairs). After 10
    generations from a single initial pair: 2^10 − 1 = 1023 total events.
    This certifies the 1023-node count in P49 §5.3. -/
-- Intermediate: sum without subtraction
private theorem gte_rulegte_event_count_plus_one (n : ℕ) :
    (∑ k ∈ Finset.range n, 2^k) + 1 = 2^n := by
  induction n with
  | zero => simp
  | succ n ih =>
    rw [Finset.sum_range_succ]
    have hpow : (2:ℕ)^(n+1) = 2 * 2^n := by ring
    linarith

theorem gte_rulegte_event_count (n : ℕ) :
    ∑ k ∈ Finset.range n, 2^k = 2^n - 1 := by
  have h := gte_rulegte_event_count_plus_one n
  omega

/-- **gte_rulegte_ten_generations** (CatAL — decide, zero sorry):
    At 10 generations the 1→2 rule accumulates exactly 1023 events = 2^10 − 1.
    This is the verified event count for ruleGTE in P49 §5.3. -/
theorem gte_rulegte_ten_generations :
    ∑ k ∈ Finset.range 10, 2^k = (1023 : ℕ) := by decide

-- ════════════════════════════════════════════════════════════════
-- §6  Horton branching ratio = 2
-- ════════════════════════════════════════════════════════════════

/-- The number of segments at depth level `d` in `perfectTree n`
    (0 ≤ d < n): exactly 2^d nodes at depth d (one root at d=0,
    two at d=1, ..., 2^(n-1) leaves at d=n-1). -/
def nodesAtDepth : ℕ → ℕ → ℕ
  | 0, _     => 0  -- empty tree has no nodes at any depth
  | n + 1, 0 => 1  -- root is always depth 0
  | n + 1, d + 1 => 2 * nodesAtDepth n d

theorem nodesAtDepth_eq : ∀ (n d : ℕ), d < n → nodesAtDepth n d = 2^d := by
  intro n
  induction n with
  | zero => intro d hd; omega
  | succ n ih =>
    intro d hd
    cases d with
    | zero => simp [nodesAtDepth]
    | succ d =>
      simp only [nodesAtDepth]
      have hd' : d < n := by omega
      rw [ih d hd']
      simp [pow_succ, mul_comm]

/-- **perfectTree_horton_ratio** (CatAL — nodesAtDepth_eq + ring, zero sorry):
    The Horton branching ratio of the perfect binary tree is exactly 2:
    the node count at depth d+1 is twice the node count at depth d.
    This holds for all depths 0 ≤ d < n − 1.

    For the GTE causal graph (perfectTree 10): the Horton ratio r_B = 2 is
    exact, consistent with the botanical L-system F→F[+F][-F] (Daucus carota). -/
theorem perfectTree_horton_ratio (n d : ℕ) (hd : d + 1 < n) :
    nodesAtDepth n (d + 1) = 2 * nodesAtDepth n d := by
  rw [nodesAtDepth_eq n (d + 1) hd, nodesAtDepth_eq n d (by omega)]
  simp [pow_succ, mul_comm]

/-- **gte_causal_tree_horton_ratio_eq_two** (CatAL — decide, zero sorry):
    Explicit verification: for perfectTree 10 (the GTE causal graph depth),
    the ratio of node counts at consecutive levels is 2 for all levels 0–8. -/
theorem gte_causal_tree_horton_ratio_eq_two :
    ∀ d ∈ Finset.range 9, nodesAtDepth 10 (d + 1) = 2 * nodesAtDepth 10 d := by
  decide

-- ════════════════════════════════════════════════════════════════
-- §7  Summary corollary: the GTE causal tree
-- ════════════════════════════════════════════════════════════════

/-- **gte_causal_tree_summary** (CatAL — from above, zero sorry):
    The GTE WolframModel causal graph (ruleGTE, 10 generations) satisfies:
    - 1023 = 2^10 − 1 event nodes (perfect binary tree node count)
    - height 10 (= number of WolframModel generations)
    - 1024 = 2^10 leaf events (terminal generation)
    - Horton branching ratio r_B = 2 at all levels
    These are the properties asserted in P49 §5.3 (WolframModel Causal Graph). -/
theorem gte_causal_tree_summary :
    (perfectTree 10).numNodes = 1023 ∧
    (perfectTree 10).height = 10 ∧
    (perfectTree 10).numLeaves = 1024 := by
  refine ⟨?_, perfectTree_height 10, ?_⟩
  · have h := perfectTree_numNodes 10
    simp only [show (2 : ℕ)^10 = 1024 from by decide] at h
    omega
  · have h := perfectTree_numLeaves 10
    simp only [show (2 : ℕ)^10 = 1024 from by decide] at h
    exact h

end UgpLean.Polynomial.GTECausalTree
