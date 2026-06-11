import Mathlib.Tactic
import Mathlib.Analysis.SpecialFunctions.Sqrt
import UgpLean.Polynomial.PolyExplorations
import UgpLean.Polynomial.SpinSevenWallSpectroscopy
import UgpLean.Polynomial.SpinSevenGapAmplitude

open UgpLean.Polynomial.PolyExplorations
open UgpLean.Polynomial.SpinSevenWallSpectroscopy

/-!
# Spin-7 spectator mechanism for the gap-law amplitude

The gap-law amplitude `A = 1` of the spin-7 transfer matrix follows from the
**spectator mechanism**: the β = ∞ zero-energy digraph has spectral radius
exactly 1 carried by the three uniform self-loops (all other pair states
transient), and three-level degenerate cluster perturbation theory on the
ground multiplet splits the chiral 0↔1 pair symmetrically about the inert
sector-5 spectator, giving ordered eigenvalue gaps `{T, 2T}` with
`T = √(t₀₁ t₁₀)` — so the gap-to-spectator amplitude is `√(c₁₀c₀₁) = 1` and
the second-to-first gap ratio is exactly 2 (`Δ₃ = 2Δ₂`, measured
`1.99999932`; the resolvent route refines this to
`Δ₃/Δ₂ = 2 − e^(−β/2) + O(e^(−β))`).

Certified here:

* **ρ = 1 package** (decidable): the three ground self-loops are the only
  outgoing zero-energy edges at the ground pairs
  (`zero_energy_ground_rows_self_loop_only`); the powers of the 49-state
  zero-energy adjacency stabilize, `Z²² = Z²³`, hence `Zᵏ = Z²²` for all
  `k ≥ 22` (power boundedness: spectral radius ≤ 1); the closed-walk count
  is exactly 3 at every positive length (the three unit-eigenvalue loops:
  spectral radius ≥ 1, and the only recurrent structure).
* **Cluster-PT skeleton** (exact, over ℝ): for the leading effective
  coupling matrix `![![0,a,0],![b,0,0],![0,0,0]]` with `a, b ≥ 0`, the
  vectors `(√a, √b, 0)`, `(√a, −√b, 0)`, `(0,0,1)` are eigenvectors with
  eigenvalues `√(ab), −√(ab), 0`; the ordered gaps are `{√(ab), 2√(ab)}`.
* **Amplitude tie-in**: with the certified minimal-wall counts
  `c₁₀ = c₀₁ = 1` (`SpinSevenGapAmplitude`), the chiral couplings are
  `t₀₁ = t², t₁₀ = t` and `T = √(t³) = t·√t`, so the gap-to-spectator
  amplitude is exactly 1 and `Δ₃ = 2Δ₂` at leading order.

Zero sorry.  Zero custom axioms.
-/

namespace UgpLean.Polynomial.SpinSevenSpectatorAmplitude

open UgpLean.Polynomial.SpinSevenGapAmplitude

-- ════════════════════════════════════════════════════════════════
-- §1  The ρ = 1 package for the zero-energy digraph
-- ════════════════════════════════════════════════════════════════

/-- Zero-energy adjacency on the 49 pair states (index `a·7 + b`), as a
    strict array matrix. -/
def zeroAdjM : Array (Array ℕ) :=
  Array.ofFn (n := 49) fun ui =>
    Array.ofFn (n := 49) fun vi =>
      let u : SpinPair := (⟨ui.val / 7, by omega⟩, ⟨ui.val % 7, by omega⟩)
      let v : SpinPair := (⟨vi.val / 7, by omega⟩, ⟨vi.val % 7, by omega⟩)
      if u.2 = v.1 ∧ tripleEnergy u.1 u.2 v.2 = 0 then 1 else 0

def matMulN (A B : Array (Array ℕ)) : Array (Array ℕ) :=
  Array.ofFn (n := 49) fun i =>
    Array.ofFn (n := 49) fun j =>
      (List.range 49).foldl
        (fun acc k =>
          acc + (A.getD i.val #[]).getD k 0 * (B.getD k #[]).getD j.val 0) 0

/-- `k`-th power of the zero-energy adjacency. -/
def zPow : ℕ → Array (Array ℕ)
  | 0 => Array.ofFn (n := 49) fun i =>
      Array.ofFn (n := 49) fun j => if i = j then 1 else 0
  | k + 1 => matMulN (zPow k) zeroAdjM

/-- Closed-walk count of length `k`. -/
def zTrace (k : ℕ) : ℕ :=
  (List.range 49).foldl (fun acc i => acc + ((zPow k).getD i #[]).getD i 0) 0

/-- **zero_energy_ground_rows_self_loop_only** (CatAL — native_decide):
    at each ground pair, the unique outgoing zero-energy edge is the
    self-loop. -/
theorem zero_energy_ground_rows_self_loop_only :
    ∀ g : Fin 7, g = 0 ∨ g = 1 ∨ g = 5 →
      ∀ vi : Fin 49,
        (zeroAdjM.getD (g.val * 7 + g.val) #[]).getD vi.val 0 =
          if vi.val = g.val * 7 + g.val then 1 else 0 := by
  native_decide

/-- **zero_energy_power_stabilizes** (CatAL — native_decide): the powers of
    the zero-energy adjacency stabilize at exponent 22 — the transient
    (interior) part is nilpotent, so the spectral radius is at most 1. -/
theorem zero_energy_power_stabilizes : zPow 22 = zPow 23 := by
  native_decide

theorem zero_energy_powers_eventually_constant :
    ∀ k, 22 ≤ k → zPow k = zPow 22 := by
  intro k hk
  obtain ⟨m, rfl⟩ := Nat.exists_eq_add_of_le hk
  induction m with
  | zero => rfl
  | succ m ih =>
    have hstep : 22 + (m + 1) = (22 + m) + 1 := by omega
    rw [hstep]
    show matMulN (zPow (22 + m)) zeroAdjM = zPow 22
    rw [ih (by omega)]
    exact zero_energy_power_stabilizes.symm

/-- Bounded closed-walk counts (native_decide): `tr(Zᵏ) = 3` for
    `1 ≤ k ≤ 22`. -/
theorem zero_energy_closed_walks_bounded :
    ∀ k : Fin 23, 1 ≤ k.val → zTrace k.val = 3 := by
  native_decide

/-- **zero_energy_closed_walk_count_three** (CatAL): the zero-energy digraph
    has exactly 3 closed walks of every positive length — the three uniform
    self-loops are the entire recurrent structure (spectral radius = 1 with
    eigenvalue-1 multiplicity 3; everything else transient). -/
theorem zero_energy_closed_walk_count_three :
    ∀ k, 1 ≤ k → zTrace k = 3 := by
  intro k hk
  by_cases hbig : 22 ≤ k
  · unfold zTrace
    rw [zero_energy_powers_eventually_constant k hbig]
    have h22 := zero_energy_closed_walks_bounded ⟨22, by omega⟩ (by simp)
    simpa [zTrace] using h22
  · push_neg at hbig
    exact zero_energy_closed_walks_bounded ⟨k, by omega⟩ hk

-- ════════════════════════════════════════════════════════════════
-- §2  Three-level cluster-PT skeleton (exact, over ℝ)
-- ════════════════════════════════════════════════════════════════

/-- Leading effective coupling matrix of the ground multiplet:
    chiral hops `0 → 1` (weight `a`) and `1 → 0` (weight `b`), spectator
    sector decoupled at leading order. -/
def clusterCoupling (a b : ℝ) : Matrix (Fin 3) (Fin 3) ℝ :=
  !![0, a, 0; b, 0, 0; 0, 0, 0]

theorem cluster_eigenvector_plus (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (clusterCoupling a b).mulVec
        ![Real.sqrt a, Real.sqrt b, 0] =
      Real.sqrt (a * b) • ![Real.sqrt a, Real.sqrt b, 0] := by
  have hsa := Real.mul_self_sqrt ha
  have hsb := Real.mul_self_sqrt hb
  funext i
  fin_cases i <;>
    simp [clusterCoupling, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Real.sqrt_mul ha, smul_eq_mul]
  · linear_combination (-Real.sqrt b) * hsa
  · linear_combination (-Real.sqrt a) * hsb

theorem cluster_eigenvector_minus (a b : ℝ) (ha : 0 ≤ a) (hb : 0 ≤ b) :
    (clusterCoupling a b).mulVec
        ![Real.sqrt a, -Real.sqrt b, 0] =
      (-Real.sqrt (a * b)) • ![Real.sqrt a, -Real.sqrt b, 0] := by
  have hsa := Real.mul_self_sqrt ha
  have hsb := Real.mul_self_sqrt hb
  funext i
  fin_cases i <;>
    simp [clusterCoupling, Matrix.mulVec, dotProduct, Fin.sum_univ_three,
      Real.sqrt_mul ha, smul_eq_mul]
  · linear_combination (-Real.sqrt b) * hsa
  · linear_combination (-Real.sqrt a) * hsb

theorem cluster_eigenvector_spectator (a b : ℝ) :
    (clusterCoupling a b).mulVec ![0, 0, 1] = (0 : ℝ) • ![0, 0, 1] := by
  funext i
  fin_cases i <;>
    simp [clusterCoupling, Matrix.mulVec, dotProduct, Fin.sum_univ_three]

/-- **cluster_gap_pair** (ring-grade): the ordered eigenvalue gaps of the
    cluster `{√(ab), 0, −√(ab)}` are `{T, 2T}` with `T = √(ab)` — the
    gap-to-spectator equals `T` and the full multiplet width equals `2T`
    (`Δ₃ = 2Δ₂` at leading order). -/
theorem cluster_gap_pair (a b : ℝ) :
    Real.sqrt (a * b) - 0 = Real.sqrt (a * b) ∧
      Real.sqrt (a * b) - (-Real.sqrt (a * b)) = 2 * Real.sqrt (a * b) := by
  constructor <;> ring

-- ════════════════════════════════════════════════════════════════
-- §3  Amplitude tie-in: A = √(c₁₀·c₀₁) = 1
-- ════════════════════════════════════════════════════════════════

/-- **spin7_spectator_amplitude** (CatAL — master bundle, LT-088-62):
    the spectator mechanism for the gap-law amplitude.  (i) ρ = 1 package:
    ground rows are self-loop-only, powers stabilize (`Z²² = Z²³`), and the
    closed-walk count is 3 at every positive length; (ii) the chiral
    couplings carry the certified unit counts `c₁₀ = c₀₁ = 1`, so
    `A² = c₁₀·c₀₁ = 1`; (iii) the cluster skeleton at couplings
    `(a, b) = (t², t)` has eigenvalue gaps `{t√t, 2t√t}` — amplitude 1 and
    `Δ₃ = 2Δ₂` at leading order. -/
theorem spin7_spectator_amplitude :
    (zPow 22 = zPow 23 ∧ ∀ k, 1 ≤ k → zTrace k = 3) ∧
      (cumThrough 1 0 45).getD 1 0 * (cumThrough 0 1 45).getD 2 0 = 1 ∧
        ∀ t : ℝ, 0 ≤ t →
          (clusterCoupling (t ^ 2) t).mulVec
              ![Real.sqrt (t ^ 2), Real.sqrt t, 0] =
            Real.sqrt (t ^ 2 * t) • ![Real.sqrt (t ^ 2), Real.sqrt t, 0] ∧
          Real.sqrt (t ^ 2 * t) - (-Real.sqrt (t ^ 2 * t)) =
            2 * (Real.sqrt (t ^ 2 * t) - 0) := by
  refine ⟨⟨zero_energy_power_stabilizes, zero_energy_closed_walk_count_three⟩,
    gap_amplitude_sq_unit, fun t ht => ⟨?_, by ring⟩⟩
  exact cluster_eigenvector_plus (t ^ 2) t (by positivity) ht

end UgpLean.Polynomial.SpinSevenSpectatorAmplitude
