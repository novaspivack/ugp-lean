import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import Mathlib.Dynamics.PeriodicPts.Lemmas
import UgpLean.Polynomial.PolyExplorations
import UgpLean.Polynomial.GoldenQuadratic
import UgpLean.Polynomial.DynamicalZeta

open UgpLean.Polynomial.PolyExplorations
open UgpLean.Polynomial.GoldenQuadratic

/-!
# Spin-7 ring ground-space rigidity

Certifies that cyclic zero-energy configurations of the spin-7 chain — rings
`(s₀,…,s_{n−1})` with `p(s_{i−1}, s_i, s_{i+1}) = 0` at every site — are exactly
the three uniform assemblies `{0ⁿ, 1ⁿ, 5ⁿ}` for every ring length `n ≥ 3`.

The general-n proof is structural: zero-energy triples define a deterministic
pair-state digraph on the `43` active vertices of `7 × 7`; `native_decide`
certifies that its only directed cycles are the three uniform self-loops
`(0,0)`, `(1,1)`, `(5,5)`.  A cyclic configuration of length `n` induces a
closed walk of length `n`; pigeonhole on `49` vertices yields a return within
`49` steps, hence only the three uniform loops survive.  Any zero cell
propagates to the vacuum ring `0ⁿ`.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Polynomial.SpinSevenGroundSpace

open UgpLean.Polynomial.DynamicalZeta
open Function

def groundSpinValues : Finset (Fin 7) := {0, 1, 5}

theorem ground_spin_values_card : groundSpinValues.card = 3 := by native_decide

def zeroEnergyWindow (L C R : Fin 7) : Prop :=
  poly_p_fin7 L C R = 0

def IsZeroEnergyRing {n : ℕ} [NeZero n] (s : Fin n → Fin 7) : Prop :=
  ∀ i : Fin n, zeroEnergyWindow (s (ringLeft i)) (s i) (s (ringRight i))

def IsUniformRing {n : ℕ} (c : Fin 7) (s : Fin n → Fin 7) : Prop :=
  ∀ i : Fin n, s i = c

def IsUniformGroundRing {n : ℕ} (s : Fin n → Fin 7) : Prop :=
  ∃ c ∈ groundSpinValues, IsUniformRing c s

instance decidableZeroEnergyRing {n : ℕ} [NeZero n] (s : Fin n → Fin 7) :
    Decidable (IsZeroEnergyRing s) := by
  dsimp [IsZeroEnergyRing, zeroEnergyWindow]
  infer_instance

instance decidableUniformGroundRing {n : ℕ} (s : Fin n → Fin 7) :
    Decidable (IsUniformGroundRing s) := by
  dsimp [IsUniformGroundRing, IsUniformRing, groundSpinValues]
  infer_instance

-- ════════════════════════════════════════════════════════════════
-- §1  Local zero-energy factorization and zero propagation
-- ════════════════════════════════════════════════════════════════

private theorem zero_energy_cell_rhs {n : ℕ} [NeZero n] (s : Fin n → Fin 7) (i : Fin n)
    (hzero : zeroEnergyWindow (s (ringLeft i)) (s i) (s (ringRight i))) :
    zmod7OfFin (s (ringRight i)) *
        (1 - zmod7OfFin (s i) * (1 + zmod7OfFin (s (ringLeft i)))) =
      -(zmod7OfFin (s i)) := by
  have hp : poly_p (α := ZMod 7) (zmod7OfFin (s (ringLeft i))) (zmod7OfFin (s i))
      (zmod7OfFin (s (ringRight i))) = 0 :=
    poly_p_fin7_cast _ _ _ 0 hzero
  have hfac := fixed_point_local_factorization (zmod7OfFin (s (ringLeft i))) (zmod7OfFin (s i))
    (zmod7OfFin (s (ringRight i)))
  simpa [hp, zero_sub] using hfac.symm

/-- A zero-energy cell with center `0` forces the right neighbor to `0`. -/
theorem zero_energy_zero_center_forces_zero_right {n : ℕ} [NeZero n] (s : Fin n → Fin 7)
    (i : Fin n) (hzero : IsZeroEnergyRing s) (hi : s i = 0) : s (ringRight i) = 0 := by
  haveI : IsDomain (ZMod 7) := inferInstance
  have hf := zero_energy_cell_rhs s i (hzero i)
  have hi0 : zmod7OfFin (s i) = 0 := by
    apply (ZMod.val_injective 7).eq_iff.mp
    simpa [ZMod.val_natCast] using congrArg Fin.val hi
  have hR : zmod7OfFin (s (ringRight i)) = 0 := by
    simpa [hi0, zero_mul, neg_zero] using hf
  exact Fin.ext (by simpa [ZMod.val_natCast, ZMod.val_zero] using congrArg ZMod.val hR)

/-- If any cell vanishes on a zero-energy ring, every cell vanishes. -/
theorem zero_energy_any_zero_forces_all_zero {n : ℕ} [NeZero n] (s : Fin n → Fin 7)
    (hzero : IsZeroEnergyRing s) (i₀ : Fin n) (hi₀ : s i₀ = 0) : ∀ j, s j = 0 := by
  have step : ∀ k : ℕ, s (ringRight (n := n)^[k] i₀) = 0 := by
    intro k
    induction k with
    | zero => simpa using hi₀
    | succ k ih =>
      simpa [Function.iterate_succ_apply'] using
        zero_energy_zero_center_forces_zero_right s (ringRight^[k] i₀) hzero ih
  intro j
  have hk := ringRight_steps_to i₀ j
  rw [← hk]
  exact step ((j.val + n - i₀.val) % n)

-- ════════════════════════════════════════════════════════════════
-- §2  Zero-energy pair digraph (43 active vertices)
-- ════════════════════════════════════════════════════════════════

private abbrev ZeroEnergyPair := Fin 7 × Fin 7

private def zeroEnergySuccList (v : ZeroEnergyPair) : List (Fin 7) :=
  (List.range 7).filterMap fun c =>
    if h : c < 7 then
      let fc := ⟨c, h⟩
      if poly_p_fin7 v.1 v.2 fc = 0 then some fc else none
    else none

private def zeroEnergyStepFun (v : ZeroEnergyPair) : ZeroEnergyPair :=
  match zeroEnergySuccList v with
  | c :: _ => (v.2, c)
  | [] => v

private def onZeroEnergyCycle (v : ZeroEnergyPair) (len : ℕ) : Bool :=
  0 < len ∧ Nat.iterate zeroEnergyStepFun len v == v

private def IsUniformPair (v : ZeroEnergyPair) : Prop :=
  v = (0, 0) ∨ v = (1, 1) ∨ v = (5, 5)

private instance decidableIsUniformPair (v : ZeroEnergyPair) : Decidable (IsUniformPair v) := by
  dsimp [IsUniformPair]
  infer_instance

/-- **zero_energy_active_pair_only_uniform_cycles** (CatAL — native_decide):
    On active pair vertices (`zeroEnergySuccList ≠ []`), the only directed cycles are
    the three uniform self-loops.  Passive dead-end pairs are excluded. -/
theorem zero_energy_active_pair_only_uniform_cycles :
    (∀ v : ZeroEnergyPair, zeroEnergySuccList v ≠ [] → onZeroEnergyCycle v 1 = true →
      IsUniformPair v) ∧
    (∀ v : ZeroEnergyPair, zeroEnergySuccList v ≠ [] → ¬ IsUniformPair v →
      ∀ len : Fin 50, 1 < len.val → onZeroEnergyCycle v len.val = false) := by
  native_decide

private theorem zero_energy_uniform_pair_one_step_cert :
    ∀ v : ZeroEnergyPair, IsUniformPair v → zeroEnergySuccList v ≠ [] →
      Nat.iterate zeroEnergyStepFun 1 v = v := by
  native_decide

private theorem zero_energy_fin_return_iff_uniform_cert :
    ∀ v : ZeroEnergyPair, zeroEnergySuccList v ≠ [] →
      ((∃ n : Fin 500, 0 < n.val ∧ Nat.iterate zeroEnergyStepFun n.val v = v) ↔
        IsUniformPair v) := by
  native_decide

private theorem zero_energy_succ_list_cert :
    ∀ L C R : Fin 7, poly_p_fin7 L C R = 0 → zeroEnergySuccList (L, C) = [R] := by
  native_decide

private theorem zero_energy_uniform_all_returns_cert :
    ∀ v : ZeroEnergyPair, IsUniformPair v → zeroEnergySuccList v ≠ [] →
      ∀ n : ℕ, Nat.iterate zeroEnergyStepFun n v = v := by
  intro v hv hact n
  induction n with
  | zero => rfl
  | succ n ih =>
    rw [Function.iterate_succ_apply', ih]
    rcases hv with rfl | rfl | rfl
    · simp [zeroEnergyStepFun, zero_energy_succ_list_cert 0 0 0 (by native_decide)]
    · simp [zeroEnergyStepFun, zero_energy_succ_list_cert 1 1 1 (by native_decide)]
    · simp [zeroEnergyStepFun, zero_energy_succ_list_cert 5 5 5 (by native_decide)]

private theorem zero_energy_step_eq_triple {n : ℕ} [NeZero n] (s : Fin n → Fin 7) (i : Fin n)
    (hzero : IsZeroEnergyRing s) :
    zeroEnergyStepFun (s (ringLeft i), s i) = (s i, s (ringRight i)) := by
  simp only [zeroEnergyStepFun, zero_energy_succ_list_cert (s (ringLeft i)) (s i)
    (s (ringRight i)) (hzero i)]

private theorem zero_energy_pair_walk {n : ℕ} [NeZero n] (s : Fin n → Fin 7) (i₀ : Fin n)
    (hzero : IsZeroEnergyRing s) :
    ∀ k : ℕ, zeroEnergyStepFun^[k] (s (ringLeft i₀), s i₀) =
      (s (ringLeft (ringRight^[k] i₀)), s (ringRight^[k] i₀)) := by
  intro k
  induction k with
  | zero => simp [Function.iterate_zero]
  | succ k ih =>
    have hleft := ringLeft_ringRight_iterate k i₀
    rw [Function.iterate_succ_apply', ih, zero_energy_step_eq_triple s (ringRight^[k] i₀) hzero]
    congr 1
    · exact congrArg s (ringLeft_ringRight_iterate k i₀).symm
    · simp only [Function.iterate_succ_apply']

private theorem pair_cycle_const_center {n : ℕ} [NeZero n] (s : Fin n → Fin 7) (i₀ : Fin n)
    (c : Fin 7) (hzero : IsZeroEnergyRing s)
    (hstart : (s (ringLeft i₀), s i₀) = (c, c))
    (hc : c = 0 ∨ c = 1 ∨ c = 5) :
    ∀ k : ℕ, s (ringRight^[k] i₀) = c := by
  intro k
  have hpoly : poly_p_fin7 c c c = 0 := by
    rcases hc with rfl | rfl | rfl <;> native_decide
  have hact : zeroEnergySuccList (c, c) ≠ [] := by
    rw [zero_energy_succ_list_cert c c c hpoly]
    simp
  have hpairret : Nat.iterate zeroEnergyStepFun k (c, c) = (c, c) :=
    zero_energy_uniform_all_returns_cert (c, c) (by
      rcases hc with rfl | rfl | rfl <;> simp [IsUniformPair]) hact k
  have hwalk := zero_energy_pair_walk s i₀ hzero k
  rw [hstart] at hwalk
  rw [hpairret] at hwalk
  exact congrArg Prod.snd hwalk.symm

private theorem uniform_pair_from_one_step (v : ZeroEnergyPair)
    (hact : zeroEnergySuccList v ≠ [])
    (h1 : Nat.iterate zeroEnergyStepFun 1 v = v) : IsUniformPair v := by
  have hcyc : onZeroEnergyCycle v 1 = true := by
    dsimp [onZeroEnergyCycle]
    simp only [beq_iff_eq, decide_eq_true_eq]
    exact ⟨by decide, h1⟩
  exact zero_energy_active_pair_only_uniform_cycles.1 v hact hcyc

private theorem zero_energy_fin_return_forces_one_step_cert :
    ∀ v : ZeroEnergyPair, zeroEnergySuccList v ≠ [] →
      ∀ len : Fin 500, 0 < len.val → Nat.iterate zeroEnergyStepFun len.val v = v →
        Nat.iterate zeroEnergyStepFun 1 v = v := by
  native_decide

private theorem exists_return_index_le_49_cert :
    ∀ v : ZeroEnergyPair, ∀ n : Fin 500, 0 < n.val → Nat.iterate zeroEnergyStepFun n.val v = v →
      ∃ k : Fin 50, 0 < k.val ∧ Nat.iterate zeroEnergyStepFun k.val v = v := by
  native_decide

private theorem nonuniform_active_no_return_cert :
    ∀ v : ZeroEnergyPair, zeroEnergySuccList v ≠ [] → ¬ IsUniformPair v →
      ∀ n : Fin 500, 0 < n.val → Nat.iterate zeroEnergyStepFun n.val v ≠ v := by
  native_decide

/-- Any return on the `49`-state pair graph occurs within `49` steps (minimal-period bound). -/
private theorem exists_return_index_le_49 {v : ZeroEnergyPair} (_hact : zeroEnergySuccList v ≠ [])
    {n : ℕ} (hn : 0 < n) (hret : Nat.iterate zeroEnergyStepFun n v = v) :
    ∃ k : ℕ, 0 < k ∧ k ≤ 49 ∧ Nat.iterate zeroEnergyStepFun k v = v := by
  let f := zeroEnergyStepFun
  have hper : IsPeriodicPt f n v := hret
  have hpos : 0 < minimalPeriod f v := IsPeriodicPt.minimalPeriod_pos hn hper
  have hle : minimalPeriod f v ≤ Fintype.card ZeroEnergyPair := minimalPeriod_le_card (f := f) (x := v)
  refine ⟨minimalPeriod f v, hpos, ?_, isPeriodicPt_minimalPeriod f v⟩
  simpa [ZeroEnergyPair] using hle

private theorem nat_return_implies_uniform_pair {v : ZeroEnergyPair}
    (hact : zeroEnergySuccList v ≠ []) {n : ℕ} (hn : 0 < n)
    (hret : Nat.iterate zeroEnergyStepFun n v = v) : IsUniformPair v := by
  obtain ⟨k, hkpos, _, hk⟩ := exists_return_index_le_49 hact hn hret
  have h1 : Nat.iterate zeroEnergyStepFun 1 v = v :=
    zero_energy_fin_return_forces_one_step_cert v hact ⟨k, by omega⟩ hkpos hk
  exact uniform_pair_from_one_step v hact h1

private theorem uniform_of_pair_cycle {n : ℕ} [NeZero n] (hn : 3 ≤ n) (s : Fin n → Fin 7)
    (i₀ : Fin n) (hzero : IsZeroEnergyRing s)
    (hcyc : Nat.iterate zeroEnergyStepFun n (s (ringLeft i₀), s i₀) =
      (s (ringLeft i₀), s i₀)) :
    IsUniformGroundRing s := by
  let v := (s (ringLeft i₀), s i₀)
  have hv : v = (s (ringLeft i₀), s i₀) := rfl
  have hact : zeroEnergySuccList v ≠ [] := by
    rw [hv, zero_energy_succ_list_cert (s (ringLeft i₀)) (s i₀) (s (ringRight i₀)) (hzero i₀)]
    simp
  have hret : Nat.iterate zeroEnergyStepFun n v = v := by simpa [hv] using hcyc
  have hpair := nat_return_implies_uniform_pair (v := v) (hact := hact) (n := n)
    (hn := by omega) (hret := hret)
  rcases hpair with h00 | h11 | h55
  · have hstart : (s (ringLeft i₀), s i₀) = (0, 0) := by rw [← hv, h00]
    refine ⟨0, by simp [groundSpinValues], ?_⟩
    intro i
    have hall := pair_cycle_const_center s i₀ 0 hzero hstart (Or.inl rfl)
    have hj := ringRight_steps_to i₀ i
    rw [← hj]
    exact hall ((i.val + n - i₀.val) % n)
  · have hstart : (s (ringLeft i₀), s i₀) = (1, 1) := by rw [← hv, h11]
    refine ⟨1, by simp [groundSpinValues], ?_⟩
    intro i
    have hall := pair_cycle_const_center s i₀ 1 hzero hstart (Or.inr (Or.inl rfl))
    have hj := ringRight_steps_to i₀ i
    rw [← hj]
    exact hall ((i.val + n - i₀.val) % n)
  · have hstart : (s (ringLeft i₀), s i₀) = (5, 5) := by rw [← hv, h55]
    refine ⟨5, by simp [groundSpinValues], ?_⟩
    intro i
    have hall := pair_cycle_const_center s i₀ 5 hzero hstart (Or.inr (Or.inr rfl))
    have hj := ringRight_steps_to i₀ i
    rw [← hj]
    exact hall ((i.val + n - i₀.val) % n)

-- ════════════════════════════════════════════════════════════════
-- §3  Uniform ground rings have zero energy
-- ════════════════════════════════════════════════════════════════

theorem uniform_ground_ring_satisfies_zero_energy {n : ℕ} [NeZero n] (c : Fin 7)
    (hc : c ∈ groundSpinValues) (s : Fin n → Fin 7) (hU : IsUniformRing c s) :
    IsZeroEnergyRing s := by
  intro i
  rw [hU (ringLeft i), hU i, hU (ringRight i)]
  simp only [zeroEnergyWindow]
  fin_cases c <;> simp [groundSpinValues, poly_p_fin7] at hc ⊢ <;> native_decide

-- ════════════════════════════════════════════════════════════════
-- §4  General-n ground-space rigidity
-- ════════════════════════════════════════════════════════════════

/-- **gte_ring_ground_states_uniform_general** (CatAL): every cyclic zero-energy
    configuration of length `n ≥ 3` is exactly `{0ⁿ, 1ⁿ, 5ⁿ}`. -/
theorem gte_ring_ground_states_uniform_general {n : ℕ} [NeZero n] (hn : 3 ≤ n)
    (s : Fin n → Fin 7) (h : IsZeroEnergyRing s) :
    IsUniformGroundRing s := by
  by_cases h0 : ∃ i, s i = 0
  · obtain ⟨i₀, hi₀⟩ := h0
    have hall := zero_energy_any_zero_forces_all_zero s h i₀ hi₀
    refine ⟨0, ?_, ?_⟩
    · simp [groundSpinValues]
    · intro i; exact hall i
  · push Not at h0
    let i₀ : Fin n := ⟨0, by omega⟩
    have hcyc : Nat.iterate zeroEnergyStepFun n (s (ringLeft i₀), s i₀) =
        (s (ringLeft i₀), s i₀) := by
      have hperiod := ringRight_iterate_period i₀
      simpa [zero_energy_pair_walk s i₀ h, hperiod] using
        (zero_energy_pair_walk s i₀ h n).symm
    exact uniform_of_pair_cycle hn s i₀ h hcyc

-- ════════════════════════════════════════════════════════════════
-- §5  Finite-length sanity certificates (n = 3..7)
-- ════════════════════════════════════════════════════════════════

private theorem gte_ring_ground_states_uniform_n3 :
    ∀ s : Fin 3 → Fin 7, IsZeroEnergyRing (n := 3) s → IsUniformGroundRing s := by
  intro s h
  exact gte_ring_ground_states_uniform_general (by decide) s h

private theorem gte_ring_ground_states_uniform_n4 :
    ∀ s : Fin 4 → Fin 7, IsZeroEnergyRing (n := 4) s → IsUniformGroundRing s := by
  intro s h
  exact gte_ring_ground_states_uniform_general (by decide) s h

private theorem gte_ring_ground_states_uniform_n5 :
    ∀ s : Fin 5 → Fin 7, IsZeroEnergyRing (n := 5) s → IsUniformGroundRing s := by
  intro s h
  exact gte_ring_ground_states_uniform_general (by decide) s h

private theorem gte_ring_ground_states_uniform_n6 :
    ∀ s : Fin 6 → Fin 7, IsZeroEnergyRing (n := 6) s → IsUniformGroundRing s := by
  intro s h
  exact gte_ring_ground_states_uniform_general (by decide) s h

private theorem gte_ring_ground_states_uniform_n7 :
    ∀ s : Fin 7 → Fin 7, IsZeroEnergyRing (n := 7) s → IsUniformGroundRing s := by
  intro s h
  exact gte_ring_ground_states_uniform_general (by decide) s h

/-- Legacy bounded-length corollary; subsumed by `gte_ring_ground_states_uniform_general`. -/
theorem gte_ring_ground_states_uniform {n : ℕ} [NeZero n] (hn : 3 ≤ n) (_hnub : n ≤ 7)
    (s : Fin n → Fin 7) (h : IsZeroEnergyRing s) :
    IsUniformGroundRing s :=
  gte_ring_ground_states_uniform_general hn s h

theorem gte_ring_ground_states_uniform_bundle {n : ℕ} [NeZero n] (hn : 3 ≤ n) :
    (∀ s : Fin n → Fin 7, IsZeroEnergyRing (n := n) s → IsUniformGroundRing s) ∧
      (∀ c ∈ groundSpinValues, IsZeroEnergyRing (n := n) (fun (_ : Fin n) => c)) := by
  refine ⟨fun s h => gte_ring_ground_states_uniform_general hn s h, ?_⟩
  intro c hc
  exact uniform_ground_ring_satisfies_zero_energy (n := n) c hc (fun (_ : Fin n) => c)
    (fun _ => rfl)

end UgpLean.Polynomial.SpinSevenGroundSpace
