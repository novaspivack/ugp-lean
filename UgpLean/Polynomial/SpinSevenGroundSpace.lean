import Mathlib.Tactic
import Mathlib.Data.Finset.Basic
import UgpLean.Polynomial.PolyExplorations
import UgpLean.Polynomial.DynamicalZeta

open UgpLean.Polynomial.PolyExplorations

/-!
# Spin-7 ring ground-space rigidity

Certifies that cyclic zero-energy configurations of the spin-7 chain — rings
`(s₀,…,s_{n−1})` with `p(s_{i−1}, s_i, s_{i+1}) = 0` at every site — are exactly
the three uniform assemblies `{0ⁿ, 1ⁿ, 5ⁿ}`.

Zero sorry. Zero custom axioms.
-/

namespace UgpLean.Polynomial.SpinSevenGroundSpace

open UgpLean.Polynomial.DynamicalZeta

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

theorem uniform_ground_ring_satisfies_zero_energy {n : ℕ} [NeZero n] (c : Fin 7)
    (hc : c ∈ groundSpinValues) (s : Fin n → Fin 7) (hU : IsUniformRing c s) :
    IsZeroEnergyRing s := by
  intro i
  rw [hU (ringLeft i), hU i, hU (ringRight i)]
  simp only [zeroEnergyWindow]
  fin_cases c <;> simp [groundSpinValues, poly_p_fin7] at hc ⊢ <;> native_decide

private theorem gte_ring_ground_states_uniform_n3 :
    ∀ s : Fin 3 → Fin 7, IsZeroEnergyRing (n := 3) s → IsUniformGroundRing s := by
  native_decide

private theorem gte_ring_ground_states_uniform_n4 :
    ∀ s : Fin 4 → Fin 7, IsZeroEnergyRing (n := 4) s → IsUniformGroundRing s := by
  native_decide

private theorem gte_ring_ground_states_uniform_n5 :
    ∀ s : Fin 5 → Fin 7, IsZeroEnergyRing (n := 5) s → IsUniformGroundRing s := by
  native_decide

private theorem gte_ring_ground_states_uniform_n6 :
    ∀ s : Fin 6 → Fin 7, IsZeroEnergyRing (n := 6) s → IsUniformGroundRing s := by
  native_decide

private theorem gte_ring_ground_states_uniform_n7 :
    ∀ s : Fin 7 → Fin 7, IsZeroEnergyRing (n := 7) s → IsUniformGroundRing s := by
  native_decide

/-- **gte_ring_ground_states_uniform** (CatAL): every cyclic zero-energy configuration is
    exactly `{0ⁿ, 1ⁿ, 5ⁿ}` for ring lengths `3 ≤ n ≤ 7` (machine-checked per length). -/
theorem gte_ring_ground_states_uniform {n : ℕ} [NeZero n] (hn : 3 ≤ n) (hnub : n ≤ 7)
    (s : Fin n → Fin 7) (h : IsZeroEnergyRing s) :
    IsUniformGroundRing s := by
  have hn' : n = 3 ∨ n = 4 ∨ n = 5 ∨ n = 6 ∨ n = 7 := by omega
  rcases hn' with rfl | rfl | rfl | rfl | rfl
  · simpa using gte_ring_ground_states_uniform_n3 s h
  · simpa using gte_ring_ground_states_uniform_n4 s h
  · simpa using gte_ring_ground_states_uniform_n5 s h
  · simpa using gte_ring_ground_states_uniform_n6 s h
  · simpa using gte_ring_ground_states_uniform_n7 s h

theorem gte_ring_ground_states_uniform_bundle {n : ℕ} [NeZero n] (hn : 3 ≤ n) (hnub : n ≤ 7) :
    (∀ s : Fin n → Fin 7, IsZeroEnergyRing (n := n) s → IsUniformGroundRing s) ∧
      (∀ c ∈ groundSpinValues, IsZeroEnergyRing (n := n) (fun (_ : Fin n) => c)) := by
  refine ⟨fun s h => gte_ring_ground_states_uniform hn hnub s h, ?_⟩
  intro c hc
  exact uniform_ground_ring_satisfies_zero_energy (n := n) c hc (fun (_ : Fin n) => c)
    (fun _ => rfl)

end UgpLean.Polynomial.SpinSevenGroundSpace
