import Mathlib
import UgpLean.Polynomial.PolyExplorations
import UgpLean.MassRelations.HiggsQuartic
import UgpLean.Algebra.F21SU3Embedding

/-!
# Eisenstein arithmetic certificates for GTE constants

Cyclotomic polynomial values Φ₃(n) = n²+n+1 and Φ₆(n) = n²−n+1 (the Eisenstein norm
`N(n+ω)`), the residue-field model of `F₂₁`, torus equivariance of the GTE polynomial `p`,
and the orbit decomposition of its zero variety over `GF(7)`.

All theorems: zero sorry, zero custom axioms.
-/

namespace UgpLean.Polynomial.EisensteinIdentities

open UgpLean.Polynomial.PolyExplorations
open UgpLean.MassRelations.HiggsQuartic
open UgpLean.Algebra.F21SU3Embedding

/-- The GTE polynomial `p(L,C,R) = C + R − C·R − L·C·R` (matches `PolyExplorations`). -/
def poly_p {K : Type*} [CommRing K] (L C Rt : K) : K :=
  C + Rt - C * Rt - L * C * Rt

-- ════════════════════════════════════════════════════════════════
-- §0  Cyclotomic polynomial values (explicit polynomial forms)
-- ════════════════════════════════════════════════════════════════

def phi3 (n : ℕ) : ℕ := n ^ 2 + n + 1

def phi6 (n : ℕ) : ℕ := n ^ 2 - n + 1

def phi12 (n : ℕ) : ℕ := n ^ 4 - n ^ 2 + 1

lemma phi6_cast (n : ℕ) : (phi6 n : ℤ) = (n : ℤ) ^ 2 - (n : ℤ) + 1 := by
  unfold phi6
  have hn : n ≤ n ^ 2 := by nlinarith [sq_nonneg n]
  have hcast : ((n ^ 2 - n : ℕ) : ℤ) = (n : ℤ) ^ 2 - (n : ℤ) := by
    rw [Nat.cast_sub hn]
    push_cast
    ring
  calc
    (phi6 n : ℤ) = ((n ^ 2 - n + 1 : ℕ) : ℤ) := rfl
    _ = ((n ^ 2 - n : ℕ) : ℤ) + 1 := by rw [Nat.cast_add, Nat.cast_one]
    _ = (n : ℤ) ^ 2 - (n : ℤ) + 1 := by rw [hcast]

private lemma int_cubic_gap_pos (a : ℤ) (ha : 4 ≤ a) :
    0 < a ^ 3 - 2 * a ^ 2 - 2 * a - 4 := by
  nlinarith [sq_nonneg (a - 4), show (4 : ℤ) ≤ a from by exact_mod_cast ha]

private lemma int_cubic_gap3_pos (a : ℤ) (ha : 6 ≤ a) :
    0 < a ^ 3 - 2 * a ^ 2 - 2 * a - 3 := by
  nlinarith [sq_nonneg (a - 3), show (6 : ℤ) ≤ a from by exact_mod_cast ha]

lemma phi6_succ_cast (n : ℕ) : (phi6 (n + 1) : ℤ) = (n : ℤ) ^ 2 + (n : ℤ) + 1 := by
  rw [phi6_cast (n + 1)]
  zify
  ring

def eisensteinNorm (a b : ℤ) : ℤ := a ^ 2 - a * b + b ^ 2

def eisensteinMul (a b c d : ℤ) : ℤ × ℤ :=
  (a * c - b * d, a * d + b * c - b * d)

-- ════════════════════════════════════════════════════════════════
-- §1  c_H = Φ₃(N_gen) = Φ₆(N_gen+1) = 13
-- ════════════════════════════════════════════════════════════════

/-- **c_H_eq_phi3_ngen** (CatAL — norm_num):
    `c_H = N_gen² + N_gen + 1 = Φ₃(N_gen) = Φ₆(N_gen+1) = 13`. -/
theorem c_H_eq_phi3_ngen :
    c_H = n_gen ^ 2 + n_gen + 1 ∧
    c_H = phi3 n_gen ∧
    c_H = phi6 (n_gen + 1) ∧
    c_H = 13 := by
  unfold c_H n_gen phi3 phi6
  norm_num

-- ════════════════════════════════════════════════════════════════
-- §2  Eisenstein norm multiplicativity and |F₂₁| = Φ₆(2)·Φ₆(3)
-- ════════════════════════════════════════════════════════════════

theorem eisensteinNorm_mul (a b c d : ℤ) :
    eisensteinNorm (eisensteinMul a b c d).1 (eisensteinMul a b c d).2 =
      eisensteinNorm a b * eisensteinNorm c d := by
  unfold eisensteinNorm eisensteinMul
  ring

theorem eisensteinNorm_two_one : eisensteinNorm 2 1 = 3 := by unfold eisensteinNorm; norm_num

theorem eisensteinNorm_three_one : eisensteinNorm 3 1 = 7 := by unfold eisensteinNorm; norm_num

theorem eisensteinNorm_five_four : eisensteinNorm 5 4 = 21 := by unfold eisensteinNorm; norm_num

/-- **f21_order_eisenstein_norm_product** (CatAL):
    `|F₂₁| = Φ₆(2)·Φ₆(3) = 21` with Eisenstein norm multiplicativity
    `N(2+ω)·N(3+ω) = N(5+4ω)`. -/
theorem f21_order_eisenstein_norm_product :
    (7 * 3 = 21) ∧
    phi6 2 * phi6 3 = 21 ∧
    eisensteinNorm 2 1 * eisensteinNorm 3 1 = eisensteinNorm 5 4 ∧
    eisensteinNorm (eisensteinMul 2 1 3 1).1 (eisensteinMul 2 1 3 1).2 =
      eisensteinNorm 2 1 * eisensteinNorm 3 1 := by
  refine ⟨f21_order, ?_, ?_, eisensteinNorm_mul 2 1 3 1⟩
  · unfold phi6; norm_num
  · rw [eisensteinNorm_two_one, eisensteinNorm_three_one, eisensteinNorm_five_four]; rfl

-- ════════════════════════════════════════════════════════════════
-- §3  Residue-field model of F₂₁ on Fin 7 × Fin 3
-- ════════════════════════════════════════════════════════════════

def fin7Add (i j : Fin 7) : Fin 7 :=
  ⟨(i.val + j.val) % 7, by omega⟩

def eisensteinZ7Action (k : Fin 3) (t : Fin 7) : Fin 7 :=
  ⟨(4 ^ k.val * t.val) % 7, by
    have ht : t.val < 7 := t.isLt
    have hk : 4 ^ k.val ≤ 16 := by fin_cases k <;> decide
    omega⟩

def eisensteinF21Mul (x y : Fin 7 × Fin 3) : Fin 7 × Fin 3 :=
  (fin7Add x.1 (eisensteinZ7Action x.2 y.1), ⟨(x.2.val + y.2.val) % 3, by omega⟩)

def standardZ7Action (k : Fin 3) (t : Fin 7) : Fin 7 :=
  ⟨(2 ^ k.val * t.val) % 7, by
    have ht : t.val < 7 := t.isLt
    have hk : 2 ^ k.val ≤ 4 := by fin_cases k <;> decide
    omega⟩

def standardF21Mul (x y : Fin 7 × Fin 3) : Fin 7 × Fin 3 :=
  (fin7Add x.1 (standardZ7Action x.2 y.1), ⟨(x.2.val + y.2.val) % 3, by omega⟩)

def f21ResidueIso (x : Fin 7 × Fin 3) : Fin 7 × Fin 3 :=
  (x.1, ⟨(2 * x.2.val) % 3, by omega⟩)

def f21ResidueIsoInv (y : Fin 7 × Fin 3) : Fin 7 × Fin 3 :=
  (y.1, ⟨(y.2.val * 2) % 3, by omega⟩)

theorem f21ResidueIso_mul (x y : Fin 7 × Fin 3) :
    f21ResidueIso (eisensteinF21Mul x y) = standardF21Mul (f21ResidueIso x) (f21ResidueIso y) := by
  fin_cases x <;> fin_cases y <;> decide

theorem f21ResidueIso_left_inv (x : Fin 7 × Fin 3) : f21ResidueIsoInv (f21ResidueIso x) = x := by
  fin_cases x <;> decide

theorem f21ResidueIso_right_inv (y : Fin 7 × Fin 3) : f21ResidueIso (f21ResidueIsoInv y) = y := by
  fin_cases y <;> decide

/-- **f21_eisenstein_residue_model** (CatAL):
    `(ℤ[ω]/(3+ω))⁺ ⋊ μ₃ ≅ F₂₁` via `φ(t,k) = (t, 2k mod 3)`; the `ω`-action is `×4`
    (Sylow-3 image `{1,2,4}`) vs the standard presentation action `×2`. -/
theorem f21_eisenstein_residue_model :
    weights = ({1, 2, 4} : Finset (ZMod 7)) ∧
    Function.Bijective f21ResidueIso ∧
    (∀ x y : Fin 7 × Fin 3,
      f21ResidueIso (eisensteinF21Mul x y) = standardF21Mul (f21ResidueIso x) (f21ResidueIso y)) ∧
    (eisensteinZ7Action ⟨1, by decide⟩ ⟨1, by decide⟩).val = 4 := by
  refine ⟨rfl, (Function.bijective_iff_has_inverse).mpr
    ⟨f21ResidueIsoInv, f21ResidueIso_left_inv, f21ResidueIso_right_inv⟩, f21ResidueIso_mul, ?_⟩
  · decide

-- ════════════════════════════════════════════════════════════════
-- §4  Torus equivariance of p
-- ════════════════════════════════════════════════════════════════

/-- Torus action `g_u(L,C,R) = (uL+u−1, uInv·C, uInv·R)` with `u·uInv = 1`. -/
def poly_p_torusAct {K : Type*} [CommRing K] (u uInv L C Rt : K) : K × K × K :=
  (u * L + u - 1, uInv * C, uInv * Rt)

theorem poly_p_torus_equivariance {K : Type*} [CommRing K] (u uInv L C Rt : K)
    (_hu : u * uInv = 1) (hinv : uInv * u = 1) :
    poly_p (u * L + u - 1) (uInv * C) (uInv * Rt) = uInv * poly_p L C Rt := by
  unfold poly_p
  have hUI : uInv ^ 2 * u = uInv := by
    calc uInv ^ 2 * u = uInv * (uInv * u) := by ring
      _ = uInv * 1 := by rw [hinv]
      _ = uInv := by ring
  have h1 : uInv ^ 2 * C * Rt * u = uInv * C * Rt := by
    calc uInv ^ 2 * C * Rt * u = (uInv ^ 2 * u) * C * Rt := by ring
      _ = uInv * C * Rt := by rw [hUI]
  ring_nf
  rw [h1]
  ring

theorem poly_p_torus_equivariance_isUnit {K : Type*} [CommRing K] (u L C Rt : K) (hu : IsUnit u) :
    poly_p (u * L + u - 1) (hu.unit.inv * C) (hu.unit.inv * Rt) =
      hu.unit.inv * poly_p L C Rt :=
  poly_p_torus_equivariance u hu.unit.inv L C Rt hu.unit.mul_inv hu.unit.inv_mul

/-- **poly_p_torus_equivariance** (CatAL — ring / decide). -/
theorem poly_p_torus_equivariance_gf7_all_units :
    ∀ u : ZMod 7, IsUnit u →
      ∀ L C Rt : ZMod 7,
        poly_p (u * L + u - 1) (u⁻¹ * C) (u⁻¹ * Rt) = u⁻¹ * poly_p L C Rt := by
  intro u hu L C Rt
  unfold poly_p
  field_simp [IsUnit.ne_zero hu]
  ring

-- ════════════════════════════════════════════════════════════════
-- §5  Variety orbit decomposition over GF(7)
-- ════════════════════════════════════════════════════════════════

abbrev gf7Triple := ZMod 7 × ZMod 7 × ZMod 7

def etherPoint : gf7Triple := (-1, 0, 0)

def torusActTriple (u : ZMod 7) (v : gf7Triple) : gf7Triple :=
  (u * v.1 + u - 1, u⁻¹ * v.2.1, u⁻¹ * v.2.2)

def poly_p_zeroFinset : Finset gf7Triple :=
  Finset.univ.filter (fun v => poly_p v.1 v.2.1 v.2.2 = 0)

def unitsZ7 : Finset (ZMod 7) :=
  ({1, 2, 3, 4, 5, 6} : Finset (ZMod 7))

def torusOrbit (v : gf7Triple) : Finset gf7Triple :=
  unitsZ7.image (fun u => torusActTriple u v)

theorem poly_p_zeroFinset_card : poly_p_zeroFinset.card = 43 := by
  native_decide

theorem poly_p_zero_variety_count_gf7_via_poly_p :
    poly_p_zeroFinset.card = 43 := poly_p_zeroFinset_card

theorem ether_in_zero_variety : etherPoint ∈ poly_p_zeroFinset := by
  native_decide

theorem ether_unique_torus_fixed :
    ∀ u : ZMod 7, IsUnit u → u ≠ 1 →
      ∀ v : gf7Triple, poly_p v.1 v.2.1 v.2.2 = 0 →
        (∀ w : ZMod 7, IsUnit w → torusActTriple w v = v) → v = etherPoint := by
  native_decide

theorem torus_orbit_card_six_of_non_ether :
    ∀ v : gf7Triple, v ∈ poly_p_zeroFinset → v ≠ etherPoint → (torusOrbit v).card = 6 := by
  native_decide

theorem torus_orbit_card_one_at_ether : (torusOrbit etherPoint).card = 1 := by
  native_decide

theorem torus_orbit_partition_count :
    (poly_p_zeroFinset.filter (· ≠ etherPoint)).card = 42 := by
  native_decide

/-- **poly_p_variety_orbit_decomposition_gf7** (CatAL):
    `V(p)(GF(7)) = {(−1,0,0)} ⊔ (7 free GF(7)*-orbits of size 6)`;
    the unique torus-fixed zero is the ether point; `card = 1 + 7·6 = 43`. -/
theorem poly_p_variety_orbit_decomposition_gf7 :
    ((Finset.univ (α := ZMod 7 × ZMod 7 × ZMod 7)).filter
      (fun v => v.2.1 + v.2.2 - v.2.1 * v.2.2 - v.1 * v.2.1 * v.2.2 = 0)).card = 43 ∧
    poly_p_zeroFinset.card = 43 ∧
    etherPoint ∈ poly_p_zeroFinset ∧
    (∀ u : ZMod 7, IsUnit u → u ≠ 1 →
      ∀ v : gf7Triple, poly_p v.1 v.2.1 v.2.2 = 0 →
        (∀ w : ZMod 7, IsUnit w → torusActTriple w v = v) → v = etherPoint) ∧
    poly_p_zeroFinset.card = 1 + 7 * 6 ∧
    (∀ v : gf7Triple, v ∈ poly_p_zeroFinset → v ≠ etherPoint → (torusOrbit v).card = 6) ∧
    (torusOrbit etherPoint).card = 1 := by
  refine ⟨?_, poly_p_zeroFinset_card, ether_in_zero_variety, ether_unique_torus_fixed, ?_, ?_, ?_⟩
  · have h := poly_p_zero_variety_count_gf7
    simpa [poly_p_zeroFinset, poly_p] using h
  · rw [poly_p_zeroFinset_card]
  · exact torus_orbit_card_six_of_non_ether
  · exact torus_orbit_card_one_at_ether

-- ════════════════════════════════════════════════════════════════
-- §6  Φ₆ identity bundle
-- ════════════════════════════════════════════════════════════════

theorem phi6_identity_I1 (n : ℤ) : n ^ 2 + n + 1 = (n + 1) ^ 2 - (n + 1) + 1 := by ring

theorem phi6_identity_I2 (n : ℤ) :
    (n ^ 2 - n + 1) * ((n + 1) ^ 2 - (n + 1) + 1) = (n ^ 2 + 1) ^ 2 - (n ^ 2 + 1) + 1 := by ring

theorem phi6_identity_I3 (n : ℤ) :
    (n ^ 2) ^ 2 - n ^ 2 + 1 = n ^ 4 - n ^ 2 + 1 := by ring

theorem phi6_identity_I4 (n : ℤ) : n ^ 3 + 1 = (n + 1) * (n ^ 2 - n + 1) := by ring

theorem phi6_succ (n : ℕ) : phi6 (n + 1) = n ^ 2 + n + 1 := by
  unfold phi6
  ring_nf
  omega

theorem phi6_sq_eq_phi12 (n : ℕ) : phi6 (n ^ 2) = phi12 n := by
  unfold phi6 phi12
  rw [show (n ^ 2) ^ 2 = n ^ 4 by ring]

theorem phi6_identity_I1_nat (n : ℕ) : phi3 n = phi6 (n + 1) := by
  rw [phi6_succ, phi3]

theorem phi6_identity_I3_nat (n : ℕ) : phi6 (n ^ 2) = phi12 n :=
  phi6_sq_eq_phi12 n

theorem phi6_identity_I4_nat (n : ℕ) : n ^ 3 + 1 = (n + 1) * phi6 n := by
  zify
  rw [phi6_cast]
  exact phi6_identity_I4 (n : ℤ)

theorem phi6_identity_I2_nat (n : ℕ) : phi6 n * phi6 (n + 1) = phi6 (n ^ 2 + 1) := by
  zify
  rw [phi6_cast, phi6_cast (n + 1), phi6_cast (n ^ 2 + 1)]
  exact phi6_identity_I2 (n : ℤ)

theorem phi6_instance_q_times_cH : 7 * c_H = phi6 10 := by
  rw [c_H_eq_phi3_ngen.2.2.2]
  unfold phi6
  norm_num

theorem phi6_instance_f21 : 3 * 7 = phi6 5 := by unfold phi6; norm_num

theorem phi12_instance_b1 : 73 = phi12 3 := by unfold phi12; norm_num

/-- **phi6_identity_bundle** (CatAL — ring / norm_num). -/
theorem phi6_identity_bundle :
    (∀ n : ℤ, n ^ 2 + n + 1 = (n + 1) ^ 2 - (n + 1) + 1) ∧
    (∀ n : ℤ,
      (n ^ 2 - n + 1) * ((n + 1) ^ 2 - (n + 1) + 1) = (n ^ 2 + 1) ^ 2 - (n ^ 2 + 1) + 1) ∧
    (∀ n : ℤ, (n ^ 2) ^ 2 - n ^ 2 + 1 = n ^ 4 - n ^ 2 + 1) ∧
    (∀ n : ℤ, n ^ 3 + 1 = (n + 1) * (n ^ 2 - n + 1)) ∧
    (∀ n : ℕ, phi3 n = phi6 (n + 1)) ∧
    (∀ n : ℕ, phi6 n * phi6 (n + 1) = phi6 (n ^ 2 + 1)) ∧
    (∀ n : ℕ, phi6 (n ^ 2) = phi12 n) ∧
    (∀ n : ℕ, n ^ 3 + 1 = (n + 1) * phi6 n) ∧
    7 * c_H = phi6 10 ∧
    3 * 7 = phi6 5 ∧
    73 = phi12 3 := by
  refine ⟨phi6_identity_I1, phi6_identity_I2, phi6_identity_I3, phi6_identity_I4,
    phi6_identity_I1_nat, phi6_identity_I2_nat, phi6_identity_I3_nat, phi6_identity_I4_nat,
    phi6_instance_q_times_cH, phi6_instance_f21, phi12_instance_b1⟩

-- ════════════════════════════════════════════════════════════════
-- §7  c_H = Φ₃(N_gen) forced uniquely at N_gen = 3
-- ════════════════════════════════════════════════════════════════

theorem phi3_eq_cubic_half_iff (n : ℕ) (hn : 0 < n) : (2 * phi3 n = n ^ 3 - 1 ↔ n = 3) := by
  constructor
  · intro h
    have hi : (2 * (n ^ 2 + n + 1) : ℤ) = n ^ 3 - 1 := by
      unfold phi3 at h
      have hn1 : 1 ≤ n ^ 3 := by nlinarith
      zify at h ⊢
      rw [Nat.cast_sub hn1] at h
      exact h
    have hfac : ((n : ℤ) - 3) * ((n : ℤ) ^ 2 + (n : ℤ) + 1) = 0 := by linarith
    have hn3 : (n : ℤ) = 3 := by
      rcases mul_eq_zero.mp hfac with h3 | hquad0
      · linarith
      · nlinarith
    exact_mod_cast hn3
  · intro h; subst h; unfold phi3; norm_num

theorem cubic_half_eq_phi3_iff (n : ℕ) (hn : 0 < n) :
    ((n ^ 3 - 1) / 2 = phi3 n ↔ n = 3) := by
  constructor
  · intro h
    match n with
    | 1 => norm_num [phi3] at h
    | 2 => norm_num [phi3] at h
    | 3 => rfl
    | n + 4 =>
      unfold phi3 at h
      exfalso
      match n with
      | 0 => norm_num at h
      | 1 => norm_num at h
      | n + 2 =>
        let a := n + 6
        have ha : 6 ≤ a := by omega
        have heq' : a ^ 3 - 1 = 2 * (a ^ 2 + a + 1) + (a ^ 3 - 1) % 2 := by
          rw [← h, Nat.div_add_mod]
        rcases (show (a ^ 3 - 1) % 2 = 0 ∨ (a ^ 3 - 1) % 2 = 1 from by omega) with r0 | r1
        · rw [r0] at heq'
          have one_le : 1 ≤ a ^ 3 := by nlinarith [show 1 ≤ a from by omega]
          have heqI : (a : ℤ) ^ 3 - 1 = 2 * ((a : ℤ) ^ 2 + (a : ℤ) + 1) := by
            zify at heq'
            rw [Nat.cast_sub one_le] at heq'
            push_cast at heq'
            linarith
          have hfI : (a : ℤ) ^ 3 - 2 * (a : ℤ) ^ 2 - 2 * (a : ℤ) - 3 = 0 := by linarith
          exact (int_cubic_gap3_pos a (by exact_mod_cast ha)).ne' hfI
        · rw [r1] at heq'
          have one_le : 1 ≤ a ^ 3 := by nlinarith [show 1 ≤ a from by omega]
          have heqI : (a : ℤ) ^ 3 - 1 = 2 * ((a : ℤ) ^ 2 + (a : ℤ) + 1) + 1 := by
            zify at heq'
            rw [Nat.cast_sub one_le] at heq'
            push_cast at heq'
            linarith
          have hfI : (a : ℤ) ^ 3 - 2 * (a : ℤ) ^ 2 - 2 * (a : ℤ) - 4 = 0 := by linarith
          exact (int_cubic_gap_pos a (by exact_mod_cast (show 4 ≤ a from by omega))).ne' hfI
  · intro h
    subst h
    unfold phi3
    norm_num

theorem phi3_eq_cH_iff (n : ℕ) (hn : 0 < n) : phi3 n = c_H ↔ n = 3 := by
  have hc : c_H = 13 := c_H_eq_phi3_ngen.2.2.2
  rw [hc]
  unfold phi3
  constructor
  · intro h
    match n with
    | 1 => norm_num at h
    | 2 => norm_num at h
    | 3 => rfl
    | n + 4 => nlinarith
  · intro h; subst h; norm_num

theorem ngen_cubic_half_eq_phi3 : (n_gen ^ 3 - 1) / 2 = phi3 n_gen := by
  unfold n_gen phi3; norm_num

/-- **cH_phi3_unique_at_ngen** (CatAL). -/
theorem cH_phi3_unique_at_ngen :
    (∀ n : ℕ, 0 < n → ((n ^ 3 - 1) / 2 = phi3 n ↔ n = 3)) ∧
    (n_gen ^ 3 - 1) / 2 = phi3 n_gen ∧
    c_H = phi3 n_gen ∧
    (∀ n : ℕ, 0 < n → c_H = phi3 n → n = n_gen) := by
  refine ⟨?_, ngen_cubic_half_eq_phi3, c_H_eq_phi3_ngen.2.1, ?_⟩
  · intro n hn
    exact cubic_half_eq_phi3_iff n hn
  · intro n hn h
    simpa [n_gen] using (phi3_eq_cH_iff n hn).mp h.symm

end UgpLean.Polynomial.EisensteinIdentities
