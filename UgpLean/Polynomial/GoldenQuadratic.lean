import Mathlib
import UgpLean.Polynomial.PolyExplorations
import UgpLean.Algebra.SRRGCABridge
import UgpLean.Universality.Z7InvariantSubsets

/-!
# Golden-Quadratic Duality

The diagonal evaluation of the GTE polynomial factors as
`p(x,x,x) − x = −x(x²+x−1)`.  The quadratic `m(x) = x²+x−1` (discriminant 5 = N_fam)
is simultaneously the SRRG fixed-point equation over ℝ and rootless over GF(7).

All theorems: zero sorry, zero custom axioms.
-/

namespace UgpLean.Polynomial.GoldenQuadratic

open UgpLean.Polynomial.PolyExplorations
open SRRGCABridge
open GTE.Z7InvariantSubsets

instance : Fact (Nat.Prime 5) := ⟨by decide⟩
instance : Fact (Nat.Prime 2) := ⟨by decide⟩
instance : Fact (Nat.Prime 3) := ⟨by decide⟩

/-- The GTE polynomial `p(L,C,R) = C + R − C·R − L·C·R` (matches PolyExplorations inline form). -/
def poly_p {α : Type*} [CommRing α] (L C r : α) : α :=
  C + r - C * r - L * C * r

/-- Diagonal evaluation `p(x,x,x)`. -/
def poly_p_diag {α : Type*} [CommRing α] (x : α) : α :=
  poly_p x x x

-- ════════════════════════════════════════════════════════════════
-- §1  Universal diagonal factorization
-- ════════════════════════════════════════════════════════════════

/-- **gte_diagonal_quadratic_factorization** (CatAL — ring):
    `p(x,x,x) − x = −x(x²+x−1)` over any commutative ring. -/
theorem gte_diagonal_quadratic_factorization {α : Type*} [CommRing α] (x : α) :
    poly_p_diag x - x = -(x * (x ^ 2 + x - 1)) := by
  unfold poly_p_diag poly_p
  ring

/-- Diagonal fixed point ⟺ zero or golden root. -/
theorem diag_fixed_iff_golden_or_zero {α : Type*} [CommRing α] [IsDomain α] (x : α) :
    poly_p_diag x = x ↔ x = 0 ∨ x ^ 2 + x - 1 = 0 := by
  constructor
  · intro h
    have hmul : x * (x ^ 2 + x - 1) = 0 := by
      have fac := gte_diagonal_quadratic_factorization x
      have : poly_p_diag x - x = 0 := sub_eq_zero.mpr h
      rw [fac] at this
      exact neg_eq_zero.mp this
    rcases mul_eq_zero.mp hmul with hx | hm
    · exact Or.inl hx
    · exact Or.inr hm
  · rintro (rfl | h)
    · simp [poly_p_diag, poly_p]
    · have fac := gte_diagonal_quadratic_factorization x
      rw [← sub_eq_zero, fac, h, mul_zero, neg_zero]

-- ════════════════════════════════════════════════════════════════
-- §2  GF(7) disc-5 dichotomy
-- ════════════════════════════════════════════════════════════════

/-- **disc5_dichotomy_gf7** (CatAL — decide):
    `x²+x−1` is rootless in GF(7) ⟺ 5 is QNR mod 7; diagonal fixed points are `{0}`. -/
theorem disc5_dichotomy_gf7 :
    (∀ x : ZMod 7, x ^ 2 + x - 1 ≠ 0) ∧
    (∀ x : ZMod 7, poly_p_diag x = x → x = 0) ∧
    (∀ x : ZMod 7, ¬IsSquare (5 : ZMod 7)) := by
  refine ⟨no_singleton_fixed_point_mod7, ?_, ?_⟩
  · intro x h
    rcases diag_fixed_iff_golden_or_zero (α := ZMod 7) x |>.mp h with hx | hm
    · exact hx
    · exact absurd hm (no_singleton_fixed_point_mod7 x)
  · decide

/-- Diagonal fixed points of `p` over GF(7) are exactly `{0}`. -/
theorem diag_fixed_points_gf7_eq_singleton_zero :
    {x : ZMod 7 | poly_p_diag x = x} = {0} := by
  ext x
  simp only [Set.mem_setOf_eq, Set.mem_singleton_iff]
  constructor
  · intro h
    exact diag_fixed_iff_golden_or_zero (α := ZMod 7) x |>.mp h |>.resolve_right
      (no_singleton_fixed_point_mod7 x)
  · rintro rfl; unfold poly_p_diag poly_p; ring

-- ════════════════════════════════════════════════════════════════
-- §3  Golden-floor duality bundle
-- ════════════════════════════════════════════════════════════════

/-- **golden_floor_duality_bundle** (CatAL):
    The SRRG fixed-point equation and the singleton-invariance anchor are the same
    quadratic `x²+x−1`: positive real root `1/φ`, rootless over GF(7). -/
theorem golden_floor_duality_bundle :
    (let x := (Real.sqrt 5 - 1) / 2; x ^ 2 + x = 1) ∧
    (∀ k : Fin 7, k * k + k ≠ 1) ∧
    (∀ x : Fin 7, x * x ≠ 5) ∧
    (∀ k : ZMod 7, k ^ 2 + k - 1 ≠ 0) ∧
    (∀ x : ZMod 7, poly_p_diag x = x → x = 0) := by
  refine ⟨gte_poly_srrg_bridge, kink_fixed_point_eq_no_solution, five_is_qnr_mod7,
    no_singleton_fixed_point_mod7, ?_⟩
  intro x h
  rcases diag_fixed_iff_golden_or_zero (α := ZMod 7) x |>.mp h with hx | hm
  · exact hx
  · exact absurd hm (no_singleton_fixed_point_mod7 x)

-- ════════════════════════════════════════════════════════════════
-- §4  7-adic floor: no root mod 7^k
-- ════════════════════════════════════════════════════════════════

private lemma no_root_master_quadratic_mod_seven :
    ∀ x : ZMod 7, x ^ 2 + x ≠ 1 := by
  intro x h
  exact no_singleton_fixed_point_mod7 x (sub_eq_zero.mpr h)

/-- **master_quadratic_no_root_mod_seven_pow** (CatAL):
    For every `k ≥ 1`, `x²+x ≠ 1` in `ZMod (7^k)`. -/
theorem master_quadratic_no_root_mod_seven_pow :
    ∀ k ≥ 1, ∀ x : ZMod (7 ^ k), x ^ 2 + x ≠ 1 := by
  intro k hk x h
  induction k, hk using Nat.le_induction with
  | base => exact no_root_master_quadratic_mod_seven x h
  | succ k _ ih =>
    have hdiv : 7 ^ k ∣ 7 ^ (k + 1) := by
      rw [pow_succ]
      exact dvd_mul_right _ _
    let φ := ZMod.castHom hdiv (ZMod (7 ^ k))
    have hred : φ x ^ 2 + φ x = 1 := by
      have := congr_arg φ h
      simpa [map_pow, map_add, map_one] using this
    exact ih (φ x) hred

-- ════════════════════════════════════════════════════════════════
-- §5  All-q split criterion via (5|q)
-- ════════════════════════════════════════════════════════════════

private lemma four_ne_zero_zmod_prime {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) : (4 : ZMod q) ≠ 0 := by
  intro h0
  have h4dvd : q ∣ 4 := (ZMod.natCast_eq_zero_iff 4 q).mp h0
  rcases h4dvd with ⟨k, hk⟩
  have hk' : q * k = 4 := by linarith [hk]
  rcases k with _ | _ | k
  · norm_num at hk'
  · have hq4 : q = 4 := by linarith [hk']
    subst hq4
    exact absurd Fact.out (by decide : ¬ Nat.Prime 4)
  · have hkmul : q * (k + 2) = 4 := by simpa using hk'
    by_cases hk0 : k = 0
    · subst hk0
      have : q = 2 := by linarith [hkmul]
      exact hq2 this
    · have hqge : 2 ≤ q := Nat.Prime.two_le Fact.out
      have hkge : 3 ≤ k + 2 := by omega
      nlinarith

private lemma two_ne_zero_zmod_prime {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) : (2 : ZMod q) ≠ 0 := by
  intro h0
  have h2 : q ∣ 2 := (ZMod.natCast_eq_zero_iff 2 q).mp h0
  have h2q : q = 2 := (Nat.prime_dvd_prime_iff_eq Fact.out (by decide : Nat.Prime 2)).mp h2
  exact hq2 h2q

/-- Completing the square: roots of `x²+x−1` exist ⟺ 5 is a square (odd characteristic). -/
theorem exists_golden_root_iff_square_five
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) :
    (∃ x : ZMod q, x ^ 2 + x - 1 = 0) ↔ IsSquare (5 : ZMod q) := by
  have h2 := two_ne_zero_zmod_prime hq2
  constructor
  · rintro ⟨x, hx⟩
    refine ⟨2 * x + 1, ?_⟩
    have h_root : x ^ 2 + x = 1 := sub_eq_zero.mp hx
    have h_eq : (2 * x + 1) * (2 * x + 1) = 5 := by
      calc (2 * x + 1) * (2 * x + 1)
        _ = (2 * x + 1) ^ 2 := by ring
        _ = 4 * (x ^ 2 + x) + 1 := by ring
        _ = 5 := by norm_num [h_root]
    exact h_eq.symm
  · rintro ⟨s, hs⟩
    set y := (s - 1) / 2
    refine ⟨y, ?_⟩
    have hs' : s * s = 5 := hs.symm
    have h2y : 2 * y + 1 = s := by
      dsimp [y]
      calc 2 * y + 1
        _ = 2 * ((s - 1) / 2) + 1 := rfl
        _ = s - 1 + 1 := by rw [mul_div_cancel₀ _ h2]
        _ = s := by ring
    have h4 : 4 * (y ^ 2 + y - 1) = 0 := by
      calc 4 * (y ^ 2 + y - 1)
        _ = (2 * y + 1) ^ 2 - 5 := by ring
        _ = s ^ 2 - 5 := by rw [h2y]
        _ = 0 := by rw [pow_two, hs', sub_self]
    have h4ne := four_ne_zero_zmod_prime hq2
    rcases mul_eq_zero.mp h4 with h4zero | hy
    · exact absurd h4zero (four_ne_zero_zmod_prime hq2)
    · exact hy

private lemma five_mod_four_eq_one : (5 : ℕ) % 4 = 1 := by decide

private lemma legendreSym_five_eq_legendreSym_q
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) :
    legendreSym q (5 : ℕ) = legendreSym 5 q := by
  simpa using legendreSym.quadratic_reciprocity_one_mod_four
    (p := 5) (q := q) five_mod_four_eq_one hq2

private lemma isSquare_five_iff_legendre_one
    {q : ℕ} [Fact q.Prime] (hq5 : q ≠ 5) (hq2 : q ≠ 2) :
    IsSquare (5 : ZMod q) ↔ legendreSym q (5 : ℕ) = 1 := by
  have h5 : (5 : ZMod q) ≠ 0 := by
    intro h0
    have h5dvd : q ∣ 5 := (ZMod.natCast_eq_zero_iff 5 q).mp h0
    have : q = 5 := (Nat.prime_dvd_prime_iff_eq Fact.out (by decide : Nat.Prime 5)).mp h5dvd
    exact hq5 this
  exact (legendreSym.eq_one_iff' (p := q) h5).symm

private lemma isSquare_mod_five_iff_residue {q : ℕ} (hq0 : (q : ZMod 5) ≠ 0) :
    IsSquare (q : ZMod 5) ↔ q % 5 = 1 ∨ q % 5 = 4 := by
  rw [← ZMod.natCast_mod q 5]
  have hbound : q % 5 < 5 := Nat.mod_lt q (by decide : 0 < 5)
  interval_cases hres : q % 5
  · rw [← ZMod.natCast_mod q 5] at hq0
    simp [hres] at hq0
  all_goals { decide }

/-- **master_quadratic_split_iff_qr5** (CatAL):
    For odd prime `q ≠ 5`: a golden root exists ⟺ 5 is a square mod `q` ⟺ `q ≡ ±1 (mod 5)`. -/
theorem master_quadratic_split_iff_qr5
    {q : ℕ} [Fact q.Prime] (hq5 : q ≠ 5) (hq2 : q ≠ 2) :
    ((∃ x : ZMod q, x ^ 2 + x = 1) ↔ IsSquare (5 : ZMod q)) ∧
      (IsSquare (5 : ZMod q) ↔ q % 5 = 1 ∨ q % 5 = 4) := by
  constructor
  · constructor
    · rintro ⟨x, hx⟩
      rcases (exists_golden_root_iff_square_five (q := q) hq2).mp ⟨x, sub_eq_zero.mpr hx⟩ with ⟨s, hs⟩
      exact ⟨s, hs⟩
    · rintro ⟨s, hs⟩
      rcases (exists_golden_root_iff_square_five (q := q) hq2).mpr ⟨s, hs⟩ with ⟨x, hx⟩
      exact ⟨x, sub_eq_zero.mp hx⟩
  · have hleg := isSquare_five_iff_legendre_one hq5 hq2
    have hrec := legendreSym_five_eq_legendreSym_q hq2
    have hq0 : (q : ZMod 5) ≠ 0 := by
      intro h0
      have h5dvd : 5 ∣ q := (ZMod.natCast_eq_zero_iff q 5).mp h0
      have : q = 5 := ((Nat.prime_dvd_prime_iff_eq (by decide : Nat.Prime 5) Fact.out).mp h5dvd).symm
      exact hq5 this
    have h5q : legendreSym 5 q = 1 ↔ IsSquare (q : ZMod 5) :=
      legendreSym.eq_one_iff' (p := 5) hq0
    have hres := isSquare_mod_five_iff_residue hq0
    constructor
    · intro h
      rw [hleg, hrec, h5q] at h
      exact hres.mp h
    · intro h
      rw [hleg, hrec, h5q]
      exact hres.mpr h

-- ════════════════════════════════════════════════════════════════
-- §6  Singleton invariant ⟺ diagonal fixed point
-- ════════════════════════════════════════════════════════════════

/-- A singleton `{k}` is closed under `p` on `k×k×k`. -/
def IsSingletonInvariant {α : Type*} [CommRing α] (k : α) : Prop :=
  poly_p k k k = k

/-- **golden_singleton_invariant_iff_diag_fixed** (CatAL):
    Singleton `{k}` is `p`-invariant ⟺ `p(k,k,k) = k` ⟺ `k = 0 ∨ k²+k−1 = 0`. -/
theorem golden_singleton_invariant_iff_diag_fixed {α : Type*} [CommRing α] [IsDomain α] (k : α) :
    (IsSingletonInvariant k ↔ poly_p_diag k = k) ∧
      (poly_p_diag k = k ↔ k = 0 ∨ k ^ 2 + k - 1 = 0) := by
  constructor
  · rfl
  · exact diag_fixed_iff_golden_or_zero k

/-- ZMod version: singleton invariance is the diagonal fixed-point equation. -/
theorem golden_singleton_finset_invariant_iff_diag_fixed
    {q : ℕ} [NeZero q] [Fact q.Prime] (k : ZMod q) :
    (∀ L C r : ZMod q, L = k → C = k → r = k → poly_p L C r = k) ↔
      k = 0 ∨ k ^ 2 + k - 1 = 0 := by
  constructor
  · intro h
    exact diag_fixed_iff_golden_or_zero k |>.mp (h k k k rfl rfl rfl)
  · rintro (rfl | h) L C r hL hC hR
    · subst_vars; unfold poly_p; ring
    · subst_vars
      rw [← poly_p_diag]
      exact eq_of_sub_eq_zero (by rw [gte_diagonal_quadratic_factorization r, h, mul_zero, neg_zero])

-- ════════════════════════════════════════════════════════════════
-- §7  Second floor ⟺ ramification at q = 5
-- ════════════════════════════════════════════════════════════════

/-- `p(0,k,k) = 3k−1` when `k²+k = 1`. -/
theorem poly_at_zero_kk_eq_three_k_minus_one
    {α : Type*} [CommRing α] (k : α) (hk : k ^ 2 + k = 1) :
    poly_p 0 k k = 3 * k - 1 := by
  unfold poly_p
  have hk' : k ^ 2 = 1 - k := (eq_sub_iff_add_eq).mpr hk
  calc
    k + k - k * k - 0 * k * k = 2 * k - k ^ 2 := by ring
    _ = 2 * k - (1 - k) := by rw [hk']
    _ = 3 * k - 1 := by ring

private lemma second_floor_zero_kk_iff_three_k
    {q : ℕ} [NeZero q] (k : ZMod q) (hk : k ^ 2 + k - 1 = 0) :
    poly_p 0 k k ∈ ({0, k} : Finset (ZMod q)) ↔ 3 * k - 1 = 0 ∨ 3 * k - 1 = k := by
  have hp0 : poly_p 0 k k = 3 * k - 1 :=
    poly_at_zero_kk_eq_three_k_minus_one k (sub_eq_zero.mp hk)
  simp only [hp0, Finset.mem_insert, Finset.mem_singleton, eq_comm]

/-- A golden root cannot equal `1/2` in `ZMod q` for odd prime `q`. -/
theorem golden_root_ne_inv_two_zmod
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (k : ZMod q) (hk : k ^ 2 + k - 1 = 0) :
    2 * k ≠ 1 := by
  intro hinv
  have hk1 : k ^ 2 + k = 1 := sub_eq_zero.mp hk
  have hfour : (4 : ZMod q) = 1 + 4 * k := by
    calc (4 : ZMod q) = 4 * (k ^ 2 + k) := by rw [hk1, mul_one]
      _ = (2 * k) ^ 2 + 4 * k := by ring
      _ = 1 + 4 * k := by rw [hinv, one_pow]
  have htwo : (2 : ZMod q) = 2 * (2 * k) := by
    calc (2 : ZMod q) = 2 * 1 := by ring
      _ = 2 * (2 * k) := by rw [hinv]
  have hthree : (3 : ZMod q) = 1 + 4 * k := by
    calc (3 : ZMod q) = 1 + 2 := by ring
      _ = 1 + 2 * (2 * k) := by rw [← htwo]
      _ = 1 + 4 * k := by ring
  have h34 : (4 : ZMod q) = 3 := hfour.trans hthree.symm
  have hf : (1 : ZMod q) = 0 := by
    calc (1 : ZMod q) = 4 - 3 := by ring
      _ = 4 - 4 := by rw [h34]
      _ = 0 := by ring
  exact one_ne_zero hf

/-- If `3k = 1` for a golden root in `ZMod q`, then `q = 5`. -/
theorem golden_three_k_eq_one_forces_q_five
    {q : ℕ} [Fact q.Prime] (k : ZMod q) (hk : k ^ 2 + k - 1 = 0) (h3 : 3 * k = 1) :
    q = 5 := by
  have hk' : k ^ 2 + k = 1 := sub_eq_zero.mp hk
  have h49 : (4 : ZMod q) = 9 := by
    calc (4 : ZMod q) = 1 + 3 := by ring
      _ = (3 * k) ^ 2 + 3 * (3 * k) := by rw [h3, one_pow, mul_one]
      _ = 9 * (k ^ 2 + k) := by ring
      _ = 9 := by rw [hk', mul_one]
  have h5 : (5 : ZMod q) = 0 := by
    have : (9 : ZMod q) - 4 = 5 := by ring
    rw [← this, h49, sub_self]
  have h5dvd : q ∣ 5 := (ZMod.natCast_eq_zero_iff 5 q).mp h5
  exact (Nat.prime_dvd_prime_iff_eq Fact.out (by decide : Nat.Prime 5)).mp h5dvd

/-- **second_floor_iff_ramified** (CatAL):
    For prime `q ≠ 2` with golden root `k`: `{0,k}` closure on the `0,k,k` face
    ⟺ `3k = 1`; this forces `q = 5`. -/
theorem second_floor_iff_ramified
    {q : ℕ} [Fact q.Prime] (hq2 : q ≠ 2) (k : ZMod q) (hk : k ^ 2 + k - 1 = 0) :
    (poly_p 0 k k ∈ ({0, k} : Finset (ZMod q)) ↔ 3 * k = 1) ∧
      (3 * k = 1 → q = 5) := by
  have h2 := two_ne_zero_zmod_prime hq2
  have hface := second_floor_zero_kk_iff_three_k k hk
  have hhalf : 3 * k - 1 ≠ k := by
    intro h
    have hinv : 2 * k = 1 := by
      calc 2 * k = (3 * k - 1) - (k - 1) := by ring
        _ = k - (k - 1) := by rw [h]
        _ = 1 := by ring
    exact absurd hinv (golden_root_ne_inv_two_zmod hq2 k hk)
  constructor
  · rw [hface]
    constructor
    · intro h
      rcases h with h0 | hk'
      · exact sub_eq_zero.mp h0
      · exact absurd hk' hhalf
    · intro h3
      exact Or.inl (sub_eq_zero.mpr h3)
  · intro h3
    exact golden_three_k_eq_one_forces_q_five k hk h3

/-- Ramified second floor at `q = 5`: `{0,2}` is closed on the `0,k,k` face. -/
theorem second_floor_zmod5_closed :
    let k := (2 : ZMod 5)
    (∀ b c : ZMod 5, b ∈ ({0, k} : Finset _) → c ∈ ({0, k} : Finset _) →
      poly_p 0 b c ∈ ({0, k} : Finset _)) := by
  decide

-- ════════════════════════════════════════════════════════════════
-- §8  GF(49) golden roots and Frobenius swap
-- ════════════════════════════════════════════════════════════════

/-- Computable model of GF(7²) as `{a + b·t | t² = 3}`. -/
inductive F49Rep where
  | mk (a b : Fin 7)
  deriving Repr, DecidableEq, Fintype

namespace F49Rep

private def add (x y : F49Rep) : F49Rep :=
  match x, y with
  | .mk xa xb, .mk ya yb => .mk (xa + ya) (xb + yb)

private def mul (x y : F49Rep) : F49Rep :=
  match x, y with
  | .mk xa xb, .mk ya yb => .mk (xa * ya + 3 * xb * yb) (xa * yb + xb * ya)

private def pow (x : F49Rep) (n : ℕ) : F49Rep :=
  n.rec (.mk 1 0) fun _ ih => mul ih x

private def golden (x : F49Rep) : Bool :=
  match add (mul x x) x with
  | .mk 1 0 => true
  | _ => false

private def goldenRoots : Finset F49Rep :=
  Finset.univ.filter (fun x => golden x)

private def frob (x : F49Rep) : F49Rep := pow x 7

end F49Rep

/-- **gf49_golden_roots_frobenius_swap** (CatAL — native_decide):
    In GF(7²), `x²+x−1` has exactly two roots; Frobenius `x ↦ x⁷` swaps them
    and fixes every subfield element with `b = 0`. -/
theorem gf49_golden_roots_frobenius_swap :
    F49Rep.goldenRoots.card = 2 ∧
    (∀ x ∈ F49Rep.goldenRoots, F49Rep.frob x ∈ F49Rep.goldenRoots ∧ F49Rep.frob x ≠ x) ∧
    (∀ a : Fin 7, F49Rep.frob (F49Rep.mk a 0) = F49Rep.mk a 0) := by
  native_decide

-- ════════════════════════════════════════════════════════════════
-- §9  Pisano period π(7) = 16
-- ════════════════════════════════════════════════════════════════

private def fibZMod7 (n : ℕ) : ZMod 7 := (Nat.fib n : ZMod 7)

/-- **pisano_seven_eq_sixteen** (CatAL — native_decide):
    The Fibonacci sequence modulo 7 has Pisano period exactly 16. -/
theorem pisano_seven_eq_sixteen :
    (∀ n : Fin 48, fibZMod7 (n.val + 16) = fibZMod7 n.val) ∧
    (∀ m : Fin 16, m.val > 0 → ∃ n : Fin 48, fibZMod7 (n.val + m.val) ≠ fibZMod7 n.val) := by
  native_decide

/-- Companion: `16 = 2(7+1)`. -/
theorem pisano_seven_eq_two_times_eight : 16 = 2 * (7 + 1) := by decide

-- ════════════════════════════════════════════════════════════════
-- §10  Splitting-field assembly (LT-089-088)
-- ════════════════════════════════════════════════════════════════

/-- **amplitude_field_is_degree2_extension** (CatAD — assembly):
    The master quadratic `m(x)=x²+x−1` is irreducible over GF(7) (disc-5 QNR);
    its splitting field GF(49) has exactly two golden roots; Frobenius `x↦x⁷`
    swaps them and fixes GF(7), modelling complex conjugation on a degree-2
    amplitude extension. -/
theorem amplitude_field_is_degree2_extension :
    (∀ x : ZMod 7, x ^ 2 + x - 1 ≠ 0) ∧
    F49Rep.goldenRoots.card = 2 ∧
    (∀ x ∈ F49Rep.goldenRoots, F49Rep.frob x ∈ F49Rep.goldenRoots ∧ F49Rep.frob x ≠ x) ∧
    (∀ a : Fin 7, F49Rep.frob (F49Rep.mk a 0) = F49Rep.mk a 0) := by
  refine ⟨no_singleton_fixed_point_mod7, ?_⟩
  exact gf49_golden_roots_frobenius_swap

-- ════════════════════════════════════════════════════════════════
-- §11  Golden universality class meta-theorem A (LT-089-089)
-- ════════════════════════════════════════════════════════════════

/-- Master quadratic discriminant equals `N_fam = 5`. -/
theorem master_quadratic_disc_eq_n_fam : (1 : ℤ) ^ 2 - 4 * 1 * (-1) = 5 := by decide

/-- **golden_universality_class_theorem** (CatAD — assembly):
    `m(x)=x²+x−1` is simultaneously certified by six independent internal GTE
    mechanisms: (1) diagonal factorization of `p`; (2) SRRG/MDL fixed point;
    (3) Rule-110 mean-field golden attractor; (4) discriminant `5=N_fam`;
    (5) dynamical vacuum uniqueness on all ring sizes; (6) GF(49) degree-2
    splitting field with Frobenius conjugation. -/
theorem golden_universality_class_theorem :
    (∀ {α : Type*} [CommRing α] (x : α), poly_p_diag x - x = -(x * (x ^ 2 + x - 1))) ∧
    (let x := (Real.sqrt 5 - 1) / 2; x ^ 2 + x = 1) ∧
    (rule110MeanField srrgFixedPoint = srrgFixedPoint) ∧
    ((1 : ℤ) ^ 2 - 4 * 1 * (-1) = 5) ∧
    ({x : ZMod 7 | poly_p_diag x = x} = {0}) ∧
    (∀ k ≥ 1, ∀ x : ZMod (7 ^ k), x ^ 2 + x ≠ 1) ∧
    ((∀ x : ZMod 7, x ^ 2 + x - 1 ≠ 0) ∧
      F49Rep.goldenRoots.card = 2 ∧
      (∀ x ∈ F49Rep.goldenRoots, F49Rep.frob x ∈ F49Rep.goldenRoots ∧ F49Rep.frob x ≠ x) ∧
      (∀ a : Fin 7, F49Rep.frob (F49Rep.mk a 0) = F49Rep.mk a 0)) := by
  refine ⟨gte_diagonal_quadratic_factorization, ?_, ?_, master_quadratic_disc_eq_n_fam,
    diag_fixed_points_gf7_eq_singleton_zero, master_quadratic_no_root_mod_seven_pow,
    amplitude_field_is_degree2_extension⟩
  · exact gte_poly_srrg_bridge
  · exact rule110_meanfield_fixed_point_golden.1

end UgpLean.Polynomial.GoldenQuadratic
