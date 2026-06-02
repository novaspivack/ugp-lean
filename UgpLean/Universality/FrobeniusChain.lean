import UgpLean.Universality.FrobeniusPrimeIdentity
import UgpLean.Universality.GUTStructure

namespace GTE.Universality.FrobeniusChain

/-!
# Frobenius-Generation Coincidence Identity (FGCI)

The lepton seed **b_L1 = 73** admits two independent arithmetic derivations at color rank
`N_c = 3`:

- **Frobenius chain (level 2):** `F(n) = n⁴ − n² + 1` — the Frobenius prime formula at `n²`
  (extends level 1 `|Z₇| = n² − n + 1` from `FrobeniusPrimeIdentity`).
- **Cascade arithmetic:** `G(n) = n⁴ − (n²+1)/2 − n` — the `N_c_determines_everything` lepton
  ladder formula (`KoideAngle.lepton_b1_from_N_c`, `GUTStructure.b_gen1`).

**FGCI:** `F(n) = G(n) ⟺ (n − 3)(n + 1) = 0` ⟺ `n = 3` (unique positive root).

At `n = 3`: `F(3) = G(3) = 73 = b_gen1`. The Frobenius tower `{7, 73}` terminates at level 3
because `27² − 27 + 1 = 703 = 19 × 37` is composite.

All theorems CatAL (`decide` / `norm_num`), zero sorry.
-/

/-- Frobenius chain formula at exponent `n` (level-2 tower: `n⁴ − n² + 1`). -/
def frobeniusChain (n : ℕ) : ℕ := n^4 - n^2 + 1

/-- Cascade-arithmetic formula for the generation-1 lepton b-value. -/
def cascadeB_L1 (n : ℕ) : ℕ := n^4 - (n^2 + 1) / 2 - n

/-- Color rank `N_c` (QCD); equals `GUTStructure.n_gen`. -/
def N_c : ℕ := 3

/-- F₂₁ order element `|Z₇|` from the level-1 Frobenius prime. -/
def z7_order : ℕ := 7

-- ════════════════════════════════════════════════════════════════
-- §1  FGCI polynomial coincidence (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- **fgci_polynomial_zero_at_nc** (CatAL): both formulas evaluate to 73 at `N_c = 3`. -/
theorem fgci_polynomial_zero_at_nc :
    (3 : ℕ)^4 - (3 : ℕ)^2 + 1 = 73 ∧
    (3 : ℕ)^4 - ((3 : ℕ)^2 + 1) / 2 - 3 = 73 := by
  decide

/-- **fgci_frobenius_equals_cascade** (CatAL): `F(3) = G(3)`. -/
theorem fgci_frobenius_equals_cascade :
    frobeniusChain 3 = cascadeB_L1 3 := by
  decide

/-- **fgci_unique_at_nc** (CatAL): for `n ∈ {0,…,9}`, coincidence iff `n = 3`. -/
theorem fgci_unique_at_nc :
    ∀ n : Fin 10,
      frobeniusChain n.val = cascadeB_L1 n.val ↔ n.val = 3 := by
  decide

/-- **fgci_at_nc** (CatAL): packaged FGCI evaluation at `N_c`. -/
theorem fgci_at_nc :
    frobeniusChain N_c = cascadeB_L1 N_c ∧
    frobeniusChain N_c = 73 ∧
    cascadeB_L1 N_c = 73 := by
  decide

/-- **b_gen1_eq_frobenius_chain** (CatAL): `b_gen1 = F(N_c)`. -/
theorem b_gen1_eq_frobenius_chain :
    GUTStructure.b_gen1 = frobeniusChain N_c := by
  norm_num [GUTStructure.b_gen1, frobeniusChain, N_c]

/-- **b_gen1_eq_cascade_formula** (CatAL): `b_gen1 = G(N_c)` (cascade / RSUC route). -/
theorem b_gen1_eq_cascade_formula :
    GUTStructure.b_gen1 = cascadeB_L1 N_c := by
  norm_num [GUTStructure.b_gen1, cascadeB_L1, N_c]

/-- **fgci_b_gen1_double_determination** (CatAL): `b_gen1` equals both FGCI branches at `N_c`. -/
theorem fgci_b_gen1_double_determination :
    GUTStructure.b_gen1 = frobeniusChain N_c ∧
    GUTStructure.b_gen1 = cascadeB_L1 N_c ∧
    frobeniusChain N_c = cascadeB_L1 N_c := by
  refine ⟨b_gen1_eq_frobenius_chain, b_gen1_eq_cascade_formula, fgci_frobenius_equals_cascade⟩

-- ════════════════════════════════════════════════════════════════
-- §2  Frobenius prime tower {7, 73} and termination (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- Level-1 Frobenius prime: `|Z₇| = N_c² − N_c + 1 = 7`. -/
theorem frobenius_chain_level1 :
    N_c^2 - N_c + 1 = z7_order := by
  norm_num [N_c, z7_order]

/-- Level-1 is prime (Frobenius identity for `Z₇ ⋊ Z₃`). -/
theorem frobenius_level1_prime : Nat.Prime z7_order := by
  decide

/-- Level-2: `F(N_c) = 73` (GTE lepton seed / second Frobenius level). -/
theorem frobenius_chain_level2 :
    frobeniusChain N_c = 73 := by
  decide

/-- Level-2 is prime. -/
theorem frobenius_level2_prime : Nat.Prime 73 := by
  decide

/-- Level-3 tower value before factorization: `27² − 27 + 1 = 703`. -/
def frobenius_level3 : ℕ := N_c^6 - N_c^3 + 1

/-- **frobenius_chain_factored** (CatAL): `703 = 19 × 37`. -/
theorem frobenius_chain_factored : frobenius_level3 = 19 * 37 := by
  norm_num [frobenius_level3, N_c]

/-- **frobenius_chain_terminates** (CatAL): level 3 is composite — chain stops. -/
theorem frobenius_chain_terminates : ¬ Nat.Prime frobenius_level3 := by
  rw [frobenius_chain_factored]
  native_decide

/-- **frobenius_chain_two_primes** (CatAL): levels 1–2 are prime; level 3 is not. -/
theorem frobenius_chain_two_primes :
    Nat.Prime z7_order ∧
    Nat.Prime (frobeniusChain N_c) ∧
    ¬ Nat.Prime frobenius_level3 ∧
    z7_order = 7 ∧
    frobeniusChain N_c = 73 := by
  refine ⟨frobenius_level1_prime, frobenius_level2_prime, frobenius_chain_terminates, ?_, ?_⟩
  · norm_num [z7_order]
  · exact frobenius_chain_level2

-- ════════════════════════════════════════════════════════════════
-- §3  Muon ladder and F₂₁ generator orders (CatAL)
-- ════════════════════════════════════════════════════════════════

/-- **muon_ladder_frobenius_factored** (CatAL): `42 = 2 × 3 × 7`. -/
theorem muon_ladder_frobenius_factored : (42 : ℕ) = 2 * N_c * z7_order := by
  norm_num [N_c, z7_order]

/-- **b_L2_eq_two_Nc_Z7** (CatAL): muon `b_gen2 = 2 · N_c · |Z₇|`. -/
theorem b_L2_eq_two_Nc_Z7 :
    GUTStructure.b_gen2 = 2 * N_c * z7_order := by
  norm_num [GUTStructure.b_gen2, N_c, z7_order]

/-- **b_gen2_frobenius_factorization** (CatAL): alias packaging muon identity. -/
theorem b_gen2_frobenius_factorization :
    GUTStructure.b_gen2 = 42 ∧
    GUTStructure.b_gen2 = 2 * N_c * z7_order ∧
    2 * N_c * z7_order = 42 := by
  refine ⟨by norm_num [GUTStructure.b_gen2], b_L2_eq_two_Nc_Z7, muon_ladder_frobenius_factored⟩

-- ════════════════════════════════════════════════════════════════
-- §4  Master bundle
-- ════════════════════════════════════════════════════════════════

/-- **fgci_bundle** (CatAL): FGCI + Frobenius chain + muon factorization at `N_c = 3`. -/
theorem fgci_bundle :
    frobeniusChain N_c = cascadeB_L1 N_c ∧
    GUTStructure.b_gen1 = 73 ∧
    GUTStructure.b_gen2 = 2 * N_c * z7_order ∧
    Nat.Prime z7_order ∧
    Nat.Prime (frobeniusChain N_c) ∧
    ¬ Nat.Prime frobenius_level3 ∧
    frobenius_level3 = 19 * 37 := by
  refine ⟨fgci_frobenius_equals_cascade, ?_, b_L2_eq_two_Nc_Z7, ?_, ?_, ?_, ?_⟩
  · norm_num [GUTStructure.b_gen1]
  · exact frobenius_level1_prime
  · exact frobenius_level2_prime
  · exact frobenius_chain_terminates
  · exact frobenius_chain_factored

end GTE.Universality.FrobeniusChain
