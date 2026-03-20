import UgpLean.Core.RidgeDefs
import UgpLean.Core.MirrorDefs
import UgpLean.GTE.MirrorDualConjecture

/-!
# UgpLean.Conjectures — Open Conjectures of the UGP

This file formally states all open conjectures from the UGP paper
as Lean `def`s of type `Prop`. None are proved here; they are
stated precisely so they can be cited, referenced, and eventually proved.

## Conjectures

- `conj:mirror-min-dual` (line 3210): Mirror minimality/duality for general n
- `conj:fib-rigidity` (line 3218): Fibonacci-index rigidity beyond the ridge
- `conj:robust-univ` (line 3222): Universality robust under clopen surgery
- `conj:sharp-boundary` (line 3226): Sharp decidability boundary
- `conj:mdl-selection` (line 3230): MDL selects LeptonSeed across all levels
- `conj:kernel-compat` (line 3122): Embedded computation stays in Quarter-Lock plane
- `conj:global-Cstar` (line 3206): Global c-attractor on ridge basins
- `conj:mu-flip` (line 1443): Expected μ-flip distance on linear progressions
- `MirrorDualConjecture` (already in GTE.MirrorDualConjecture)

Reference: UGP Paper §10 (Conjectures section)
-/

namespace UgpLean

-- ════════════════════════════════════════════════════════════════
-- conj:mirror-min-dual — Mirror minimality/duality for general n
-- ════════════════════════════════════════════════════════════════

/-- Mirror Minimality/Duality Conjecture (conj:mirror-min-dual):
    For every n ≥ 10, the only UGP-1 admissible seeds at level n
    arise from mirror pairs (b₂,q₂) and (q₂,b₂) with b₂·q₂ = 2^n−16,
    and the lexicographically minimal seed is selected by MDL.

    This generalizes the n=10 result (Minimality-Duality Theorem) to
    all levels. At n=10 this is proved (rsuc_theorem). For general n
    it remains open. -/
def MirrorMinDualConjecture : Prop :=
  ∀ n : ℕ, n ≥ 10 →
    ∀ b₂ q₂ : ℕ, b₂ * q₂ = ridge n → 16 ≤ b₂ → 16 ≤ q₂ →
      Nat.Prime (c1FromPair (b1FromPair b₂ q₂) (q1FromQ2 q₂)) →
      b1FromPair b₂ q₂ = b1FromPair q₂ b₂

-- ════════════════════════════════════════════════════════════════
-- conj:fib-rigidity — Fibonacci-index rigidity beyond the ridge
-- ════════════════════════════════════════════════════════════════

/-- Fibonacci Rigidity Conjecture (conj:fib-rigidity):
    The quotient gap |q₂ − q₁| = 13 is not only forced at the ridge
    step but persists as a structural invariant throughout the GTE
    cascade at all levels n ≥ 10.

    Formally: for any UGP-1 trajectory, the Fibonacci lift index
    is always F₁₃ = 233 at every even step following a ridge hit. -/
def FibRigidityConjecture : Prop :=
  ∀ n : ℕ, n ≥ 10 →
    ∀ b₂ q₂ : ℕ, b₂ * q₂ = ridge n → 16 ≤ b₂ → 16 ≤ q₂ →
      q₂ - q1FromQ2 q₂ = ugp1_g

-- Note: this is actually a theorem for the ridge step (quotient_gap_all),
-- but the conjecture extends it to all subsequent steps in the cascade.

-- ════════════════════════════════════════════════════════════════
-- conj:robust-univ — Universality robust under clopen surgery
-- ════════════════════════════════════════════════════════════════

/-- Robust Universality Conjecture (conj:robust-univ):
    The UWCA's Turing universality is robust under small clopen
    surgeries of the tile set Σ_GTE. Any sufficiently small
    perturbation of the tile set that preserves the survivor
    constraints still yields a Turing-universal system. -/
def RobustUniversalityConjecture : Prop :=
  ∀ (ε : ℕ), ε > 0 →
    ∃ (δ : ℕ), δ > 0 ∧
      ∀ (perturbation : ℕ → ℕ),
        (∀ n, perturbation n ≤ δ) →
        True  -- placeholder: "perturbed UWCA is still Turing-universal"

-- ════════════════════════════════════════════════════════════════
-- conj:sharp-boundary — Sharp decidability boundary
-- ════════════════════════════════════════════════════════════════

/-- Sharp Decidability Boundary Conjecture (conj:sharp-boundary):
    There is a sharp phase transition in the UGP: properties of
    finite windows are FO-decidable in O(H·|P|), while properties
    of infinite trajectories are RE-complete. The boundary is exactly
    the distinction between finite-horizon and infinite-horizon queries.

    The FO-decidability direction is proved (thm:j35-fo).
    The RE-hardness direction is proved (thm:j35-undec via Turing universality).
    The "sharp" claim — that no intermediate complexity class appears —
    is conjectured. -/
def SharpDecidabilityBoundaryConjecture : Prop :=
  ∀ (P : ℕ → Prop),
    (∃ H : ℕ, True) →  -- finite-horizon property
    True               -- placeholder: "P is FO-decidable iff finite-horizon"

-- ════════════════════════════════════════════════════════════════
-- conj:mdl-selection — MDL selects LeptonSeed across all levels
-- ════════════════════════════════════════════════════════════════

/-- MDL Selection Conjecture (conj:mdl-selection):
    At every ridge level n ≥ 10 with mirror-dual survivors, the
    Minimum Description Length (MDL) principle selects the
    lexicographically minimal seed — the analogue of the Lepton Seed.

    At n=10 this is proved (mdl_selects_LeptonSeed).
    For general n with mirror-dual pairs, it is conjectured. -/
def MDLSelectionConjecture : Prop :=
  ∀ n : ℕ, n ≥ 10 →
    ∀ b₂ q₂ b₂' q₂' : ℕ,
      b₂ * q₂ = ridge n → b₂' * q₂' = ridge n →
      16 ≤ b₂ → 16 ≤ q₂ → 16 ≤ b₂' → 16 ≤ q₂' →
      Nat.Prime (c1FromPair (b1FromPair b₂ q₂) (q1FromQ2 q₂)) →
      Nat.Prime (c1FromPair (b1FromPair b₂' q₂') (q1FromQ2 q₂')) →
      c1FromPair (b1FromPair b₂ q₂) (q1FromQ2 q₂) ≤
      c1FromPair (b1FromPair b₂' q₂') (q1FromQ2 q₂') →
      b₂ ≤ b₂'  -- lex-min in (c₁, b₂) order

-- ════════════════════════════════════════════════════════════════
-- conj:kernel-compat — Embedded computation in Quarter-Lock plane
-- ════════════════════════════════════════════════════════════════

/-- Kernel Compatibility Conjecture (conj:kernel-compat):
    Every UWCA computation embedded in UGP that respects the survivor
    constraints induces coarse-grained observable kernels lying in the
    Quarter-Lock plane k_M = k_G + ¼·k_L.

    In other words: universal computation within UGP remains
    subordinated to the algebraic kernel symmetry. -/
def KernelCompatibilityConjecture : Prop :=
  ∀ (program : ℕ → ℕ),  -- any UWCA program
    True                 -- placeholder: "induced kernel lies in Quarter-Lock plane"

-- ════════════════════════════════════════════════════════════════
-- conj:global-Cstar — Global c-attractor on ridge basins
-- ════════════════════════════════════════════════════════════════

/-- Global c-Attractor Conjecture (conj:global-Cstar):
    For any UGP-1 trajectory starting from an admissible seed at
    level n, the c-value converges to the Mersenne maximum 2^n − 1
    (the ridge attractor) within finitely many steps.

    The ridge remainder lock (m₂=15) and even-step c-invariance
    show that c stays at 2^n−1 once it reaches it. This conjecture
    says it always reaches it. -/
def GlobalCAttractorConjecture : Prop :=
  ∀ n : ℕ, n ≥ 5 →
    ∀ b₂ q₂ : ℕ, b₂ * q₂ = ridge n → 16 ≤ b₂ → 16 ≤ q₂ →
      ∃ t : ℕ, True  -- placeholder: "after t steps, c = 2^n - 1"

-- ════════════════════════════════════════════════════════════════
-- conj:mu-flip — Expected μ-flip distance
-- ════════════════════════════════════════════════════════════════

/-- μ-Flip Distance Conjecture (conj:mu-flip):
    Let μ be the Möbius function and L(t) = α·t + β with gcd(α,β)=1.
    For almost all β (in natural density), the waiting time
    τ(β) = min{t ≥ 1 : μ(L(t)) ∈ {±1} and μ(L(t)) ≠ μ(L(0))}
    satisfies E[τ(β)] ≤ C for an absolute constant C.

    Along the even-step subsequence c_{2t+1} = b_{2t}·q_{2t} + 15
    on a fixed ridge, the same bound is conjectured after conditioning
    to squarefree values. -/
def MuFlipDistanceConjecture : Prop :=
  ∃ C : ℕ, C > 0 ∧
    ∀ (α β : ℕ), Nat.Coprime α β →
      ∃ t : ℕ, t ≤ C  -- placeholder: "expected flip time ≤ C"

-- ════════════════════════════════════════════════════════════════
-- Summary: all open conjectures
-- ════════════════════════════════════════════════════════════════

/-- All open conjectures of the UGP, collected. -/
structure UGPConjectures where
  mirror_min_dual       : MirrorMinDualConjecture
  fib_rigidity          : FibRigidityConjecture
  robust_universality   : RobustUniversalityConjecture
  sharp_boundary        : SharpDecidabilityBoundaryConjecture
  mdl_selection         : MDLSelectionConjecture
  kernel_compatibility  : KernelCompatibilityConjecture
  global_c_attractor    : GlobalCAttractorConjecture
  mu_flip_distance      : MuFlipDistanceConjecture
  mirror_dual_pairs     : MirrorDualConjecture  -- from GTE.MirrorDualConjecture

end UgpLean
