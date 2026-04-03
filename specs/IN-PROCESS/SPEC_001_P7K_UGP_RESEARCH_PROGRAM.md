# SPEC_001_P7K — UGP Lean Research Program: Open Conjectures and New Directions

**Status:** IN-PROCESS  
**Date:** April 2026  
**Repository:** ugp-lean  
**Authors:** Nova Spivack  

---

## Purpose

This spec records the research program for ugp-lean: the mathematically important
open questions about UGP that we believe can be proved or substantially advanced by
Lean formalization. Items are ordered by mathematical depth and downstream value.

Each item is a precise, self-contained conjecture or research direction with:
- A clear mathematical statement
- The evidence or heuristic supporting it
- Why it matters (downstream value)
- The likely Lean strategy

---

## ITEM 1 — Mirror-Dual Singular Series

**Conjecture:** The mirror-dual pair count $M(N) = |\{n \leq N : R_n \text{ has a mirror-dual pair}\}|$
satisfies

$$M(N) \sim \mathfrak{S} \cdot \sum_{n=1}^{N} \frac{\tau'(R_n)}{(n \ln 2)^2}$$

where $\mathfrak{S} \approx 5.56$ is a singular series correction factor, $\tau'(R_n)$
counts strict-ridge divisor pairs, and the factor $(n \ln 2)^2$ comes from the two
independent primality conditions on $c_1(b_2,q_2)$ and $c_1(q_2,b_2)$.

**Evidence:** Computational data through $n=50$ gives 30 pairs; naive heuristic gives 5.4;
correction factor 5.56. This is strikingly similar to the twin prime singular series
$\mathfrak{C}_2 \approx 1.32$ (Bateman-Horn), but much larger, suggesting UGP primes
are "more prime" than expected due to the algebraic constraints of the ridge sieve.

**Why it matters:** A proven asymptotic for $M(N)$ would:
1. Establish the Mirror-Dual Conjecture as "morally true" in the Bateman-Horn sense
2. Compute the singular series $\mathfrak{S}$ as a product over primes — potentially
   derivable from the $\rho_F$ local factor data already in ugp-lean
3. Connect UGP prime density to the Euler product structure already partially formalized
   in `ResonantFactory.lean`

**Lean strategy:**
- Formalize the Bateman-Horn conjecture statement for the UGP prime formula
- Prove the local factors $E_p = 1 - \rho_F(p)/(p-1)^2$ exactly from the certified
  $\rho_F$ data (already in `ResonantFactory.lean` for $p \leq 113$)
- State: $\mathfrak{S} = \prod_p E_p$ as a formal definition, certify its positivity
- The product $\mathfrak{S} > 0$ would be a provable lower bound from certified local data

---

## ITEM 2 — The 137 Derivation Theorem

**Conjecture:** The arithmetic identity $2b_1 - a_2 = 137$ is not a coincidence
but is the unique consequence of three UGP-1 structural constraints at $n=10$:
(a) $b_1$ is determined by the survivor pair $(42, 24)$ of $R_{10} = 1008$,
(b) $a_2$ is determined by the first odd-step orbit via $a_2 = m_1 - (n+2-1) = 20 - 12 = 8$
    (wait — need to recheck: actually $a_2 = 9$ in the orbit), and
(c) the result 137 is prime and equal to the integer nearest to $1/\alpha_{em}$
    where $\alpha_{em}$ is the fine structure constant.

The formal claim: 137 is the **unique** prime $p$ expressible as $2b_1 - a_2$ for the
unique $n$ (namely $n=10$) where a mirror-dual pair exists with $b_2 < q_2 \leq 2b_2$.

**Evidence:** At $n=10$: $2 \cdot 73 - 9 = 137$. At $n=13$: $2 \cdot 209 - a_2^{(13)} = ?$
(need to compute the n=13 orbit). The claim is that this formula only produces 137 at $n=10$
with the canonical survivor pair. This would explain why 137 appears: it is the forced
arithmetic output of the smallest mirror-dual level.

**Why it matters:**
- This is the rigorous version of the "137 echo" already in ugp-lean as `alpha_echo`
- A uniqueness proof would transform this from a numerical curiosity into a structural theorem
- Downstream: motivates the claim that UGP may have relevance to fundamental constants

**Lean strategy:**
- For each ridge level $n \in \{10, 13, 16\}$ with mirror-dual pairs, compute $2b_1^{(n)} - a_2^{(n)}$
- Prove that only $n=10$ with pair $(42,24)$ gives a prime in this formula
- This is a finite `native_decide` computation at the certified levels

---

## ITEM 3 — Asymptotic Sparsity of Prime-Locked Levels

**Conjecture:** Let $N(X) = |\{10 \leq n \leq X : R_n \text{ has at least one prime-locked seed}\}|$.
Then $N(X) / X \to 0$ as $X \to \infty$.

More precisely: $N(X) = O(X / \log X)$ by the heuristic argument (each level contributes
$\sim \tau'(R_n) / (n \ln 2)$ expected prime-locked seeds, and the sum converges slowly).

**Evidence:** Computation gives $N(60) / 50 \approx 0.54$, which is still substantial,
but the heuristic predicts this falls as $n$ grows. The key fact: $c_1 \sim 2^n$
(exponentially large), so primality probability $\sim 1/(n \ln 2) \to 0$.

**Why it matters:**
- Rigorously quantifies the "rarity" of the $n=10$ solution
- A proven upper bound $N(X) = O(X^\alpha)$ for $\alpha < 1$ would imply asymptotic sparsity
- The proof strategy is cleaner than the mirror-dual conjecture (only one primality condition)

**Lean strategy:**
- Prove: $\Pr[c_1(b_2,q_2) \text{ prime}] \lesssim 1/(n \ln 2)$ for typical pairs at level $n$
- This requires formalizing a version of the prime number theorem for the UGP formula
- A weaker version: prove that $\sum_{n=10}^{\infty} 1/(n \ln 2)$ converges, giving
  finite expected count — this is a `norm_num` / `linarith` computation

---

## ITEM 4 — Quarter-Lock Stability Under Ridge Surgery

**Conjecture:** For any finite "clopen surgery" (small perturbation) of the UGP-1
parameters $(s, g, t) = (7, 13, 20)$ that preserves the ridge divisibility structure
$b_2 q_2 = R_n$, the Quarter-Lock identity $k_M = k_{G_2} + \frac{1}{4}k_L^2$
continues to hold to first order in the perturbation parameter $\epsilon$.

**More precisely:** Define the perturbed parameters $s_\epsilon = 7 + \epsilon s'$,
$g_\epsilon = 13 + \epsilon g'$, $t_\epsilon = 20 + \epsilon t'$. Then
$\Phi(\epsilon) := k_M(\epsilon) - k_{G_2}(\epsilon) - \frac{1}{4}k_L^2(\epsilon) = O(\epsilon^2)$.

This is the **Stability of the Quarter-Lock** (already stated in the paper and
`quarterLockStability_holds` in Lean), but the precise $O(\epsilon^2)$ bound is not proved.

**Why it matters:**
- The Quarter-Lock is the key algebraic invariant; proving it is stable to second order
  establishes it as a "robust" feature, not an artifact of the exact parameter values
- This is the analogue of Noether's theorem for UGP: the invariant persists under small
  deformations of the "law"

**Lean strategy:**
- Formalize the perturbed Quarter-Lock as a function of $(\epsilon s', \epsilon g', \epsilon t')$
- Prove $D\Phi|_{\epsilon=0} = 0$ (first derivative vanishes) using the rank-one structure
  of the Kernel Symmetry Theorem
- This requires formalizing the "defect triple" $(\mathcal{M}, \mathcal{G}, \mathcal{L})$
  as a polynomial function of the parameters — all computable via `ring`

---

## ITEM 5 — GTE Orbit Complexity is Maximal

**Conjecture:** The GTE trajectory $(G_1, G_2, G_3, \ldots)$ starting from the Lepton
Seed is **algorithmically incompressible** in the following sense: for any $n$, the
Kolmogorov complexity of the first $k$ values of the orbit satisfies
$K(G_1, \ldots, G_k) \geq k \cdot \log_2 \min_i |G_i| - O(1)$.

Equivalently: the orbit cannot be compressed by any finite description shorter than
the orbit itself.

**A weaker provable version:** The GTE trajectory is **not eventually periodic**
at any finite ridge level: $G_t \neq G_{t+T}$ for all $T > 0$ and all sufficiently
large $t$.

**Why it matters:**
- This would establish that the GTE is not a "degenerate" dynamical system (no periodic orbits)
- The weaker version (no eventual period) is likely provable: $c_t \to \infty$ strictly
  (monotone bit-length theorem, already in ugp-lean), so the orbit escapes to infinity
  and cannot repeat

**Lean strategy:**
- Prove: $c_t$ is strictly increasing along the canonical orbit beyond $G_3$
  (this follows from `c_values_strictly_monotone` plus the Mersenne ladder structure)
- Corollary: $G_t \neq G_{t+T}$ for all $T > 0$ — the orbit never repeats
- This is a `native_decide` check for small $t$ and an induction argument for large $t$

---

## ITEM 6 — The Ridge Spectrum and Mersenne Selectivity

**Conjecture (Mersenne Shell):** Among all levels $n$, the ones that produce
mirror-dual pairs are those where $R_n = 2^n - 16$ factors as a product of "balanced"
divisors — specifically, where $\tau(R_n)$ (the divisor count) is large relative to $n$.
Precisely: if $\tau(R_n) \geq C \cdot n^{1+\epsilon}$ for some $C, \epsilon > 0$,
then $n$ is more likely to have a mirror-dual pair.

The connection: $\tau(R_n) = 5 \cdot \tau(2^{n-4}-1)$ (already proved in ugp-lean as
`tau_ridge_exact`), and $\tau(2^m - 1)$ is large when $m$ has many divisors (Mersenne
divisibility structure).

**Lean strategy:**
- Prove: $n$ has many divisors $\Rightarrow$ $R_{n+4}$ has many divisors
  (from `tau_ridge_exact`)
- Formalize the connection: large $\tau(R_n)$ gives more "candidate" pairs,
  increasing the expected mirror-dual count
- This is a quantitative strengthening of `card_divisors_ridge_unbounded`

---

## ITEM 7 — Higher-Order Symmetry Loops

**Conjecture:** If the divisor graph of $R_n$ admits a non-trivial automorphism
subgroup $G$ that preserves prime-lock and the $b_1$-invariant, then the invariant
space contains a forced loop of length $|G|$.

The $|G|=2$ case is the mirror involution, already proved in `mirror_pair_induces_loop`.

**The $|G|=3$ case:** Does $R_n$ ever have a triad $(b_2, q_2, r_2)$ with
$b_2 q_2 = b_2 r_2 = q_2 r_2 = R_n^{2/3}$ (approximately) such that all three
$c_1$ values are prime? This would be a "triple mirror" configuration.

**Why it matters:**
- Classifies all possible symmetry types of UGP configurations
- The $|G|=2$ case (mirror duality) is the one we have; the $|G|=3$ case would be
  a new phenomenon with potentially different physics/number theory
- Lean: `mirror_pair_induces_loop` already handles $|G|=2$; extend to $|G|=3$

**Lean strategy:**
- Define a "triple" mirror configuration as three distinct $b_2$ values
  with the same $b_1$ (impossible since $b_1 = b_2 + q_2 + 7$ and $b_2 q_2 = R_n$
  uniquely determines $(b_2, q_2)$ up to swap)
- Therefore prove: **no order-3 loops exist** for the UGP-1 formula — the
  symmetry group is exactly $\mathbb{Z}/2\mathbb{Z}$
- This would be a uniqueness theorem, provable by arithmetic

---

## ITEM 8 — Computational Universality at Minimal Tile Count

**Conjecture:** The UWCA simulation of Rule 110 is tile-minimal: no proper subset
of the 5 UWCA tiles (the minterms $S_{110} = \{1,2,3,5,6\}$) can simulate any
Turing-universal CA.

More precisely: removing any single tile from the Rule 110 UWCA embedding produces
a non-universal CA (one with bounded orbit complexity).

**Why it matters:**
- Proves that the Turing universality of UGP is "efficient" — it uses the minimum
  possible tile set
- This is the analogue of the Wolfram minimal universality result for Rule 110

**Lean strategy:**
- For each of the 5 tiles, construct an explicit infinite configuration that the
  remaining 4 tiles cannot simulate correctly (this is a finite `native_decide` check
  for each missing tile on a specific neighborhood)
- `uwca_tile_verification` already checks all 8 neighborhoods; removing each tile
  produces a wrong output at some neighborhood — provable by `native_decide`

---

## ITEM 9 — The MDL Selection Principle as a Theorem

**Conjecture (MDL as Theorem):** At every ridge level $n$ where a mirror-dual pair
exists, the MDL-minimal seed (the one with smaller $c_1$) is the unique solution to
a specific minimization problem: minimize the description length of the seed triple
$(a, b_1, c_1)$ over all prime-locked triples at that level.

**More precisely:** Among all 6 candidate triples at $n=10$ (three $a$-values $\times$
two $c$-values), the LeptonSeed $(1, 73, 823)$ is the minimum under the lexicographic
order $(c, b, a)$. This is already proved in ugp-lean as `leptonSeed_is_lex_min_residual`.

The **generalization** to all levels: for any $n$ with mirror-dual pairs, the
lex-min seed under $(c_1, b_1, a)$ ordering is the unique canonical seed.

**Lean strategy:**
- Define `canonicalSeed n` as the lex-min of all prime-locked triples at level $n$
- Prove `canonicalSeed 10 = LeptonSeed` — already done
- Prove `canonicalSeed 13 = (1, 209, 9007)` — `native_decide`
- Prove the general statement: canonicalSeed is well-defined (lex-min is unique)
  for any non-empty set of prime-locked triples

---

## ITEM 10 — The UGP Orbital Zeta Function

**Conjecture:** Define the formal Dirichlet series associated to the UGP primes
(sequence $p_1 = 823, p_2 = 2137, p_3 = 9007, \ldots$):
$$Z_{\text{UGP}}(s) = \sum_{k=1}^{\infty} p_k^{-s}$$

This series has abscissa of convergence $\sigma_0 = 1$ (same as the prime zeta function),
and admits analytic continuation to $\text{Re}(s) > 0$ via the $L$-function structure
$L(s, \chi_-)^2 \cdot L(s, \chi_+)^2 \cdot G(s)$ already conjectured in the resonant
factory analysis.

**A provable piece:** The partial sums $\sum_{k=1}^{K} p_k^{-s}$ for the 57 certified
UGP primes (up to $10^8$) provide rigorous lower bounds on $|Z_{\text{UGP}}(s)|$ for
$s > 1$.

**Why it matters:**
- Connects UGP primes to the theory of $L$-functions and analytic number theory
- The $\rho_F$ identity (already in `ResonantFactory.lean`) gives the Euler product
  structure directly: $Z_{\text{UGP}}(s) = \prod_p (1 - p^{-s})^{-\rho_F^*(p)}$
  for appropriate local factors
- This is the bridge between the algebraic UGP structure and the analytic structure
  studied in the companion twins project

**Lean strategy:**
- Formally define $Z_{\text{UGP}}$ as a `tsum` over the certified UGP prime sequence
- Prove convergence for $s > 1$ from the prime counting bound for UGP primes
- Compute certified lower bounds from the 57 known terms via `norm_num`

---

## Priority and Dependencies

| Item | Difficulty | Lean Feasibility | Downstream Value |
|------|-----------|-----------------|-----------------|
| 1 (Singular Series) | Medium | High (local factors certified) | High |
| 2 (137 Derivation) | Low | Very High (`native_decide`) | High |
| 3 (Asymptotic Sparsity) | Medium | Medium | Medium |
| 4 (Quarter-Lock Stability) | Medium | High (`ring` + `linarith`) | High |
| 5 (Orbit Non-Periodicity) | Low | High (monotonicity + induction) | Medium |
| 6 (Ridge Spectrum) | Medium | High (builds on `tau_ridge_exact`) | Medium |
| 7 (No Order-3 Loops) | Low | Very High (`native_decide`) | Medium |
| 8 (Minimal Tile Count) | Low | Very High (`native_decide`) | Medium |
| 9 (MDL as Theorem) | Low | Very High (`native_decide` per level) | High |
| 10 (Orbital Zeta) | High | Medium | Very High |

**Recommended first batch:** Items 2, 5, 7, 8, 9 — all achievable with `native_decide`
plus clean arithmetic proofs, and together form a coherent story about UGP's uniqueness
and minimality properties.

**Recommended second batch:** Items 1, 4, 6 — require more Mathlib machinery but
have the highest mathematical depth.

**Long-term:** Item 10 requires the twins-project $L$-function machinery.

---

## Notes on Admissibility

All items above are:
- **Scoped to the UGP framework**: they are about the ridged arithmetic objects, not
  about physics or other external domains
- **Formally statable in Lean**: each has a precise Lean `Prop` formulation
- **Supported by evidence**: either computational data, structural arguments, or
  connection to known theorems
- **Not trivial**: each requires new proof ideas beyond what is currently in ugp-lean

Items are **not** included if they:
- Require connecting UGP to physics (out of scope for ugp-lean paper)
- Are already proved (those go in the main body, not the spec)
- Are obviously false based on computation

*SPEC_001_P7K — April 2026*
