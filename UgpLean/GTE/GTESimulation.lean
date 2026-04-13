import Mathlib
import UgpLean.Core.TripleDefs
import UgpLean.GTE.UpdateMap

/-!
# UgpLean.GTE.GTESimulation — Multi-step strict GTE trajectory (n = 10)

Deterministic recurrence from `UpdateMap` (odd step: ridge to `2^n - 1`; even step:
`c' = b * q + 15` with Fibonacci lift on `Nat.dist q q_prev`).

See `EntropyNonMonotone` for Shannon entropy along this trajectory (ML-9 companion).
-/

namespace UgpLean

/-- One GTE transition at global step index `t ≥ 1` (the first transition off the seed is `t = 1`).
    `qPrev` must be `some` on every even `t` in valid runs starting from the Lepton Seed. -/
def gteTransition (n t : ℕ) (qPrev : Option ℕ) (tri : Triple) : Triple × Option ℕ :=
  let b := tri.b; let c := tri.c
  let q := gteQuotient c b
  let m := gteRemainder c b
  if h : t % 2 = 1 then
    let a' := oddStepA m n t
    let b' := oddStepB b m q
    let c' : ℕ := oddStepC n
    (⟨a', b', c'⟩, Option.some q)
  else
    have _ht0 : t % 2 = 0 := by
      omega
    match qPrev with
    | none =>
      -- Dummy; unreachable in `gteAfterSteps` (first even step has prior quotient).
      (tri, qPrev)
    | some qp =>
      let gap := Nat.dist q qp
      let fibg := Nat.fib gap
      let a' := evenStepA m n t
      let b' := evenStepB b fibg
      let c' := evenStepC b q
      (⟨a', b', c'⟩, Option.some q)

/-- Apply `s` transitions (`s = 0` returns the seed). Step indices `1 … s`. -/
def gteAfterSteps (n s : ℕ) : Triple :=
  let rec go (rem : ℕ) (tri : Triple) (qp : Option ℕ) (t : ℕ) : Triple :=
    match rem with
    | 0 => tri
    | Nat.succ rem' =>
      let p := gteTransition n t qp tri
      go rem' p.1 p.2 (t + 1)
  go s LeptonSeed none 1

/-! ### Lepton-seed trajectory at n = 10 (first nine states) -/

theorem gte_s0 : gteAfterSteps 10 0 = LeptonSeed := rfl

theorem gte_s1 : gteAfterSteps 10 1 = ⟨9, 42, 1023⟩ := by native_decide

theorem gte_s2 : gteAfterSteps 10 2 = ⟨5, 275, 1023⟩ := by native_decide

theorem gte_s3 : gteAfterSteps 10 3 = ⟨189, 74, 1023⟩ := by native_decide

theorem gte_s4 : gteAfterSteps 10 4 = ⟨53, 129, 977⟩ := by native_decide

theorem gte_s5 : gteAfterSteps 10 5 = ⟨67, 48, 1023⟩ := by native_decide

theorem gte_s6 : gteAfterSteps 10 6 = ⟨9, 425, 1023⟩ := by native_decide

theorem gte_s7 : gteAfterSteps 10 7 = ⟨168, 250, 1023⟩ := by native_decide

theorem gte_s8 : gteAfterSteps 10 8 = ⟨19, 251, 1015⟩ := by native_decide

end UgpLean
