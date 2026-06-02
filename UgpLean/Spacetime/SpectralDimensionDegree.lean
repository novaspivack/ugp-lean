import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import UgpLean.Spacetime.CausalGraph
import UgpLean.Spacetime.SpectralDimension

namespace GTE.Spacetime

/-! ## Periodic Successor / Predecessor -/

def finPeriodicSucc (L : ℕ) (hL : 1 < L) (a : Fin L) : Fin L :=
  finShift L a ⟨1, hL⟩

def finPeriodicPred (L : ℕ) (hL : 0 < L) (a : Fin L) : Fin L :=
  finShift L a ⟨L - 1, Nat.sub_lt hL Nat.zero_lt_one⟩

def finTimePeriodicSucc (T : ℕ) (hT : 1 < T + 1) (t : Fin (T + 1)) : Fin (T + 1) :=
  finTimeShift T t ⟨1, hT⟩

def finTimePeriodicPred (T : ℕ) (_hT : 0 < T + 1) (t : Fin (T + 1)) : Fin (T + 1) :=
  finTimeShift T t ⟨T, Nat.lt_succ_self T⟩

theorem finPeriodicSucc_adj {L : ℕ} (hL : 1 < L) (a : Fin L) :
    FinAdjPeriodic L (finPeriodicSucc L hL a) a := by
  dsimp [FinAdjPeriodic, finPeriodicSucc, finShift]
  right; rfl

theorem finPeriodicSucc_val {L : ℕ} (hL : 1 < L) (a : Fin L) :
    (finPeriodicSucc L hL a).val = (a.val + 1) % L := by
  unfold finPeriodicSucc finShift; simp [Fin.val_mk]

theorem finPeriodicPred_val {L : ℕ} (hL : 0 < L) (a : Fin L) :
    (finPeriodicPred L hL a).val = (a.val + (L - 1)) % L := by
  unfold finPeriodicPred finShift; simp [Fin.val_mk]

theorem finPeriodicSucc_pred {L : ℕ} (hL0 : 0 < L) (hL1 : 1 < L) (a : Fin L) :
    finPeriodicSucc L hL1 (finPeriodicPred L hL0 a) = a := by
  apply Fin.ext
  simp only [finPeriodicSucc_val hL1, finPeriodicPred_val hL0]
  have ha : a.val < L := a.isLt
  rcases Nat.eq_zero_or_pos a.val with h0 | hpos
  · rw [h0, Nat.zero_add,
        Nat.mod_eq_of_lt (Nat.sub_lt hL0 Nat.zero_lt_one),
        Nat.sub_add_cancel hL0, Nat.mod_self]
  · rw [show a.val + (L - 1) = a.val - 1 + L from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : a.val - 1 < L),
        show a.val - 1 + 1 = a.val from Nat.sub_add_cancel hpos,
        Nat.mod_eq_of_lt ha]

theorem finPeriodicPred_succ {L : ℕ} (hL0 : 0 < L) (hL1 : 1 < L) (a : Fin L) :
    finPeriodicPred L hL0 (finPeriodicSucc L hL1 a) = a := by
  apply Fin.ext
  simp only [finPeriodicPred_val hL0, finPeriodicSucc_val hL1]
  have ha : a.val < L := a.isLt
  rcases Nat.lt_or_ge (a.val + 1) L with hlt | hge
  · rw [Nat.mod_eq_of_lt hlt,
        show a.val + 1 + (L - 1) = a.val + L from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt ha]
  · have heq : a.val + 1 = L := by omega
    rw [show (a.val + 1) % L = 0 from by rw [heq]; exact Nat.mod_self L,
        Nat.zero_add, Nat.mod_eq_of_lt (Nat.sub_lt hL0 Nat.zero_lt_one)]
    omega

theorem finPeriodicPred_adj {L : ℕ} (hL : 0 < L) (a : Fin L) :
    FinAdjPeriodic L a (finPeriodicPred L hL a) := by
  by_cases hL1 : 1 < L
  · have h := finPeriodicSucc_adj hL1 (finPeriodicPred L hL a)
    rw [finPeriodicSucc_pred hL hL1 a] at h
    exact h
  · have : L = 1 := by omega
    subst this
    fin_cases a
    simp [FinAdjPeriodic, finPeriodicPred, finShift, Fin.ext_iff, Fin.val_zero, Nat.mod_one]

theorem finTimePeriodicSucc_val {T : ℕ} (hT : 1 < T + 1) (t : Fin (T + 1)) :
    (finTimePeriodicSucc T hT t).val = (t.val + 1) % (T + 1) := by
  unfold finTimePeriodicSucc finTimeShift; simp [Fin.val_mk]

theorem finTimePeriodicPred_val {T : ℕ} (hT : 0 < T + 1) (t : Fin (T + 1)) :
    (finTimePeriodicPred T hT t).val = (t.val + T) % (T + 1) := by
  unfold finTimePeriodicPred finTimeShift; simp [Fin.val_mk]

theorem finTimePeriodicSucc_pred {T : ℕ} (hT0 : 0 < T + 1) (hT1 : 1 < T + 1) (t : Fin (T + 1)) :
    finTimePeriodicSucc T hT1 (finTimePeriodicPred T hT0 t) = t := by
  apply Fin.ext
  simp only [finTimePeriodicSucc_val hT1, finTimePeriodicPred_val hT0]
  have ht : t.val < T + 1 := t.isLt
  rcases Nat.eq_zero_or_pos t.val with h0 | hpos
  · rw [h0, Nat.zero_add,
        Nat.mod_eq_of_lt (by omega : T < T + 1)]
    exact Nat.mod_self _
  · rw [show t.val + T = t.val - 1 + (T + 1) from by omega,
        Nat.add_mod_right, Nat.mod_eq_of_lt (by omega : t.val - 1 < T + 1),
        show t.val - 1 + 1 = t.val from Nat.sub_add_cancel hpos,
        Nat.mod_eq_of_lt ht]

theorem finTimePeriodicPred_timelike_forward {T : ℕ} (hT0 : 0 < T + 1) (hT1 : 1 < T + 1)
    (t : Fin (T + 1)) :
    ((finTimePeriodicPred T hT0 t).val + 1) % (T + 1) = t.val := by
  have h : (finTimePeriodicSucc T hT1 (finTimePeriodicPred T hT0 t)).val = t.val :=
    congrArg Fin.val (finTimePeriodicSucc_pred hT0 hT1 t)
  rwa [finTimePeriodicSucc_val hT1] at h

private theorem one_lt_L_of_three_lt {L : ℕ} (hL : 3 < L) : 1 < L := by omega
private theorem one_lt_Tp1_of_two_lt {T : ℕ} (hT : 2 < T) : 1 < T + 1 := by omega
private theorem zero_lt_L_of_three_lt {L : ℕ} (hL : 3 < L) : 0 < L := by omega
private theorem zero_lt_Tp1_of_two_lt {T : ℕ} (hT : 2 < T) : 0 < T + 1 := by omega

private theorem finPeriodicSucc_ne_self {L : ℕ} (hL : 3 < L) (a : Fin L) :
    finPeriodicSucc L (one_lt_L_of_three_lt hL) a ≠ a := by
  intro h
  have hval : (finPeriodicSucc L (one_lt_L_of_three_lt hL) a).val ≠ a.val := by
    rw [finPeriodicSucc_val (one_lt_L_of_three_lt hL)]
    rcases a with ⟨v, hv⟩
    simp only [Fin.val_mk]
    rcases Nat.lt_or_ge (v + 1) L with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; intro heq; omega
    · have hvL : v + 1 = L := by omega
      rw [hvL, Nat.mod_self]; intro heq
      have : v = L - 1 := by omega
      rw [this] at hv; omega
  exact hval (congrArg Fin.val h)

private theorem finPeriodicPred_ne_self {L : ℕ} (hL : 3 < L) (a : Fin L) :
    finPeriodicPred L (zero_lt_L_of_three_lt hL) a ≠ a := by
  intro h
  exact finPeriodicSucc_ne_self hL a <|
    (congrArg (finPeriodicSucc L (one_lt_L_of_three_lt hL)) h.symm).trans
      (finPeriodicSucc_pred (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) a)

private theorem finPeriodicSucc_ne_pred {L : ℕ} (hL : 3 < L) (a : Fin L) :
    finPeriodicSucc L (one_lt_L_of_three_lt hL) a ≠
      finPeriodicPred L (zero_lt_L_of_three_lt hL) a := by
  intro h
  have hval := congrArg Fin.val h
  simp only [finPeriodicSucc_val (one_lt_L_of_three_lt hL),
             finPeriodicPred_val (zero_lt_L_of_three_lt hL)] at hval
  have ha : a.val < L := a.isLt
  rcases Nat.eq_zero_or_pos a.val with h0 | hpos
  · simp only [h0, Nat.zero_add,
               Nat.mod_eq_of_lt (by omega : 1 < L),
               Nat.mod_eq_of_lt (by omega : L - 1 < L)] at hval
    omega
  · rcases Nat.lt_or_ge (a.val + 1) L with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hval
      have key : (a.val + (L - 1)) % L = a.val - 1 := by
        have h1 : a.val + (L - 1) = (a.val - 1) + L := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [key] at hval; omega
    · have heq : a.val + 1 = L := by omega
      rw [show (a.val + 1) % L = 0 from by rw [heq]; exact Nat.mod_self L] at hval
      have key : (a.val + (L - 1)) % L = L - 2 := by
        have h1 : a.val + (L - 1) = (L - 2) + L := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [key] at hval; omega

private theorem finTimePeriodicSucc_ne_self {T : ℕ} (hT : 2 < T) (t : Fin (T + 1)) :
    finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT) t ≠ t := by
  intro h
  have hval : (finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT) t).val ≠ t.val := by
    rw [finTimePeriodicSucc_val (one_lt_Tp1_of_two_lt hT)]
    rcases t with ⟨v, hv⟩
    simp only [Fin.val_mk]
    rcases Nat.lt_or_ge (v + 1) (T + 1) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt]; intro heq; omega
    · have hvT : v + 1 = T + 1 := by omega
      rw [hvT, Nat.mod_self]; intro heq
      have : v = T := by omega
      rw [this] at hv; omega
  exact hval (congrArg Fin.val h)

private theorem finTimePeriodicPred_ne_self {T : ℕ} (hT : 2 < T) (t : Fin (T + 1)) :
    finTimePeriodicPred T (zero_lt_Tp1_of_two_lt hT) t ≠ t := by
  intro h
  exact finTimePeriodicSucc_ne_self hT t <|
    (congrArg (finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT)) h.symm).trans
      (finTimePeriodicSucc_pred (zero_lt_Tp1_of_two_lt hT) (one_lt_Tp1_of_two_lt hT) t)

private theorem finTimePeriodicSucc_ne_pred {T : ℕ} (hT : 2 < T) (t : Fin (T + 1)) :
    finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT) t ≠
      finTimePeriodicPred T (zero_lt_Tp1_of_two_lt hT) t := by
  intro h
  have hval := congrArg Fin.val h
  simp only [finTimePeriodicSucc_val (one_lt_Tp1_of_two_lt hT),
             finTimePeriodicPred_val (zero_lt_Tp1_of_two_lt hT)] at hval
  have ht : t.val < T + 1 := t.isLt
  rcases Nat.eq_zero_or_pos t.val with h0 | hpos
  · simp only [h0, Nat.zero_add,
               Nat.mod_eq_of_lt (by omega : 1 < T + 1),
               Nat.mod_eq_of_lt (by omega : T < T + 1)] at hval
    omega
  · rcases Nat.lt_or_ge (t.val + 1) (T + 1) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at hval
      have key : (t.val + T) % (T + 1) = t.val - 1 := by
        have h1 : t.val + T = (t.val - 1) + (T + 1) := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [key] at hval; omega
    · have heq : t.val + 1 = T + 1 := by omega
      rw [show (t.val + 1) % (T + 1) = 0 from by rw [heq]; exact Nat.mod_self (T + 1)] at hval
      have key : (t.val + T) % (T + 1) = T - 1 := by
        have h1 : t.val + T = (T - 1) + (T + 1) := by omega
        rw [h1, Nat.add_mod_right, Nat.mod_eq_of_lt (by omega)]
      rw [key] at hval; omega

private theorem finAdjPeriodic_symm' {L : ℕ} {a b : Fin L} :
    FinAdjPeriodic L a b ↔ FinAdjPeriodic L b a := finAdjPeriodic_symm

private theorem finAdjPeriodic_decompose {L : ℕ} (hL0 : 0 < L) (hL1 : 1 < L) {a b : Fin L}
    (h : FinAdjPeriodic L a b) :
    b = finPeriodicSucc L hL1 a ∨ a = finPeriodicSucc L hL1 b := by
  rcases h with h | h
  · exact Or.inl (Fin.ext h.symm)
  · exact Or.inr (Fin.ext h.symm)

def periodicCausalNeighbors (L T : ℕ) (hL : 3 < L) (hT : 2 < T) (n : CausalNode L T) :
    Finset (CausalNode L T) :=
  let hL0 := zero_lt_L_of_three_lt hL
  let hL1 := one_lt_L_of_three_lt hL
  let hT0 := zero_lt_Tp1_of_two_lt hT
  let hT1 := one_lt_Tp1_of_two_lt hT
  let t := n.1
  let x := n.2.1
  let y := n.2.2.1
  let z := n.2.2.2
  let xp := finPeriodicSucc L hL1 x
  let xm := finPeriodicPred L hL0 x
  let yp := finPeriodicSucc L hL1 y
  let ym := finPeriodicPred L hL0 y
  let zp := finPeriodicSucc L hL1 z
  let zm := finPeriodicPred L hL0 z
  let tp := finTimePeriodicSucc T hT1 t
  let tm := finTimePeriodicPred T hT0 t
  { (t, xp, y, z), (t, xm, y, z), (t, x, yp, z), (t, x, ym, z), (t, x, y, zp), (t, x, y, zm),
    (tp, x, y, z), (tm, x, y, z),
    (tp, xp, y, z), (tp, xm, y, z), (tp, x, yp, z), (tp, x, ym, z), (tp, x, y, zp), (tp, x, y, zm),
    (tm, xp, y, z), (tm, xm, y, z), (tm, x, yp, z), (tm, x, ym, z), (tm, x, y, zp), (tm, x, y, zm) }

private def periodicNeighborAtAux (L T : ℕ) (hL : 3 < L) (hT : 2 < T) (n : CausalNode L T) :
    (k : ℕ) → k < 20 → CausalNode L T
  | 0, _ =>
    (n.1, finPeriodicSucc L (one_lt_L_of_three_lt hL) n.2.1, n.2.2.1, n.2.2.2)
  | 1, _ =>
    (n.1, finPeriodicPred L (zero_lt_L_of_three_lt hL) n.2.1, n.2.2.1, n.2.2.2)
  | 2, _ =>
    (n.1, n.2.1, finPeriodicSucc L (one_lt_L_of_three_lt hL) n.2.2.1, n.2.2.2)
  | 3, _ =>
    (n.1, n.2.1, finPeriodicPred L (zero_lt_L_of_three_lt hL) n.2.2.1, n.2.2.2)
  | 4, _ =>
    (n.1, n.2.1, n.2.2.1, finPeriodicSucc L (one_lt_L_of_three_lt hL) n.2.2.2)
  | 5, _ =>
    (n.1, n.2.1, n.2.2.1, finPeriodicPred L (zero_lt_L_of_three_lt hL) n.2.2.2)
  | 6, _ =>
    (finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT) n.1, n.2.1, n.2.2.1, n.2.2.2)
  | 7, _ =>
    (finTimePeriodicPred T (zero_lt_Tp1_of_two_lt hT) n.1, n.2.1, n.2.2.1, n.2.2.2)
  | 8, _ =>
    (finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT) n.1, finPeriodicSucc L (one_lt_L_of_three_lt hL) n.2.1, n.2.2.1, n.2.2.2)
  | 9, _ =>
    (finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT) n.1, finPeriodicPred L (zero_lt_L_of_three_lt hL) n.2.1, n.2.2.1, n.2.2.2)
  | 10, _ =>
    (finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT) n.1, n.2.1, finPeriodicSucc L (one_lt_L_of_three_lt hL) n.2.2.1, n.2.2.2)
  | 11, _ =>
    (finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT) n.1, n.2.1, finPeriodicPred L (zero_lt_L_of_three_lt hL) n.2.2.1, n.2.2.2)
  | 12, _ =>
    (finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT) n.1, n.2.1, n.2.2.1, finPeriodicSucc L (one_lt_L_of_three_lt hL) n.2.2.2)
  | 13, _ =>
    (finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT) n.1, n.2.1, n.2.2.1, finPeriodicPred L (zero_lt_L_of_three_lt hL) n.2.2.2)
  | 14, _ =>
    (finTimePeriodicPred T (zero_lt_Tp1_of_two_lt hT) n.1, finPeriodicSucc L (one_lt_L_of_three_lt hL) n.2.1, n.2.2.1, n.2.2.2)
  | 15, _ =>
    (finTimePeriodicPred T (zero_lt_Tp1_of_two_lt hT) n.1, finPeriodicPred L (zero_lt_L_of_three_lt hL) n.2.1, n.2.2.1, n.2.2.2)
  | 16, _ =>
    (finTimePeriodicPred T (zero_lt_Tp1_of_two_lt hT) n.1, n.2.1, finPeriodicSucc L (one_lt_L_of_three_lt hL) n.2.2.1, n.2.2.2)
  | 17, _ =>
    (finTimePeriodicPred T (zero_lt_Tp1_of_two_lt hT) n.1, n.2.1, finPeriodicPred L (zero_lt_L_of_three_lt hL) n.2.2.1, n.2.2.2)
  | 18, _ =>
    (finTimePeriodicPred T (zero_lt_Tp1_of_two_lt hT) n.1, n.2.1, n.2.2.1, finPeriodicSucc L (one_lt_L_of_three_lt hL) n.2.2.2)
  | 19, _ =>
    (finTimePeriodicPred T (zero_lt_Tp1_of_two_lt hT) n.1, n.2.1, n.2.2.1, finPeriodicPred L (zero_lt_L_of_three_lt hL) n.2.2.2)
  | _ + 20, h => absurd h (by omega)

private def periodicNeighborAt (L T : ℕ) (hL : 3 < L) (hT : 2 < T) (n : CausalNode L T)
    (i : Fin 20) : CausalNode L T :=
  periodicNeighborAtAux L T hL hT n i.val i.isLt

private theorem periodicNeighborAt_injective {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    Function.Injective (periodicNeighborAt L T hL hT n) := by
  intro i j hij
  apply Fin.ext
  revert hij
  fin_cases i
  · fin_cases j
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.2.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.2.2))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.2.2).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1).symm)
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.2).symm)
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.2).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.2).symm)
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.2).symm)
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.2.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.2))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.2.2))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.2))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.2.2).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1))
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1))
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1))
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1))
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.2.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1))
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1))
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.2))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1).symm)
    · intro hij; rfl
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.2.2))
  · fin_cases j
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicPred_ne_self hT n.1))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.2))
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finTimePeriodicSucc_ne_pred hT n.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_self hL n.2.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.fst ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicPred_ne_self hL n.2.2.1).symm)
    · intro hij
      have hcomp := congrArg (Prod.snd ∘ Prod.snd ∘ Prod.snd) hij
      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp
      exact absurd hcomp ((finPeriodicSucc_ne_pred hL n.2.2.2).symm)
    · intro hij; rfl


private theorem periodicNeighborAt_adj_0 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨0, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inl (Or.inl ⟨rfl, Or.inl ⟨?_, rfl, rfl⟩⟩)
  · exact (finAdjPeriodic_symm' (L := L)).mp (finPeriodicSucc_adj (one_lt_L_of_three_lt hL) n.2.1)

private theorem periodicNeighborAt_adj_1 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨1, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inr (Or.inl ⟨rfl, Or.inl ⟨?_, rfl, rfl⟩⟩)
  · exact (finAdjPeriodic_symm' (L := L)).mp (finPeriodicPred_adj (zero_lt_L_of_three_lt hL) n.2.1)

private theorem periodicNeighborAt_adj_2 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨2, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inl (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, ?_, rfl⟩)⟩)
  · exact (finAdjPeriodic_symm' (L := L)).mp (finPeriodicSucc_adj (one_lt_L_of_three_lt hL) n.2.2.1)

private theorem periodicNeighborAt_adj_3 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨3, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inr (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, ?_, rfl⟩)⟩)
  · exact (finAdjPeriodic_symm' (L := L)).mp (finPeriodicPred_adj (zero_lt_L_of_three_lt hL) n.2.2.1)

private theorem periodicNeighborAt_adj_4 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨4, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inl (Or.inl ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩)
  · exact (finAdjPeriodic_symm' (L := L)).mp (finPeriodicSucc_adj (one_lt_L_of_three_lt hL) n.2.2.2)

private theorem periodicNeighborAt_adj_5 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨5, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inr (Or.inl ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩)
  · exact (finAdjPeriodic_symm' (L := L)).mp (finPeriodicPred_adj (zero_lt_L_of_three_lt hL) n.2.2.2)

private theorem periodicNeighborAt_adj_6 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨6, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inl (Or.inr (Or.inl ⟨?_, rfl⟩))
  · exact finTimePeriodicSucc_val (one_lt_Tp1_of_two_lt hT) n.1

private theorem periodicNeighborAt_adj_7 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨7, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inr (Or.inr (Or.inl ⟨?_, rfl⟩))
  · exact finTimePeriodicPred_timelike_forward (zero_lt_Tp1_of_two_lt hT) (one_lt_Tp1_of_two_lt hT) n.1

private theorem periodicNeighborAt_adj_8 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨8, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inl (Or.inr (Or.inr ⟨?_, Or.inl ⟨?_, rfl, rfl⟩⟩))
  · exact finTimePeriodicSucc_val (one_lt_Tp1_of_two_lt hT) n.1
  · exact (finAdjPeriodic_symm' (L := L)).mp (finPeriodicSucc_adj (one_lt_L_of_three_lt hL) n.2.1)

private theorem periodicNeighborAt_adj_9 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨9, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inl (Or.inr (Or.inr ⟨?_, Or.inl ⟨?_, rfl, rfl⟩⟩))
  · exact finTimePeriodicSucc_val (one_lt_Tp1_of_two_lt hT) n.1
  · exact finPeriodicPred_adj (zero_lt_L_of_three_lt hL) n.2.1

private theorem periodicNeighborAt_adj_10 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨10, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inl (Or.inr (Or.inr ⟨?_, Or.inr (Or.inl ⟨rfl, ?_, rfl⟩)⟩))
  · exact finTimePeriodicSucc_val (one_lt_Tp1_of_two_lt hT) n.1
  · exact (finAdjPeriodic_symm' (L := L)).mp (finPeriodicSucc_adj (one_lt_L_of_three_lt hL) n.2.2.1)

private theorem periodicNeighborAt_adj_11 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨11, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inl (Or.inr (Or.inr ⟨?_, Or.inr (Or.inl ⟨rfl, ?_, rfl⟩)⟩))
  · exact finTimePeriodicSucc_val (one_lt_Tp1_of_two_lt hT) n.1
  · exact finPeriodicPred_adj (zero_lt_L_of_three_lt hL) n.2.2.1

private theorem periodicNeighborAt_adj_12 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨12, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inl (Or.inr (Or.inr ⟨?_, Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩))
  · exact finTimePeriodicSucc_val (one_lt_Tp1_of_two_lt hT) n.1
  · exact (finAdjPeriodic_symm' (L := L)).mp (finPeriodicSucc_adj (one_lt_L_of_three_lt hL) n.2.2.2)

private theorem periodicNeighborAt_adj_13 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨13, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inl (Or.inr (Or.inr ⟨?_, Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩))
  · exact finTimePeriodicSucc_val (one_lt_Tp1_of_two_lt hT) n.1
  · exact finPeriodicPred_adj (zero_lt_L_of_three_lt hL) n.2.2.2

private theorem periodicNeighborAt_adj_14 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨14, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inr (Or.inr (Or.inr ⟨?_, Or.inl ⟨?_, rfl, rfl⟩⟩))
  · exact finTimePeriodicPred_timelike_forward (zero_lt_Tp1_of_two_lt hT) (one_lt_Tp1_of_two_lt hT) n.1
  · exact finPeriodicSucc_adj (one_lt_L_of_three_lt hL) n.2.1

private theorem periodicNeighborAt_adj_15 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨15, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inr (Or.inr (Or.inr ⟨?_, Or.inl ⟨?_, rfl, rfl⟩⟩))
  · exact finTimePeriodicPred_timelike_forward (zero_lt_Tp1_of_two_lt hT) (one_lt_Tp1_of_two_lt hT) n.1
  · exact (finAdjPeriodic_symm' (L := L)).mp (finPeriodicPred_adj (zero_lt_L_of_three_lt hL) n.2.1)

private theorem periodicNeighborAt_adj_16 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨16, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inr (Or.inr (Or.inr ⟨?_, Or.inr (Or.inl ⟨rfl, ?_, rfl⟩)⟩))
  · exact finTimePeriodicPred_timelike_forward (zero_lt_Tp1_of_two_lt hT) (one_lt_Tp1_of_two_lt hT) n.1
  · exact finPeriodicSucc_adj (one_lt_L_of_three_lt hL) n.2.2.1

private theorem periodicNeighborAt_adj_17 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨17, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inr (Or.inr (Or.inr ⟨?_, Or.inr (Or.inl ⟨rfl, ?_, rfl⟩)⟩))
  · exact finTimePeriodicPred_timelike_forward (zero_lt_Tp1_of_two_lt hT) (one_lt_Tp1_of_two_lt hT) n.1
  · exact (finAdjPeriodic_symm' (L := L)).mp (finPeriodicPred_adj (zero_lt_L_of_three_lt hL) n.2.2.1)

private theorem periodicNeighborAt_adj_18 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨18, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inr (Or.inr (Or.inr ⟨?_, Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩))
  · exact finTimePeriodicPred_timelike_forward (zero_lt_Tp1_of_two_lt hT) (one_lt_Tp1_of_two_lt hT) n.1
  · exact finPeriodicSucc_adj (one_lt_L_of_three_lt hL) n.2.2.2

private theorem periodicNeighborAt_adj_19 {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n ⟨19, by decide⟩) := by
  dsimp [CausalGraphPeriodic]
  refine Or.inr (Or.inr (Or.inr ⟨?_, Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩))
  · exact finTimePeriodicPred_timelike_forward (zero_lt_Tp1_of_two_lt hT) (one_lt_Tp1_of_two_lt hT) n.1
  · exact (finAdjPeriodic_symm' (L := L)).mp (finPeriodicPred_adj (zero_lt_L_of_three_lt hL) n.2.2.2)

private theorem periodicNeighborAt_adj {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) (i : Fin 20) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n
      (periodicNeighborAt L T hL hT n i) := by
  fin_cases i
  · exact periodicNeighborAt_adj_0 hL hT n
  · exact periodicNeighborAt_adj_1 hL hT n
  · exact periodicNeighborAt_adj_2 hL hT n
  · exact periodicNeighborAt_adj_3 hL hT n
  · exact periodicNeighborAt_adj_4 hL hT n
  · exact periodicNeighborAt_adj_5 hL hT n
  · exact periodicNeighborAt_adj_6 hL hT n
  · exact periodicNeighborAt_adj_7 hL hT n
  · exact periodicNeighborAt_adj_8 hL hT n
  · exact periodicNeighborAt_adj_9 hL hT n
  · exact periodicNeighborAt_adj_10 hL hT n
  · exact periodicNeighborAt_adj_11 hL hT n
  · exact periodicNeighborAt_adj_12 hL hT n
  · exact periodicNeighborAt_adj_13 hL hT n
  · exact periodicNeighborAt_adj_14 hL hT n
  · exact periodicNeighborAt_adj_15 hL hT n
  · exact periodicNeighborAt_adj_16 hL hT n
  · exact periodicNeighborAt_adj_17 hL hT n
  · exact periodicNeighborAt_adj_18 hL hT n
  · exact periodicNeighborAt_adj_19 hL hT n

private theorem periodicCausalNeighbors_eq_map {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    periodicCausalNeighbors L T hL hT n =
      Finset.univ.map (Function.Embedding.mk (periodicNeighborAt L T hL hT n)
        (periodicNeighborAt_injective hL hT n)) := by
  ext m
  simp only [periodicCausalNeighbors, periodicNeighborAt, periodicNeighborAtAux,
    Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]
  constructor
  · intro hm
    simp only [periodicCausalNeighbors, periodicNeighborAt, periodicNeighborAtAux] at hm
    rcases hm with rfl | hm
    · exact ⟨⟨0, by decide⟩, rfl⟩
    · rcases hm with rfl | hm
      · exact ⟨⟨1, by decide⟩, rfl⟩
      · rcases hm with rfl | hm
        · exact ⟨⟨2, by decide⟩, rfl⟩
        · rcases hm with rfl | hm
          · exact ⟨⟨3, by decide⟩, rfl⟩
          · rcases hm with rfl | hm
            · exact ⟨⟨4, by decide⟩, rfl⟩
            · rcases hm with rfl | hm
              · exact ⟨⟨5, by decide⟩, rfl⟩
              · rcases hm with rfl | hm
                · exact ⟨⟨6, by decide⟩, rfl⟩
                · rcases hm with rfl | hm
                  · exact ⟨⟨7, by decide⟩, rfl⟩
                  · rcases hm with rfl | hm
                    · exact ⟨⟨8, by decide⟩, rfl⟩
                    · rcases hm with rfl | hm
                      · exact ⟨⟨9, by decide⟩, rfl⟩
                      · rcases hm with rfl | hm
                        · exact ⟨⟨10, by decide⟩, rfl⟩
                        · rcases hm with rfl | hm
                          · exact ⟨⟨11, by decide⟩, rfl⟩
                          · rcases hm with rfl | hm
                            · exact ⟨⟨12, by decide⟩, rfl⟩
                            · rcases hm with rfl | hm
                              · exact ⟨⟨13, by decide⟩, rfl⟩
                              · rcases hm with rfl | hm
                                · exact ⟨⟨14, by decide⟩, rfl⟩
                                · rcases hm with rfl | hm
                                  · exact ⟨⟨15, by decide⟩, rfl⟩
                                  · rcases hm with rfl | hm
                                    · exact ⟨⟨16, by decide⟩, rfl⟩
                                    · rcases hm with rfl | hm
                                      · exact ⟨⟨17, by decide⟩, rfl⟩
                                      · rcases hm with rfl | hm
                                        · exact ⟨⟨18, by decide⟩, rfl⟩
                                        · rcases hm with rfl | hm
                                          · exact ⟨⟨19, by decide⟩, rfl⟩
  · rintro ⟨i, rfl⟩
    fin_cases i <;> simp [periodicNeighborAt, periodicNeighborAtAux]

theorem periodicCausalNeighbors_card {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (periodicCausalNeighbors L T hL hT n).card = 20 := by
  rw [periodicCausalNeighbors_eq_map hL hT n, Finset.card_map, Finset.card_univ, Fintype.card_fin]

private theorem mem_periodicCausalNeighbors_adj {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n m : CausalNode L T) (hm : m ∈ periodicCausalNeighbors L T hL hT n) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n m := by
  rw [periodicCausalNeighbors_eq_map] at hm
  simp only [Finset.mem_map, Finset.mem_univ, true_and] at hm
  rcases hm with ⟨i, hi⟩
  rw [← hi]
  exact periodicNeighborAt_adj hL hT n i

private theorem adj_mem_periodicCausalNeighbors {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n m : CausalNode L T)
    (h : (CausalGraphPeriodic L T (by omega) (by omega)).Adj n m) :
    m ∈ periodicCausalNeighbors L T hL hT n := by
  rw [periodicCausalNeighbors_eq_map]
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  suffices ∃ i : Fin 20, periodicNeighborAt L T hL hT n i = m from this
  dsimp [CausalGraphPeriodic] at h
  have hL0 := zero_lt_L_of_three_lt hL
  have hL1 := one_lt_L_of_three_lt hL
  have hT0 := zero_lt_Tp1_of_two_lt hT
  have hT1 := one_lt_Tp1_of_two_lt hT
  -- Helper: prove finPeriodicPred n.x = m.x when hfa : n.x = finPeriodicSucc m.x
  have pred_succ_x : ∀ (a b : Fin L), a = finPeriodicSucc L hL1 b →
      finPeriodicPred L hL0 a = b := fun a b h => by
    rw [h]; exact finPeriodicPred_succ hL0 hL1 b
  -- Helper: prove time successor equals m.1 when ht : (n.1.val + 1) % (T+1) = m.1.val
  have time_succ_eq : ∀ (ht : (n.1.val + 1) % (T + 1) = m.1.val),
      finTimePeriodicSucc T hT1 n.1 = m.1 := fun ht =>
    Fin.ext (by rw [finTimePeriodicSucc_val]; exact ht)
  -- Helper: prove time predecessor equals m.1 when ht : (m.1.val + 1) % (T+1) = n.1.val
  have time_pred_eq : ∀ (ht : (m.1.val + 1) % (T + 1) = n.1.val),
      finTimePeriodicPred T hT0 n.1 = m.1 := fun ht => by
    apply Fin.ext
    rw [finTimePeriodicPred_val]
    rcases Nat.lt_or_ge (m.1.val + 1) (T + 1) with hlt | hge
    · rw [Nat.mod_eq_of_lt hlt] at ht
      rw [show n.1.val + T = m.1.val + (T + 1) from by omega,
          Nat.add_mod_right, Nat.mod_eq_of_lt m.1.isLt]
    · have heq : m.1.val + 1 = T + 1 := by omega
      rw [show m.1.val + 1 = T + 1 from heq, Nat.mod_self] at ht
      rw [← ht, Nat.zero_add, Nat.mod_eq_of_lt (by omega : T < T + 1)]
      omega
  rcases h with h | h
  · -- h : CausalAdjPeriodic L T n m
    rcases h with h | h | h
    · -- SpacelikeAdjPeriodic L T n m: ht : n.1 = m.1
      rcases h with ⟨ht, hsp⟩
      rcases hsp with ⟨hfa, hy, hz⟩ | ⟨hx, hfa, hz⟩ | ⟨hx, hy, hfa⟩
      · rcases finAdjPeriodic_decompose hL0 hL1 hfa with hfa | hfa
        · refine ⟨⟨0, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext ht (Prod.ext hfa.symm (Prod.ext hy hz))
        · refine ⟨⟨1, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext ht (Prod.ext (pred_succ_x n.2.1 m.2.1 hfa) (Prod.ext hy hz))
      · rcases finAdjPeriodic_decompose hL0 hL1 hfa with hfa | hfa
        · refine ⟨⟨2, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext ht (Prod.ext hx (Prod.ext hfa.symm hz))
        · refine ⟨⟨3, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext ht (Prod.ext hx (Prod.ext (pred_succ_x n.2.2.1 m.2.2.1 hfa) hz))
      · rcases finAdjPeriodic_decompose hL0 hL1 hfa with hfa | hfa
        · refine ⟨⟨4, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext ht (Prod.ext hx (Prod.ext hy hfa.symm))
        · refine ⟨⟨5, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext ht (Prod.ext hx (Prod.ext hy (pred_succ_x n.2.2.2 m.2.2.2 hfa)))
    · -- TimelikeAdjPeriodic L T n m: ht : n.1.val + 1 = m.1.val, hs : n.2 = m.2
      rcases h with ⟨ht, hs⟩
      refine ⟨⟨6, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
      exact Prod.ext (time_succ_eq ht) hs
    · -- LightConeAdjPeriodic L T n m: ht : n.1.val + 1 = m.1.val, hlc
      rcases h with ⟨ht, hlc⟩
      have hts := time_succ_eq ht
      rcases hlc with ⟨hfa, hy, hz⟩ | ⟨hx, hfa, hz⟩ | ⟨hx, hy, hfa⟩
      · rcases finAdjPeriodic_decompose hL0 hL1 hfa with hfa | hfa
        · refine ⟨⟨8, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext hts (Prod.ext hfa.symm (Prod.ext hy hz))
        · refine ⟨⟨9, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext hts (Prod.ext (pred_succ_x n.2.1 m.2.1 hfa) (Prod.ext hy hz))
      · rcases finAdjPeriodic_decompose hL0 hL1 hfa with hfa | hfa
        · refine ⟨⟨10, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext hts (Prod.ext hx (Prod.ext hfa.symm hz))
        · refine ⟨⟨11, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext hts (Prod.ext hx (Prod.ext (pred_succ_x n.2.2.1 m.2.2.1 hfa) hz))
      · rcases finAdjPeriodic_decompose hL0 hL1 hfa with hfa | hfa
        · refine ⟨⟨12, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext hts (Prod.ext hx (Prod.ext hy hfa.symm))
        · refine ⟨⟨13, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext hts (Prod.ext hx (Prod.ext hy (pred_succ_x n.2.2.2 m.2.2.2 hfa)))
  · -- h : CausalAdjPeriodic L T m n (reversed: hypotheses go m→n direction)
    rcases h with h | h | h
    · -- SpacelikeAdjPeriodic L T m n: ht : m.1 = n.1 (reversed)
      rcases h with ⟨ht, hsp⟩
      rcases hsp with ⟨hfa, hy, hz⟩ | ⟨hx, hfa, hz⟩ | ⟨hx, hy, hfa⟩
      · -- x-adj: hfa : FinAdjPeriodic L m.2.1 n.2.1
        rcases finAdjPeriodic_decompose hL0 hL1 hfa with hfa | hfa
        · -- hfa : n.2.1 = finPeriodicSucc ... m.2.1 → k=1
          refine ⟨⟨1, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext ht.symm (Prod.ext (pred_succ_x n.2.1 m.2.1 hfa) (Prod.ext hy.symm hz.symm))
        · -- hfa : m.2.1 = finPeriodicSucc ... n.2.1 → k=0
          refine ⟨⟨0, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext ht.symm (Prod.ext hfa.symm (Prod.ext hy.symm hz.symm))
      · -- y-adj
        rcases finAdjPeriodic_decompose hL0 hL1 hfa with hfa | hfa
        · refine ⟨⟨3, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext ht.symm (Prod.ext hx.symm (Prod.ext (pred_succ_x n.2.2.1 m.2.2.1 hfa) hz.symm))
        · refine ⟨⟨2, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext ht.symm (Prod.ext hx.symm (Prod.ext hfa.symm hz.symm))
      · -- z-adj
        rcases finAdjPeriodic_decompose hL0 hL1 hfa with hfa | hfa
        · refine ⟨⟨5, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext ht.symm (Prod.ext hx.symm (Prod.ext hy.symm (pred_succ_x n.2.2.2 m.2.2.2 hfa)))
        · refine ⟨⟨4, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext ht.symm (Prod.ext hx.symm (Prod.ext hy.symm hfa.symm))
    · -- TimelikeAdjPeriodic L T m n: ht : m.1.val + 1 = n.1.val, hs : m.2 = n.2
      rcases h with ⟨ht, hs⟩
      refine ⟨⟨7, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
      exact Prod.ext (time_pred_eq ht) hs.symm
    · -- LightConeAdjPeriodic L T m n: ht : m.1.val + 1 = n.1.val, hlc
      rcases h with ⟨ht, hlc⟩
      have htp := time_pred_eq ht
      rcases hlc with ⟨hfa, hy, hz⟩ | ⟨hx, hfa, hz⟩ | ⟨hx, hy, hfa⟩
      · rcases finAdjPeriodic_decompose hL0 hL1 hfa with hfa | hfa
        · refine ⟨⟨15, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext htp (Prod.ext (pred_succ_x n.2.1 m.2.1 hfa) (Prod.ext hy.symm hz.symm))
        · refine ⟨⟨14, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext htp (Prod.ext hfa.symm (Prod.ext hy.symm hz.symm))
      · rcases finAdjPeriodic_decompose hL0 hL1 hfa with hfa | hfa
        · refine ⟨⟨17, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext htp (Prod.ext hx.symm (Prod.ext (pred_succ_x n.2.2.1 m.2.2.1 hfa) hz.symm))
        · refine ⟨⟨16, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext htp (Prod.ext hx.symm (Prod.ext hfa.symm hz.symm))
      · rcases finAdjPeriodic_decompose hL0 hL1 hfa with hfa | hfa
        · refine ⟨⟨19, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext htp (Prod.ext hx.symm (Prod.ext hy.symm (pred_succ_x n.2.2.2 m.2.2.2 hfa)))
        · refine ⟨⟨18, by decide⟩, ?_⟩; simp only [periodicNeighborAt, periodicNeighborAtAux]
          exact Prod.ext htp (Prod.ext hx.symm (Prod.ext hy.symm hfa.symm))
private theorem mem_periodicCausalNeighbors_iff_adj {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n m : CausalNode L T) :
    m ∈ periodicCausalNeighbors L T hL hT n ↔
      (CausalGraphPeriodic L T (by omega) (by omega)).Adj n m := by
  constructor
  · exact mem_periodicCausalNeighbors_adj hL hT n m
  · exact adj_mem_periodicCausalNeighbors hL hT n m

theorem periodic_causal_node_degree (hL : 3 < L) (hT : 2 < T) (n : CausalNode L T) :
    ∃ (S : Finset (CausalNode L T)), S.card = 20 ∧
      ∀ m, m ∈ S ↔ (CausalGraphPeriodic L T (by omega) (by omega)).Adj n m := by
  refine ⟨periodicCausalNeighbors L T hL hT n, ?_, ?_⟩
  · exact periodicCausalNeighbors_card hL hT n
  · intro m; exact mem_periodicCausalNeighbors_iff_adj hL hT n m

end GTE.Spacetime
