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
