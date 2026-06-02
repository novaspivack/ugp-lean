from pathlib import Path

neighbors = [
  ("t", "xp", "y", "z"), ("t", "xm", "y", "z"), ("t", "x", "yp", "z"), ("t", "x", "ym", "z"),
  ("t", "x", "y", "zp"), ("t", "x", "y", "zm"), ("tp", "x", "y", "z"), ("tm", "x", "y", "z"),
  ("tp", "xp", "y", "z"), ("tp", "xm", "y", "z"), ("tp", "x", "yp", "z"), ("tp", "x", "ym", "z"),
  ("tp", "x", "y", "zp"), ("tp", "x", "y", "zm"), ("tm", "xp", "y", "z"), ("tm", "xm", "y", "z"),
  ("tm", "x", "yp", "z"), ("tm", "x", "ym", "z"), ("tm", "x", "y", "zp"), ("tm", "x", "y", "zm"),
]

proj = [
  "Prod.fst",
  "Prod.fst ∘ Prod.snd",
  "Prod.fst ∘ Prod.snd ∘ Prod.snd",
  "Prod.snd ∘ Prod.snd ∘ Prod.snd",
]

def diff_lemma(a, b):
    idx = next(i for i,(x,y) in enumerate(zip(a,b)) if x != y)
    va, vb = a[idx], b[idx]
    if idx == 0:
        if {va,vb} == {"tp","tm"}: return "finTimePeriodicSucc_ne_pred hT n.1", va=="tp"
        if va == "tp": return "finTimePeriodicSucc_ne_self hT n.1", True
        if vb == "tp": return "finTimePeriodicSucc_ne_self hT n.1", False
        if va == "tm": return "finTimePeriodicPred_ne_self hT n.1", True
        return "finTimePeriodicPred_ne_self hT n.1", False
    fin = ["n.2.1", "n.2.2.1", "n.2.2.2"][idx-1]
    succ_tags = {"xp", "yp", "zp"}
    pred_tags = {"xm", "ym", "zm"}
    base_tags = {"x", "y", "z"}
    if (va in succ_tags and vb in pred_tags) or (va in pred_tags and vb in succ_tags):
        return f"finPeriodicSucc_ne_pred hL {fin}", va in succ_tags
    if va in succ_tags and vb in base_tags:
        return f"finPeriodicSucc_ne_self hL {fin}", True
    if va in base_tags and vb in succ_tags:
        return f"finPeriodicSucc_ne_self hL {fin}", False
    if va in pred_tags and vb in base_tags:
        return f"finPeriodicPred_ne_self hL {fin}", True
    if va in base_tags and vb in pred_tags:
        return f"finPeriodicPred_ne_self hL {fin}", False
    raise ValueError(a, b)

lines = []
lines.append("private theorem periodicNeighborAt_injective {L T : ℕ} (hL : 3 < L) (hT : 2 < T)")
lines.append("    (n : CausalNode L T) :")
lines.append("    Function.Injective (periodicNeighborAt L T hL hT n) := by")
lines.append("  intro i j hij")
lines.append("  apply Fin.ext")
lines.append("  revert hij")
lines.append("  fin_cases i")
for i in range(20):
    lines.append(f"  · fin_cases j")
    for j in range(20):
        if i == j:
            lines.append(f"    · intro hij; rfl")
        else:
            idx = next(k for k,(x,y) in enumerate(zip(neighbors[i], neighbors[j])) if x != y)
            lem, forward = diff_lemma(neighbors[i], neighbors[j])
            sym = "" if forward else ".symm"
            p = proj[idx]
            lines.append(f"    · intro hij")
            lines.append(f"      have hcomp := congrArg ({p}) hij")
            lines.append(f"      simp [periodicNeighborAt, periodicNeighborAtAux] at hcomp")
            lines.append(f"      exact absurd hcomp (({lem}){sym})")

_repo_root = Path(__file__).resolve().parents[1]
(_repo_root / "inj_proof_gen.lean").write_text("\n".join(lines) + "\n")
for i in range(20):
    for j in range(20):
        if i != j:
            diff_lemma(neighbors[i], neighbors[j])
print(len(lines), "ok")
