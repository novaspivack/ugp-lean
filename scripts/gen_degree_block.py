#!/usr/bin/env python3
"""Generate degree proof block for splicing into SpectralDimension.lean."""

import subprocess
from pathlib import Path

ROOT = Path(__file__).resolve().parents[1]
subprocess.run(["python3", str(ROOT / "scripts" / "gen_inj.py")], check=True)

HEADER = r'''/-! ## Periodic Successor / Predecessor -/

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
  simp only [finPeriodicSucc_val hL1, finPeriodicPred_val hL0, Fin.val_mk]
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
  simp only [finTimePeriodicSucc_val hT1, finTimePeriodicPred_val hT0, Fin.val_mk]
  omega

theorem finTimePeriodicPred_timelike_forward {T : ℕ} (hT0 : 0 < T + 1) (hT1 : 1 < T + 1)
    (t : Fin (T + 1)) :
    ((finTimePeriodicPred T hT0 t).val + 1) % (T + 1) = t.val := by
  rw [finTimePeriodicPred_val hT0]
  simp only [Fin.val_mk]
  omega

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
  have h1 : finPeriodicSucc L (one_lt_L_of_three_lt hL) a =
      finPeriodicSucc L (one_lt_L_of_three_lt hL) (finPeriodicPred L (zero_lt_L_of_three_lt hL) a) :=
    congrArg (finPeriodicSucc L (one_lt_L_of_three_lt hL)) h.symm
  rw [finPeriodicSucc_pred (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) a] at h1
  exact finPeriodicSucc_ne_self hL a h1

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
  have h1 : finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT) t =
      finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT) (finTimePeriodicPred T (zero_lt_Tp1_of_two_lt hT) t) :=
    congrArg (finTimePeriodicSucc T (one_lt_Tp1_of_two_lt hT)) h.symm
  rw [finTimePeriodicSucc_pred (zero_lt_Tp1_of_two_lt hT) (one_lt_Tp1_of_two_lt hT) t] at h1
  exact finTimePeriodicSucc_ne_self hT t h1

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

'''

def aux_body(k):
    hL0 = "(zero_lt_L_of_three_lt hL)"
    hL1 = "(one_lt_L_of_three_lt hL)"
    hT0 = "(zero_lt_Tp1_of_two_lt hT)"
    hT1 = "(one_lt_Tp1_of_two_lt hT)"
    t, x, y, z = "n.1", "n.2.1", "n.2.2.1", "n.2.2.2"
    xp = f"finPeriodicSucc L {hL1} {x}"
    xm = f"finPeriodicPred L {hL0} {x}"
    yp = f"finPeriodicSucc L {hL1} {y}"
    ym = f"finPeriodicPred L {hL0} {y}"
    zp = f"finPeriodicSucc L {hL1} {z}"
    zm = f"finPeriodicPred L {hL0} {z}"
    tp = f"finTimePeriodicSucc T {hT1} {t}"
    tm = f"finTimePeriodicPred T {hT0} {t}"
    nodes = [
        (t, xp, y, z), (t, xm, y, z), (t, x, yp, z), (t, x, ym, z), (t, x, y, zp), (t, x, y, zm),
        (tp, x, y, z), (tm, x, y, z),
        (tp, xp, y, z), (tp, xm, y, z), (tp, x, yp, z), (tp, x, ym, z), (tp, x, y, zp), (tp, x, y, zm),
        (tm, xp, y, z), (tm, xm, y, z), (tm, x, yp, z), (tm, x, ym, z), (tm, x, y, zp), (tm, x, y, zm),
    ]
    a, b, c, d = nodes[k]
    return f"  | {k}, _ =>\n    ({a}, {b}, {c}, {d})"

AUX = ["private def periodicNeighborAtAux (L T : ℕ) (hL : 3 < L) (hT : 2 < T) (n : CausalNode L T) :",
       "    (k : ℕ) → k < 20 → CausalNode L T"]
for k in range(20):
    AUX.append(aux_body(k))
AUX.append("  | _ + 20, h => absurd h (by omega)")

NEIGHBOR_AT = [
    "private def periodicNeighborAt (L T : ℕ) (hL : 3 < L) (hT : 2 < T) (n : CausalNode L T)",
    "    (i : Fin 20) : CausalNode L T :=",
    "  periodicNeighborAtAux L T hL hT n i.val i.isLt",
    "",
]

KINDS = [
    ("sp_fwd", "x"), ("sp_rev", "x"), ("sp_fwd", "y"), ("sp_rev", "y"), ("sp_fwd", "z"), ("sp_rev", "z"),
    ("tm_fwd", None), ("tm_rev", None),
    ("lc_fwd", "x"), ("lc_rev", "x"), ("lc_fwd", "y"), ("lc_rev", "y"), ("lc_fwd", "z"), ("lc_rev", "z"),
    ("lc_back", "x"), ("lc_back_rev", "x"), ("lc_back", "y"), ("lc_back_rev", "y"),
    ("lc_back", "z"), ("lc_back_rev", "z"),
]

def spatial_adj_for_lightcone(forward_spatial, graph_forward, coord, hL0, hL1):
    fin = {"x": "n.2.1", "y": "n.2.2.1", "z": "n.2.2.2"}[coord]
    if forward_spatial:
        if graph_forward:
            return f"(finAdjPeriodic_symm' (L := L)).mp (finPeriodicSucc_adj ({hL1}) {fin})"
        return f"finPeriodicSucc_adj ({hL1}) {fin}"
    if graph_forward:
        return f"finPeriodicPred_adj ({hL0}) {fin}"
    return f"(finAdjPeriodic_symm' (L := L)).mp (finPeriodicPred_adj ({hL0}) {fin})"

def fin_adj_lemma(forward, coord, hL0, hL1):
    fin = {"x": "n.2.1", "y": "n.2.2.1", "z": "n.2.2.2"}[coord]
    if forward:
        return f"(finAdjPeriodic_symm' (L := L)).mp (finPeriodicSucc_adj ({hL1}) {fin})"
    return f"(finAdjPeriodic_symm' (L := L)).mp (finPeriodicPred_adj ({hL0}) {fin})"

def spacelike_refine(forward, coord, hL0, hL1):
    outer = "Or.inl" if forward else "Or.inr"
    adj = fin_adj_lemma(forward, coord, hL0, hL1)
    if coord == "x":
        return [
            f"  refine {outer} (Or.inl ⟨rfl, Or.inl ⟨?_, rfl, rfl⟩⟩)",
            f"  · exact {adj}",
        ]
    if coord == "y":
        return [
            f"  refine {outer} (Or.inl ⟨rfl, Or.inr (Or.inl ⟨rfl, ?_, rfl⟩)⟩)",
            f"  · exact {adj}",
        ]
    return [
        f"  refine {outer} (Or.inl ⟨rfl, Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩)",
        f"  · exact {adj}",
    ]

def lightcone_refine(forward_time, forward_spatial, coord, hL0, hL1, hT0, hT1, graph_forward):
    outer = "Or.inl" if graph_forward else "Or.inr"
    adj = spatial_adj_for_lightcone(forward_spatial, graph_forward, coord, hL0, hL1)
    if forward_time:
        time_pf = f"finTimePeriodicSucc_val ({hT1}) n.1"
    else:
        time_pf = f"finTimePeriodicPred_timelike_forward ({hT0}) ({hT1}) n.1"
    if coord == "x":
        return [
            f"  refine {outer} (Or.inr (Or.inr ⟨?_, Or.inl ⟨?_, rfl, rfl⟩⟩))",
            f"  · exact {time_pf}",
            f"  · exact {adj}",
        ]
    if coord == "y":
        return [
            f"  refine {outer} (Or.inr (Or.inr ⟨?_, Or.inr (Or.inl ⟨rfl, ?_, rfl⟩)⟩))",
            f"  · exact {time_pf}",
            f"  · exact {adj}",
        ]
    return [
        f"  refine {outer} (Or.inr (Or.inr ⟨?_, Or.inr (Or.inr ⟨rfl, rfl, ?_⟩)⟩))",
        f"  · exact {time_pf}",
        f"  · exact {adj}",
    ]

def adj_proof(i, kind, coord):
    hL0 = "zero_lt_L_of_three_lt hL"
    hL1 = "one_lt_L_of_three_lt hL"
    hT0 = "zero_lt_Tp1_of_two_lt hT"
    hT1 = "one_lt_Tp1_of_two_lt hT"
    lines = [
        f"private theorem periodicNeighborAt_adj_{i} {{L T : ℕ}} (hL : 3 < L) (hT : 2 < T)",
        f"    (n : CausalNode L T) :",
        f"    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n",
        f"      (periodicNeighborAt L T hL hT n ⟨{i}, by decide⟩) := by",
        "  dsimp [CausalGraphPeriodic]",
    ]
    if kind.startswith("sp_"):
        lines += spacelike_refine(kind.endswith("fwd"), coord, hL0, hL1)
    elif kind == "tm_fwd":
        lines += [
            "  refine Or.inl (Or.inr (Or.inl ⟨?_, rfl⟩))",
            f"  · exact finTimePeriodicSucc_val ({hT1}) n.1",
        ]
    elif kind == "tm_rev":
        lines += [
            "  refine Or.inr (Or.inr (Or.inl ⟨?_, rfl⟩))",
            f"  · exact finTimePeriodicPred_timelike_forward ({hT0}) ({hT1}) n.1",
        ]
    elif kind.startswith("lc_"):
        if kind.startswith("lc_back_rev"):
            graph_forward = False
            forward_time = False
            forward_spatial = False
        elif kind.startswith("lc_back"):
            graph_forward = False
            forward_time = False
            forward_spatial = True
        elif kind.startswith("lc_rev"):
            graph_forward = True
            forward_time = True
            forward_spatial = False
        else:
            graph_forward = True
            forward_time = True
            forward_spatial = True
        lines += lightcone_refine(forward_time, forward_spatial, coord, hL0, hL1, hT0, hT1, graph_forward)
    return "\n".join(lines) + "\n"

ADJ_PROOFS = [adj_proof(i, KINDS[i][0], KINDS[i][1]) for i in range(20)]
ADJ_COMBINED = [
    "private theorem periodicNeighborAt_adj {L T : ℕ} (hL : 3 < L) (hT : 2 < T)",
    "    (n : CausalNode L T) (i : Fin 20) :",
    "    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n",
    "      (periodicNeighborAt L T hL hT n i) := by",
    "  fin_cases i",
] + [f"  · exact periodicNeighborAt_adj_{k} hL hT n" for k in range(20)]

def gen_eq_map_fwd():
    lines = [
        "  · intro hm",
        "    simp only [periodicCausalNeighbors, periodicNeighborAt, periodicNeighborAtAux] at hm",
    ]
    for i in range(20):
        ind = "    " + "  " * i
        if i == 0:
            lines.append(f"{ind}rcases hm with rfl | hm")
        lines.append(f"{ind}· exact ⟨⟨{i}, by decide⟩, rfl⟩")
        if i < 19:
            lines.append(f"{ind}· rcases hm with rfl | hm")
    return lines

EQ_MAP = [
    "private theorem periodicCausalNeighbors_eq_map {L T : ℕ} (hL : 3 < L) (hT : 2 < T)",
    "    (n : CausalNode L T) :",
    "    periodicCausalNeighbors L T hL hT n =",
    "      Finset.univ.map (Function.Embedding.mk (periodicNeighborAt L T hL hT n)",
    "        (periodicNeighborAt_injective L T hL hT n)) := by",
    "  ext m",
    "  simp only [periodicCausalNeighbors, periodicNeighborAt, periodicNeighborAtAux,",
    "    Finset.mem_map, Finset.mem_univ, true_and, Finset.mem_insert, Finset.mem_singleton]",
    "  constructor",
] + gen_eq_map_fwd() + [
    "  · rintro ⟨i, _, hi⟩",
    "    fin_cases i",
] + [f"    · simp [hi, periodicNeighborAt, periodicNeighborAtAux]" for _ in range(20)]

FOOTER = r'''
theorem periodicCausalNeighbors_card {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n : CausalNode L T) :
    (periodicCausalNeighbors L T hL hT n).card = 20 := by
  rw [periodicCausalNeighbors_eq_map hL hT n, Finset.card_map, Finset.card_univ, Fintype.card_fin]

private theorem mem_periodicCausalNeighbors_adj {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n m : CausalNode L T) (hm : m ∈ periodicCausalNeighbors L T hL hT n) :
    (CausalGraphPeriodic L T (by omega) (by omega)).Adj n m := by
  rw [periodicCausalNeighbors_eq_map] at hm
  rcases hm with ⟨i, _, hi⟩
  rw [← hi]
  exact periodicNeighborAt_adj hL hT n i

private theorem adj_mem_periodicCausalNeighbors {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n m : CausalNode L T)
    (h : (CausalGraphPeriodic L T (by omega) (by omega)).Adj n m) :
    m ∈ periodicCausalNeighbors L T hL hT n := by
  rw [periodicCausalNeighbors_eq_map]
  simp only [Finset.mem_map, Finset.mem_univ, true_and]
  dsimp [CausalGraphPeriodic] at h
  rcases h with h | h
  · rcases h with h | h | h
    · rcases h with ⟨ht, hsp⟩
      simp [SpacelikeAdjPeriodic] at ht hsp
      rcases hsp with ⟨hfa, hy, hz⟩ | ⟨hx, hfa, hz⟩ | ⟨hx, hy, hfa⟩
      · rcases finAdjPeriodic_decompose (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) hfa with hfa | hfa
        · refine ⟨⟨⟨0, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hy, hz]⟩
        · refine ⟨⟨⟨1, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hy, hz]⟩
      · rcases finAdjPeriodic_decompose (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) hfa with hfa | hfa
        · refine ⟨⟨⟨2, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hz]⟩
        · refine ⟨⟨⟨3, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hz]⟩
      · rcases finAdjPeriodic_decompose (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) hfa with hfa | hfa
        · refine ⟨⟨⟨4, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hy]⟩
        · refine ⟨⟨⟨5, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hy]⟩
    · rcases h with ⟨ht, hs⟩
      by_cases hf : (n.1.val + 1) % (T + 1) = m.1.val
      · refine ⟨⟨6, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hf, hs]⟩
      · refine ⟨⟨7, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hs,
          finTimePeriodicPred_timelike_forward, ht]⟩
    · rcases h with ⟨ht, hlc⟩
      rcases hlc with ⟨hfa, hy, hz⟩ | ⟨hx, hfa, hz⟩ | ⟨hx, hy, hfa⟩
      · rcases finAdjPeriodic_decompose (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) hfa with hfa | hfa
        · refine ⟨⟨⟨8, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hy, hz]⟩
        · refine ⟨⟨⟨9, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hy, hz]⟩
      · rcases finAdjPeriodic_decompose (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) hfa with hfa | hfa
        · refine ⟨⟨⟨10, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hz]⟩
        · refine ⟨⟨⟨11, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hz]⟩
      · rcases finAdjPeriodic_decompose (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) hfa with hfa | hfa
        · refine ⟨⟨⟨12, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hy]⟩
        · refine ⟨⟨⟨13, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hy]⟩
  · rcases h with h | h | h
    · rcases h with ⟨ht, hsp⟩
      simp [SpacelikeAdjPeriodic] at ht hsp
      rcases hsp with ⟨hfa, hy, hz⟩ | ⟨hx, hfa, hz⟩ | ⟨hx, hy, hfa⟩
      · rcases finAdjPeriodic_decompose (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) hfa with hfa | hfa
        · refine ⟨⟨⟨0, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hy, hz]⟩
        · refine ⟨⟨⟨1, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hy, hz]⟩
      · rcases finAdjPeriodic_decompose (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) hfa with hfa | hfa
        · refine ⟨⟨⟨2, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hz]⟩
        · refine ⟨⟨⟨3, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hz]⟩
      · rcases finAdjPeriodic_decompose (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) hfa with hfa | hfa
        · refine ⟨⟨⟨4, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hy]⟩
        · refine ⟨⟨⟨5, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hy]⟩
    · rcases h with ⟨ht, hs⟩
      by_cases hf : (n.1.val + 1) % (T + 1) = m.1.val
      · refine ⟨⟨6, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hf, hs]⟩
      · refine ⟨⟨7, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hs,
          finTimePeriodicPred_timelike_forward, ht]⟩
    · rcases h with ⟨ht, hlc⟩
      rcases hlc with ⟨hfa, hy, hz⟩ | ⟨hx, hfa, hz⟩ | ⟨hx, hy, hfa⟩
      · rcases finAdjPeriodic_decompose (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) hfa with hfa | hfa
        · refine ⟨⟨⟨14, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hy, hz]⟩
        · refine ⟨⟨⟨15, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hy, hz]⟩
      · rcases finAdjPeriodic_decompose (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) hfa with hfa | hfa
        · refine ⟨⟨⟨16, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hz]⟩
        · refine ⟨⟨⟨17, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hz]⟩
      · rcases finAdjPeriodic_decompose (zero_lt_L_of_three_lt hL) (one_lt_L_of_three_lt hL) hfa with hfa | hfa
        · refine ⟨⟨⟨18, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hy]⟩
        · refine ⟨⟨⟨19, by decide⟩, by simp [periodicNeighborAt, periodicNeighborAtAux, hfa, ht, hx, hy]⟩

private theorem mem_periodicCausalNeighbors_iff_adj {L T : ℕ} (hL : 3 < L) (hT : 2 < T)
    (n m : CausalNode L T) :
    m ∈ periodicCausalNeighbors L T hL hT n ↔
      (CausalGraphPeriodic L T (by omega) (by omega)).Adj n m := by
  constructor
  · exact mem_periodicCausalNeighbors_adj hL hT n m
  · exact adj_mem_periodicCausalNeighbors hL hT n m
'''

THEOREM = r'''
theorem periodic_causal_node_degree (hL : 3 < L) (hT : 2 < T) (n : CausalNode L T) :
    ∃ (S : Finset (CausalNode L T)), S.card = 20 ∧
      ∀ m, m ∈ S ↔ (CausalGraphPeriodic L T (by omega) (by omega)).Adj n m := by
  refine ⟨periodicCausalNeighbors L T hL hT n, ?_, ?_⟩
  · exact periodicCausalNeighbors_card hL hT n
  · intro m; exact mem_periodicCausalNeighbors_iff_adj hL hT n m
'''

inj = (ROOT / "inj_proof_gen.lean").read_text()
block = (HEADER + "\n".join(AUX) + "\n\n" + "\n".join(NEIGHBOR_AT) + "\n" + inj + "\n\n" +
         "\n".join(ADJ_PROOFS) + "\n" + "\n".join(ADJ_COMBINED) + "\n\n" +
         "\n".join(EQ_MAP) + "\n" + FOOTER + THEOREM + "\nend GTE.Spacetime\n")
(ROOT / "degree_block.lean").write_text(block)
# also write degree module with imports
DEGREE_HEADER = '''import Mathlib.Combinatorics.SimpleGraph.Basic
import Mathlib.Combinatorics.SimpleGraph.Finite
import Mathlib.Data.Fin.Basic
import Mathlib.Data.Nat.Basic
import UgpLean.Spacetime.CausalGraph
import UgpLean.Spacetime.SpectralDimension

namespace GTE.Spacetime

'''
(ROOT / "UgpLean/Spacetime/SpectralDimensionDegree.lean").write_text(
    DEGREE_HEADER + block)
print("wrote SpectralDimensionDegree.lean:", len((DEGREE_HEADER + block).splitlines()), "lines")
