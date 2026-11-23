import Mathlib
import PEqualNP.Defs

namespace PEqualNP.Outside.Meta273

open PEqualNP.CircuitLowerBounds

private abbrev T := BitVec 6
private def inputs : List T := [1,2,4,8,16,32]
private def targets : Finset T := {7,28,49}
private def good (g : Gate) := (g.op = .and ∨ g.op = .or) ∧ g.inputs.length = 2
private def read (p : Fin 6) (v : T) := v.getLsbD p.val
private def gt (ws : List T) (g : Gate) : T :=
  let a := ws.getD (g.inputs.getD 0 0) 0
  let b := ws.getD (g.inputs.getD 1 0) 0
  match g.op with
  | .and => a &&& b
  | _ => a ||| b

private def trace : List Gate → List T → List T
  | [], _ => []
  | g :: gs, ws => gt ws g :: trace gs (ws ++ [gt ws g])

private theorem trace_len (gs : List Gate) (ws : List T) : (trace gs ws).length = gs.length := by
  induction gs generalizing ws with
  | nil => rfl
  | cons g gs ih => simp [trace, ih]

private theorem get_read (p : Fin 6) (ws : List T) (i : ℕ) :
    (ws.map (read p)).getD i false = read p (ws.getD i 0) := by
  by_cases hi : i < ws.length
  · simp [List.getD_eq_getElem?_getD, hi]
  · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by omega)]
    simp [read]

private theorem gate_read (p : Fin 6) (ws : List T) (g : Gate) (h : good g) :
    g.op.eval (g.inputs.map fun i => (ws.map (read p)).getD i false) = read p (gt ws g) := by
  obtain ⟨op, ins⟩ := g
  obtain ⟨hop, hl⟩ := h
  match ins, hl with
  | [i,j], _ => rcases hop with rfl | rfl <;>
      simp only [List.map_cons, List.map_nil, get_read] <;> simp [gt, read, GateOp.eval]
  | [], h => simp at h
  | [_], h => simp at h
  | _ :: _ :: _ :: _, h => simp at h

private theorem sim_wires (p : Fin 6) (gs : List Gate) (ws : List T)
    (h : ∀ g ∈ gs, good g) :
    (Circuit.wires ⟨gs, 0⟩ (ws.map (read p))) = (ws ++ trace gs ws).map (read p) := by
  induction gs generalizing ws with
  | nil => simp [Circuit.wires, trace]
  | cons g gs ih =>
    have e := gate_read p ws g (h g (by simp))
    change Circuit.wires ⟨gs,0⟩ (_ ++ [_]) = _
    rw [e, ← List.map_singleton, ← List.map_append]
    rw [ih _ (fun g' hg => h g' (by simp [hg]))]
    simp [trace, List.append_assoc]

private theorem available (ws : List T) (i : ℕ) : ws.getD i 0 ∈ 0 :: ws := by
  by_cases h : i < ws.length
  · rw [List.getD_eq_getElem _ _ h]
    exact List.mem_cons_of_mem _ (List.getElem_mem h)
  · rw [List.getD_eq_default _ _ (by omega)]
    simp

private theorem first_gate (gs : List Gate) (ws : List T) (t : T)
    (hin : t ∈ trace gs ws) (hold : t ∉ 0 :: ws) :
    ∃ a ∈ 0 :: (ws ++ trace gs ws), ∃ b ∈ 0 :: (ws ++ trace gs ws),
      a ≠ t ∧ b ≠ t ∧ (a &&& b = t ∨ a ||| b = t) := by
  induction gs generalizing ws with
  | nil => simp [trace] at hin
  | cons g gs ih =>
    let v := gt ws g
    change t ∈ v :: trace gs (ws ++ [v]) at hin
    by_cases he : v = t
    · let a := ws.getD (g.inputs.getD 0 0) 0
      let b := ws.getD (g.inputs.getD 1 0) 0
      have ha : a ∈ 0 :: ws := available _ _
      have hb : b ∈ 0 :: ws := available _ _
      refine ⟨a, ?_, b, ?_, fun h => hold (h ▸ ha), fun h => hold (h ▸ hb), ?_⟩
      · simpa only [List.mem_cons, List.mem_append] using (List.mem_cons.mp ha).imp_right (fun h => Or.inl h)
      · simpa only [List.mem_cons, List.mem_append] using (List.mem_cons.mp hb).imp_right (fun h => Or.inl h)
      · rw [← he]
        cases h : g.op <;> simp [v, gt, h, a, b]
    · have hin' := (List.mem_cons.mp hin).resolve_left (Ne.symm he)
      have ho : t ∉ 0 :: (ws ++ [v]) := by simpa [List.mem_cons, Ne.symm he] using hold
      simpa [trace, v, List.append_assoc] using ih (ws ++ [v]) hin' ho

private def pool (a b : T) : List T := [0,1,2,4,8,16,32,7,28,49,a,b]
private def test (a b t : T) : Bool :=
  (pool a b).any fun u => u != t && (pool a b).any fun v =>
    v != t && ((u &&& v == t) || (u ||| v == t))

private theorem cover (s : Finset T) (hs : s.card ≤ 2) : ∃ a b : T, ∀ x ∈ s, x = a ∨ x = b := by
  rcases Nat.lt_or_eq_of_le hs with h | h
  · by_cases he : s.card = 0
    · rw [Finset.card_eq_zero.mp he]
      simp
    · obtain ⟨a, rfl⟩ := Finset.card_eq_one.mp (show s.card = 1 by omega)
      exact ⟨a,a,by simp⟩
  · obtain ⟨a,b,_,rfl⟩ := Finset.card_eq_two.mp h
    exact ⟨a,b,by simp⟩

private def tests (a b : T) := test a b 7 && test a b 28 && test a b 49

set_option maxHeartbeats 0 in
private theorem row0 : ∀ j : Fin 64, tests 0 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row1 : ∀ j : Fin 64, tests 1 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row2 : ∀ j : Fin 64, tests 2 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row3 : ∀ j : Fin 64, tests 3 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row4 : ∀ j : Fin 64, tests 4 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row5 : ∀ j : Fin 64, tests 5 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row6 : ∀ j : Fin 64, tests 6 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row7 : ∀ j : Fin 64, tests 7 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row8 : ∀ j : Fin 64, tests 8 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row9 : ∀ j : Fin 64, tests 9 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row10 : ∀ j : Fin 64, tests 10 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row11 : ∀ j : Fin 64, tests 11 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row12 : ∀ j : Fin 64, tests 12 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row13 : ∀ j : Fin 64, tests 13 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row14 : ∀ j : Fin 64, tests 14 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row15 : ∀ j : Fin 64, tests 15 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row16 : ∀ j : Fin 64, tests 16 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row17 : ∀ j : Fin 64, tests 17 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row18 : ∀ j : Fin 64, tests 18 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row19 : ∀ j : Fin 64, tests 19 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row20 : ∀ j : Fin 64, tests 20 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row21 : ∀ j : Fin 64, tests 21 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row22 : ∀ j : Fin 64, tests 22 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row23 : ∀ j : Fin 64, tests 23 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row24 : ∀ j : Fin 64, tests 24 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row25 : ∀ j : Fin 64, tests 25 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row26 : ∀ j : Fin 64, tests 26 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row27 : ∀ j : Fin 64, tests 27 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row28 : ∀ j : Fin 64, tests 28 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row29 : ∀ j : Fin 64, tests 29 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row30 : ∀ j : Fin 64, tests 30 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row31 : ∀ j : Fin 64, tests 31 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row32 : ∀ j : Fin 64, tests 32 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row33 : ∀ j : Fin 64, tests 33 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row34 : ∀ j : Fin 64, tests 34 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row35 : ∀ j : Fin 64, tests 35 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row36 : ∀ j : Fin 64, tests 36 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row37 : ∀ j : Fin 64, tests 37 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row38 : ∀ j : Fin 64, tests 38 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row39 : ∀ j : Fin 64, tests 39 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row40 : ∀ j : Fin 64, tests 40 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row41 : ∀ j : Fin 64, tests 41 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row42 : ∀ j : Fin 64, tests 42 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row43 : ∀ j : Fin 64, tests 43 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row44 : ∀ j : Fin 64, tests 44 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row45 : ∀ j : Fin 64, tests 45 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row46 : ∀ j : Fin 64, tests 46 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row47 : ∀ j : Fin 64, tests 47 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row48 : ∀ j : Fin 64, tests 48 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row49 : ∀ j : Fin 64, tests 49 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row50 : ∀ j : Fin 64, tests 50 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row51 : ∀ j : Fin 64, tests 51 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row52 : ∀ j : Fin 64, tests 52 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row53 : ∀ j : Fin 64, tests 53 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row54 : ∀ j : Fin 64, tests 54 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row55 : ∀ j : Fin 64, tests 55 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row56 : ∀ j : Fin 64, tests 56 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row57 : ∀ j : Fin 64, tests 57 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row58 : ∀ j : Fin 64, tests 58 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row59 : ∀ j : Fin 64, tests 59 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row60 : ∀ j : Fin 64, tests 60 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row61 : ∀ j : Fin 64, tests 61 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row62 : ∀ j : Fin 64, tests 62 (BitVec.ofFin j) = false := by decide +kernel

set_option maxHeartbeats 0 in
private theorem row63 : ∀ j : Fin 64, tests 63 (BitVec.ofFin j) = false := by decide +kernel

private theorem excluded (a b : T) : tests a b = false := by
  obtain ⟨⟨i,hi⟩⟩ := a
  interval_cases i
  · exact row0 b.toFin
  · exact row1 b.toFin
  · exact row2 b.toFin
  · exact row3 b.toFin
  · exact row4 b.toFin
  · exact row5 b.toFin
  · exact row6 b.toFin
  · exact row7 b.toFin
  · exact row8 b.toFin
  · exact row9 b.toFin
  · exact row10 b.toFin
  · exact row11 b.toFin
  · exact row12 b.toFin
  · exact row13 b.toFin
  · exact row14 b.toFin
  · exact row15 b.toFin
  · exact row16 b.toFin
  · exact row17 b.toFin
  · exact row18 b.toFin
  · exact row19 b.toFin
  · exact row20 b.toFin
  · exact row21 b.toFin
  · exact row22 b.toFin
  · exact row23 b.toFin
  · exact row24 b.toFin
  · exact row25 b.toFin
  · exact row26 b.toFin
  · exact row27 b.toFin
  · exact row28 b.toFin
  · exact row29 b.toFin
  · exact row30 b.toFin
  · exact row31 b.toFin
  · exact row32 b.toFin
  · exact row33 b.toFin
  · exact row34 b.toFin
  · exact row35 b.toFin
  · exact row36 b.toFin
  · exact row37 b.toFin
  · exact row38 b.toFin
  · exact row39 b.toFin
  · exact row40 b.toFin
  · exact row41 b.toFin
  · exact row42 b.toFin
  · exact row43 b.toFin
  · exact row44 b.toFin
  · exact row45 b.toFin
  · exact row46 b.toFin
  · exact row47 b.toFin
  · exact row48 b.toFin
  · exact row49 b.toFin
  · exact row50 b.toFin
  · exact row51 b.toFin
  · exact row52 b.toFin
  · exact row53 b.toFin
  · exact row54 b.toFin
  · exact row55 b.toFin
  · exact row56 b.toFin
  · exact row57 b.toFin
  · exact row58 b.toFin
  · exact row59 b.toFin
  · exact row60 b.toFin
  · exact row61 b.toFin
  · exact row62 b.toFin
  · exact row63 b.toFin

private theorem impossible (gs : List Gate) (hn : gs.length ≤ 5)
    (hh : targets ⊆ (trace gs inputs).toFinset) : False := by
  let s := (trace gs inputs).toFinset
  have hcard : s.card ≤ 5 := (List.toFinset_card_le _).trans ((trace_len _ _).le.trans hn)
  have hc : targets.card = 3 := by decide
  obtain ⟨a,b,hcover⟩ := cover (s \ targets) (by rw [Finset.card_sdiff_of_subset (show targets ⊆ s from hh), hc]; omega)
  have incl : ∀ u ∈ 0 :: (inputs ++ trace gs inputs), u ∈ pool a b := by
    intro u hu
    simp only [List.mem_cons, List.mem_append] at hu
    rcases hu with rfl | hu | hu
    · simp [pool]
    · simp [inputs] at hu
      simp [pool]
      tauto
    · have hus : u ∈ s := List.mem_toFinset.mpr hu
      by_cases ht : u ∈ targets
      · simp [targets] at ht
        simp [pool]
        tauto
      · have he := hcover u (Finset.mem_sdiff.mpr ⟨hus,ht⟩)
        rcases he with rfl | rfl <;> simp [pool]
  have get (t : T) (ht : t ∈ targets) (h0 : t ∉ 0 :: inputs) : test a b t = true := by
    obtain ⟨u,hu,v,hv,nu,nv,he⟩ := first_gate gs inputs t (List.mem_toFinset.mp (hh ht)) h0
    apply List.any_eq_true.mpr
    refine ⟨u,incl u hu, Bool.and_eq_true_iff.mpr ⟨by simpa using nu, ?_⟩⟩
    apply List.any_eq_true.mpr
    refine ⟨v,incl v hv, Bool.and_eq_true_iff.mpr ⟨by simpa using nv, ?_⟩⟩
    simpa using he
  have yes : tests a b = true := by
    simp only [tests, Bool.and_eq_true_iff]
    exact ⟨⟨get 7 (by decide) (by decide), get 28 (by decide) (by decide)⟩,get 49 (by decide) (by decide)⟩
  rw [excluded] at yes
  contradiction

end PEqualNP.Outside.Meta273

open PEqualNP.Outside.Meta273 PEqualNP.CircuitLowerBounds

theorem PEqualNP.Outside.L_meta_273 : ¬ ∃ (C : PEqualNP.CircuitLowerBounds.Circuit) (o : Fin 3 → ℕ), C.size ≤ 5 ∧ (∀ g ∈ C.gates, (g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨ g.op = PEqualNP.CircuitLowerBounds.GateOp.or) ∧ g.inputs.length = 2) ∧ ∀ i : Fin 3, (∀ p : Fin 6, (C.wires (List.ofFn (fun q : Fin 6 => decide (q = p)))).getD (o i) false = true ↔ p ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i) ∧ ∀ x : Fin 6 → Bool, (Finset.univ.filter (fun q : Fin 6 => x q = true)).card ≤ 2 → (∀ q ∈ (![{0, 1, 2}, {2, 3, 4}, {4, 5, 0}] : Fin 3 → Finset (Fin 6)) i, x q = false) → (C.wires (List.ofFn x)).getD (o i) false = false := by
  rintro ⟨C,o,hs,hg,ho⟩
  apply impossible C.gates hs
  let masks : Fin 3 → T := ![7,28,49]
  let sets : Fin 3 → Finset (Fin 6) := ![{0,1,2},{2,3,4},{4,5,0}]
  have val (i : Fin 3) : (inputs ++ trace C.gates inputs).getD (o i) 0 = masks i := by
    apply BitVec.eq_of_getLsbD_eq
    intro j hj
    let p : Fin 6 := ⟨j,hj⟩
    have init (k : Fin 6) : List.ofFn (fun q : Fin 6 => decide (q = k)) = inputs.map (read k) := by
      fin_cases k <;> decide
    have spec := (ho i).1 p
    change (Circuit.wires ⟨C.gates,0⟩ _).getD (o i) false = true ↔ p ∈ sets i at spec
    rw [init p, sim_wires p C.gates inputs hg, get_read] at spec
    have ref (k : Fin 3) (z : Fin 6) : read z (masks k) = true ↔ z ∈ sets k := by fin_cases k <;> fin_cases z <;> decide
    change read p _ = read p _
    exact Bool.eq_iff_iff.mpr (spec.trans (ref i p).symm)
  have occurs (i : Fin 3) : masks i ∈ (trace C.gates inputs).toFinset := by
    have h := available (inputs ++ trace C.gates inputs) (o i)
    rw [val] at h
    have notIn : masks i ∉ 0 :: inputs := by fin_cases i <;> decide
    simp only [List.mem_cons, List.mem_append] at h notIn
    exact List.mem_toFinset.mpr (by tauto)
  intro t ht
  simp [targets] at ht
  rcases ht with rfl | rfl | rfl
  · exact occurs 0
  · exact occurs 1
  · exact occurs 2
