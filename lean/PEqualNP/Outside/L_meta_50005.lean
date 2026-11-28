import Mathlib
import PEqualNP.Defs
import PEqualNP.Defs.NestedCoverCircuit
import PEqualNP.Defs.NotBracket

namespace PEqualNP.Outside.L_meta_50005_aux

open PEqualNP.CircuitLowerBounds

def geval : GateOp → List ℕ → ℕ
  | GateOp.and, l => l.foldr (fun a b => a &&& b) 31
  | GateOp.or, l => l.foldr (fun a b => a ||| b) 0
  | GateOp.not, l => 31 ^^^ l.headD 0
  | _, _ => 0

def stepT (m : List ℕ) (g : Gate) : List ℕ :=
  m ++ [geval g.op (g.inputs.map fun i => m.getD i 0)]

def base : List ℕ := [30, 28, 24, 16, 0, 31]

def tab (gs : List Gate) : List ℕ := gs.foldl stepT base

def setOf (m : List ℕ) : ℕ := m.foldl (fun S v => S ||| 2 ^ v) 0

def elems (S : ℕ) : List ℕ := (List.range 32).filter (fun a => S.testBit a)

def succ (c : ℕ × ℕ) : List (ℕ × ℕ) :=
  (elems c.1).flatMap (fun a =>
    (elems c.1).flatMap (fun b => [(c.1 ||| 2 ^ (a &&& b), c.2), (c.1 ||| 2 ^ (a ||| b), c.2)]) ++
      (if c.2 < 2 then [(c.1 ||| 2 ^ (31 ^^^ a), c.2 + 1)] else []))

def ins (L : List (ℕ × ℕ)) (x : ℕ × ℕ) : List (ℕ × ℕ) :=
  if L.contains x then L else x :: L

def nextL (L : List (ℕ × ℕ)) : List (ℕ × ℕ) := (L.flatMap succ).foldl ins []

def reach : ℕ → List (ℕ × ℕ)
  | 0 => [(setOf base, 0)]
  | j + 1 => nextL (reach j)

def safe (c : ℕ × ℕ) : Bool := !(c.1.testBit 2 && c.1.testBit 11 && c.1.testBit 19)

theorem mem_ins (L : List (ℕ × ℕ)) (x y : ℕ × ℕ) (h : y ∈ L ∨ y = x) : y ∈ ins L x := by
  unfold ins
  split
  · rename_i hc
    rcases h with h | h
    · exact h
    · subst h; simpa using hc
  · rcases h with h | h
    · exact List.mem_cons_of_mem _ h
    · subst h; exact List.mem_cons_self

theorem mem_foldl_ins (l : List (ℕ × ℕ)) :
    ∀ (acc : List (ℕ × ℕ)) (y : ℕ × ℕ), y ∈ acc ∨ y ∈ l → y ∈ l.foldl ins acc := by
  induction l with
  | nil => intro acc y h; simpa using h
  | cons x l ih =>
    intro acc y h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | h
    · exact Or.inl (mem_ins _ _ _ (Or.inl h))
    · rcases List.mem_cons.mp h with h | h
      · exact Or.inl (mem_ins _ _ _ (Or.inr h))
      · exact Or.inr h

theorem mem_nextL (L : List (ℕ × ℕ)) (c d : ℕ × ℕ) (hc : c ∈ L) (hd : d ∈ succ c) :
    d ∈ nextL L := by
  unfold nextL
  apply mem_foldl_ins
  exact Or.inr (List.mem_flatMap.mpr ⟨c, hc, hd⟩)

theorem mem_elems (S a : ℕ) (ha : a < 32) (h : S.testBit a = true) : a ∈ elems S := by
  unfold elems
  simp [List.mem_filter, List.mem_range, ha, h]

theorem setOf_snoc (m : List ℕ) (b : ℕ) : setOf (m ++ [b]) = setOf m ||| 2 ^ b := by
  simp [setOf, List.foldl_append]

theorem setOf_mem_aux (m : List ℕ) : ∀ (S a : ℕ), (S.testBit a = true ∨ a ∈ m) →
    (m.foldl (fun S v => S ||| 2 ^ v) S).testBit a = true := by
  induction m with
  | nil => intro S a h; simpa using h
  | cons v m ih =>
    intro S a h
    simp only [List.foldl_cons]
    apply ih
    rcases h with h | h
    · left; simp [Nat.testBit_lor, h]
    · rcases List.mem_cons.mp h with h | h
      · left; subst h; simp [Nat.testBit_lor, Nat.testBit_two_pow_self]
      · right; exact h

theorem setOf_mem (m : List ℕ) (a : ℕ) (h : a ∈ m) : (setOf m).testBit a = true :=
  setOf_mem_aux m 0 a (Or.inr h)

theorem bit31 (t : ℕ) (ht : t < 5) : (31 : ℕ).testBit t = true := by
  interval_cases t <;> decide

theorem eval_and (t : ℕ) (ht : t < 5) (L : List ℕ) :
    (L.map fun a => a.testBit t).all id = (L.foldr (fun a b => a &&& b) 31).testBit t := by
  induction L with
  | nil => simp [bit31 t ht]
  | cons a L ih => simp [Nat.testBit_land, ← ih]

theorem eval_or (t : ℕ) (L : List ℕ) :
    (L.map fun a => a.testBit t).any id = (L.foldr (fun a b => a ||| b) 0).testBit t := by
  induction L with
  | nil => simp
  | cons a L ih => simp [Nat.testBit_lor, ← ih]

theorem eval_gate (t : ℕ) (ht : t < 5) (op : GateOp)
    (hop : op = GateOp.and ∨ op = GateOp.or ∨ op = GateOp.not) (L : List ℕ) :
    op.eval (L.map fun a => a.testBit t) = (geval op L).testBit t := by
  rcases hop with h | h | h <;> subst h
  · exact eval_and t ht L
  · exact eval_or t L
  · cases L with
    | nil => simp [GateOp.eval, geval, bit31 t ht]
    | cons a L => simp [GateOp.eval, geval, Nat.testBit_xor, bit31 t ht]

theorem wires_rel (t : ℕ) (ht : t < 5) (gs : List Gate)
    (hops : ∀ g ∈ gs, g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) :
    ∀ (w : List Bool) (m : List ℕ), w.length = m.length →
      (∀ i, w.getD i false = (m.getD i 0).testBit t) →
      ∀ i, (gs.foldl (fun w g => w ++ [g.op.eval (g.inputs.map fun i => w.getD i false)]) w).getD
        i false = ((gs.foldl stepT m).getD i 0).testBit t := by
  induction gs with
  | nil => intro w m _ h i; exact h i
  | cons g gs ih =>
    intro w m hl h
    simp only [List.foldl_cons]
    apply ih (fun g hg => hops g (List.mem_cons_of_mem _ hg))
    · simp [stepT, hl]
    · intro i
      have hv : g.op.eval (g.inputs.map fun i => w.getD i false) =
          (geval g.op (g.inputs.map fun i => m.getD i 0)).testBit t := by
        rw [← eval_gate t ht g.op (hops g List.mem_cons_self), List.map_map]
        congr 1
        apply List.map_congr_left
        intro j _
        exact h j
      unfold stepT
      rcases Nat.lt_trichotomy i w.length with hi | hi | hi
      · rw [List.getD_append _ _ _ _ hi, List.getD_append _ _ _ _ (hl ▸ hi)]
        exact h i
      · subst hi
        rw [List.getD_append_right _ _ _ _ (le_refl _), hl,
          List.getD_append_right _ _ _ _ (le_refl _)]
        simpa using hv
      · rw [List.getD_eq_default _ _ (by simp; omega), List.getD_eq_default _ _ (by simp; omega)]
        simp

theorem base_rel (t : ℕ) (ht : t < 5) (i : ℕ) :
    ((List.ofFn (fun j : Fin 4 => decide (j.val < t))) ++ [false, true]).getD i false =
      (base.getD i 0).testBit t := by
  interval_cases t <;>
  rcases i with _ | _ | _ | _ | _ | _ | i <;> simp [base, List.ofFn_succ] <;> decide

theorem lt32_step (m : List ℕ) (hm : ∀ v ∈ m, v < 32) (g : Gate) : ∀ v ∈ stepT m g, v < 32 := by
  have hL : ∀ v ∈ g.inputs.map (fun i => m.getD i 0), v < 32 := by
    intro v hv
    obtain ⟨i, _, rfl⟩ := List.mem_map.mp hv
    rcases Nat.lt_or_ge i m.length with hi | hi
    · rw [List.getD_eq_getElem _ _ hi]; exact hm _ (List.getElem_mem hi)
    · rw [List.getD_eq_default _ _ hi]; omega
  have hg : geval g.op (g.inputs.map fun i => m.getD i 0) < 32 := by
    generalize g.inputs.map (fun i => m.getD i 0) = L at hL
    cases g.op with
    | and =>
      simp only [geval]
      induction L with
      | nil => simp
      | cons a L ih =>
        simp only [List.foldr_cons]
        exact Nat.and_lt_two_pow (n := 5) _
          (ih (fun v hv => hL v (List.mem_cons_of_mem _ hv)))
    | or =>
      simp only [geval]
      induction L with
      | nil => simp
      | cons a L ih =>
        simp only [List.foldr_cons]
        exact Nat.or_lt_two_pow (n := 5) (hL a List.mem_cons_self)
          (ih (fun v hv => hL v (List.mem_cons_of_mem _ hv)))
    | not => exact Nat.xor_lt_two_pow (n := 5) (by norm_num) (by
        cases L with
        | nil => simp
        | cons a L => exact hL a List.mem_cons_self)
    | mod _ => simp [geval]
    | maj => simp [geval]
  intro v hv
  rcases List.mem_append.mp hv with hv | hv
  · exact hm v hv
  · simp at hv; subst hv; exact hg


theorem lt32_tab_aux (gs : List Gate) : ∀ m : List ℕ, (∀ v ∈ m, v < 32) →
    ∀ v ∈ gs.foldl stepT m, v < 32 := by
  induction gs with
  | nil => intro m hm; simpa using hm
  | cons g gs ih => intro m hm; exact ih _ (lt32_step m hm g)

theorem lt32_tab (gs : List Gate) : ∀ v ∈ tab gs, v < 32 :=
  lt32_tab_aux gs base (by decide)

theorem sub_tab_aux (gs : List Gate) : ∀ m : List ℕ, ∀ v ∈ m, v ∈ gs.foldl stepT m := by
  induction gs with
  | nil => intro m v hv; simpa using hv
  | cons g gs ih =>
    intro m v hv
    exact ih _ v (List.mem_append_left _ hv)

theorem len_tab_aux (gs : List Gate) : ∀ m : List ℕ,
    (gs.foldl stepT m).length = m.length + gs.length := by
  induction gs with
  | nil => intro m; simp
  | cons g gs ih => intro m; rw [List.foldl_cons, ih]; simp [stepT]; omega

theorem len_tab (gs : List Gate) : (tab gs).length = 6 + gs.length := by
  unfold tab; rw [len_tab_aux]; rfl

def nc (gs : List Gate) : ℕ := PEqualNP.NotBracket.notCount ⟨gs, 0⟩

theorem nc_snoc (hs : List Gate) (g : Gate) : nc (hs ++ [g]) = nc hs + nc [g] := by
  unfold nc PEqualNP.NotBracket.notCount
  simp only [List.filter_append, List.length_append]

theorem nc_and (l : List ℕ) : nc [⟨GateOp.and, l⟩] = 0 := by
  simp [nc, PEqualNP.NotBracket.notCount]

theorem nc_or (l : List ℕ) : nc [⟨GateOp.or, l⟩] = 0 := by
  simp [nc, PEqualNP.NotBracket.notCount]

theorem nc_not (l : List ℕ) : nc [⟨GateOp.not, l⟩] = 1 := by
  simp [nc, PEqualNP.NotBracket.notCount]

theorem mem_succ_and (S k a b : ℕ) (ha : a < 32) (ha' : S.testBit a = true) (hb : b < 32)
    (hb' : S.testBit b = true) : (S ||| 2 ^ (a &&& b), k) ∈ succ (S, k) := by
  unfold succ
  simp only [List.mem_flatMap, List.mem_append]
  exact ⟨a, mem_elems S a ha ha', Or.inl ⟨b, mem_elems S b hb hb', by simp⟩⟩

theorem mem_succ_or (S k a b : ℕ) (ha : a < 32) (ha' : S.testBit a = true) (hb : b < 32)
    (hb' : S.testBit b = true) : (S ||| 2 ^ (a ||| b), k) ∈ succ (S, k) := by
  unfold succ
  simp only [List.mem_flatMap, List.mem_append]
  exact ⟨a, mem_elems S a ha ha', Or.inl ⟨b, mem_elems S b hb hb', by simp⟩⟩

theorem mem_succ_not (S k a : ℕ) (ha : a < 32) (ha' : S.testBit a = true) (hk : k < 2) :
    (S ||| 2 ^ (31 ^^^ a), k + 1) ∈ succ (S, k) := by
  unfold succ
  simp only [List.mem_flatMap, List.mem_append]
  exact ⟨a, mem_elems S a ha ha', Or.inr (by simp [hk])⟩

theorem and31 : ∀ a < 32, a &&& 31 = a := by decide

theorem step (hs : List Gate) (g : Gate)
    (hop : g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not)
    (hlen : g.inputs.length ≤ 2) (hrd : ∀ i ∈ g.inputs, i < 6 + hs.length)
    (hnc : nc (hs ++ [g]) ≤ 2) :
    (setOf (tab (hs ++ [g])), nc (hs ++ [g])) ∈ succ (setOf (tab hs), nc hs) := by
  have htab : tab (hs ++ [g]) = stepT (tab hs) g := by simp [tab, List.foldl_append]
  rw [htab, stepT, setOf_snoc, nc_snoc]
  rw [nc_snoc] at hnc
  have hval : ∀ i, i < 6 + hs.length → (tab hs).getD i 0 < 32 ∧
      (setOf (tab hs)).testBit ((tab hs).getD i 0) = true := by
    intro i hi
    have hi' : i < (tab hs).length := by rw [len_tab]; exact hi
    rw [List.getD_eq_getElem _ _ hi']
    exact ⟨lt32_tab hs _ (List.getElem_mem hi'), setOf_mem _ _ (List.getElem_mem hi')⟩
  have h31 : (setOf (tab hs)).testBit 31 = true :=
    setOf_mem _ _ (sub_tab_aux hs base 31 (by decide))
  have h0 : (setOf (tab hs)).testBit 0 = true :=
    setOf_mem _ _ (sub_tab_aux hs base 0 (by decide))
  obtain ⟨op, ins⟩ := g
  simp only at hop hlen hrd hnc ⊢
  match ins, hlen, hrd with
  | [], _, _ =>
    rcases hop with h | h | h <;> subst h
    · rw [nc_and]
      have e : geval GateOp.and (List.map (fun i => (tab hs).getD i 0) []) = 31 &&& 31 := rfl
      rw [e]
      exact mem_succ_and (setOf (tab hs)) (nc hs) 31 31 (by decide) h31 (by decide) h31
    · rw [nc_or]
      have e : geval GateOp.or (List.map (fun i => (tab hs).getD i 0) []) = 0 ||| 0 := rfl
      rw [e]
      exact mem_succ_or (setOf (tab hs)) (nc hs) 0 0 (by decide) h0 (by decide) h0
    · rw [nc_not] at hnc ⊢
      have e : geval GateOp.not (List.map (fun i => (tab hs).getD i 0) []) = 31 ^^^ 0 := rfl
      rw [e]
      exact mem_succ_not (setOf (tab hs)) (nc hs) 0 (by decide) h0 (by omega)
  | [i], _, hrd =>
    obtain ⟨a1, a2⟩ := hval i (hrd i (by simp))
    rcases hop with h | h | h <;> subst h
    · rw [nc_and]
      have e : geval GateOp.and (List.map (fun i => (tab hs).getD i 0) [i]) =
          (tab hs).getD i 0 &&& (tab hs).getD i 0 := by
        simp only [List.map, geval, List.foldr]; rw [and31 _ a1, Nat.and_self]
      rw [e]
      exact mem_succ_and (setOf (tab hs)) (nc hs) _ _ a1 a2 a1 a2
    · rw [nc_or]
      have e : geval GateOp.or (List.map (fun i => (tab hs).getD i 0) [i]) =
          (tab hs).getD i 0 ||| (tab hs).getD i 0 := by
        simp only [List.map, geval, List.foldr]; rw [Nat.or_zero, Nat.or_self]
      rw [e]
      exact mem_succ_or (setOf (tab hs)) (nc hs) _ _ a1 a2 a1 a2
    · rw [nc_not] at hnc ⊢
      have e : geval GateOp.not (List.map (fun i => (tab hs).getD i 0) [i]) =
          31 ^^^ (tab hs).getD i 0 := rfl
      rw [e]
      exact mem_succ_not (setOf (tab hs)) (nc hs) _ a1 a2 (by omega)
  | [i, j], _, hrd =>
    obtain ⟨a1, a2⟩ := hval i (hrd i (by simp))
    obtain ⟨b1, b2⟩ := hval j (hrd j (by simp))
    rcases hop with h | h | h <;> subst h
    · rw [nc_and]
      have e : geval GateOp.and (List.map (fun i => (tab hs).getD i 0) [i, j]) =
          (tab hs).getD i 0 &&& (tab hs).getD j 0 := by
        simp only [List.map, geval, List.foldr]; rw [and31 _ b1]
      rw [e]
      exact mem_succ_and (setOf (tab hs)) (nc hs) _ _ a1 a2 b1 b2
    · rw [nc_or]
      have e : geval GateOp.or (List.map (fun i => (tab hs).getD i 0) [i, j]) =
          (tab hs).getD i 0 ||| (tab hs).getD j 0 := by
        simp only [List.map, geval, List.foldr]; rw [Nat.or_zero]
      rw [e]
      exact mem_succ_or (setOf (tab hs)) (nc hs) _ _ a1 a2 b1 b2
    · rw [nc_not] at hnc ⊢
      have e : geval GateOp.not (List.map (fun i => (tab hs).getD i 0) [i, j]) =
          31 ^^^ (tab hs).getD i 0 := rfl
      rw [e]
      exact mem_succ_not (setOf (tab hs)) (nc hs) _ a1 a2 (by omega)
  | _ :: _ :: _ :: _, hlen, _ => simp at hlen

def Good (gs : List Gate) : Prop :=
  (∀ g ∈ gs, (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
    g.inputs.length ≤ 2) ∧
  (∀ j < gs.length, ∀ i ∈ (gs.getD j ⟨GateOp.or, []⟩).inputs, i < 6 + j) ∧ nc gs ≤ 2

theorem good_split (hs : List Gate) (g : Gate) (h : Good (hs ++ [g])) :
    Good hs ∧ (g.op = GateOp.and ∨ g.op = GateOp.or ∨ g.op = GateOp.not) ∧
      g.inputs.length ≤ 2 ∧ (∀ i ∈ g.inputs, i < 6 + hs.length) ∧ nc (hs ++ [g]) ≤ 2 := by
  obtain ⟨h1, h2, h3⟩ := h
  have hn := nc_snoc hs g
  refine ⟨⟨fun g' hg' => h1 g' (List.mem_append_left _ hg'), ?_, by omega⟩,
    (h1 g (by simp)).1, (h1 g (by simp)).2, ?_, h3⟩
  · intro j hj i hi
    apply h2 j (by simp; omega) i
    rw [List.getD_append _ _ _ _ hj]; exact hi
  · intro i hi
    have := h2 hs.length (by simp) i
    rw [List.getD_append_right _ _ _ _ (le_refl _), Nat.sub_self] at this
    exact this hi

set_option maxRecDepth 100000 in
theorem fin_check : ((reach 0).all safe && (reach 1).all safe && (reach 2).all safe &&
    (reach 3).all safe && (reach 4).all safe &&
    (reach 4).all (fun c => (succ c).all safe)) = true := by decide +kernel

theorem in_reach (gs : List Gate) (h : Good gs) :
    (setOf (tab gs), nc gs) ∈ reach gs.length := by
  induction gs using List.reverseRecOn with
  | nil => simp [reach, tab, nc, PEqualNP.NotBracket.notCount]
  | append_singleton hs g ih =>
    obtain ⟨hg, a, b, c, d⟩ := good_split hs g h
    rw [List.length_append, List.length_singleton]
    exact mem_nextL _ _ _ (ih hg) (step hs g a b c d)

theorem all_safe (gs : List Gate) (h : Good gs) (hl : gs.length ≤ 5) :
    safe (setOf (tab gs), nc gs) = true := by
  have hf := fin_check
  simp only [Bool.and_eq_true, List.all_eq_true] at hf
  obtain ⟨⟨⟨⟨⟨f0, f1⟩, f2⟩, f3⟩, f4⟩, f5⟩ := hf
  have hr := in_reach gs h
  rcases Nat.lt_or_ge gs.length 5 with hlt | hge
  · generalize hn : gs.length = n at hr hlt
    interval_cases n
    · exact f0 _ hr
    · exact f1 _ hr
    · exact f2 _ hr
    · exact f3 _ hr
    · exact f4 _ hr
  · obtain ⟨hs, g, rfl⟩ : ∃ hs g, gs = hs ++ [g] := by
      rcases List.eq_nil_or_concat gs with h0 | ⟨hs, g, h1⟩
      · subst h0; simp at hge
      · exact ⟨hs, g, by rw [h1, List.concat_eq_append]⟩
    obtain ⟨hg, a, b, c, d⟩ := good_split hs g h
    have h4 : hs.length = 4 := by simp at hl hge; omega
    have := in_reach hs hg
    rw [h4] at this
    exact f5 _ this _ (step hs g a b c d)

theorem eq_of_bits (v c : ℕ) (hv : v < 32) (hc : c < 32)
    (h : ∀ t : Fin 5, v.testBit t.val = c.testBit t.val) : v = c := by
  apply Nat.eq_of_testBit_eq
  intro t
  rcases Nat.lt_or_ge t 5 with ht | ht
  · exact h ⟨t, ht⟩
  · have h32 : 32 ≤ 2 ^ t := by
      calc (32 : ℕ) = 2 ^ 5 := by norm_num
        _ ≤ 2 ^ t := Nat.pow_le_pow_right (by norm_num) ht
    rw [Nat.testBit_lt_two_pow (lt_of_lt_of_le hv h32),
      Nat.testBit_lt_two_pow (lt_of_lt_of_le hc h32)]

end PEqualNP.Outside.L_meta_50005_aux

open PEqualNP.Outside.L_meta_50005_aux
theorem PEqualNP.Outside.L_meta_50005 : (¬ (∃ (D : PEqualNP.CircuitLowerBounds.Circuit) (p q r : Fin (6+D.size)),
  PEqualNP.MetaComplexity.FanInTwo D ∧ PEqualNP.MetaComplexity.NestedCover.ReadsBack 6 D ∧
  PEqualNP.NotBracket.notCount D ≤ 2 ∧ D.size ≤ 5 ∧
  ∀ t : Fin 5,
    let xs := (List.ofFn (fun i : Fin 4 => decide (i.val < t.val))) ++ [false,true]
    let w := D.wires xs
    w.getD p.val false = (2 : Nat).testBit t.val ∧
    w.getD q.val false = (11 : Nat).testBit t.val ∧
    w.getD r.val false = (19 : Nat).testBit t.val)) := by
  rintro ⟨⟨gs, o⟩, p, q, r, hfan, hrb, hnc, hsz, hw⟩
  have hgood : Good gs := by
    refine ⟨fun g hg => ?_, fun j hj i hi => hrb j hj i hi, hnc⟩
    obtain ⟨h1, h2⟩ := hfan g hg
    simp only [Set.mem_insert_iff, Set.mem_singleton_iff] at h1
    exact ⟨h1, h2⟩
  have hops : ∀ g ∈ gs, g.op = PEqualNP.CircuitLowerBounds.GateOp.and ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.or ∨
      g.op = PEqualNP.CircuitLowerBounds.GateOp.not := fun g hg => (hgood.1 g hg).1
  have hsafe := all_safe gs hgood hsz
  have hrel : ∀ (t : Fin 5) (i : ℕ),
      ((⟨gs, o⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
        ((List.ofFn (fun j : Fin 4 => decide (j.val < t.val))) ++ [false,true])).getD i false =
        ((tab gs).getD i 0).testBit t.val := by
    intro t i
    exact wires_rel t.val t.isLt gs hops _ base (by simp [base]) (base_rel t.val t.isLt) i
  have hlen : (tab gs).length = 6 + gs.length := len_tab gs
  have key : ∀ (x : Fin (6 + gs.length)) (c : ℕ), c < 32 →
      (∀ t : Fin 5, ((⟨gs, o⟩ : PEqualNP.CircuitLowerBounds.Circuit).wires
        ((List.ofFn (fun j : Fin 4 => decide (j.val < t.val))) ++ [false,true])).getD x.val false =
          c.testBit t.val) → (setOf (tab gs)).testBit c = true := by
    intro x c hc hx
    have hxl : x.val < (tab gs).length := by rw [hlen]; exact x.isLt
    have hv : (tab gs).getD x.val 0 = c := by
      apply eq_of_bits _ _ _ hc
      · intro t; rw [← hrel t x.val]; exact hx t
      · rw [List.getD_eq_getElem _ _ hxl]; exact lt32_tab gs _ (List.getElem_mem hxl)
    rw [← hv, List.getD_eq_getElem _ _ hxl]
    exact setOf_mem _ _ (List.getElem_mem hxl)
  have k2 := key p 2 (by decide) (fun t => (hw t).1)
  have k11 := key q 11 (by decide) (fun t => (hw t).2.1)
  have k19 := key r 19 (by decide) (fun t => (hw t).2.2)
  simp [safe, k2, k11, k19] at hsafe
