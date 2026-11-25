import Mathlib
import PEqualNP.Defs

open PEqualNP.CircuitLowerBounds PEqualNP.MetaComplexity PEqualNP.ReadK
open PEqualNP.MetaComplexity.NestedCover PEqualNP.TopForm

set_option maxHeartbeats 2500000 in
theorem PEqualNP.Outside.R_meta_2583_417
    (plane_bound : ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → N * (q + 2) ≤ C.size + 1)
    (stars : ∀ (x1 x2 : ℕ) (x3 : Finset (Fin x1 × Fin x2)) (x4 : Finset (Fin x1)) (x5 : Finset (Fin x2)),   (∀ x6 ∈ x3, x6.1 ∈ x4 ∨ x6.2 ∈ x5) →     ∃ (x7 : PEqualNP.CircuitLowerBounds.Circuit) (x8 : Bool → Finset ℕ),       PEqualNP.TopForm.IsAO2 (x1 + x2) x7 ∧         x7.size ≤ x3.card + x4.card + x5.card - (1 : ℕ) ∧           (∀ (x9 : Fin (x1 + x2) → Bool), PEqualNP.MetaComplexity.circuitFun (x1 + x2) x7 x9 = Decidable.decide (∃ (x10 : Fin x1) (x11 : Fin x2), (x10, x11) ∈ x3 ∧ x9 (Fin.castAdd x2 x10) = Bool.true ∧ x9 (Fin.natAdd x1 x11) = Bool.true)) ∧             have x9 : ℕ → PEqualNP.CircuitLowerBounds.Gate := PEqualNP.MetaComplexity.NestedCover.gateAt x7;             (∀ (x10 : Bool), ∀ x11 ∈ x8 x10, x11 < x1 + x2 ∧ Decidable.decide (x1 ≤ x11) = x10 ∨ ∃ x13 < x7.size, x11 = x1 + x2 + x13 ∧ (x9 x13).op = PEqualNP.CircuitLowerBounds.GateOp.or ∧ ∀ x14 ∈ (x9 x13).inputs, x14 ∈ x8 x10) ∧ ∀ x10 < x7.size, (x9 x10).op = PEqualNP.CircuitLowerBounds.GateOp.and → ∃ (x13 : ℕ) (x14 : ℕ), (x9 x10).inputs = [x13, x14] ∧ x13 ∈ x8 Bool.false ∧ x14 ∈ x8 Bool.true) :
    ∀ (q N : ℕ) (I : Fin N → Fin N → Prop) [DecidableRel I] (C : PEqualNP.CircuitLowerBounds.Circuit), 2 ≤ q → N = q ^ 2 + q + 1 → (∀ l : Fin N, (Finset.univ.filter (fun p => I p l)).card = q + 1) → (∀ p p' : Fin N, p ≠ p' → ∃! l : Fin N, I p l ∧ I p' l) → PEqualNP.TopForm.IsAO2 (N + N) C → (∀ z : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) C z = decide (∃ p l : Fin N, I p l ∧ z (Fin.castAdd N p) = true ∧ z (Fin.natAdd N l) = true)) → ∃ D : PEqualNP.CircuitLowerBounds.Circuit, PEqualNP.TopForm.IsAO2 (N + N) D ∧ (∀ y : Fin (N + N) → Bool, PEqualNP.MetaComplexity.circuitFun (N + N) D y = decide (∃ p l : Fin N, I p l ∧ y (Fin.castAdd N p) = true ∧ y (Fin.natAdd N l) = true)) ∧ D.size ≤ C.size ∧ PEqualNP.ReadK.IsReadK (N + N) D 1 := by
  classical
  let unit (s : List ℕ) (u : ℕ) := s.map fun i => if i = u then 1 else 0

  let small (z : List ℕ) := z.all fun v => decide (v ≤ 1)

  have unit_small (s : List ℕ) (u : ℕ) : small (unit s u) = true := by
    simp [small,unit,List.all_eq_true]
    intro i _
    split <;> decide

  have two_small (s : List ℕ) (u v : ℕ) (hne : u ≠ v) :
      small (capAdd 1 (capAdd 1 (s.map fun _ => 0) (unit s u)) (unit s v)) = true := by
    have cap_eq (a b : List ℕ) : capAdd 1 a b = List.zipWith (fun x y => min (x+y) 2) a b := rfl
    induction s with
    | nil => rfl
    | cons x xs ih =>
      by_cases hx : x = u <;> by_cases hy : x = v
      · exact (hne (hx.symm.trans hy)).elim
      all_goals simpa [small,unit,cap_eq,hx,hy,hne,Ne.symm hne] using ih

  have mem_insert (z w : List ℕ) (a : List (List ℕ)) :
      z ∈ insertNew a w ↔ z ∈ a ∨ z = w := by
    unfold insertNew
    split <;> rename_i h
    · aesop
    · simp

  have mem_fold (z : List ℕ) (ws a : List (List ℕ)) :
      z ∈ ws.foldl insertNew a ↔ z ∈ a ∨ z ∈ ws := by
    induction ws generalizing a with
    | nil => simp
    | cons w ws ih =>
      simp only [List.foldl_cons,ih,mem_insert,List.mem_cons]
      tauto

  have mem_union (z : List ℕ) (banks : (List (List (List ℕ)))) (a : List (List ℕ)) :
      z ∈ banks.foldl (fun acc ws => ws.foldl insertNew acc) a ↔
        z ∈ a ∨ ∃ w ∈ banks, z ∈ w := by
    induction banks generalizing a with
    | nil =>
      constructor
      · exact Or.inl
      · rintro (hz|⟨w,hw,_⟩)
        · exact hz
        · exact (List.not_mem_nil hw).elim
    | cons w ws ih =>
      simp only [List.foldl_cons,ih,mem_fold,List.mem_cons]
      aesop

  have mem_add (z t : List ℕ) (a b : List (List ℕ)) (hz : z ∈ a) (ht : t ∈ b) :
      capAdd 1 z t ∈ andStep 1 a b := by
    unfold andStep
    apply (mem_fold ..).2
    right
    exact List.mem_flatMap.mpr ⟨z,hz,List.mem_map.mpr ⟨t,ht,rfl⟩⟩

  let bit (v : List Bool) (g : Gate) :=
    g.op.eval (g.inputs.map fun i => v.getD i false)

  let counts (s : List ℕ) (r : (List (List (List ℕ)))) (g : Gate) : List (List ℕ) :=
    let args : (List (List (List ℕ))) := g.inputs.map fun i => r.getD i []
    GateOp.casesOn (motive := fun _ => List (List ℕ)) g.op
      (args.foldl (andStep 1) [s.map fun _ => 0])
      (args.foldl (fun acc (a : List (List ℕ)) => a.foldl insertNew acc) []) [] (fun _ => []) []

  let Good (P : ℕ) (W : Bool → Finset ℕ) (s : List ℕ)
      (i : ℕ) (active : Bool) (vecs : List (List ℕ)) : Prop :=
    active = true →
      (∃ z ∈ vecs, small z = true) ∧
      ∀ b, i ∈ W b → ∃ v, decide (P ≤ v) = b ∧ unit s v ∈ vecs

  let Allowed (W : Bool → Finset ℕ) (i : ℕ) (g : Gate) : Prop :=
    (g.op = .and ∨ g.op = .or) ∧
    (∀ b, i ∈ W b → g.op = .or ∧ ∀ j ∈ g.inputs, j ∈ W b) ∧
    (g.op = .and → ∃ a b, g.inputs = [a,b] ∧ a ∈ W false ∧ b ∈ W true)

  have gate_good (P : ℕ) (W : Bool → Finset ℕ) (s : List ℕ) (i : ℕ)
      (v : List Bool) (r : (List (List (List ℕ)))) (g : Gate) (hg : Allowed W i g)
      (prev : ∀ j, Good P W s j (v.getD j false) (r.getD j [])) :
      Good P W s i (bit v g) (counts s r g) := by
    intro active
    rcases hg with ⟨kind,sides,hands⟩
    have and_eval (a : List Bool) : GateOp.eval .and a = a.all id := rfl
    have or_eval (a : List Bool) : GateOp.eval .or a = a.any id := rfl
    rcases kind with ha|ho
    · obtain ⟨a,b,hab,hal,hbl⟩ := hands ha
      have hon : v.getD a false = true ∧ v.getD b false = true := by
        simpa [bit,ha,hab,and_eval] using active
      obtain ⟨u,hu,hzu⟩ := (prev a hon.1).2 false hal
      obtain ⟨t,ht,hzt⟩ := (prev b hon.2).2 true hbl
      have ne : u ≠ t := by rintro rfl; simp_all
      constructor
      · refine ⟨_,?_,two_small s u t ne⟩
        simp only [counts,ha,hab,List.map_cons,List.map_nil,List.foldl_cons,List.foldl_nil]
        exact mem_add _ _ _ _ (mem_add _ _ _ _ (by simp) hzu) hzt
      · intro side hs
        have contra := (sides side hs).1
        rw [ha] at contra
        contradiction
    · have exists_child : ∃ j ∈ g.inputs, v.getD j false = true := by
        simpa [bit,ho,or_eval,List.any_eq_true] using active
      obtain ⟨j,hj,htrue⟩ := exists_child
      have keep : ∀ z ∈ r.getD j [], z ∈ counts s r g := by
        intro z hz
        simp only [counts,ho,mem_union]
        exact Or.inr ⟨_,List.mem_map.mpr ⟨j,hj,rfl⟩,hz⟩
      obtain ⟨⟨z,hz,hs⟩,hc⟩ := prev j htrue
      refine ⟨⟨z,keep z hz,hs⟩,?_⟩
      intro side hw
      obtain ⟨u,hu,hzu⟩ := hc side ((sides side hw).2 j hj)
      exact ⟨u,hu,keep _ hzu⟩

  have fold_good (P : ℕ) (W : Bool → Finset ℕ) (s : List ℕ)
      (gs : List Gate) (k : ℕ) (v : List Bool) (r : (List (List (List ℕ))))
      (hv : v.length = k) (hr : r.length = k)
      (start : ∀ j, Good P W s j (v.getD j false) (r.getD j []))
      (allowed : ∀ j (hj : j < gs.length), Allowed W (k+j) gs[j]) :
      ∀ i, Good P W s i
        ((gs.foldl (fun a g => a ++ [bit a g]) v).getD i false)
        ((gs.foldl (fun a g => a ++ [counts s a g]) r).getD i []) := by
    induction gs generalizing k v r with
    | nil => simpa using start
    | cons g gs ih =>
      refine ih (k+1) (v ++ [bit v g]) (r ++ [counts s r g]) ?_ ?_ ?_ ?_
      · simp [hv]
      · simp [hr]
      · intro i
        rcases lt_trichotomy i k with h|rfl|h
        · have h1 : i < v.length := hv.symm ▸ h
          have h2 : i < r.length := hr.symm ▸ h
          simpa only [List.getD,List.getElem?_append_left h1,List.getElem?_append_left h2]
            using start i
        · have hg := allowed 0 (by simp)
          change Allowed W (i+0) g at hg
          have latest := gate_good P W s i v r g hg start
          have vnew : (v ++ [bit v g]).getD i false = bit v g := by rw [← hv]; simp [List.getD]
          have rnew : (r ++ [counts s r g]).getD i [] = counts s r g := by rw [← hr]; simp [List.getD]
          rwa [vnew,rnew]
        · intro active
          have ge : (v ++ [bit v g]).length ≤ i := by simp [hv]; omega
          simp [List.getD,List.getElem?_eq_none ge] at active
      · intro j hj
        have ht := allowed (j+1) (by simpa using hj)
        change Allowed W (k+(j+1)) gs[j] at ht
        simpa only [Nat.add_assoc,Nat.add_comm 1 j] using ht

  have side_normal_read (P L : ℕ) (C : Circuit) (W : Bool → Finset ℕ)
      (ao : PEqualNP.TopForm.IsAO2 (P+L) C)
      (sides : ∀ b, ∀ w ∈ W b, (w < P+L ∧ decide (P ≤ w) = b) ∨
        ∃ j < C.size, w = P+L+j ∧ (gateAt C j).op = .or ∧
          ∀ t ∈ (gateAt C j).inputs, t ∈ W b)
      (hands : ∀ j < C.size, (gateAt C j).op = .and →
        ∃ a b, (gateAt C j).inputs = [a,b] ∧ a ∈ W false ∧ b ∈ W true) :
      IsReadK (P+L) C 1 := by
    intro S hp
    let s := setList S
    let v := List.ofFn (setInput S)
    let r := (List.range (P+L)).map (leafVectors s 1)
    have hv : v.length = P+L := by simp [v]
    have hr : r.length = P+L := by simp [r]
    have start : ∀ i, Good P W s i (v.getD i false) (r.getD i []) := by
      intro i on
      by_cases hi : i < P+L
      · have set_in (x : Fin (P+L)) : setInput S x = decide (x ∈ S) := rfl
        have hm : (⟨i,hi⟩ : Fin (P+L)) ∈ S := by simpa [v,List.getD,hi,set_in] using on
        have hs : i ∈ s := by
          apply List.mem_map.mpr
          exact ⟨⟨i,hi⟩,List.mem_filter.mpr ⟨List.mem_finRange _,by simpa using hm⟩,rfl⟩
        have leaf : leafVectors s 1 i = if i ∈ s then [unit s i] else [] := rfl
        have rr : r.getD i [] = [unit s i] := by
          simp [r,List.getD,hi,leaf,hs]
        refine ⟨⟨unit s i,by rw [rr]; simp,unit_small s i⟩,?_⟩
        intro b h
        rcases sides b i h with par|⟨j,_,eq,_⟩
        · exact ⟨i,par.2,by rw [rr]; simp⟩
        · omega
      · have ge : v.length ≤ i := by omega
        simp [List.getD,List.getElem?_eq_none ge] at on
    have legal : ∀ j (hj : j < C.gates.length), Allowed W (P+L+j) C.gates[j] := by
      intro j hj
      have elt : gateAt C j = C.gates[j] := by
        change C.gates.getD j ⟨.or,[]⟩ = C.gates[j]
        simp [List.getD,hj]
      refine ⟨ao.1 _ (List.getElem_mem _),?_,?_⟩
      · intro b hw
        rcases sides b _ hw with ⟨lt,_⟩|⟨t,_,eq,og,sub⟩
        · omega
        · have te : j=t := by omega
          subst t
          simpa [elt] using And.intro og sub
      · simpa [elt] using hands j hj
    have last := fold_good P W s C.gates (P+L) v r hv hr start legal C.output
    have yes : (C.gates.foldl (fun a g => a ++ [bit a g]) v).getD C.output false = true := hp.1
    obtain ⟨z,hz,smallz⟩ := (last yes).1
    have same_bank : readVectors C (P+L) (setList S) 1 =
        C.gates.foldl (fun a g => a ++ [counts s a g]) r := by
      unfold readVectors
      congr 1
      funext a g
      rcases g with ⟨op,ins⟩
      cases op <;> rfl
    unfold readsAtMost
    rw [same_bank]
    apply List.any_eq_true.mpr
    exact ⟨z,hz,smallz⟩
  intro q N I inst C hq hN lines unique ao correct
  let E : Finset (Fin N × Fin N) := Finset.univ.filter fun e => I e.1 e.2
  have mem (p : Fin N) (l : Fin N) : (p,l) ∈ E ↔ I p l := by simp [E]
  have count : E.card = N * (q + 1) := by
    have h1 : E.card = ∑ l : Fin N, (Finset.univ.filter (fun p => I p l)).card := by
      simp only [E, Finset.card_filter]
      rw [Fintype.sum_prod_type, Finset.sum_comm]
    rw [h1]
    simp [lines]
  have paid := plane_bound q N I C hq hN lines unique ao correct
  obtain ⟨D,W,strict,size,eval,closed,hands⟩ :=
    stars N N E Finset.univ ∅ (fun e _ => Or.inl (Finset.mem_univ _))
  refine ⟨D,strict,by simpa only [mem] using eval,?_,side_normal_read N N D W strict closed hands⟩
  simp only [Finset.card_univ, Fintype.card_fin, Finset.card_empty, add_zero, count] at size
  have e : N * (q + 2) = N * (q + 1) + N := by ring
  omega
