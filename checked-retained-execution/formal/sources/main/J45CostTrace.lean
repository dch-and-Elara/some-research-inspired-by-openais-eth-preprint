import J45CostDP
import OuterNodePacking

/-! Literal loops for the finite gather schedule and the matched-slot bound. -/
namespace J45Cost
open scoped BigOperators Classical

section Trace

variable {D R V : Type*} [Fintype D] [CommSemiring R]
  {U : V → Type*} [∀ v,Fintype (U v)]

private theorem fold_acc {X : Type*} (s : List X) (f : X→R) (r : R) :
    s.foldl (fun a x => a+f x) r = r+(s.map f).sum := by
  induction s generalizing r with
  | nil => simp
  | cons x s ih => simp [List.foldl_cons,ih,add_assoc]

/-- Actual accumulation loop of one new cell. -/
noncomputable def gatherLoop (H : D→ℕ) (v : V) (w : ∀ v,U v→R)
    (inc : ∀ v,U v→D→ℕ) (old : Box H→R) (x : Box H) : R :=
  (Finset.univ : Finset (U v)).toList.foldl
    (fun sum z => sum+w v z*predecessor H old x (inc v z)) 0

omit [Fintype D] in
theorem gatherLoop_eq (H : D→ℕ) (v : V) (w : ∀ v,U v→R)
    (inc : ∀ v,U v→D→ℕ) (old : Box H→R) (x : Box H) :
    gatherLoop H v w inc old x = dpStep H v w inc old x := by
  unfold gatherLoop dpStep
  rw [fold_acc,zero_add]
  exact Finset.sum_map_toList (Finset.univ : Finset (U v)) _

omit [CommSemiring R] in
/-- Writes to one cell do not change any other cell. The immutable old
buffer supplying predecessor lookups is not the buffer being updated. -/
private theorem write_loop {X : Type*} [DecidableEq X] (xs : List X) (val : X→R)
    (target : X→R) (x : X) :
    xs.foldl (fun out y => Function.update out y (val y)) target x =
      if x∈xs then val x else target x := by
  induction xs generalizing target with
  | nil => simp
  | cons y ys ih =>
    rw [List.foldl_cons,ih]
    by_cases h : x∈ys
    · simp [List.mem_cons,h]
    · by_cases he : x=y <;> simp [List.mem_cons,h,he,Function.update_apply]

/-- Process every destination exactly once. This entire loop is one
two-buffer sweep, and agrees with the DP for every entry. -/
noncomputable def fillBuffer (H : D→ℕ) (v : V) (w : ∀ v,U v→R)
    (inc : ∀ v,U v→D→ℕ) (old target : Box H→R) : Box H→R :=
  (Finset.univ : Finset (Box H)).toList.foldl
    (fun out x => Function.update out x (gatherLoop H v w inc old x)) target

theorem buffer_sweep_eq (H : D→ℕ) (v : V) (w : ∀ v,U v→R)
    (inc : ∀ v,U v→D→ℕ) (old target : Box H→R) :
    fillBuffer H v w inc old target = dpStep H v w inc old := by
  funext x
  rw [fillBuffer,write_loop]
  simp only [Finset.mem_toList,Finset.mem_univ,if_true]
  exact gatherLoop_eq H v w inc old x

theorem destination_visits (H : D→ℕ) :
    (Finset.univ : Finset (Box H)).toList.length = ∏ d,(H d+1) := by
  simp

end Trace

section Boundary

open OuterNodePacking
variable {P : Type*} [DecidableEq P] {L : ℕ}

/-- Finite overlap bound for *any* integer shift. Each retained column
must have a real row in the same packet; padding can only delete matches. -/
theorem actual_matched_bound (packets : Finset P) (rowReal colReal : Slot P L→Bool) (t : ℤ) :
    (matchedColumns packets rowReal colReal t).card ≤ packets.card * (L-t.natAbs) := by
  classical
  let source := matchedColumns packets rowReal colReal t
  let dest := packets.product (Finset.range (L-t.natAbs))
  let f (y : Slot P L) : P×ℕ := (y.1, if 0≤t then y.2.val-t.natAbs else y.2.val)
  have lo (y : Slot P L) (hy : y∈source) :
      y.1∈packets ∧ (if 0≤t then t.natAbs≤y.2.val else y.2.val+t.natAbs<L) := by
    obtain ⟨hP,_,x,_,hshift⟩ := (mem_matchedColumns packets rowReal colReal t y).mp hy
    refine ⟨hP,?_⟩
    have hx := x.isLt
    by_cases h : 0≤t
    · rw [if_pos h]
      omega
    · rw [if_neg h]
      omega
  have hmap : ∀ y∈source, f y∈dest := by
    intro y hy
    obtain ⟨hp,hy⟩ := lo y hy
    have hb := y.2.isLt
    change (y.1, if 0≤t then y.2.val-t.natAbs else y.2.val) ∈
      packets.product (Finset.range (L-t.natAbs))
    apply Finset.mem_product.mpr
    refine ⟨hp,Finset.mem_range.mpr ?_⟩
    by_cases ht : 0≤t <;> simp only [ht, ↓reduceIte] at hy ⊢ <;> omega
  have hinj : Set.InjOn f source := by
    intro y hy z hz h
    have ha := (lo y hy).2
    have hb := (lo z hz).2
    have hEq : y.1=z.1 := congrArg (fun p : P×ℕ => p.1) h
    refine Prod.ext hEq ?_
    apply Fin.ext
    have hs := congrArg Prod.snd h
    by_cases ht : 0≤t <;> simp only [f,ht, ↓reduceIte] at ha hb hs <;> omega
  have hc := Finset.card_le_card_of_injOn f hmap hinj
  simpa [source,dest] using hc

/-- On the actual partial wiring it is this many Boolean boundary patterns
that the loop can visit; upstream original column assignments are not counted. -/
theorem actual_boundary_words (packets : Finset P) (rowReal colReal : Slot P L→Bool) (t : ℤ) :
    Fintype.card (↥(matchedColumns packets rowReal colReal t)→Bool) ≤
      2^(packets.card*(L-t.natAbs)) := by
  have h := Nat.pow_le_pow_right (by decide : 0<(2:ℕ))
    (actual_matched_bound packets rowReal colReal t)
  simpa using h

theorem outer_boundary_words (packets : Finset P) (rowReal colReal : Slot P L→Bool)
    (t : ℤ) (hL : 0<L) (ht : t.natAbs=L-1) :
    Fintype.card (↥(matchedColumns packets rowReal colReal t)→Bool) ≤ 2^packets.card := by
  have hh : L-t.natAbs=1 := by omega
  simpa [hh] using actual_boundary_words packets rowReal colReal t

end Boundary

#print axioms gatherLoop_eq
#print axioms buffer_sweep_eq
#print axioms destination_visits
#print axioms actual_matched_bound
#print axioms actual_boundary_words
#print axioms outer_boundary_words

end J45Cost