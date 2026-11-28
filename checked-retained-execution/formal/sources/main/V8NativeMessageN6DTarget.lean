import P5D1LiteralCount
import P5HybridClosureProduct
import P5HybridClosureGraph

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 4400000

/-! The exterior target of v8 N6 uses the original exterior matching
of the four-clone triangle replacement. Outside a selected pair the
actual pins are fixed true, not the false-switch slice of v8 C2. -/
namespace V8NativeMessage.N6D
open scoped Classical Polynomial BigOperators
open Polynomial J6R10Repack J6R9Recursive
open Paper5.HybridClosure Paper5.D1Literal
noncomputable section

def orValue (R : Type*) [CommSemiring R] (x y : Bool) : R :=
  if x||y then 1 else 0

variable {V : Type} [DecidableEq V]
variable (E : Finset (V×V)) (cubic : ∀ v, GraphCutMoments.degree E v=3)

def seat (e : E) (b : Bool) : TriVertex V := exteriorPort E cubic (e,b)

def pairsWord (w : E→Bool×Bool) (v : TriVertex V) : Bool :=
  let s := (exteriorPort E cubic).symm v
  if s.2 then (w s.1).2 else (w s.1).1

theorem pairsWord_on (w : E→Bool×Bool) (e : E) (b : Bool) :
    pairsWord E cubic w (seat E cubic e b) =
      if b then (w e).2 else (w e).1 := by
  simp [pairsWord,seat]

def pairWord (chosen : E) (x y : Bool) (v : TriVertex V) : Bool :=
  pairsWord E cubic (fun e => if e=chosen then (x,y) else (true,true)) v

theorem pairWord_seated (e q : E) (x y b : Bool) :
    pairWord E cubic e x y (seat E cubic q b) =
      if q=e then (if b then y else x) else true := by
  unfold pairWord
  rw [pairsWord_on]
  by_cases h : q=e <;> cases b <;> simp [h]

theorem pairWord_left_only (e : E) (x y : Bool) (v : TriVertex V)
    (away : v ≠ seat E cubic e true) :
    pairWord E cubic e x y v=pairWord E cubic e x true v := by
  obtain ⟨⟨q,b⟩,rfl⟩ := (exteriorPort E cubic).surjective v
  change pairWord E cubic e x y (seat E cubic q b) =
    pairWord E cubic e x true (seat E cubic q b)
  rw [pairWord_seated,pairWord_seated]
  by_cases h : q=e
  · subst q
    cases b
    · simp
    · exact (away rfl).elim
  · simp [h]

theorem pairWord_right_only (e : E) (x y : Bool) (v : TriVertex V)
    (away : v ≠ seat E cubic e false) :
    pairWord E cubic e x y v=pairWord E cubic e true y v := by
  obtain ⟨⟨q,b⟩,rfl⟩ := (exteriorPort E cubic).surjective v
  change pairWord E cubic e x y (seat E cubic q b) =
    pairWord E cubic e true y (seat E cubic q b)
  rw [pairWord_seated,pairWord_seated]
  by_cases h : q=e
  · subst q
    cases b
    · exact (away rfl).elim
    · simp
  · simp [h]

theorem pairWord_false_location (e : E) (x y : Bool) (v : TriVertex V)
    (hfalse : pairWord E cubic e x y v=false) :
    v=seat E cubic e false ∨ v=seat E cubic e true := by
  obtain ⟨⟨q,b⟩,rfl⟩ := (exteriorPort E cubic).surjective v
  change pairWord E cubic e x y (seat E cubic q b)=false at hfalse
  by_cases h : q=e
  · subst q
    cases b
    · exact Or.inl rfl
    · exact Or.inr rfl
  · simp [pairWord_seated,h] at hfalse

def UD (R : Type*) [CommSemiring R] (σ : TriVertex V→Bool) : R :=
  ∏ e : E, orValue R (σ (seat E cubic e false)) (σ (seat E cubic e true))

theorem UD_is_outer_edges (R : Type*) [CommSemiring R] (σ : TriVertex V→Bool) :
    UD E cubic R σ = ∏ e ∈ outerEdges E cubic, orValue R (σ e.1) (σ e.2) := by
  unfold UD outerEdges
  rw [Finset.prod_image (fun _ _ _ _ h => outerEdge_injective E cubic h)]
  rfl

theorem UD_one_pair (R : Type*) [CommSemiring R] (e : E) (x y : Bool) :
    UD E cubic R (pairWord E cubic e x y)=orValue R x y := by
  unfold UD
  trans ∏ q : E, if q=e then orValue R x y else 1
  · refine Finset.prod_congr rfl (fun q _ => ?_)
    by_cases h : q=e <;> simp [pairWord_seated,h,orValue]
  · simp

omit [DecidableEq V] in
theorem triangle_step_ne (j : Fin 3) : j≠j+1 := by
  fin_cases j <;> decide

variable [Fintype V]

theorem adjacent_in_inner_ne {q : TriVertex V×TriVertex V} (hq : q∈innerEdges V) :
    q.1≠q.2 := by
  obtain ⟨⟨v,j⟩,_,rfl⟩ := Finset.mem_image.mp hq
  intro h
  exact triangle_step_ne j (congrArg Prod.snd h)

theorem inner_edge_neutral_on_one_pair (loopless : ∀v,(v,v)∉E)
    (e : E) (x y : Bool) (q : TriVertex V×TriVertex V) (hq : q∈innerEdges V) :
    pairWord E cubic e x y q.1=true ∨ pairWord E cubic e x y q.2=true := by
  cases ha : pairWord E cubic e x y q.1
  · cases hb : pairWord E cubic e x y q.2
    · have huv : q.1.1=q.2.1 := innerEdges_stay_in_triangle hq
      have hne : q.1≠q.2 := adjacent_in_inner_ne hq
      have hsep : (seat E cubic e false).1≠(seat E cubic e true).1 := by
        intro he
        have hp : (outerEdge E cubic e) ∈ outerEdges E cubic :=
          Finset.mem_image.mpr ⟨e,Finset.mem_univ e,rfl⟩
        exact outerEdges_join_distinct_triangles E cubic loopless hp he
      rcases pairWord_false_location E cubic e x y q.1 ha with h1|h1 <;>
        rcases pairWord_false_location E cubic e x y q.2 hb with h2|h2
      · exact (hne (h1.trans h2.symm)).elim
      · exact (hsep (by rw [← h1,← h2]; exact huv)).elim
      · exact (hsep (by rw [← h1,← h2]; exact huv.symm)).elim
      · exact (hne (h1.trans h2.symm)).elim
    · exact Or.inr rfl
  · exact Or.inl rfl

theorem all_edges_one_pair_iff (loopless : ∀v,(v,v)∉E)
    (e : E) (x y : Bool) :
    PinnedCNF.AllEdges (replacedEdges E cubic) (pairWord E cubic e x y) ↔ x=true ∨ y=true := by
  constructor
  · intro h
    have he : (outerEdge E cubic e)∈replacedEdges E cubic :=
      Finset.mem_union.mpr (Or.inr (Finset.mem_image.mpr ⟨e,Finset.mem_univ e,rfl⟩))
    have ha := h (outerEdge E cubic e) he
    change pairWord E cubic e x y (seat E cubic e false)=true ∨
      pairWord E cubic e x y (seat E cubic e true)=true at ha
    simpa only [pairWord_seated,ite_true] using ha
  · intro h q hq
    rcases Finset.mem_union.mp hq with hq|hq
    · exact inner_edge_neutral_on_one_pair E cubic loopless e x y q hq
    · obtain ⟨j,_,rfl⟩ := Finset.mem_image.mp hq
      change pairWord E cubic e x y (seat E cubic j false)=true ∨
        pairWord E cubic e x y (seat E cubic j true)=true
      by_cases hj : j=e <;> simp [pairWord_seated,hj,h]

/-- On this one-pair slice (not on arbitrary multi-pair inputs), the
literal whole pinned CNF's integer count is exactly the exterior OR. -/
theorem native_count_one_pair (loopless : ∀v,(v,v)∉E)
    (e : E) (x y : Bool) :
    let F := replacedEdges E cubic
    let h := replaced_cubic E cubic loopless
    PinnedCNF.modelCount (MainClonedCNF.formula F (MainClonedCNF.leftSlot F h)
      (MainClonedCNF.rightSlot F h) (pairWord E cubic e x y))=orValue ℕ x y := by
  dsimp only
  rw [MainClonedCNF.modelCount_cloned,PinnedCNF.count_eq_indicator,all_edges_one_pair_iff E cubic loopless]
  cases x <;> cases y <;> simp [orValue]

theorem old_root_one_pair (loopless : ∀v,(v,v)∉E)
    (f : ℤ[X]) (hf : f.Monic) (p : ℕ) (e : E) (x y : Bool) :
    let F := replacedEdges E cubic
    let h := replaced_cubic E cubic loopless
    reduce p f 1 (trueContraction (dNetwork F h)
      (oldRowFile F h f p (pairWord E cubic e x y)) hf) =
      orValue (Residue f 1 p) x y := by
  dsimp only
  rw [oldRow_contraction_reduce, native_count_one_pair E cubic loopless e x y]
  cases x <;> cases y <;> simp [orValue]

#print axioms pairsWord_on
#print axioms pairWord_left_only
#print axioms pairWord_right_only
#print axioms pairWord_false_location
#print axioms UD_is_outer_edges
#print axioms UD_one_pair
#print axioms inner_edge_neutral_on_one_pair
#print axioms all_edges_one_pair_iff
#print axioms native_count_one_pair
#print axioms old_root_one_pair

end
end V8NativeMessage.N6D
