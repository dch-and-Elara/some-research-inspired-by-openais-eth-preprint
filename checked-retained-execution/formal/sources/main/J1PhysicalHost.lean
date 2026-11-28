import MainClonedCNF
import J1MainSourceLabels
import Mathlib.Tactic

/-! Physical triangle replacement of a graph with three ports at each base
vertex. An exterior port matching has one mate per port and joins distinct
base vertices. The stored edge set keeps one orientation of each actual edge. -/
namespace J1PhysicalHost

open scoped BigOperators
variable {B : Type*} [Fintype B] [DecidableEq B]
abbrev Vertex (B : Type*) := B × Fin 3

structure Match (B : Type*) where
  mate : Vertex B → Vertex B
  inv : Function.Involutive mate
  cross : ∀ v, (mate v).1 ≠ v.1

omit [Fintype B] [DecidableEq B] in
theorem Match.mate_ne (M : Match B) (v : Vertex B) : M.mate v ≠ v :=
  fun h => M.cross v (congrArg Prod.fst h)

def next (v : Vertex B) : Vertex B := (v.1,v.2+1)
def prev (v : Vertex B) : Vertex B := (v.1,v.2-1)

omit [Fintype B] [DecidableEq B] in
theorem next_prev (v : Vertex B) : next (prev v) = v := by
  rcases v with ⟨b,i⟩
  have hh : i-1+1=i := by fin_cases i <;> decide
  exact Prod.ext rfl hh

omit [Fintype B] [DecidableEq B] in
theorem prev_next (v : Vertex B) : prev (next v) = v := by
  rcases v with ⟨b,i⟩
  have hh : i+1-1=i := by fin_cases i <;> decide
  exact Prod.ext rfl hh

omit [Fintype B] [DecidableEq B] in
theorem next_ne (v : Vertex B) : next v ≠ v := by
  rcases v with ⟨b,i⟩
  intro h
  have hs : i+1=i := congrArg Prod.snd h
  fin_cases i <;> contradiction

def nextEdge : Vertex B ↪ (Vertex B × Vertex B) where
  toFun v := (v,next v)
  inj' := fun _ _ h => congrArg Prod.fst h

def interior (B : Type*) [Fintype B] : Finset (Vertex B × Vertex B) :=
  Finset.univ.map nextEdge

omit [DecidableEq B] in
theorem mem_interior (v w : Vertex B) : (v,w) ∈ interior B ↔ w=next v := by
  constructor
  · intro hb
    obtain ⟨t,_,ht⟩ := Finset.mem_map.mp hb
    have h1 : t=v := congrArg Prod.fst ht
    have h2 : next t=w := congrArg Prod.snd ht
    exact h2.symm.trans (congrArg next h1)
  · intro h
    exact Finset.mem_map.mpr ⟨v,Finset.mem_univ _,Prod.ext rfl h.symm⟩

noncomputable def pick (M : Match B) (v : Vertex B) : Prop :=
  let order := Fintype.equivFin (Vertex B)
  order v < order (M.mate v)

open Classical in
noncomputable def exterior (M : Match B) : Finset (Vertex B × Vertex B) :=
  (Finset.univ.filter (pick M)).map ⟨fun v => (v,M.mate v),fun _ _ h => congrArg Prod.fst h⟩

omit [DecidableEq B] in
theorem mem_exterior (M : Match B) (v w : Vertex B) :
    (v,w) ∈ exterior M ↔ w=M.mate v ∧ pick M v := by
  classical
  constructor
  · intro hb
    obtain ⟨t,ht,hp⟩ := Finset.mem_map.mp hb
    have h1 : t=v := congrArg Prod.fst hp
    have h2 : M.mate t=w := congrArg Prod.snd hp
    exact ⟨h2.symm.trans (congrArg M.mate h1),h1 ▸ (Finset.mem_filter.mp ht).2⟩
  · rintro ⟨h,hp⟩
    exact Finset.mem_map.mpr ⟨v,Finset.mem_filter.mpr ⟨Finset.mem_univ _,hp⟩,
      Prod.ext rfl h.symm⟩

omit [DecidableEq B] in
theorem pick_mate_iff (M : Match B) (v : Vertex B) :
    pick M (M.mate v) ↔ ¬pick M v := by
  let order := Fintype.equivFin (Vertex B)
  have h : order (M.mate v) ≠ order v := fun h' => M.mate_ne v (order.injective h')
  change (order (M.mate v) < order (M.mate (M.mate v))) ↔ ¬(order v < order (M.mate v))
  rw [M.inv v,not_lt]
  exact lt_iff_le_and_ne.trans (by simp [h])

noncomputable def edges (M : Match B) : Finset (Vertex B × Vertex B) := interior B ∪ exterior M

omit [DecidableEq B] in
theorem layers_disjoint (M : Match B) : Disjoint (interior B) (exterior M) := by
  apply Finset.disjoint_left.mpr
  rintro ⟨v,w⟩ hi he
  have h1 := (mem_interior v w).mp hi
  have h2 := ((mem_exterior M v w).mp he).1
  have hz := congrArg Prod.fst (h2.symm.trans h1)
  exact M.cross v hz

theorem interior_out (v : Vertex B) :
    (interior B).filter (fun e => e.1=v) = {(v,next v)} := by
  ext e
  rcases e with ⟨p,q⟩
  simp only [Finset.mem_filter,mem_interior,Finset.mem_singleton]
  constructor
  · rintro ⟨h,rfl⟩
    exact Prod.ext rfl h
  · rintro h
    have h1 := congrArg Prod.fst h
    have h2 := congrArg Prod.snd h
    exact ⟨h2.trans (congrArg next h1).symm,h1⟩

theorem interior_in (v : Vertex B) :
    (interior B).filter (fun e => e.2=v) = {(prev v,v)} := by
  ext e
  rcases e with ⟨p,q⟩
  simp only [Finset.mem_filter,mem_interior,Finset.mem_singleton]
  constructor
  · rintro ⟨h,rfl⟩
    exact Prod.ext ((prev_next p).symm.trans (congrArg prev h).symm) rfl
  · intro h
    have h1 : p=prev v := congrArg Prod.fst h
    have h2 : q=v := congrArg Prod.snd h
    refine ⟨?_,h2⟩
    rw [h1,h2,next_prev]

open Classical in
theorem exterior_out (M : Match B) (v : Vertex B) :
    (exterior M).filter (fun e => e.1=v) = if pick M v then {(v,M.mate v)} else ∅ := by
  classical
  ext e
  rcases e with ⟨p,q⟩
  simp only [Finset.mem_filter,mem_exterior]
  by_cases hv : pick M v
  · rw [if_pos hv,Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h,_⟩,rfl⟩
      exact Prod.ext rfl h
    · intro h
      have h1 : p=v := congrArg Prod.fst h
      have h2 : q=M.mate v := congrArg Prod.snd h
      exact ⟨⟨h2.trans (congrArg M.mate h1).symm,h1.symm ▸ hv⟩,h1⟩
  · rw [if_neg hv]
    constructor
    · rintro ⟨⟨_,h⟩,rfl⟩
      exact False.elim (hv h)
    · simp

open Classical in
theorem exterior_in (M : Match B) (v : Vertex B) :
    (exterior M).filter (fun e => e.2=v) = if pick M v then ∅ else {(M.mate v,v)} := by
  classical
  ext e
  rcases e with ⟨p,q⟩
  simp only [Finset.mem_filter,mem_exterior]
  by_cases hv : pick M v
  · rw [if_pos hv]
    constructor
    · rintro ⟨⟨h,pickp⟩,rfl⟩
      have := (pick_mate_iff M p).mp (h ▸ hv)
      exact False.elim (this pickp)
    · simp
  · rw [if_neg hv,Finset.mem_singleton]
    constructor
    · rintro ⟨⟨h,_⟩,rfl⟩
      exact Prod.ext ((M.inv p).symm.trans (congrArg M.mate h).symm) rfl
    · intro h
      have h1 : p=M.mate v := congrArg Prod.fst h
      have h2 : q=v := congrArg Prod.snd h
      refine ⟨⟨?_,h1.symm ▸ (pick_mate_iff M v).mpr hv⟩,h2⟩
      rw [h1,h2,M.inv v]

/-- Exactly three actual graph ports at every triangle vertex. -/
theorem degree_eq_three (M : Match B) (v : Vertex B) :
    GraphCutMoments.degree (edges M) v = 3 := by
  classical
  have hdis := layers_disjoint M
  have hd (f : (Vertex B × Vertex B) → Prop) [DecidablePred f] :
      Disjoint ((interior B).filter f) ((exterior M).filter f) :=
    hdis.mono (Finset.filter_subset _ _) (Finset.filter_subset _ _)
  unfold GraphCutMoments.degree edges
  rw [Finset.filter_union,Finset.filter_union,Finset.card_union_of_disjoint (hd _),
    Finset.card_union_of_disjoint (hd _),interior_out,interior_in,exterior_out,exterior_in]
  by_cases hv : pick M v <;> simp [hv]

theorem no_loops (M : Match B) (v : Vertex B) : (v,v) ∉ edges M := by
  intro h
  rcases Finset.mem_union.mp h with hi | he
  · exact next_ne v ((mem_interior v v).mp hi).symm
  · exact M.mate_ne v ((mem_exterior M v v).mp he).1.symm

theorem block_card (b : B) :
    (Finset.univ.filter (fun v : Vertex B => v.1=b)).card = 3 := by
  classical
  have h : Finset.univ.filter (fun v : Vertex B => v.1=b) =
      (Finset.univ : Finset (Fin 3)).map ⟨(fun i => (b,i)),fun _ _ h => congrArg Prod.snd h⟩ := by
    ext v
    rcases v with ⟨b',j⟩
    simp [eq_comm]
  rw [h,Finset.card_map]
  simp

omit [DecidableEq B] in
theorem interior_same_block (v w : Vertex B) :
    (v,w) ∈ interior B ∨ (w,v) ∈ interior B ↔
      J1MainSourceLabels.triangleEdge Prod.fst v w := by
  rw [mem_interior,mem_interior]
  constructor
  · rintro (rfl | h)
    · exact ⟨(next_ne v).symm,rfl⟩
    · exact ⟨fun he => next_ne w (h.symm.trans he),
        (show v.1 = (next w).1 from congrArg Prod.fst h)⟩
  · intro h
    rcases v with ⟨b,i⟩
    rcases w with ⟨b',j⟩
    have hb : b=b' := h.2
    subst b'
    have hij : i≠j := fun h' => h.1 (Prod.ext rfl h')
    have ht : ∀ i j : Fin 3, i≠j → (j=i+1 ∨ i=j+1) := by decide
    exact (ht i j hij).imp (Prod.ext rfl) (Prod.ext rfl)

omit [DecidableEq B] in
theorem exterior_adjacent (M : Match B) (v w : Vertex B) :
    ((v,w) ∈ exterior M ∨ (w,v) ∈ exterior M) ↔ w=M.mate v := by
  rw [mem_exterior,mem_exterior]
  constructor
  · rintro (⟨h,_⟩ | ⟨h,_⟩)
    · exact h
    · exact (M.inv w).symm.trans (congrArg M.mate h).symm
  · intro h
    subst w
    by_cases hp : pick M v
    · exact Or.inl ⟨rfl,hp⟩
    · exact Or.inr ⟨(M.inv v).symm,(pick_mate_iff M v).mpr hp⟩

#print axioms degree_eq_three
#print axioms no_loops
#print axioms block_card
#print axioms interior_same_block
#print axioms exterior_adjacent

end J1PhysicalHost
