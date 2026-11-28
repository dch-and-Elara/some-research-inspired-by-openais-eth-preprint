import A2R45LiteralDirectTensor

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 7600000
set_option maxRecDepth 2250
set_option linter.unusedSectionVars false

/-! Exact literal-occurrence incidence capacities for the direct equality
path (v9 2316 to 2324); this concerns the concrete pre-packing Network. -/
namespace A2R45Literal
open scoped Classical BigOperators
open Std.Sat J7R9Compiler J6R10Repack
noncomputable section

theorem first_path_sublist {A : Type*} (l : List A) :
    List.Sublist ((directPath l).map Prod.fst) l := by
  induction l with
  | nil => exact List.Sublist.slnil
  | cons a t ih =>
    cases t with
    | nil => exact List.nil_sublist _
    | cons b t =>
      simpa only [directPath,List.map_cons] using List.Sublist.cons₂ a ih

theorem second_path_sublist {A : Type*} (l : List A) :
    List.Sublist ((directPath l).map Prod.snd) l := by
  rw [path_second_ends]
  cases l with
  | nil => exact List.Sublist.slnil
  | cons a t => exact List.Sublist.cons a (List.Sublist.refl t)

variable {V : Type} [DecidableEq V] (F : CNF V)

theorem occurrence_list_nodup (v : V) : (occurrences F v).Nodup := by
  exact Finset.nodup_toList _

theorem direct_equality_port_variable (e : DirectLink F) (j : Fin 2) :
    (literal F (directOccurrence F (.inr e) j)).1 = e.1 := by
  let L := occurrences F e.1
  have m : directEndpoints F e ∈ directPath L :=
    List.get_mem (directPath L) e.2
  apply (mem_occurrences F e.1 _).mp
  change (if j.val=0 then (directEndpoints F e).1 else (directEndpoints F e).2)∈L
  by_cases hz : j.val=0
  · rw [if_pos hz]
    exact (first_path_sublist L).subset (List.mem_map.mpr ⟨directEndpoints F e,m,rfl⟩)
  · rw [if_neg hz]
    exact (second_path_sublist L).subset (List.mem_map.mpr ⟨directEndpoints F e,m,rfl⟩)

theorem direct_same_equality_side_injective (j : Fin 2) :
    Function.Injective (fun e : DirectLink F=>directOccurrence F (.inr e) j) := by
  rintro ⟨v,a⟩ ⟨w,b⟩ h
  have eq : v=w :=
    (direct_equality_port_variable F ⟨v,a⟩ j).symm.trans
      ((congrArg (fun o=>(literal F o).1) h).trans (direct_equality_port_variable F ⟨w,b⟩ j))
  subst w
  let L := directPath (occurrences F v)
  let s : Occurrence F×Occurrence F→Occurrence F := if j.val=0 then Prod.fst else Prod.snd
  have hs : (L.map s).Nodup := by
    unfold s
    split
    · exact (first_path_sublist (occurrences F v)).nodup (occurrence_list_nodup F v)
    · exact (second_path_sublist (occurrences F v)).nodup (occurrence_list_nodup F v)
  let a' : Fin (L.map s).length := ⟨a.val,by rw [List.length_map]; exact a.isLt⟩
  let b' : Fin (L.map s).length := ⟨b.val,by rw [List.length_map]; exact b.isLt⟩
  have eqGet : (L.map s).get a'=(L.map s).get b' := by
    simp only [List.get_eq_getElem,List.getElem_map]
    unfold s
    by_cases hz : j.val=0
    · simp only [directOccurrence,directEndpoints,if_pos hz] at h ⊢
      exact h
    · simp only [directOccurrence,directEndpoints,if_neg hz] at h ⊢
      exact h
  have hi : a'=b' := (List.nodup_iff_injective_get.mp hs) eqGet
  have hab : a=b := Fin.ext (congrArg (fun n : Fin (L.map s).length=>n.val) hi)
  subst b
  rfl

def directPortSide : DirectWire F→Option (Fin 2)
  | ⟨.inl _,_⟩=>none
  | ⟨.inr _,j,_⟩=>some j

theorem direct_real_column_injected (o : Occurrence F) :
    Function.Injective (fun u : {e : DirectWire F//directOwner F e=.inl o}=>directPortSide F u.val) := by
  rintro ⟨⟨r,j,t⟩,ha⟩ ⟨⟨s,k,u⟩,hb⟩ h
  cases t
  · simp only [directOwner,Bool.false_eq_true,if_false,Sum.inl.injEq] at ha
    cases u
    · simp only [directOwner,Bool.false_eq_true,if_false,Sum.inl.injEq] at hb
      cases r with
      | inl c =>
        cases s with
        | inl d =>
          change (⟨c,j⟩:Occurrence F)=o at ha
          change (⟨d,k⟩:Occurrence F)=o at hb
          have hh := ha.trans hb.symm
          cases hh
          rfl
        | inr _ => cases h
      | inr a =>
        cases s with
        | inl _ => cases h
        | inr b =>
          change some j=some k at h
          have hh := Option.some.inj h
          subst k
          have ee := direct_same_equality_side_injective F j (ha.trans hb.symm)
          subst b
          rfl
    · cases hb
  · cases ha

theorem direct_real_column_degree (o : Occurrence F) :
    Nat.card {e : DirectWire F//directOwner F e=.inl o}≤3 := by
  have card := Nat.card_le_card_of_injective _ (direct_real_column_injected F o)
  exact card.trans (by simp [Nat.card_eq_fintype_card,Fintype.card_option])

theorem direct_pin_column_degree (p : DirectPort F) :
    Nat.card {e : DirectWire F//directOwner F e=.inr p}≤1 := by
  have h : Subsingleton {e : DirectWire F//directOwner F e=.inr p} := by
    refine ⟨?_⟩
    rintro ⟨⟨r,j,t⟩,ha⟩ ⟨⟨s,k,u⟩,hb⟩
    cases t
    · cases ha
    cases u
    · cases hb
    have h := (Sum.inr.inj ha).trans (Sum.inr.inj hb).symm
    cases h
    rfl
  simpa using Nat.card_le_card_of_injective (fun _ : {e : DirectWire F//directOwner F e=.inr p}=>())
    (fun a b _=>h.elim a b)

def directRowWires (r : DirectRow F) :
    (Fin (directArity F r)×Bool) ≃ {e : DirectWire F//(directNetwork F).row e=r} where
  toFun x := ⟨⟨r,x⟩,rfl⟩
  invFun e := e.property ▸ e.val.2
  left_inv _ := rfl
  right_inv := by
    rintro ⟨⟨q,j⟩,h⟩
    change q=r at h
    subst q
    rfl

theorem direct_concrete_network_degrees (w : ∀ cl∈F,cl.length≤3) :
    (∀ r,Nat.card {e : DirectWire F//(directNetwork F).row e=r}≤6) ∧
    (∀ c,Nat.card {e : DirectWire F//(directNetwork F).col e=c}≤3) := by
  constructor
  · intro r
    rw [←Nat.card_congr (directRowWires F r),Nat.card_eq_fintype_card]
    exact actual_direct_row_wire_bound F w r
  · rintro (o|p)
    · exact direct_real_column_degree F o
    · exact (direct_pin_column_degree F p).trans (by decide)

#print axioms direct_equality_port_variable
#print axioms direct_same_equality_side_injective
#print axioms direct_concrete_network_degrees
end
end A2R45Literal
