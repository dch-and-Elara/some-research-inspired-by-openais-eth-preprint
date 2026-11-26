import P5MainBalanceM6DirectChart

/-! On the literal printed endpoint numbering, a clone has one
original occurrence and at most one incoming and outgoing cycle
occurrence. The abstract clone count alone would not imply this. -/
namespace P5MainBalance.M6.Direct
open P5MainBalance.M6 P5MainIterator
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

abbrev EndpointChart (graph : Finset (V×V)) := Σ v : V,MainClonedCNF.EndpointSlot graph v

def encodeEndpoint (graph : Finset (V×V)) : graph×Bool→EndpointChart graph
  | (e,false) => ⟨e.val.1,.inl ⟨e.val,Finset.mem_filter.mpr ⟨e.property,rfl⟩⟩⟩
  | (e,true) => ⟨e.val.2,.inr ⟨e.val,Finset.mem_filter.mpr ⟨e.property,rfl⟩⟩⟩

def decodeEndpoint (graph : Finset (V×V)) : EndpointChart graph→graph×Bool
  | ⟨_,.inl e⟩ => (⟨e.val,(Finset.mem_filter.mp e.property).1⟩,false)
  | ⟨_,.inr e⟩ => (⟨e.val,(Finset.mem_filter.mp e.property).1⟩,true)

omit [Fintype V] in
theorem endpoint_encode_injective (graph : Finset (V×V)) :
    Function.Injective (encodeEndpoint graph) := by
  apply Function.LeftInverse.injective (g:=decodeEndpoint graph)
  rintro ⟨e,b⟩
  cases b <;> rfl

noncomputable def placedEndpoint (graph : Finset (V×V))
    (reg : ∀ v,GraphCutMoments.degree graph v=3) (p : EndpointChart graph) : V×Fin 4 :=
  (p.1,(MainClonedCNF.edgeNumber graph reg p.1 p.2).succ)

omit [Fintype V] in
theorem placedEndpoint_injective (graph : Finset (V×V))
    (reg : ∀ v,GraphCutMoments.degree graph v=3) :
    Function.Injective (placedEndpoint graph reg) := by
  rintro ⟨v,p⟩ ⟨w,q⟩ h
  have hv : v=w := congrArg Prod.fst h
  subst w
  suffices hpq : p=q by subst q; rfl
  apply (MainClonedCNF.edgeNumber graph reg v).injective
  have hf := congrArg Prod.snd h
  change (MainClonedCNF.edgeNumber graph reg v p).succ =
    (MainClonedCNF.edgeNumber graph reg v q).succ at hf
  apply Fin.ext
  exact Nat.succ.inj (congrArg Fin.val hf)

noncomputable def originalPlaced (graph : Finset (V×V))
    (reg : ∀ v,GraphCutMoments.degree graph v=3) :
    (V ⊕ (graph×Bool))→V×Fin 4
  | .inl v => (v,0)
  | .inr p => placedEndpoint graph reg (encodeEndpoint graph p)

omit [Fintype V] in
theorem originalPlaced_injective (graph : Finset (V×V))
    (reg : ∀ v,GraphCutMoments.degree graph v=3) :
    Function.Injective (originalPlaced graph reg) := by
  intro u v h
  rcases u with u|u <;> rcases v with v|v
  · exact congrArg Sum.inl (congrArg Prod.fst h)
  · have h' := congrArg (fun p : V×Fin 4=>p.2.val) h
    simp [originalPlaced,placedEndpoint] at h'
  · have h' := congrArg (fun p : V×Fin 4=>p.2.val) h
    simp [originalPlaced,placedEndpoint] at h'
  · exact congrArg Sum.inr (endpoint_encode_injective graph (placedEndpoint_injective graph reg h))

omit [Fintype V] [DecidableEq V] in
def portSplit (graph : Finset (V×V)) : MainClonedCNF.Port graph ≃
    (V⊕(graph×Bool)) ⊕ (V×Fin 4×Bool) :=
  (Equiv.sumAssoc _ _ _).symm

noncomputable def portKey (graph : Finset (V×V))
    (reg : ∀ v,GraphCutMoments.degree graph v=3) :
    ((V⊕(graph×Bool)) ⊕ (V×Fin 4×Bool))→(V×Fin 4)×Fin 3
  | .inl x => (originalPlaced graph reg x,0)
  | .inr (v,j,false) => ((v,j),1)
  | .inr (v,j,true) => ((v,j+1),2)

omit [Fintype V] in
theorem portKey_injective (graph : Finset (V×V))
    (reg : ∀ v,GraphCutMoments.degree graph v=3) :
    Function.Injective (portKey graph reg) := by
  intro u v h
  rcases u with u|⟨a,j,b⟩ <;> rcases v with v|⟨a',j',b'⟩
  · exact congrArg Sum.inl (originalPlaced_injective graph reg (congrArg Prod.fst h))
  · have he := congrArg (fun p : (V×Fin 4)×Fin 3=>p.2.val) h
    cases b' <;> simp [portKey] at he
  · have he := congrArg (fun p : (V×Fin 4)×Fin 3=>p.2.val) h
    cases b <;> simp [portKey] at he
  · have hh := congrArg Prod.snd h
    cases b <;> cases b'
    · have h0 : (a,j)=(a',j') := congrArg Prod.fst h
      exact congrArg Sum.inr (congrArg (fun p : V×Fin 4=>(p.1,p.2,false)) h0)
    · simp [portKey] at hh
    · simp [portKey] at hh
    · have h0 : (a,j+1)=(a',j'+1) := congrArg Prod.fst h
      have hv : a=a' := congrArg Prod.fst h0
      have hi : j=j' := add_right_cancel (congrArg Prod.snd h0)
      subst a'; subst j'; rfl

omit [Fintype V] in
theorem portKey_literal_owner (graph : Finset (V×V))
    (reg : ∀ v,GraphCutMoments.degree graph v=3) (e : MainClonedCNF.Port graph) :
    (portKey graph reg (portSplit graph e)).1 =
      ownerOf graph (MainClonedCNF.leftSlot graph reg) (MainClonedCNF.rightSlot graph reg) e := by
  rcases e with v|⟨e,b⟩|⟨v,i,b⟩
  · rfl
  · cases b <;> rfl
  · cases b <;> rfl

omit [Fintype V] in
theorem printed_clone_scope_at_most_three (graph : Finset (V×V))
    (reg : ∀ v,GraphCutMoments.degree graph v=3) (w : V×Fin 4) [Fintype V] :
    Fintype.card {e : MainClonedCNF.Port graph //
      ownerOf graph (MainClonedCNF.leftSlot graph reg) (MainClonedCNF.rightSlot graph reg) e=w} ≤3 := by
  let X := {e : MainClonedCNF.Port graph // 
    ownerOf graph (MainClonedCNF.leftSlot graph reg) (MainClonedCNF.rightSlot graph reg) e=w}
  let f (e : X) := (portKey graph reg (portSplit graph e.val)).2
  have hi : Function.Injective f := by
    intro e e' he
    apply Subtype.ext
    apply (portSplit graph).injective
    apply portKey_injective graph reg
    apply Prod.ext
    · rw [portKey_literal_owner,portKey_literal_owner,e.property,e'.property]
    · exact he
  simpa only [Fintype.card_fin] using Fintype.card_le_of_injective f hi

#print axioms endpoint_encode_injective
#print axioms originalPlaced_injective
#print axioms portKey_literal_owner
#print axioms printed_clone_scope_at_most_three
end P5MainBalance.M6.Direct
