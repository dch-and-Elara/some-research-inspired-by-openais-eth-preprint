import F5R60AmbientCut

/-! The degree bound is derived on the literal-occurrence graph. A
neighbor is coded either by another slot of the same clause or by
another occurrence of the same variable; padding has degree zero. -/
namespace F5R60.Ambient
set_option autoImplicit false
open scoped Classical

variable {n : ℕ}

abbrev Neighbor {A : Type*} (G : SimpleGraph A) (x : A) := {y : A // G.Adj x y}

abbrev VariableSlots {C V : Type} (S : F5R59.ClauseSystem C V) (v : V) :=
  {x : F5R59.Vertex S // (F5R59.term S x).var=v}

private theorem remaining_card {A : Type*} [Finite A] (x : A) :
    Nat.card {y : A // y≠x}+1 = Nat.card A := by
  classical
  letI : Fintype A := Fintype.ofFinite A
  have hEq : Finset.univ.filter (fun a : A => a≠x) = Finset.univ.erase x := by
    ext i
    simp
  calc
    Nat.card {y : A // y≠x}+1 = (Finset.univ.erase x).card+1 := by
      rw [card_filter_subtype,hEq]
    _ = (Finset.univ : Finset A).card := Finset.card_erase_add_one (Finset.mem_univ _)
    _ = Nat.card A := by rw [Finset.card_univ,Nat.card_eq_fintype_card]

variable {C V : Type}
variable (S : F5R59.ClauseSystem C V)

private abbrev SameSlots (x : F5R59.Vertex S) :=
  {i : Fin (S.width x.1) // i≠x.2}

private abbrev OtherSlots (x : F5R59.Vertex S) :=
  {y : F5R59.Vertex S // (F5R59.term S y).var=(F5R59.term S x).var ∧ y≠x}

private theorem transport_slot (x y : F5R59.Vertex S) (eq : y.1=x.1) :
    (⟨x.1,Fin.cast (congrArg S.width eq) y.2⟩ : F5R59.Vertex S)=y := by
  rcases x with ⟨x,i⟩
  rcases y with ⟨y,j⟩
  change y=x at eq
  subst y
  rfl

private def otherSlotsEquiv (x : F5R59.Vertex S) :
    OtherSlots S x ≃ {v : VariableSlots S (F5R59.term S x).var // v≠⟨x,rfl⟩} where
  toFun y := ⟨⟨y.val,y.property.1⟩,fun eq => y.property.2 (congrArg Subtype.val eq)⟩
  invFun v := ⟨v.val.val,v.val.property,fun eq => v.property (Subtype.ext eq)⟩
  left_inv _ := rfl
  right_inv _ := rfl

private def neighborDecode (x : F5R59.Vertex S) :
    SameSlots S x ⊕ OtherSlots S x → F5R59.Vertex S
  | .inl i => ⟨x.1,i.val⟩
  | .inr y => y.val

private noncomputable def neighborCode (x : F5R59.Vertex S)
    (y : Neighbor (conflictGraph S) x) : SameSlots S x ⊕ OtherSlots S x := by
  let conflict : F5R59.conflict S x y.val := y.property
  by_cases eq : y.val.1=x.1
  · let idx := Fin.cast (congrArg S.width eq) y.val.2
    have ne : idx≠x.2 := by
      intro same
      apply conflict.1
      have hu := transport_slot S x y.val eq
      change (⟨x.1, idx⟩ : F5R59.Vertex S)=y.val at hu
      rw [same] at hu
      exact hu
    exact .inl ⟨idx,ne⟩
  · have opp := conflict.2.resolve_left (fun h => eq h.symm)
    exact .inr ⟨y.val,opp.1.symm,conflict.1.symm⟩

private theorem decode_neighbor_code (x : F5R59.Vertex S)
    (y : Neighbor (conflictGraph S) x) :
    neighborDecode S x (neighborCode S x y)=y.val := by
  unfold neighborCode
  dsimp only
  split
  · exact transport_slot S x y.val ‹y.val.1=x.1›
  · rfl

theorem conflict_degree_at_most_four [Finite C]
    (width : ∀ c, S.width c≤3) (occ : ∀ v, Nat.card (VariableSlots S v)≤3)
    (x : F5R59.Vertex S) :
    Nat.card (Neighbor (conflictGraph S) x) ≤ 4 := by
  have inj : Function.Injective (neighborCode S x) := by
    intro a b e
    have eq := congrArg (neighborDecode S x) e
    rw [decode_neighbor_code,decode_neighbor_code] at eq
    exact Subtype.ext eq
  have bound := Nat.card_le_card_of_injective (neighborCode S x) inj
  rw [Nat.card_sum] at bound
  have hs : Nat.card (SameSlots S x)+1 = S.width x.1 :=
    (remaining_card x.2).trans (Nat.card_fin _)
  have ho : Nat.card (OtherSlots S x)+1 = Nat.card (VariableSlots S (F5R59.term S x).var) := by
    rw [Nat.card_congr (otherSlotsEquiv S x)]
    exact remaining_card (⟨x,rfl⟩ : VariableSlots S (F5R59.term S x).var)
  have w := width x.1
  have o := occ (F5R59.term S x).var
  omega

noncomputable def actual_neighbor_equiv (key : F5R59.Vertex S ↪ Fin n) (x : F5R59.Vertex S) :
    Neighbor (conflictGraph S) x ≃ Neighbor (paddedH S key) (key x) := by
  let transfer (y : Neighbor (conflictGraph S) x) : Neighbor (paddedH S key) (key x) :=
    ⟨key y.val,(enabled_old_conflict_iff S key x y.val).2 y.property⟩
  apply Equiv.ofBijective transfer
  constructor
  · intro a b e
    exact Subtype.ext (key.injective (congrArg Subtype.val e))
  · intro a
    obtain ⟨u,v,h,hu,hv⟩ :=
      (SimpleGraph.map_adj key (conflictGraph S) (key x) a.val).1 a.property
    have eq := key.injective hu
    subst u
    exact ⟨⟨v,h⟩,Subtype.ext hv⟩

theorem actual_padded_degree_at_most_four [Finite C]
    (key : F5R59.Vertex S ↪ Fin n) (width : ∀ c, S.width c≤3)
    (occ : ∀ v, Nat.card (VariableSlots S v)≤3)
    (i : Fin n) : Nat.card (Neighbor (paddedH S key) i)≤4 := by
  by_cases present : ∃ x, key x=i
  · obtain ⟨x,hx⟩ := present
    subst i
    rw [← Nat.card_congr (actual_neighbor_equiv S key x)]
    exact conflict_degree_at_most_four S width occ x
  · have noEdge : IsEmpty (Neighbor (paddedH S key) i) :=
      ⟨fun j => padding_isolated_in_old S key i j.val present j.property⟩
    rw [Nat.card_eq_zero.mpr (Or.inl noEdge)]
    decide

private def sameIndexUnit (i : Fin n) : {j : Fin n // i=j} ≃ Unit where
  toFun _ := ()
  invFun _ := ⟨i,rfl⟩
  left_inv j := Subtype.ext j.property
  right_inv _ := rfl

theorem actual_left_degree (H B : SimpleGraph (Fin n)) (i : Fin n) :
    Nat.card (Neighbor (joined H B) (.inl i))=Nat.card (Neighbor H i)+1 := by
  have e : Neighbor (joined H B) (.inl i) ≃ Neighbor H i ⊕ Unit :=
    Equiv.subtypeSum.trans (Equiv.sumCongr (Equiv.refl _) (sameIndexUnit i))
  rw [Nat.card_congr e,Nat.card_sum]
  simp

theorem actual_right_degree (H B : SimpleGraph (Fin n)) (i : Fin n) :
    Nat.card (Neighbor (joined H B) (.inr i))=Nat.card (Neighbor B i)+1 := by
  have e : Neighbor (joined H B) (.inr i) ≃ Unit ⊕ Neighbor B i :=
    Equiv.subtypeSum.trans (Equiv.sumCongr (sameIndexUnit i) (Equiv.refl _))
  rw [Nat.card_congr e,Nat.card_sum,Nat.add_comm]
  simp

theorem actual_ambient_degree_at_most_five [Finite C]
    (key : F5R59.Vertex S ↪ Fin n) (B : SimpleGraph (Fin n))
    (width : ∀ c, S.width c≤3) (occ : ∀ v, Nat.card (VariableSlots S v)≤3)
    (cubic : ∀ i, Nat.card (Neighbor B i)=3) (v : Vertices n) :
    Nat.card (Neighbor (joined (paddedH S key) B) v)≤5 := by
  cases v with
  | inl i =>
    rw [actual_left_degree]
    have h := actual_padded_degree_at_most_four S key width occ i
    omega
  | inr i =>
    rw [actual_right_degree,cubic i]
    decide

#print axioms conflict_degree_at_most_four
#print axioms actual_neighbor_equiv
#print axioms actual_padded_degree_at_most_four
#print axioms actual_left_degree
#print axioms actual_right_degree
#print axioms actual_ambient_degree_at_most_five
end F5R60.Ambient
