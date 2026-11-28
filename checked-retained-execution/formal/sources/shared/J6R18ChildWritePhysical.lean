import J6R18ChildWriteSource
import J6R12BlueprintPacket

/-! Reindex the physical real row/column fibres to a serialized order.
This bridges geometry and bits, not precomputed coefficient values.
The views can be supplied by a later full child-incidence writer. -/
namespace J6R18ChildWrite
open scoped BigOperators Classical Polynomial
open Polynomial
open AOracleMachineTime AOracleCoordinates J6R15ModeCost
open P11FullPacking P1DyadicGrid J6R9PacketScopes J6R9PacketChild J6R9PacketLocal
open J6R9PacketTiles J6R10Repack J6R10RowAffine J6R10RowIdentity

theorem sum_ordered {A R : Type*} [Fintype A] [AddCommMonoid R] (xs : List A)
    (hn : xs.Nodup) (hA : ∀ a,a∈xs) (f : A→R) :
    (xs.map f).sum=∑ a,f a := by
  classical
  have hU : xs.toFinset=Finset.univ := by ext a; simp [hA a]
  rw [← List.sum_toFinset _ hn,hU]

theorem prod_ordered {A R : Type*} [Fintype A] [CommMonoid R] (xs : List A)
    (hn : xs.Nodup) (hA : ∀ a,a∈xs) (f : A→R) :
    (xs.map f).prod=∏ a,f a := by
  classical
  have hU : xs.toFinset=Finset.univ := by ext a; simp [hA a]
  rw [← List.prod_toFinset _ hn,hU]

variable {E A B G : Type} [Fintype E] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}

abbrev RowsOf (P : PhysicalPacking N a G) (i : Fin a) (g : G) (k : Page a P.copies G) :=
  {r : E // childBlock P i r=(g,k)}

abbrev ColsOf (P : PhysicalPacking N a G) (i : Fin a) (g : G) (k : Page a P.copies G) :=
  {c : E // colGroup P.mask i (P.seat c)=g ∧ (P.seat c).1=k}

omit [Fintype E] in
theorem row_scope (P : PhysicalPacking N a G) (i : Fin a) {g : G} {k : Page a P.copies G}
    (r : RowsOf P i g k) :
    rowGroup P.mask i (P.seat r.val)=g ∧ (P.seat r.val).1=k :=
  ⟨congrArg Prod.fst r.property,congrArg Prod.snd r.property⟩

noncomputable def realRow (P : PhysicalPacking N a G) (i : Fin a) {g : G} {k : Page a P.copies G}
    (v : PhysicalState P i g) (r : RowsOf P i g k) : SlotBit a :=
  ⟨word (P.seat r.val).2.val,v.1 ⟨r.val,(row_scope P i r).1⟩⟩

def realCol (P : PhysicalPacking N a G) (i : Fin a) {g : G} {k : Page a P.copies G}
    (v : PhysicalState P i g) (c : ColsOf P i g k) : SlotBit a :=
  ⟨word (P.seat c.val).2.val,v.2 ⟨c.val,c.property.1⟩⟩

omit [Fintype E] in
theorem realRow_index (P : PhysicalPacking N a G) (i : Fin a) {g : G} {k : Page a P.copies G}
    (v : PhysicalState P i g) (r : RowsOf P i g k) :
    (realRow P i v r).index.val=(P.seat r.val).2.val :=
  word_val (P.seat r.val).2.isLt

omit [Fintype E] in
theorem realCol_index (P : PhysicalPacking N a G) (i : Fin a) {g : G} {k : Page a P.copies G}
    (v : PhysicalState P i g) (r : ColsOf P i g k) :
    (realCol P i v r).index.val=(P.seat r.val).2.val :=
  word_val (P.seat r.val).2.isLt

omit [Fintype E] in
theorem realRow_bit (P : PhysicalPacking N a G) (i : Fin a) {g : G} {k : Page a P.copies G}
    (v : PhysicalState P i g) (r : RowsOf P i g k) :
    (realRow P i v r).assigned=groupBit (fun e=>P.seat e) (fun e=>P.seat e) P.mask i g v r.val := by
  simp only [realRow,groupBit,dif_pos (row_scope P i r).1]

omit [Fintype E] in
theorem row_order_max (P : PhysicalPacking N a G) (i : Fin a) (g : G) (k : Page a P.copies G)
    (rs : List (RowsOf P i g k)) (hn : rs.Nodup) :
    rs.length≤2^a := by
  have hi : Function.Injective (fun r : RowsOf P i g k => (P.seat r.val).2) := by
    intro x y h
    apply Subtype.ext
    apply P.seat.injective
    exact Prod.ext ((row_scope P i x).2.trans (row_scope P i y).2.symm) h
  classical
  let ys := rs.map (fun r : RowsOf P i g k => (P.seat r.val).2)
  have hd : ys.Nodup := hn.map hi
  calc
    rs.length = ys.length := (List.length_map _).symm
    _ = ys.toFinset.card := (List.toFinset_card_of_nodup hd).symm
    _ ≤ _ := by simpa only [Fintype.card_fin] using Finset.card_le_univ ys.toFinset

theorem localMeaning_physical {R : Type*} [CommRing R]
    (P : PhysicalPacking N a G) (i : Fin a) {g : G} {k : Page a P.copies G}
    (p : ℕ) (hnil : (2:R)^p=0) (t : ℤ) (z : R) (v : PhysicalState P i g)
    (r : RowsOf P i g k) (cs : List (ColsOf P i g k)) (hN : cs.Nodup) (hA : ∀ c,c∈cs) :
    localMeaning p hnil t z (realRow P i v r) (cs.map (realCol P i v)) =
      groupBase (fun e=>P.seat e) (fun e=>P.seat e) P.mask i t p hnil z g v r.val := by
  classical
  have hg := (row_scope P i r).1
  have hk := (row_scope P i r).2
  let U := {c : E // colGroup P.mask i (P.seat c)=rowGroup P.mask i (P.seat r.val)}
  let H (c : U) : R :=
    (W a t (((P.seat c.val).2.val:ℤ)-((P.seat r.val).2.val:ℤ))).eval₂ (J6ZeroTransport.reduceAt p hnil) z *
      bit R (v.2 ⟨c.val,c.property.trans hg⟩)
  let X := {c : U // (P.seat c.val).1=(P.seat r.val).1}
  let e : ColsOf P i g k ≃ X :=
    { toFun := fun c=>⟨⟨c.val,c.property.1.trans hg.symm⟩,c.property.2.trans hk.symm⟩
      invFun := fun c=>⟨c.val.val,⟨c.val.property.trans hg,c.property.trans hk⟩⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  unfold localMeaning
  rw [List.map_map,sum_ordered cs hN hA]
  simp only [Function.comp_def,realCol_index,realRow_index]
  simp only [groupBase,dif_pos hg]
  unfold localValue
  change _ = ∑ c : U,if (P.seat c.val).1=(P.seat r.val).1 then H c else 0
  calc
    _ = ∑ c : X,H c.val := Fintype.sum_equiv e _ _ (fun _=>rfl)
    _ = _ := by
      let pred (c : U) := (P.seat c.val).1=(P.seat r.val).1
      have h := (Finset.sum_subtype (p:=pred) (F:=(inferInstance : Fintype X))
        ((Finset.univ : Finset U).filter pred) (by simp) H).symm
      calc
        _=∑ c : U,@ite R (pred c) (Classical.propDecidable (pred c)) (H c) 0 :=
          h.trans (Finset.sum_filter (s:=Finset.univ) pred H)
        _=_ := by
          apply Finset.sum_congr rfl
          intro c _
          have hpred : pred c ↔ (P.seat c.val).1=(P.seat r.val).1 := Iff.rfl
          by_cases hu : pred c
          · simp only [if_pos hu,if_pos (hpred.mp hu)]
          · simp only [if_neg hu,if_neg (fun he=>hu (hpred.mpr he))]

theorem sourceMoment_physical {R : Type*} [CommRing R]
    (P : PhysicalPacking N a G) (i : Fin a) {g : G} {k : Page a P.copies G}
    (p : ℕ) (v : PhysicalState P i g)
    (m : Mode i p P.mask) (hm : childSource P i m=(g,k))
    (cs : List (ColsOf P i g k)) (hN : cs.Nodup) (hA : ∀ c,c∈cs) :
    (sourceMoment i m.tile.val m.order.val (cs.map (realCol P i v)):R)=stateMoment P i g p v m := by
  classical
  have hg : source P.mask i m=g := congrArg Prod.fst hm
  have hk : m.page=k := congrArg Prod.snd hm
  subst g
  subst k
  let U := ColsOf P i (source P.mask i m) m.page
  let H (u : U) : R := (coord i.val (P.seat u.val).2.val:R)^m.order.val *
    bit R (v.2 ⟨u.val,u.property.1⟩)
  let T := columns (fun c : E=>(P.seat c).1) (fun c =>(P.seat c).2.val) i.val m.page m.tile.val
  let X := {u : U // tile i.val (P.seat u.val).2.val=m.tile.val}
  let Y := {e : E // e∈T}
  let e : X ≃ Y :=
    { toFun := fun u => ⟨u.val.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,u.val.property.2,u.property⟩⟩
      invFun := fun c => ⟨⟨c.val,⟨column_source_group (fun e=>P.seat e) P.mask i m c.val c.property,
          (Finset.mem_filter.mp c.property).2.1⟩⟩,(Finset.mem_filter.mp c.property).2.2⟩
      left_inv := fun _=>rfl
      right_inv := fun _=>rfl }
  unfold sourceMoment
  rw [List.map_map,sum_ordered cs hN hA]
  simp only [Function.comp_def,realCol_index]
  simp only [stateMoment]
  unfold moment
  change (∑ c : U,if tile i.val (P.seat c.val).2.val=m.tile.val then H c else 0)=_
  calc
    _=∑ x : X,H x.val := by
      rw [← Finset.sum_filter]
      exact Finset.sum_subtype _ (by simp) H
    _=∑ u : Y,(coord i.val (P.seat u.val).2.val:R)^m.order.val*
      bit R (v.2 ⟨u.val,column_source_group (fun e=>P.seat e) P.mask i m u.val u.property⟩) :=
      Fintype.sum_equiv e _ _ (fun _=>rfl)
    _=_ := by
      let F (u : Y) : R := (coord i.val (P.seat u.val).2.val:R)^m.order.val*
        bit R (v.2 ⟨u.val,column_source_group (fun e=>P.seat e) P.mask i m u.val u.property⟩)
      change (∑ u : Y,F u)=∑ u ∈ T.attach,F u
      congr 1

#print axioms sum_ordered
#print axioms row_order_max
#print axioms localMeaning_physical
#print axioms sourceMoment_physical
end J6R18ChildWrite







