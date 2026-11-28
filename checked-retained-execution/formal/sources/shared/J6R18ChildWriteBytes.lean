import A1R12Combine
import J6R12BlueprintPacket
import J6R15ModeCostCursor

/-! Wire format for one evaluated packet entry, not an exponential
truth table. Retained descriptions are immutable handles with their
original creation word; only the port-order interface is replaced. -/
namespace J6R18ChildWrite
open scoped Polynomial
open AOracleMachineTime AOracleMachineTimeTape
open J6R11Blueprint J6R10Repack P11FullPacking J6R9PacketScopes
open J6R15ModeCost

def flattenEntry {p ell : ℕ} {fw : List (A1R10.Word p)} (w : A1R10.UVBlock fw ell) : List Bool :=
  w.val.flatMap (fun v=>v.val.flatMap Subtype.val)

theorem constant_flat_len {A B : Type*} (xs : List A) (k : ℕ) (f : A→List B)
    (h : ∀ x∈xs,(f x).length=k) :
    (xs.flatMap f).length=xs.length*k := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    rw [List.flatMap_cons,List.length_append,h x List.mem_cons_self,ih (fun y hy=>h y (List.mem_cons_of_mem _ hy)),
      List.length_cons,Nat.succ_mul,Nat.add_comm]

theorem flattenEntry_len {p ell : ℕ} {fw : List (A1R10.Word p)} (w : A1R10.UVBlock fw ell) :
    (flattenEntry w).length=ell*(fw.length*p) := by
  unfold flattenEntry
  rw [constant_flat_len _ (fw.length*p) _ _,w.property]
  intro u _
  rw [constant_flat_len _ p _ (fun x _=>x.property),u.property]

def splitAtWidth (k : ℕ) : ℕ → List Bool → List (List Bool)
  | 0,_ => []
  | n+1,bs => bs.take k::splitAtWidth k n (bs.drop k)

theorem split_flat (k : ℕ) (xs : List (List Bool)) (hx : ∀ x∈xs,x.length=k) :
    splitAtWidth k xs.length xs.flatten=xs := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have h := hx x List.mem_cons_self
    rw [List.length_cons,List.flatten_cons,splitAtWidth,← h,List.take_left,List.drop_left,h,
      ih (fun y hy=>hx y (List.mem_cons_of_mem _ hy))]

def frameRead (tagWidth p e ell : ℕ) (bs : List Bool) :
    List Bool × List (List (List Bool)) :=
  (bs.take tagWidth, (splitAtWidth (e*p) ell (bs.drop tagWidth)).map (splitAtWidth p e))

def writeEntry {q p ell : ℕ} {fw : List (A1R10.Word p)} (tag : Word q)
    (w : A1R10.UVBlock fw ell) : Meter (List Bool) :=
  ⟨tag.bits++flattenEntry w,4*q+6*ell*(fw.length*p+1)+16⟩

theorem write_roundtrip {q p ell : ℕ} {fw : List (A1R10.Word p)} (tag : Word q)
    (w : A1R10.UVBlock fw ell) :
    let op := writeEntry tag w
    op.result.length=q+ell*(fw.length*p) ∧
      frameRead q p fw.length ell op.result=(tag.bits,w.val.map (fun u=>u.val.map Subtype.val)) ∧
      op.steps=4*q+6*ell*(fw.length*p+1)+16 := by
  let rows := w.val.map (fun v=>v.val.flatMap Subtype.val)
  have hRows : rows.length=ell := by simp only [rows,List.length_map,w.property]
  have hU : ∀ xs∈rows,xs.length=fw.length*p := by
    intro xs hx
    obtain ⟨u,_,rfl⟩ := List.mem_map.mp hx
    rw [constant_flat_len _ p _ (fun x _=>x.property),u.property]
  have hF : rows.flatten=flattenEntry w := by rw [flattenEntry]; rfl
  have outer := split_flat (fw.length*p) rows hU
  rw [hRows,hF] at outer
  refine ⟨by rw [writeEntry,List.length_append,tag.size,flattenEntry_len],?_,rfl⟩
  unfold frameRead writeEntry
  dsimp only
  have hTake : (tag.bits++flattenEntry w).take q=tag.bits := by
    simpa only [tag.size] using (@List.take_left Bool tag.bits (flattenEntry w))
  have hDrop : (tag.bits++flattenEntry w).drop q=flattenEntry w := by
    simpa only [tag.size] using (@List.drop_left Bool tag.bits (flattenEntry w))
  rw [hTake,hDrop,outer]
  congr 1
  rw [show rows=w.val.map (fun v=>v.val.flatMap Subtype.val) from rfl,List.map_map]
  apply List.map_congr_left
  intro v _
  let rs := v.val.map Subtype.val
  have hL : rs.length=fw.length := by simp only [rs,List.length_map,v.property]
  have hC : ∀ b∈rs,b.length=p := by
    intro b hb
    obtain ⟨x,_,rfl⟩ := List.mem_map.mp hb
    exact x.property
  have hF' : rs.flatten=v.val.flatMap Subtype.val := rfl
  have H := split_flat p rs hC
  rw [hL,hF'] at H
  exact H

structure FrozenRef (q : ℕ) where
  address : List Bool
  creation : Word q
  oldPorts : List (Word q)

def retainRef {q : ℕ} (old : FrozenRef q) (newPorts : List (Word q)) : Meter (FrozenRef q) :=
  ⟨⟨old.address,old.creation,newPorts⟩,4*old.address.length+4*q+newPorts.length*(4*q+8)+12⟩

theorem retainRef_exact {q : ℕ} (old : FrozenRef q) (newPorts : List (Word q)) :
    let z := retainRef old newPorts
    z.result.address=old.address ∧ z.result.creation=old.creation ∧ z.result.oldPorts=newPorts ∧
      z.steps=4*old.address.length+4*q+newPorts.length*(4*q+8)+12 :=
  ⟨rfl,rfl,rfl,rfl⟩

theorem retained_host_tag {E A B G : Type} [Fintype E] [Fintype A] [Fintype B]
    [LinearOrder G] [Fintype G]
    {a : ℕ} {N : Network E A B} {f : ℤ[X]} {ell q : ℕ}
    (P : PhysicalPacking N a G) (i : Fin a) {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (p : ℕ) (hnil : (2:Residue f ell p)^p=0) (z : Residue f ell p)
    (old : EntryFile f ell N) (β : Mode i p P.mask→₀ℕ) (g : G) (v : Old (atGroup P i) g)
    (tape : FrozenRef q) (portMap : List (Word q))
    (hTag : tape.creation.val=(old v.val).created) :
    (retainRef tape portMap).result.creation.val=
      ((actualPacketHost P i ht hv p hnil z old β g).file (.inl v)).created :=
  hTag

#print axioms flattenEntry_len
#print axioms split_flat
#print axioms write_roundtrip
#print axioms retainRef_exact
#print axioms retained_host_tag
end J6R18ChildWrite


