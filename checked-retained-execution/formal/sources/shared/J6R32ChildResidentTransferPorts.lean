import J6R26DescriptorTreeTags
import J6R27OriginalGateSlots

/-! Paid transfer of the exact retained half-ports of an installed parent
to one source child. The new graph's old endpoint, page endpoint, immutable
old entry stamp, and occurrence ID are copied, not recomputed from labels. -/
namespace J6R32ChildResidentTransfer
open scoped Classical Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree
open J6R27OriginalGate P11FullPacking J6R9PacketScopes J6R10Repack J6R11Blueprint
set_option maxHeartbeats 8000000

structure ChildLane (r k e w p : ℕ) where
  oldKey : Word r
  pageKey : Word k
  parentEdge : Word e
  oldSide : Bool
  stamp : Stamp w p

structure ParentHalfWord (r k e w p : ℕ) where
  group : Word 6
  lane : ChildLane r k e w p

def copyLane {r k e w p : ℕ} (x : ChildLane r k e w p) : Meter (ChildLane r k e w p) :=
  let R := duplicateWord x.oldKey
  let C := duplicateWord x.pageKey
  let I := duplicateWord x.parentEdge
  let S := duplicateStamp x.stamp
  ⟨⟨R.result,C.result,I.result,x.oldSide,S.result⟩,R.steps+C.steps+I.steps+S.steps+5⟩

def laneFee (r k e w p : ℕ) := 3*r+3*k+3*e+3*w+3*p+29

theorem copy_lane_exact {r k e w p : ℕ} (x : ChildLane r k e w p) :
    copyLane x=⟨x,laneFee r k e w p⟩ := by
  cases x
  simp only [copyLane,duplicate_word_exact,duplicate_stamp_exact,laneFee]
  congr 1
  omega

def transferChild {r k e w p : ℕ} (g : Word 6) :
    List (ParentHalfWord r k e w p)→Meter (List (ChildLane r k e w p))
  | [] => ⟨[],4⟩
  | x::xs =>
    let cmp := cmpAddr g x.group
    let z := transferChild g xs
    if cmp.result then
      let y := copyLane x.lane
      ⟨y.result::z.result,cmp.steps+y.steps+z.steps+8⟩
    else ⟨z.result,cmp.steps+z.steps+8⟩

def transferFee (r k e w p n hit : ℕ) := 4+73*n+laneFee r k e w p*hit

theorem transfer_child_exact {r k e w p : ℕ} (g : Word 6)
    (raw : List (ParentHalfWord r k e w p)) :
    let out := transferChild g raw
    let desired := (raw.filter (fun x=>decide (g=x.group))).map ParentHalfWord.lane
    out.result=desired ∧ out.steps=transferFee r k e w p raw.length desired.length := by
  induction raw with
  | nil => simp [transferChild,transferFee]
  | cons x xs ih =>
    obtain ⟨result,fee⟩ := ih
    have ff : (cmpAddr g x.group).steps=65 := (cmpAddr_exact g x.group).2
    by_cases hg : g=x.group
    · have cp : (cmpAddr g x.group).result=true := (cmpAddr_exact g x.group).1.mpr hg
      simp only [transferChild,cp,ff,if_true,copy_lane_exact,List.length_cons,
        List.filter_cons,decide_eq_true hg,List.map_cons,result,fee]
      exact ⟨True.intro,by unfold transferFee; simp only [Nat.mul_add,Nat.mul_one]; omega⟩
    · have cp : (cmpAddr g x.group).result=false := Bool.eq_false_iff.mpr (fun h=>hg ((cmpAddr_exact g x.group).1.mp h))
      simp only [transferChild,cp,ff,Bool.false_eq_true,if_false,
        List.length_cons,List.filter_cons,decide_eq_false hg,result,fee]
      exact ⟨True.intro,by unfold transferFee; omega⟩

variable {E A B : Type} {N : Network E A B}
variable {a r k e w p : ℕ}

def installedLane (P : PhysicalPacking N a (Fin 64))
    (oldKey : A⊕B→Word r) (pageKey : Page a P.copies (Fin 64)→Word k)
    (edgeID : E→Word e) (stamp : A⊕B→Stamp w p)
    (v : Port E) : ChildLane r k e w p :=
  ⟨oldKey (owner N v),pageKey (atPacket P (edge v)),edgeID (edge v),side v,stamp (owner N v)⟩

def installedHalf (P : PhysicalPacking N a (Fin 64)) (i : Fin a)
    (oldKey : A⊕B→Word r) (pageKey : Page a P.copies (Fin 64)→Word k)
    (edgeID : E→Word e) (stamp : A⊕B→Stamp w p) (v : Port E) :
    ParentHalfWord r k e w p :=
  ⟨word (retainedGroup N (atGroup P i) v).val,installedLane P oldKey pageKey edgeID stamp v⟩

theorem lane_provenance_is_injective (P : PhysicalPacking N a (Fin 64))
    (oldKey : A⊕B→Word r) (pageKey : Page a P.copies (Fin 64)→Word k)
    (edgeID : E→Word e) (stamp : A⊕B→Stamp w p) (injective : Function.Injective edgeID) :
    Function.Injective (fun v : Port E=>
      let row := installedLane P oldKey pageKey edgeID stamp v
      (row.parentEdge,row.oldSide)) := by
  intro x y h
  change (edgeID (edge x),side x)=(edgeID (edge y),side y) at h
  cases x <;> cases y
  · exact congrArg Sum.inl (injective (congrArg Prod.fst h))
  · exact Bool.noConfusion (congrArg Prod.snd h)
  · exact Bool.noConfusion (congrArg Prod.snd h)
  · exact congrArg Sum.inr (injective (congrArg Prod.fst h))

noncomputable def childLaneOrder (P : PhysicalPacking N a (Fin 64)) (i : Fin a)
    (g : Fin 64) (order : List (Port E)) : List (ChildEdge N (atGroup P i) g) :=
  scanSubtype (fun v=>retainedGroup N (atGroup P i) v=g) order

theorem child_lane_order_complete (P : PhysicalPacking N a (Fin 64)) (i : Fin a)
    (g : Fin 64) (order : List (Port E)) (hn : order.Nodup) (hall : ∀ v,v∈order) :
    (childLaneOrder P i g order).Nodup ∧ ∀ z,z∈childLaneOrder P i g order :=
  ⟨scan_subtype_nodup _ _ hn,fun z=>(scan_subtype_mem _ _ z).mpr (hall z.val)⟩

theorem installed_transfer_physical (P : PhysicalPacking N a (Fin 64)) (i : Fin a)
    (g : Fin 64) (oldKey : A⊕B→Word r) (pageKey : Page a P.copies (Fin 64)→Word k)
    (edgeID : E→Word e) (stamp : A⊕B→Stamp w p) (order : List (Port E))
    (raw : List (ParentHalfWord r k e w p))
    (receipt : raw=order.map (installedHalf P i oldKey pageKey edgeID stamp)) :
    let C := child N (atGroup P i) (atPacket P) g
    let ch := childLaneOrder P i g order
    let run := transferChild (word g.val) raw
    run.result=ch.map (fun x=>⟨oldKey (C.row x).val,pageKey (C.col x),edgeID (edge x.val),
      side x.val,stamp (C.row x).val⟩) ∧
    run.steps=transferFee r k e w p order.length ch.length := by
  let row := installedHalf P i oldKey pageKey edgeID stamp
  have eqGroup (v : Port E) : word (q:=6) g.val=(row v).group ↔
      retainedGroup N (atGroup P i) v=g := by
    change (word (q:=6) g.val=word (retainedGroup N (atGroup P i) v).val) ↔ _
    constructor
    · intro h
      have v' := congrArg Word.val h
      rw [word_val g.isLt,word_val (retainedGroup N (atGroup P i) v).isLt] at v'
      exact (Fin.ext v').symm
    · intro h
      rw [h]
  have exactL (xs : List (Port E)) :
      (((xs.map row).filter (fun x=>decide (word (q:=6) g.val=x.group))).map ParentHalfWord.lane)
        =(childLaneOrder P i g xs).map (fun x=>installedLane P oldKey pageKey edgeID stamp x.val) := by
    induction xs with
    | nil => rfl
    | cons x xs ih =>
      unfold childLaneOrder scanSubtype at *
      by_cases hx : retainedGroup N (atGroup P i) x=g
      · simp only [List.map_cons,List.filter_cons,decide_eq_true ((eqGroup x).mpr hx),if_true,
          List.filterMap_cons,dif_pos hx,ih]
        rfl
      · simp only [List.map_cons,List.filter_cons,decide_eq_false (fun q=>hx ((eqGroup x).mp q)),Bool.false_eq_true,if_false,
          List.filterMap_cons,dif_neg hx,ih]
  obtain ⟨m,h⟩ := transfer_child_exact (word g.val) raw
  change raw=order.map row at receipt
  rw [receipt,exactL] at m h
  rw [List.length_map,List.length_map] at h
  rw [receipt]
  exact ⟨m,h⟩

variable [Fintype E] [Fintype A] [Fintype B]

theorem literal_child_keeps_birth {f : ℤ[X]} {ell a0 q : ℕ}
    (P : PhysicalPacking N a0 (Fin 64)) (i : Fin a0) (g : Fin 64)
    {t : ℤ} (ht : t≠0) (hv : padicValInt 2 t=i.val)
    (nil : (2:Residue f ell q)^q=0) (z : Residue f ell q)
    (old : EntryFile f ell N) (β : Mode i q P.mask →₀ ℕ)
    (oldKey : A⊕B→Word r) (pageKey : Page a0 P.copies (Fin 64)→Word k)
    (edgeID : E→Word e) (stamp : A⊕B→Stamp w p)
    (stored : ∀ v,(stamp v).created.val=(old v).created)
    (x : ChildEdge N (atGroup P i) g) :
    let C := actualPacketHost P i ht hv q nil z old β g
    (installedLane P oldKey pageKey edgeID stamp x.val).stamp.created.val=
      (C.file (.inl ((child N (atGroup P i) (atPacket P) g).row x))).created := by
  exact stored (owner N x.val)

#print axioms copy_lane_exact
#print axioms transfer_child_exact
#print axioms lane_provenance_is_injective
#print axioms child_lane_order_complete
#print axioms installed_transfer_physical
#print axioms literal_child_keeps_birth
end J6R32ChildResidentTransfer