import J6R49SourceLayoutVertex

/-! Select the actual retained old vertex keys from the registered
parent vertex table, rather than collecting only touched endpoints.
The table must contain isolated factors as well: no occurrence in
the edge tape is required for the selected vertex to survive. -/
namespace J6R49SourceLayout
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate J6R34RootAtlas
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes J6R32ChildResidentTransfer
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2900
set_option maxHeartbeats 6200000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

structure OwnerGroup (w : ℕ) where
  key : Word w
  group : Word 6

def selectOwnerKeys {w : ℕ} (g : Word 6) : List (OwnerGroup w)→Meter (List (Word w))
  | []=>⟨[],3⟩
  | x::xs =>
    let cmp := cmpAddr g x.group
    let rest := selectOwnerKeys g xs
    if cmp.result then
      let o := copyFixed x.key
      ⟨o.result::rest.result,cmp.steps+rest.steps+o.steps+3*w+12⟩
    else ⟨rest.result,cmp.steps+rest.steps+3*w+12⟩

theorem select_owner_keys_exact {w : ℕ} (g : Word 6) (xs : List (OwnerGroup w)) :
    let kept := (xs.filter (fun x=>decide (g=x.group))).map OwnerGroup.key
    selectOwnerKeys g xs = ⟨kept,3+(3*w+77)*xs.length+(3*w+1)*kept.length⟩ := by
  induction xs with
  | nil => rfl
  | cons x xs ih =>
    have cf : (cmpAddr g x.group).steps=65 := (cmpAddr_exact g x.group).2
    by_cases e : g=x.group
    · have h : (cmpAddr g x.group).result=true := (cmpAddr_exact g x.group).1.mpr e
      simp only [selectOwnerKeys,h,cf,if_true,copy_fixed_exact,ih,List.filter_cons,
        decide_eq_true e,List.map_cons,List.length_cons,Nat.mul_succ]
      congr 1
      omega
    · have h : (cmpAddr g x.group).result=false :=
          Bool.eq_false_iff.mpr (fun q=>e ((cmpAddr_exact g x.group).1.mp q))
      simp only [selectOwnerKeys,h,cf,Bool.false_eq_true,if_false,ih,List.filter_cons,
        decide_eq_false e,List.length_cons,Nat.mul_succ]
      congr 1
      omega

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {I : OccurrenceInput T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable (S : SiteInputs (compileOccurrence I) previous)
local notation "U" => (v.parent.host.Row⊕v.parent.host.Col)

def ownerGroupRow (x : U) : OwnerGroup S.ownerWidth :=
  ⟨S.oldKey x,word ((atGroup (layout T v) (axis T v)) x).val⟩

def parentGroup (x : U) : Prop := (atGroup (layout T v) (axis T v)) x=v.groupAt

theorem owner_group_read_eq (x : U) :
    word (q:=6) v.groupAt.val=(ownerGroupRow S x).group ↔ parentGroup (T:=T) (v:=v) x := by
  change word (q:=6) v.groupAt.val=word ((atGroup (layout T v) (axis T v)) x).val ↔ _
  constructor
  · intro h
    have e := congrArg Word.val h
    rw [word_val v.groupAt.isLt,word_val ((atGroup (layout T v) (axis T v)) x).isLt] at e
    exact (Fin.ext e).symm
  · intro h
    change (atGroup (layout T v) (axis T v)) x=v.groupAt at h
    rw [h]

structure ParentOwnerHeaders (S : SiteInputs (compileOccurrence I) previous) where
  order : List U
  unique : order.Nodup
  all : ∀ x,x∈order
  raw : List (OwnerGroup S.ownerWidth)
  same : raw=order.map (ownerGroupRow S)

def retainedPositions (order : List U) : List (OldAt T v) :=
  scanSubtype (parentGroup (T:=T) (v:=v)) order

theorem filter_real_owner_keys (order : List U) :
    (List.filter (fun x=>decide (word (q:=6) v.groupAt.val=x.group))
      (order.map (ownerGroupRow S))).map OwnerGroup.key =
        (retainedPositions (T:=T) (v:=v) order).map (fun u=>S.oldKey u.val) := by
  induction order with
  | nil => rfl
  | cons x xs ih =>
    unfold retainedPositions scanSubtype at *
    by_cases h : parentGroup (T:=T) (v:=v) x
    · simp only [List.map_cons,List.filter_cons,decide_eq_true ((owner_group_read_eq S x).mpr h),
        if_true,List.filterMap_cons,dif_pos h,ih]
      rfl
    · simp only [List.map_cons,List.filter_cons,decide_eq_false (fun t=>h ((owner_group_read_eq S x).mp t)),
        Bool.false_eq_true,if_false,List.filterMap_cons,dif_neg h,ih]

def readOldVertices (F : ParentOwnerHeaders S) : Meter (OldVertexKeys S) :=
  let O := selectOwnerKeys (word v.groupAt.val) F.raw
  let kept := retainedPositions (T:=T) (v:=v) F.order
  let e := physicalChildRows (T:=T) (v:=v)
  let rows := kept.map e.symm
  ⟨⟨rows,
    (scan_subtype_nodup (parentGroup (T:=T) (v:=v)) F.order F.unique).map e.symm.injective,
    fun u=>List.mem_map.mpr ⟨e u,by
      unfold kept retainedPositions
      exact (scan_subtype_mem (parentGroup (T:=T) (v:=v)) F.order (e u)).mpr (F.all (e u).val),
      e.symm_apply_apply u⟩,
    O.result,by
      unfold O
      rw [F.same,select_owner_keys_exact]
      change (List.filter (fun x=>decide (word (q:=6) v.groupAt.val=x.group))
        (F.order.map (ownerGroupRow S))).map OwnerGroup.key=rows.map (nativeRowKey S)
      rw [filter_real_owner_keys S F.order,List.map_map]
      apply List.map_congr_left
      intro u _
      change S.oldKey u.val=S.oldKey (e (e.symm u)).val
      rw [Equiv.apply_symm_apply]⟩,O.steps+4⟩

theorem exact_old_vertices_from_grouped_headers (F : ParentOwnerHeaders S) :
    let O := readOldVertices S F
    O.result.raw=(selectOwnerKeys (word v.groupAt.val) F.raw).result ∧
    O.steps=7+(3*S.ownerWidth+77)*F.raw.length+(3*S.ownerWidth+1)*O.result.rows.length := by
  let M := selectOwnerKeys (word v.groupAt.val) F.raw
  let O := readOldVertices S F
  have h : M.steps=3+(3*S.ownerWidth+77)*F.raw.length+(3*S.ownerWidth+1)*M.result.length := by
    obtain w := select_owner_keys_exact (word v.groupAt.val) F.raw
    change (selectOwnerKeys _ F.raw) = _ at w
    unfold M
    rw [w]
  have e : M.result.length=O.result.rows.length := by
    have len := congrArg List.length O.result.exact
    rw [List.length_map] at len
    exact len
  refine ⟨rfl,?_⟩
  change M.steps+4=7+(3*S.ownerWidth+77)*F.raw.length+(3*S.ownerWidth+1)*O.result.rows.length
  rw [h,e]
  omega

#print axioms select_owner_keys_exact
#print axioms owner_group_read_eq
#print axioms filter_real_owner_keys
#print axioms exact_old_vertices_from_grouped_headers
end
end J6R49SourceLayout