
import J6R27OriginalGateModeCompare
import J6R20AncestorWiring

/-! The generated packet's two slot arrays are written by scanning its
parent's installed physical seat file. A row and a column at a single
physical seat are separate fields; side and group membership are tested
independently. Validating/producing the installation is a separate cost. -/
namespace J6R27OriginalGate
open AOracleMachineTime J6R15ModeCost J6R21Ancestor

structure SeatField (a b : ℕ) where
  page : Word b
  slot : Word a
  rowGroup : Word 6
  colGroup : Word 6

def selectedSlots {a b : ℕ} (key : Word b) (g : Word 6) :
    List (SeatField a b)→Meter (List (Word a)×List (Word a))
  | [] => ⟨([],[]),4⟩
  | x::xs =>
    let p := cmpAddr key x.page
    let r := cmpAddr g x.rowGroup
    let c := cmpAddr g x.colGroup
    let old := selectedSlots key g xs
    let bit1 := copyFixed x.slot
    let bit2 := copyFixed x.slot
    ⟨(if p.result && r.result then bit1.result::old.result.1 else old.result.1,
      if p.result && c.result then bit2.result::old.result.2 else old.result.2),
      p.steps+r.steps+c.steps+old.steps+bit1.steps+bit2.steps+18⟩

def slotStride (a b : ℕ) := 10*b+6*a+155

def chooseRow {a b : ℕ} (key : Word b) (g : Word 6) (x : SeatField a b) : Option (Word a) :=
  if (cmpAddr key x.page).result && (cmpAddr g x.rowGroup).result then some x.slot else none

def chooseCol {a b : ℕ} (key : Word b) (g : Word 6) (x : SeatField a b) : Option (Word a) :=
  if (cmpAddr key x.page).result && (cmpAddr g x.colGroup).result then some x.slot else none

theorem selected_slots_exact {a b : ℕ} (key : Word b) (g : Word 6)
    (rows : List (SeatField a b)) :
    selectedSlots key g rows=⟨(rows.filterMap (chooseRow key g),rows.filterMap (chooseCol key g)),
      4+rows.length*slotStride a b⟩ := by
  induction rows with
  | nil => simp [selectedSlots]
  | cons x xs ih =>
    unfold selectedSlots
    dsimp only
    rw [ih,copy_fixed_exact,(cmpAddr_exact key x.page).2,(cmpAddr_exact g x.rowGroup).2,
      (cmpAddr_exact g x.colGroup).2]
    simp only [List.filterMap_cons,List.length_cons,Nat.add_mul,Nat.one_mul,slotStride]
    congr 1
    · congr 1
      · unfold chooseRow
        split <;> rfl
      · unfold chooseCol
        split <;> rfl
    · omega

open P11FullPacking J6R9PacketScopes J6R18ChildWrite J6R20Ancestor J6R10Repack
open J6R9PacketChild

variable {E X Y : Type} {N : Network E X Y} {a b : ℕ}
variable (P : PhysicalPacking N a (Fin 64)) (i : Fin a)
variable (pageWord : Page a P.copies (Fin 64)→Word b)

def physicalSeatField (e : E) : SeatField a b :=
  ⟨pageWord (P.seat e).1,slotWord P e,word (rowGroup P.mask i (P.seat e)).val,
    word (colGroup P.mask i (P.seat e)).val⟩

private theorem symbol_cmp {r g : Fin 64} :
    (cmpAddr (word (q:=6) g.val) (word (q:=6) r.val)).result=true ↔ r=g := by
  rw [(cmpAddr_exact _ _).1]
  constructor
  · intro h
    have e := congrArg Word.val h
    rw [word_val g.isLt,word_val r.isLt] at e
    exact Fin.ext e.symm
  · rintro rfl
    rfl

def scanSubtype {A : Type*} (Q : A→Prop) [DecidablePred Q] (xs : List A) :
    List {e // Q e} :=
  xs.filterMap fun x=>if h : Q x then some ⟨x,h⟩ else none

theorem scan_subtype_mem {A : Type*} (Q : A→Prop) [DecidablePred Q] (xs : List A) (x : {e // Q e}) :
    x∈scanSubtype Q xs↔x.val∈xs := by
  constructor
  · intro H
    obtain ⟨y,hy,e⟩ := List.mem_filterMap.mp H
    by_cases h : Q y
    · rw [dif_pos h] at e
      exact congrArg Subtype.val (Option.some.inj e) ▸ hy
    · rw [dif_neg h] at e
      cases e
  · intro H
    exact List.mem_filterMap.mpr ⟨x.val,H,dif_pos x.property⟩

theorem scan_subtype_nodup {A : Type*} (Q : A→Prop) [DecidablePred Q] (xs : List A)
    (h : xs.Nodup) : (scanSubtype Q xs).Nodup := by
  induction xs with
  | nil => exact List.nodup_nil
  | cons x xs ih =>
    obtain ⟨miss,nd⟩ := List.nodup_cons.mp h
    unfold scanSubtype at *
    rw [List.filterMap_cons]
    by_cases q : Q x
    · rw [dif_pos q]
      change (⟨x,q⟩::scanSubtype Q xs).Nodup
      exact List.nodup_cons.mpr ⟨fun h=>(miss ((scan_subtype_mem Q xs ⟨x,q⟩).mp h)),ih nd⟩
    · rw [dif_neg q]
      exact ih nd

variable [DecidableEq (Page a P.copies (Fin 64))]

def sourceRows (g : Fin 64) (k : Page a P.copies (Fin 64)) (xs : List E) :
    List (RowsOf P i g k) := scanSubtype (fun e=>childBlock P i e=(g,k)) xs

def sourceCols (g : Fin 64) (k : Page a P.copies (Fin 64)) (xs : List E) :
    List (ColsOf P i g k) := scanSubtype (fun e=>colGroup P.mask i (P.seat e)=g ∧ (P.seat e).1=k) xs

set_option maxHeartbeats 3500000 in
theorem physical_slots_emitted (injective : Function.Injective pageWord)
    (g : Fin 64) (k : Page a P.copies (Fin 64)) (xs : List E) (hn : xs.Nodup) (hall : ∀ e,e∈xs)
    (resident : List (SeatField a b)) (valid : resident=xs.map (physicalSeatField P i pageWord)) :
    let R := sourceRows P i g k xs
    let C := sourceCols P i g k xs
    let Z := selectedSlots (pageWord k) (word g.val) resident
    Z.result=(R.map (fun r=>slotWord P r.val),C.map (fun c=>slotWord P c.val)) ∧
      Z.steps=4+xs.length*slotStride a b ∧ R.Nodup ∧ C.Nodup ∧ (∀ r,r∈R) ∧ (∀ c,c∈C) := by
  let R := sourceRows P i g k xs
  let C := sourceCols P i g k xs
  have pOK (e : E) :
      (cmpAddr (pageWord k) (physicalSeatField P i pageWord e).page).result=true ↔ (P.seat e).1=k :=
    (cmpAddr_exact _ _).1.trans (by
      change pageWord k=pageWord (P.seat e).1 ↔ _
      rw [injective.eq_iff,eq_comm])
  have rOK (e : E) :
      ((cmpAddr (pageWord k) (physicalSeatField P i pageWord e).page).result &&
        (cmpAddr (word g.val) (physicalSeatField P i pageWord e).rowGroup).result)=true ↔
        childBlock P i e=(g,k) := by
    rw [Bool.and_eq_true,pOK]
    change ((_)=k ∧ (cmpAddr (word (q:=6) g.val)
      (word (q:=6) (rowGroup P.mask i (P.seat e)).val)).result=true) ↔ _
    rw [symbol_cmp]
    constructor
    · exact fun h=>Prod.ext h.2 h.1
    · exact fun h=>⟨congrArg Prod.snd h,congrArg Prod.fst h⟩
  have cOK (e : E) :
      ((cmpAddr (pageWord k) (physicalSeatField P i pageWord e).page).result &&
        (cmpAddr (word g.val) (physicalSeatField P i pageWord e).colGroup).result)=true ↔
        colGroup P.mask i (P.seat e)=g ∧ (P.seat e).1=k := by
    rw [Bool.and_eq_true,pOK]
    change ((_)=k ∧ (cmpAddr (word (q:=6) g.val)
      (word (q:=6) (colGroup P.mask i (P.seat e)).val)).result=true) ↔ _
    rw [symbol_cmp,and_comm]
  have hR : (xs.map (physicalSeatField P i pageWord)).filterMap (chooseRow (pageWord k) (word g.val))=
      R.map (fun r=>slotWord P r.val) := by
    unfold R sourceRows scanSubtype
    rw [List.filterMap_map,List.map_filterMap]
    apply List.filterMap_congr
    intro e _
    by_cases h : childBlock P i e=(g,k)
    · rw [Function.comp_apply,chooseRow,if_pos ((rOK e).mpr h),dif_pos h]
      rfl
    · rw [Function.comp_apply,chooseRow,if_neg (fun u=>h ((rOK e).mp u)),dif_neg h]
      rfl
  have hC : (xs.map (physicalSeatField P i pageWord)).filterMap (chooseCol (pageWord k) (word g.val))=
      C.map (fun r=>slotWord P r.val) := by
    unfold C sourceCols scanSubtype
    rw [List.filterMap_map,List.map_filterMap]
    apply List.filterMap_congr
    intro e _
    by_cases h : colGroup P.mask i (P.seat e)=g ∧ (P.seat e).1=k
    · rw [Function.comp_apply,chooseCol,if_pos ((cOK e).mpr h),dif_pos h]
      rfl
    · rw [Function.comp_apply,chooseCol,if_neg (fun u=>h ((cOK e).mp u)),dif_neg h]
      rfl
  have h1 : R.Nodup := scan_subtype_nodup _ _ hn
  have h2 : C.Nodup := scan_subtype_nodup _ _ hn
  have h3 : ∀ r,r∈R := fun r=>(scan_subtype_mem _ _ r).mpr (hall _)
  have h4 : ∀ c,c∈C := fun c=>(scan_subtype_mem _ _ c).mpr (hall _)
  dsimp only
  rw [valid,selected_slots_exact,hR,hC,List.length_map]
  exact ⟨rfl,rfl,h1,h2,h3,h4⟩

#print axioms selected_slots_exact
#print axioms scan_subtype_mem
#print axioms scan_subtype_nodup
#print axioms physical_slots_emitted
end J6R27OriginalGate


