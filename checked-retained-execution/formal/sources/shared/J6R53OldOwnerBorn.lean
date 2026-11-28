import J6R53OldOwnerTape
import J6R50SourceProducerOnline

/-! Use the grouped full owner headers for retained rows, not a
set of touched endpoints. Fresh column origins come from the same
actual all-page Birth. An isolated owner follows exactly the same
raw state-preserving logic as every other owner. -/
namespace J6R53OldOwner
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6R49SourceLayout
open J6ActiveRun J6R50SourceProducer
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3300
set_option maxHeartbeats 12500000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

theorem sum_cast_inl {f : ℤ[X]} {ell : ℕ} {A B : PhysicalHost f ell}
    (eq : A=B) (x : A.Row) :
    Equiv.cast (congrArg (fun H : PhysicalHost f ell=>H.Row⊕H.Col) eq) (.inl x)=
    .inl (Equiv.cast (congrArg PhysicalHost.Row eq) x) := by
  subst B
  rfl

theorem sum_cast_inr {f : ℤ[X]} {ell : ℕ} {A B : PhysicalHost f ell}
    (eq : A=B) (x : A.Col) :
    Equiv.cast (congrArg (fun H : PhysicalHost f ell=>H.Row⊕H.Col) eq) (.inr x)=
    .inr (Equiv.cast (congrArg PhysicalHost.Col eq) x) := by
  subst B
  rfl

def stitchOwners {A : Type} (fresh : List A) : List A→Meter (List A)
  | []=>⟨fresh,3⟩
  | a::as=>
    let rest := stitchOwners fresh as
    ⟨a::rest.result,rest.steps+4⟩

theorem stitch_owners_exact {A : Type} (old fresh : List A) :
    stitchOwners fresh old=⟨old++fresh,4*old.length+3⟩ := by
  induction old with
  | nil=>rfl
  | cons a as ih=>
    simp only [stitchOwners,ih,List.cons_append,List.length_cons,Nat.mul_succ]

variable {f : ℤ[X]} {ell s C key prec tw bw page gate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "P" => (v.parent.host.Row⊕v.parent.host.Col)
local notation "V" => (v.child.host.Row⊕v.child.host.Col)
local notation "G" => (Option (CodeGate (Word gate)))

def parentData (X : StoredSite T v key prec tw bw page) (gates : P→G) (u : P) :
    OwnerData gate key prec page := ⟨X.origins u,gates u⟩

def childGate (gates : P→G) (u : V) : G :=
  match childVertices T v u with
  | .inl old=>gates old.val
  | .inr _=>none

def childData (X : StoredSite T v key prec tw bw page) (gates : P→G) (u : V) :
    OwnerData gate key prec page := ⟨X.childOrigins u,childGate (T:=T) gates u⟩

theorem child_data_retained (X : StoredSite T v key prec tw bw page) (gates : P→G) (u : v.child.host.Row) :
    childData X gates (.inl u)=parentData X gates (physicalChildRows (T:=T) (v:=v) u).val := by
  have port : childVertices T v (.inl u)=.inl (physicalChildRows (T:=T) (v:=v) u) :=
    sum_cast_inl (actual_ticket_host T v) u
  unfold childData StoredSite.childOrigins childGate
  rw [port]
  rfl

theorem child_data_born (X : StoredSite T v key prec tw bw page) (gates : P→G) (u : v.child.host.Col) :
    childData X gates (.inr u)=
      freshOwnerData X.birth.job.immutable.payload.stamp (nativeColKey X.site u) := by
  have port : childVertices T v (.inr u)=.inr (physicalChildCols (T:=T) (v:=v) u) :=
    sum_cast_inr (actual_ticket_host T v) u
  unfold childData StoredSite.childOrigins childGate nativeColKey
  rw [port,X.canonical]
  rfl

def bornOwnerData (X : StoredSite T v key prec tw bw page) (gates : P→G)
    (source : CompleteRoster X.site.oldKey (parentData X gates)) (H : ParentOwnerHeaders X.site) :
    Meter (Option (List (OwnerData gate key prec page))) :=
  let old := readOldVertices X.site H
  let whole := vertexKeysOfBirth X.site old.result X.canonical
  let found := gatherOwners source.raw whole.result.rawRows
  match found.result with
  | none=>⟨none,old.steps+whole.steps+found.steps+4⟩
  | some inherited =>
    let fresh := writeFreshOwners (gate:=gate) X.birth.job.immutable.payload.stamp whole.result.rawCols
    let joined := stitchOwners fresh.result inherited
    ⟨some joined.result,old.steps+whole.steps+found.steps+fresh.steps+joined.steps+7⟩

theorem born_owner_data_actual (X : StoredSite T v key prec tw bw page) (gates : P→G)
    (source : CompleteRoster X.site.oldKey (parentData X gates)) (H : ParentOwnerHeaders X.site)
    (inj : Function.Injective X.site.oldKey) :
    let old := readOldVertices X.site H
    let whole := vertexKeysOfBirth X.site old.result X.canonical
    let found := gatherOwners source.raw whole.result.rawRows
    let fresh := writeFreshOwners (gate:=gate) X.birth.job.immutable.payload.stamp whole.result.rawCols
    bornOwnerData X gates source H=
      ⟨some ((whole.result.order X.site).map (childData X gates)),
        old.steps+whole.steps+found.steps+fresh.steps+(4*whole.result.rows.length+3)+7⟩ := by
  let old := readOldVertices X.site H
  let whole := vertexKeysOfBirth X.site old.result X.canonical
  let found := gatherOwners source.raw whole.result.rawRows
  let fresh := writeFreshOwners (gate:=gate) X.birth.job.immutable.payload.stamp whole.result.rawCols
  have read (row : v.child.host.Row) :
      (locate (nativeRowKey X.site row) source.raw).result=some (childData X gates (.inl row)) := by
    rw [child_data_retained]
    exact complete_owner_hit source inj (physicalChildRows (T:=T) (v:=v) row).val
  have left : found.result=some (whole.result.rows.map (fun u=>childData X gates (.inl u))) := by
    unfold found
    rw [whole.result.exactRows,gather_owner_words_exact source.raw (nativeRowKey X.site)
      (fun u=>childData X gates (.inl u)) whole.result.rows (fun u _=>read u)]
  have right : fresh.result=whole.result.cols.map (fun u=>childData X gates (.inr u)) := by
    unfold fresh
    rw [whole.result.exactCols,write_fresh_owners_exact]
    dsimp only
    rw [List.map_map]
    apply List.map_congr_left
    intro u _
    exact (child_data_born X gates u).symm
  change bornOwnerData X gates source H=⟨some ((whole.result.order X.site).map (childData X gates)),
    old.steps+whole.steps+found.steps+fresh.steps+(4*whole.result.rows.length+3)+7⟩
  unfold bornOwnerData
  change ((match found.result with
    | none=>⟨none,old.steps+whole.steps+found.steps+4⟩
    | some inherited=>
      let joined := stitchOwners fresh.result inherited
      ⟨some joined.result,old.steps+whole.steps+found.steps+fresh.steps+joined.steps+7⟩) :
    Meter (Option (List (OwnerData gate key prec page))))=_
  rw [left]
  dsimp only
  rw [stitch_owners_exact,right]
  simp only [List.length_map,VertexKeys.order,List.map_append,List.map_map,Function.comp_def]

theorem every_actual_child_owner_has_raw_entry
    (X : StoredSite T v key prec tw bw page) (gates : P→G)
    (source : CompleteRoster X.site.oldKey (parentData X gates)) (H : ParentOwnerHeaders X.site)
    (inj : Function.Injective X.site.oldKey) (u : V) :
    ∃ data,(bornOwnerData X gates source H).result=some data ∧ childData X gates u∈data := by
  let U := (vertexKeysOfBirth X.site (readOldVertices X.site H).result X.canonical).result
  refine ⟨(U.order X.site).map (childData X gates),?_,?_⟩
  · rw [born_owner_data_actual X gates source H inj]
  · exact List.mem_map.mpr ⟨u,(U.valid_order X.site).2 u,rfl⟩

#print axioms child_data_retained
#print axioms child_data_born
#print axioms born_owner_data_actual
#print axioms every_actual_child_owner_has_raw_entry
end
end J6R53OldOwner
