import J6R53OldOwnerNext
import J6R52FreshExteriorWordsRetained
import J6R57PublicRequestCore

/-! One deterministic word chart for *this* child: the tag keeps
identical inherited-row and new-page bit patterns distinct. The
roster uses the actual retained-owner scan and the actual published
page order, including owners not occurring in an edge. -/
namespace J6R58RequestSource
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R50SourceProducer
open J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R51ParentFrames J6R49SourceLayout J6R48RawRoute J6ActiveRun
open J6R52FreshExterior J6R53OldOwner J6R57PublicRequest
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 19200000
set_option maxRecDepth 4700
set_option Elab.async false

def tagWord (s : Bool) : Word 1 := ⟨[s],rfl⟩

def blankWord (w : ℕ) : Word w := ⟨List.replicate w false,List.length_replicate⟩

def taggedName {own page : ℕ} : Word own ⊕ Word page → Word (1+(own+page))
  | .inl x => joinKey (tagWord false) (joinKey x (blankWord page))
  | .inr y => joinKey (tagWord true) (joinKey (blankWord own) y)

theorem tagged_name_injective {own page : ℕ} :
    Function.Injective (taggedName (own:=own) (page:=page)) := by
  intro a b eq
  cases a with
  | inl x =>
    cases b with
    | inl y =>
      have h := (join_key_equality (join_key_equality eq).2).1
      exact congrArg Sum.inl h
    | inr y =>
      have h : tagWord false=tagWord true := (join_key_equality eq).1
      cases congrArg Word.bits h
  | inr x =>
    cases b with
    | inl y =>
      have h : tagWord true=tagWord false := (join_key_equality eq).1
      cases congrArg Word.bits h
    | inr y =>
      have h := (join_key_equality (join_key_equality eq).2).2
      exact congrArg Sum.inr h

def writeBlank (w : ℕ) : Meter (Word w) :=
  let Z := emitZeros w
  ⟨⟨Z.result,(congrArg List.length (emitted_zeros_exact w).1).trans List.length_replicate⟩,Z.steps⟩

theorem written_blank_exact (w : ℕ) :
    writeBlank w=⟨blankWord w,4*w+1⟩ := by
  have z := emitted_zeros_exact w
  unfold writeBlank blankWord
  simp only [z.1,z.2]

def tagFieldFee (own page blank : ℕ) := 4*blank+6*(1+(own+page))+7

def writeTaggedName {own page : ℕ} : Word own ⊕ Word page→Meter (Word (1+(own+page)))
  | .inl x =>
    let Z := writeBlank page
    let O := copyFixed (joinKey (tagWord false) (joinKey x Z.result))
    ⟨O.result,Z.steps+O.steps+3*(1+(own+page))+5⟩
  | .inr y =>
    let Z := writeBlank own
    let O := copyFixed (joinKey (tagWord true) (joinKey Z.result y))
    ⟨O.result,Z.steps+O.steps+3*(1+(own+page))+5⟩

theorem actual_tagged_write_exact {own page : ℕ} (x : Word own ⊕ Word page) :
    writeTaggedName x=⟨taggedName x,tagFieldFee own page (match x with | .inl _=>page | .inr _=>own)⟩ := by
  cases x <;> simp only [writeTaggedName,written_blank_exact,copy_fixed_exact,taggedName,tagFieldFee]
  all_goals (congr 1; omega)

def tagOwnerWords {own page : ℕ} (rows : List (Word own)) (cols : List (Word page)) :
    Meter (List (Word (1+(own+page)))) :=
  let L := emitRows (fun x=>writeTaggedName (.inl x)) rows
  let R := emitRows (fun y=>writeTaggedName (.inr y)) cols
  let full := prependRows R.result L.result
  ⟨full.result,L.steps+R.steps+full.steps+4⟩

theorem emitted_owner_words_exact {own page : ℕ} (rows : List (Word own)) (cols : List (Word page)) :
    (tagOwnerWords rows cols).result=
      rows.map (fun x=>taggedName (.inl x))++cols.map (fun y=>taggedName (.inr y)) := by
  unfold tagOwnerWords
  simp only [prepend_rows_exact]
  rw [(emitted_rows_exact _ rows).1,(emitted_rows_exact _ cols).1]
  simp only [actual_tagged_write_exact]

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable (X : StoredSite T v key prec tw bw page)
local notation "Owner" => (v.child.host.Row⊕v.child.host.Col)
local notation "ow" => (1+(X.site.ownerWidth+page))

def currentOwnerEndpoint : Owner→(Word X.site.ownerWidth ⊕ Word page)
  | .inl r => Sum.inl (nativeRowKey X.site r)
  | .inr c => Sum.inr (nativeColKey X.site c)

def nameCurrentOwner (u : Owner) : Word ow := taggedName (currentOwnerEndpoint X u)

theorem generated_name_stays_injective (oldInj : Function.Injective X.site.oldKey) :
    Function.Injective (nameCurrentOwner X) := by
  have rowName : Function.Injective (nativeRowKey X.site) :=
    oldInj.comp (Subtype.val_injective.comp (physicalChildRows (T:=T) (v:=v)).injective)
  have pageName : Function.Injective (nativeColKey X.site) :=
    (X.canonical.symm ▸ occurrence_page_word_injective X.input).comp
      (physicalChildCols (T:=T) (v:=v)).injective
  intro x y eq
  have same := tagged_name_injective (show taggedName (currentOwnerEndpoint X x)=taggedName (currentOwnerEndpoint X y) from eq)
  cases x with
  | inl r =>
    cases y with
    | inl w => exact congrArg Sum.inl (rowName (Sum.inl.inj same))
    | inr c => cases same
  | inr c =>
    cases y with
    | inl r => cases same
    | inr w => exact congrArg Sum.inr (pageName (Sum.inr.inj same))

variable (H : ParentOwnerHeaders X.site)

def actualOwnerNameTape : Meter (List (Word ow)) :=
  let O := readOldVertices X.site H
  let V := vertexKeysOfBirth X.site O.result X.canonical
  let W := tagOwnerWords V.result.rawRows V.result.rawCols
  ⟨W.result,O.steps+V.steps+W.steps+4⟩

theorem actual_child_names_have_no_missing_owner :
    let O := readOldVertices X.site H
    let V := vertexKeysOfBirth X.site O.result X.canonical
    let W := tagOwnerWords V.result.rawRows V.result.rawCols
    let M := actualOwnerNameTape X H
    M.result=(bornOwnerOrder X H).map (nameCurrentOwner X) ∧
      M.steps=O.steps+V.steps+W.steps+4 := by
  refine ⟨?_,rfl⟩
  let O := readOldVertices X.site H
  let V := vertexKeysOfBirth X.site O.result X.canonical
  change (tagOwnerWords V.result.rawRows V.result.rawCols).result=
    (V.result.order X.site).map (nameCurrentOwner X)
  rw [emitted_owner_words_exact,V.result.exactRows,V.result.exactCols,VertexKeys.order,List.map_append]
  simp only [List.map_map]
  rfl

#print axioms tagged_name_injective
#print axioms actual_tagged_write_exact
#print axioms emitted_owner_words_exact
#print axioms generated_name_stays_injective
#print axioms actual_child_names_have_no_missing_owner
end
end J6R58RequestSource
