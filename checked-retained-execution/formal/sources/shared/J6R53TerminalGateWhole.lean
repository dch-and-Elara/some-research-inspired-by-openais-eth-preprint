import J6R53TerminalGateOwner
import J6R53TerminalGateRaw

/-! Whole terminal consuming real raw owner metadata and real cached
frames, not a LeafChart or an old command list. The proof-side local
source correspondence is separated from charge and traversal. -/
namespace J6R53TerminalGate
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R34ChildPath J6R36ChildFramedRoute J6R49SourceLayout J6R27OriginalGate
open J6R53OldOwner J6R50Leaf J6R50SourceProducer J6R51ParentFrames J6R52Terminal
open J6R26DescriptorTree J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R9Recursive J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6ActiveRun J6R22Active
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 37000000
set_option maxRecDepth 4900
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page w : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

def joinPaidTerminal
    (site : StoredSite T v key prec tw bw page) (saved : CachedParentFrames site.site)
    (old : Meter (Option (List (ReadCmd key page)))) (F : Frame f v.child.prec)
    (B : PageBank f ell key prec tw bw page) : Meter (Option (Block F ell)) :=
  match old.result with
  | none=>⟨none,old.steps+4⟩
  | some older =>
    let fresh := compileAllFresh site saved
    match fresh.result with
    | none=>⟨none,old.steps+fresh.steps+6⟩
    | some new =>
      let joined := stitchOwners new older
      let clock := visitFramesClock saved.rows
      let run := runRows hf F T.vPositive B clock.result joined.result
      ⟨some run.result,old.steps+fresh.steps+joined.steps+clock.steps+run.steps+11⟩

theorem measured_joined_terminal_exact
    (site : StoredSite T v key prec tw bw page) (saved : CachedParentFrames site.site)
    (old : Meter (Option (List (ReadCmd key page)))) (F : Frame f v.child.prec)
    (B : PageBank f ell key prec tw bw page) (older : List (ReadCmd key page))
    (oldSuccess : old.result=some older) :
    let fresh := compileAllFresh site saved
    let clock := visitFramesClock saved.rows
    let ready := (trueFreshPages site).map (freshWord site)
    let run := runRows hf F T.vPositive B clock.result (older++ready)
    joinPaidTerminal site saved old F B=
     ⟨some run.result,old.steps+fresh.steps+(4*older.length+3)+clock.steps+run.steps+11⟩ := by
  dsimp only [joinPaidTerminal]
  rw [oldSuccess]
  dsimp only
  rw [(all_fresh_commands_from_actual_paid_roster site saved).1]
  dsimp only
  rw [stitch_owners_exact]

def meteredTerminalFromOwners
    (site : StoredSite T v key prec tw bw page) (saved : CachedParentFrames site.site)
    (rawHeaders : List (OwnerGroup site.site.ownerWidth))
    (rawOwners : RawRoster site.site.ownerWidth w key prec page) (b : ℕ) (F : Frame f v.child.prec)
    (B : PageBank f ell key prec tw bw page) :
    Meter (Option (Block F ell)) :=
  let old := compileSelectedOwners b (cachedBook site saved) saved.rows rawOwners rawHeaders (word v.groupAt.val)
  joinPaidTerminal site saved old F B

theorem acquired_terminal_from_real_owner_rows
    (site : StoredSite T v key prec tw bw page) (saved : CachedParentFrames site.site)
    (headers : ParentOwnerHeaders site.site)
    (gates : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word w)))
    (roster : CompleteRoster site.site.oldKey (parentData site gates))
    (inj : Function.Injective site.site.oldKey) (b : ℕ)
    {c : Call (PhysicalHost f ell)} (path : Path sel r c)
    (born : J6R33StatefulArithmeticPage.Births T key prec tw bw page)
    (wasBorn : OnPath born site.birth.job path)
    (rootLive : PageBank f ell key prec tw bw page→Prop)
    (B : PageBank f ell key prec tw bw page) (live : opened born rootLive path B)
    (F : Frame f v.child.prec)
    (ownerCorrespondence : ∀ u : v.child.host.Row,
      let parent := (physicalChildRows (T:=T) (v:=v) u).val
      ∃ cmd : ReadCmd key page,
        (compileByOwnerData b (cachedBook site saved).result saved.rows
          (site.site.oldKey parent) (parentData site gates parent)).result=some cmd ∧
        ∀ bits : Fin v.child.edges→Bool,
          F.decode (cmd.read hf F T.vPositive B (List.ofFn bits)).result=
          (v.child.host.file (.inl u)).read hf v.child.prec (assignment v.child.host.network
            (bits∘(actualEdgeOrder T v site.birth.native.physical).symm) (.inl u))) :
    let out := meteredTerminalFromOwners site saved headers.raw roster.raw b F B
    ∃ word,out.result=some word ∧ F.decode word=reduce v.child.prec f ell (v.child.host.contract hf) := by
  let oldCode (u : v.child.host.Row) := Classical.choose (ownerCorrespondence u)
  let O := (readOldVertices site.site headers).result
  let V := (vertexKeysOfBirth site.site O site.canonical).result
  let rows := V.order site.site
  let clock := visitFramesClock saved.rows
  let code (u : v.child.host.Row⊕v.child.host.Col) :=
    match u with
    | .inl u=>oldCode u
    | .inr u=>freshWord site (physicalChildCols (T:=T) (v:=v) u)
  have layout := V.valid_order site.site
  have values (bits : Fin v.child.edges→Bool) (u : v.child.host.Row⊕v.child.host.Col) :
      F.decode ((code u).read hf F T.vPositive B (List.ofFn bits)).result =
        (v.child.host.file u).read hf v.child.prec (assignment v.child.host.network
          (bits∘(actualEdgeOrder T v site.birth.native.physical).symm) u) := by
    cases u with
    | inl row => exact (Classical.choose_spec (ownerCorrespondence row)).2 bits
    | inr col => exact emitted_fresh_word_is_actual_child_column site col path born wasBorn rootLive B live F bits
  have loaded := (complete_source_old_commands_are_acquired site saved headers gates roster inj b oldCode
    (fun u=>(Classical.choose_spec (ownerCorrespondence u)).1)).1
  have same :
      rows.map code=O.rows.map oldCode++((trueFreshPages site).map (freshWord site)) := by
    unfold rows VertexKeys.order
    rw [List.map_append,List.map_map,List.map_map]
    congr 1
    change (colsOfBirth (T:=T) (v:=v)).map (fun col=>freshWord site (physicalChildCols (T:=T) (v:=v) col))=_
    unfold colsOfBirth trueFreshPages
    rw [List.map_map]
    apply List.map_congr_left
    intro k _
    simp only [Function.comp_apply,Equiv.apply_symm_apply]
  have r := exact_raw_terminal_physical_order hf F T.vPositive B (actualEdgeOrder T v site.birth.native.physical)
    clock.result (clock_from_actual_frame_has_all_bits site saved) rows layout.1 layout.2 code values
  rw [same] at r
  have paid := measured_joined_terminal_exact site saved _ F B (O.rows.map oldCode) loaded
  refine ⟨_,?_,r⟩
  change (joinPaidTerminal site saved _ F B).result=_
  rw [paid]
end
#print axioms measured_joined_terminal_exact
#print axioms acquired_terminal_from_real_owner_rows
end J6R53TerminalGate
