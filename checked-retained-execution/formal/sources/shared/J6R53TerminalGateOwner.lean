import J6R53OldOwnerBorn
import J6R53TerminalGateCached
import J6R49SourceLayoutOwners

/-! A retained terminal reads one complete owner roster, not a list of
prepared leaf commands. The real group filter includes isolates. Each
retained opcode selects the paid Gate compiler or the paid Page
compiler; the measured edge book is bought once for all old rows. -/
namespace J6R53TerminalGate
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R34ChildPath J6R36ChildFramedRoute J6R49SourceLayout
open J6R53OldOwner J6R50Leaf J6R50SourceProducer J6R51ParentFrames J6R52Terminal
open J6R26DescriptorTree J6R33StatefulArithmeticPage
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6ActiveRun
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 26000000
set_option maxRecDepth 4200
set_option Elab.async false

def compileByOwnerData {own W w key prec page : ℕ} (b : ℕ)
    (book : List (Word W)) (frames : List (FramedEdge W own key prec page))
    (owner : Word own) (data : OwnerData w key prec page) : Meter (Option (ReadCmd key page)) :=
  let op := match data.gateCode with
    | some gate=>compileSavedGate b book frames owner gate
    | none=>compileKeptPage owner data.origin book frames
  ⟨op.result,op.steps+4⟩

def compileByRoster {own W w key prec page : ℕ} (b : ℕ)
    (book : List (Word W)) (frames : List (FramedEdge W own key prec page))
    (roster : RawRoster own w key prec page) (owner : Word own) : Meter (Option (ReadCmd key page)) :=
  let head := paidOwnerLookup roster owner
  match head.result with
  | none=>⟨none,head.steps+3⟩
  | some data=>
    let chosen := compileByOwnerData b book frames owner data
    ⟨chosen.result,head.steps+chosen.steps+4⟩

theorem compile_by_same_owner_roster {V : Type} {own W w key prec page : ℕ}
    {name : V→Word own} {value : V→OwnerData w key prec page}
    (roster : CompleteRoster name value) (inj : Function.Injective name) (v : V)
    (book : List (Word W)) (frames : List (FramedEdge W own key prec page)) (b : ℕ) :
    let chosen := compileByOwnerData b book frames (name v) (value v)
    compileByRoster b book frames roster.raw (name v)=
      ⟨chosen.result,(locate (name v) roster.raw).steps+ownerDataFee (value v)+chosen.steps+8⟩ := by
  unfold compileByRoster
  dsimp only
  rw [paid_owner_lookup_exact roster.raw (name v) (value v) (complete_owner_hit roster inj v)]
  dsimp only
  congr 1
  omega

def compileSelectedOwners {own W w key prec page : ℕ} (b : ℕ)
    (book : Meter (List (Word W))) (frames : List (FramedEdge W own key prec page))
    (roster : RawRoster own w key prec page) (headers : List (OwnerGroup own)) (group : Word 6) :
    Meter (Option (List (ReadCmd key page))) :=
  let chosen := selectOwnerKeys group headers
  let codes := gatherOptions 1 (compileByRoster b book.result frames roster) chosen.result
  ⟨codes.result,book.steps+chosen.steps+codes.steps+5⟩

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page w : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

theorem complete_source_old_commands_are_acquired
    (site : StoredSite T v key prec tw bw page) (saved : CachedParentFrames site.site)
    (headers : ParentOwnerHeaders site.site)
    (gates : v.parent.host.Row⊕v.parent.host.Col→Option (CodeGate (Word w)))
    (roster : CompleteRoster site.site.oldKey (parentData site gates))
    (inj : Function.Injective site.site.oldKey) (b : ℕ)
    (expected : v.child.host.Row→ReadCmd key page)
    (honest : ∀ u : v.child.host.Row,
      let z := (physicalChildRows (T:=T) (v:=v) u).val
      (compileByOwnerData b (cachedBook site saved).result saved.rows
        (site.site.oldKey z) (parentData site gates z)).result=some (expected u)) :
    let book := cachedBook site saved
    let O := (readOldVertices site.site headers).result
    let program := compileSelectedOwners b book saved.rows roster.raw headers.raw (word v.groupAt.val)
    program.result=some (O.rows.map expected) ∧
      program.steps=book.steps+(selectOwnerKeys (word v.groupAt.val) headers.raw).steps+
        (3+(O.rows.map (fun u=>
          let z := (physicalChildRows (T:=T) (v:=v) u).val
          (compileByRoster b book.result saved.rows roster.raw (site.site.oldKey z)).steps+7)).sum)+5 := by
  let book := cachedBook site saved
  let O := (readOldVertices site.site headers).result
  let choose := selectOwnerKeys (word v.groupAt.val) headers.raw
  let name (u : v.child.host.Row) := nativeRowKey site.site u
  let compile (u : v.child.host.Row) := compileByRoster b book.result saved.rows roster.raw (name u)
  have actual : choose.result=O.rows.map name :=
    (exact_old_vertices_from_grouped_headers site.site headers).1.symm.trans O.exact
  have succeed (u : v.child.host.Row) : (compile u).result=some (expected u) := by
    let z := (physicalChildRows (T:=T) (v:=v) u).val
    have load := compile_by_same_owner_roster roster inj z book.result saved.rows b
    change (compileByRoster b book.result saved.rows roster.raw (site.site.oldKey z)).result=_
    rw [load]
    exact honest u
  have listRewrite (xs : List v.child.host.Row) :
      gatherOptions 1 (compileByRoster b book.result saved.rows roster.raw) (xs.map name) =
        gatherOptions 1 compile xs := by
    induction xs with
    | nil => rfl
    | cons u us ih => simp only [gatherOptions,List.map_cons,compile,ih]
  have acquired := gather_options_exact 1 compile expected O.rows (fun x _=>succeed x)
  dsimp only [compileSelectedOwners]
  rw [show (selectOwnerKeys (word v.groupAt.val) headers.raw).result=O.rows.map name from actual,
    listRewrite,acquired]
  dsimp only
  exact ⟨rfl,rfl⟩

end
#print axioms compile_by_same_owner_roster
#print axioms complete_source_old_commands_are_acquired
end J6R53TerminalGate
