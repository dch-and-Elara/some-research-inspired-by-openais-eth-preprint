import J6R53OldOwnerTape
import J6R52CacheSourceReplay
import J6R50SourceProducerOnline

/-! The complete paid roster can feed the existing R49 owner selector.
The current chosen chart's actual group words are read as explicit
ordered input, not regenerated from a subset of incident edges. -/
namespace J6R53OldOwner
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6R49SourceLayout
open J6ActiveRun J6R50SourceProducer J6R52CacheSource
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3100
set_option maxHeartbeats 11000000
set_option maxSynthPendingDepth 12
set_option Elab.async false

def writeOwnerHeaders {own gate key prec page : ℕ} :
    RawRoster own gate key prec page→List (Word 6)→Meter (Option (List (OwnerGroup own)))
  | [],[]=>⟨some [],3⟩
  | x::xs,g::gs=>
    let id := copyFixed x.address
    let grp := copyFixed g
    let tail := writeOwnerHeaders xs gs
    ⟨tail.result.map (fun out=>⟨id.result,grp.result⟩::out),
      id.steps+grp.steps+tail.steps+5⟩
  | _,_=>⟨none,3⟩

theorem write_owner_headers_exact {A : Type} {own gate key prec page : ℕ}
    (name : A→Word own) (value : A→OwnerData gate key prec page) (grp : A→Word 6) (xs : List A) :
    writeOwnerHeaders (xs.map (fun a=>⟨name a,value a⟩)) (xs.map grp)=
      ⟨some (xs.map (fun a=>⟨name a,grp a⟩)),3+(3*own+25)*xs.length⟩ := by
  induction xs with
  | nil=>rfl
  | cons a as ih =>
    simp only [List.map_cons,writeOwnerHeaders,copy_fixed_exact,ih,Option.map_some,List.length_cons,
      Nat.mul_succ]
    congr 1
    omega

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page gate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
local notation "V" => (v.parent.host.Row⊕v.parent.host.Col)

theorem actual_group_header_tape (X : StoredSite T v key prec tw bw page)
    (value : V→OwnerData gate key prec page) (data : CompleteRoster X.site.oldKey value)
    (groups : List (Word 6)) (aligned : groups=data.order.map (fun x=>(ownerGroupRow X.site x).group)) :
    writeOwnerHeaders data.raw groups=⟨some (data.order.map (ownerGroupRow X.site)),
      3+(3*X.site.ownerWidth+25)*data.order.length⟩ := by
  rw [data.exactRows,aligned,write_owner_headers_exact]
  rfl

def useCompleteRoster (X : StoredSite T v key prec tw bw page)
    (value : V→OwnerData gate key prec page) (data : CompleteRoster X.site.oldKey value)
    (groups : List (Word 6)) (aligned : groups=data.order.map (fun x=>(ownerGroupRow X.site x).group)) :
    Meter (ParentOwnerHeaders X.site) :=
  let raw := writeOwnerHeaders data.raw groups
  have complete := actual_group_header_tape X value data groups aligned
  let ok := unwrapSuccess raw (by
    change (writeOwnerHeaders data.raw groups).result.isSome
    rw [complete]
    rfl)
  ⟨⟨data.order,data.unique,data.complete,ok.result,
    congrArg Meter.result (unwrap_success_exact _ _ _ (congrArg Meter.result complete))⟩,ok.steps⟩

theorem old_selection_from_actual_owner_table (X : StoredSite T v key prec tw bw page)
    (value : V→OwnerData gate key prec page) (data : CompleteRoster X.site.oldKey value)
    (groups : List (Word 6)) (aligned : groups=data.order.map (fun x=>(ownerGroupRow X.site x).group)) :
    let parent := useCompleteRoster X value data groups aligned
    let retained := readOldVertices X.site parent.result
    (∀ x,x∈retained.result.rows) ∧
      parent.steps+retained.steps=
        (3+(3*X.site.ownerWidth+25)*data.order.length)+
          (7+(3*X.site.ownerWidth+77)*data.order.length+(3*X.site.ownerWidth+1)*retained.result.rows.length) := by
  let parent := useCompleteRoster X value data groups aligned
  let R := readOldVertices X.site parent.result
  refine ⟨R.result.all,?_⟩
  have head : parent.steps=3+(3*X.site.ownerWidth+25)*data.order.length :=
    congrArg Meter.steps (actual_group_header_tape X value data groups aligned)
  have bin := (exact_old_vertices_from_grouped_headers X.site parent.result).2
  have rows : parent.result.raw.length=data.order.length := by rw [parent.result.same]; exact List.length_map ..
  change parent.steps+R.steps=_
  rw [head,bin,rows]

#print axioms write_owner_headers_exact
#print axioms actual_group_header_tape
#print axioms useCompleteRoster
#print axioms old_selection_from_actual_owner_table
end
end J6R53OldOwner
