import J6R51OnlineCore

/-! The frozen OnlineMachine type alone does not determine boot origin
tags. This proof-only countermodel keeps the identical measured
occurrence and physical body, and reconstructs only the sidecar
alignment at an arbitrary tag function. It is not an executable
ingress and makes no fee claim. -/
namespace J6R55TerminalOrigin
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6R26DescriptorTree J6R34ChildPath J6R33StatefulArithmeticPage J6R36ChildFramedRoute
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6ActiveRun J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R41StructuredAllPaths J6R32StatefulArithmetic
open J6R50SourceProducer J6R34RootAtlas J6R51Online
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17000000
set_option maxRecDepth 4100
set_option quotPrecheck false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}

def specSidecarWithArbitraryTags
    (A : StoredSite T v key prec tw bw page)
    (t : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page) :
    StoredSite T v key prec tw bw page :=
  let S : SiteInputs A.birth t :=
    ⟨A.site.ownerWidth,A.site.oldKey,A.site.pageKey,
      A.birth.native.physical.order.map (addonAt T v A.site.oldKey t A.site.pageKey),rfl⟩
  ⟨A.input,t,S,A.canonical⟩

def specMachineWithArbitraryTags
    (M : OnlineMachine T key prec tw bw page rate)
    (t : r.host.Row⊕r.host.Col→Origin key prec page) :
    OnlineMachine T key prec tw bw page rate :=
  {M with initial := fun w=>let A:=M.initial w; ⟨specSidecarWithArbitraryTags A.result t,A.steps⟩}

def oppositePresence {key prec page : ℕ} (o : Origin key prec page) : Origin key prec page :=
  ⟨o.stamp,if o.pageKey.isSome then none else some (word 0)⟩

theorem opposite_presence_is_different {key prec page : ℕ} (o : Origin key prec page) :
    oppositePresence o≠o := by
  obtain ⟨s,a⟩ := o
  cases a with
  | none =>
    intro same
    have h : some (word (q:=page) 0)=(none : Option (Word page)) := congrArg Origin.pageKey same
    cases h
  | some p =>
    intro same
    have h : (none : Option (Word page))=some p := congrArg Origin.pageKey same
    cases h

theorem unrestricted_initial_has_no_origin_law
    (M : OnlineMachine T key prec tw bw page rate)
    (wanted : r.host.Row⊕r.host.Col→Origin key prec page)
    (u : r.host.Row⊕r.host.Col) :
    ∃ N : OnlineMachine T key prec tw bw page rate, ∀ w : (Plan sel).Slot r,
      (N.initial w).result.input=(M.initial w).result.input ∧
      (∀ h,((N.initial w).result.birth.native.physical.record h).body=
        ((M.initial w).result.birth.native.physical.record h).body) ∧
      (N.initial w).result.origins u≠wanted u := by
  refine ⟨specMachineWithArbitraryTags M (fun x=>oppositePresence (wanted x)),?_⟩
  intro w
  exact ⟨rfl,fun _=>rfl,opposite_presence_is_different (wanted u)⟩

end
#print axioms specSidecarWithArbitraryTags
#print axioms unrestricted_initial_has_no_origin_law
end J6R55TerminalOrigin
