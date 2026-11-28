import J6R50SourceProducerPublish
import J6R48DFSScope

/-! Load the actual source occurrence immediately before its one scoped
publication. Pass the same stored descendant to the child evaluator
and restore the caller's live registry on return. -/
namespace J6R50SourceProducer
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath
open J6R33StatefulArithmeticPage J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion J6ActiveRun J6R30ProducedGateRegistry J6R48RawRoute
open J6R32StatefulArithmetic J6R48DFS
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3100
set_option maxHeartbeats 9000000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (X : StoredSite T v key prec tw bw page)
variable {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q}
variable {H : Replayed X.site w q U}
variable (W : NativeEventOnly H) (D : LocalDirectory X W)
variable {Result : Type}

def visitWithActualLoad
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (child : StoredSite T (successorTicket v w) key prec tw bw page →
      J6R32StatefulArithmetic.SM (PageBank f ell key prec tw bw page) Result)
    (fallback : Meter Result)
    (registry : PageBank f ell key prec tw bw page) : Meter (Result × PageBank f ell key prec tw bw page) :=
  let generated := prepareOnlineAdvance X W D
  @J6R48DFS.withScope key prec tw bw (PagedEnvelope f ell prec page) Result retire
    generated.next.birth.job (child generated.next) fallback registry

theorem paid_actual_visit_is_one_scope_transaction
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (child : StoredSite T (successorTicket v w) key prec tw bw page →
      J6R32StatefulArithmetic.SM (PageBank f ell key prec tw bw page) Result)
    (fallback : Meter Result)
    (registry : PageBank f ell key prec tw bw page) (sync : registry.synced)
    (fresh : ∀ e∈registry.headers,e.id≠W.issued.result) :
    let made := prepareOnlineAdvance X W D
    let B := made.next.birth
    let pushed := B.job.install registry
    let returned := child made.next pushed.result.1
    visitWithActualLoad X W D retire child fallback registry=
      ⟨(returned.result.1,registry),
        publishFee registry B.job.entry B.job.offset
          ⟨some ⟨B.shape,B.rows⟩,B.compilePages.steps+shapeFrameFee prec⟩+
          returned.steps+retire B.job+4⟩ := by
  let made := prepareOnlineAdvance X W D
  let B := made.next.birth
  have live := actual_visit_loads_and_publishes_same_native_packet X W D registry sync fresh
  have pass : (B.job.install registry).result.2=true := live.1
  have bill : (B.job.install registry).steps=publishFee registry B.job.entry B.job.offset
      ⟨some ⟨B.shape,B.rows⟩,B.compilePages.steps+shapeFrameFee prec⟩ := live.2.2.2.2.2.2.2
  unfold visitWithActualLoad withScope
  dsimp only
  rw [pass,if_pos (Eq.refl true),bill]

theorem paid_actual_visit_restores_parent
    (retire : PageJob f ell key prec tw bw page→ℕ)
    (child : StoredSite T (successorTicket v w) key prec tw bw page →
      J6R32StatefulArithmetic.SM (PageBank f ell key prec tw bw page) Result)
    (fallback : Meter Result)
    (registry : PageBank f ell key prec tw bw page) :
    (visitWithActualLoad X W D retire child fallback registry).result.2=registry :=
  scope_always_restores retire _ _ fallback registry

#print axioms paid_actual_visit_is_one_scope_transaction
#print axioms paid_actual_visit_restores_parent
end
end J6R50SourceProducer