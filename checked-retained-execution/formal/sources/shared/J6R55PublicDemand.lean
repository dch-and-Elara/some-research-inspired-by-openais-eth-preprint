import J6R55PublicReady
import J6R55DispatchIssuer

/-! An actual demand provider may use the already verified fixed-chart
picker. It supplies a measured request recipe and evidence of a hit;
it does not supply the returned carrier, a child issuer, or a Ready
certificate. The picker result and its measured fee are used once. -/
namespace J6R55Public
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6ActiveRun J6R10Reachable J6R11Blueprint
open J6R12Blueprint J1PPrinted J6R24MeteredRecursion J6R26DescriptorTree
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer
open J6R51Online J6R52Dispatch J6R53Dispatch J6R54Dispatch J6R55Dispatch
set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 17000000
set_option maxRecDepth 3550
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page rate : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}

structure FixedRequest {v : Ticket sel root} (X : StoredSite T v key prec tw bw page)
    (u : (Plan sel).Slot v.child) where
  q : ℕ
  emitted : ExplicitSelectedWords X.site u q
  replay : Replayed X.site u q emitted
  raw : List (Word (q+1))
  group : Fin 64
  find : FixedPicker replay
  hit : (find raw group).result.isSome
  shell : PayloadShell replay
  directory : DirectorySeed replay shell

variable {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
variable {u : (Plan sel).Slot v.child}
variable (input : Meter (FixedRequest X u))

def meteredSelectedDemand : Meter (LocalLoad X u) :=
  let Q := input.result
  let pick := Q.find Q.raw Q.group
  let actual := pick.result.get Q.hit
  let shell := usingParentIssuer Q.replay Q.shell
  let dir := usingParentIssuerDirectory Q.replay Q.shell Q.directory
  let loaded := forDemand pick.steps (actual.val.load shell dir)
  ⟨loaded.result,input.steps+loaded.steps+3⟩

theorem same_measured_lookup_drives_the_actual_demand :
    let Q := input.result
    let measured := Q.find Q.raw Q.group
    let old := mountedIncrementDemand Q.replay Q.find (measured.result.get Q.hit) Q.shell Q.directory
    (meteredSelectedDemand input).result=old.result ∧
      (meteredSelectedDemand input).steps=input.steps+old.steps+3 :=
  ⟨rfl,rfl⟩

theorem selected_demand_uses_real_increment :
    (meteredSelectedDemand input).result.event.issued=increment X.birth.job.identifier := rfl

theorem counted_selected_demand_exact :
    let Q := input.result
    let A := Q.find Q.raw Q.group
    let K := meteredSelectedDemand input
    paidAcquisition K=input.steps+A.steps+(A.result.get Q.hit).val.dispatch.steps+6+4+3+K.result.sidecarCharge := by
  let Q := input.result
  let B := Q.find Q.raw Q.group
  let old := mountedIncrementDemand Q.replay Q.find (B.result.get Q.hit) Q.shell Q.directory
  have same := same_measured_lookup_drives_the_actual_demand input
  have bill := (dispatcher_actually_increments_issuer Q.replay Q.find (B.result.get Q.hit)
    Q.shell Q.directory).2.2
  change old.steps+old.result.sidecarCharge=
    B.steps+(B.result.get Q.hit).val.dispatch.steps+6+4+old.result.sidecarCharge at bill
  change (meteredSelectedDemand input).steps+(meteredSelectedDemand input).result.sidecarCharge=
    input.steps+B.steps+(B.result.get Q.hit).val.dispatch.steps+6+4+3+
      (meteredSelectedDemand input).result.sidecarCharge
  rw [same.1,same.2]
  change input.steps+old.steps+3+old.result.sidecarCharge=
    input.steps+B.steps+(B.result.get Q.hit).val.dispatch.steps+6+4+3+old.result.sidecarCharge
  omega

variable (M : OnlineMachine T key prec tw bw page rate)
variable (req : ∀ {v : Ticket sel root} (X : StoredSite T v key prec tw bw page)
  (u : (Plan sel).Slot v.child),Meter (FixedRequest X u))

def withSelectedDemands : OnlineMachine T key prec tw bw page rate :=
  {M with demand := fun X u=>meteredSelectedDemand (req X u)}

theorem first_issuer_unchanged_by_real_demand (keyMeter : Meter (Word key))
    (h : UsesFirstIssuer M keyMeter) :
    UsesFirstIssuer (withSelectedDemands M req) keyMeter := h

theorem actual_machine_first_to_child_issuer :
    UsesChildIncrement (withSelectedDemands M req) := by
  intro c p u w
  exact selected_demand_uses_real_increment (req (sourceState (withSelectedDemands M req) p u) w)

#print axioms meteredSelectedDemand
#print axioms same_measured_lookup_drives_the_actual_demand
#print axioms selected_demand_uses_real_increment
#print axioms counted_selected_demand_exact
#print axioms withSelectedDemands
#print axioms first_issuer_unchanged_by_real_demand
#print axioms actual_machine_first_to_child_issuer
end
end J6R55Public

