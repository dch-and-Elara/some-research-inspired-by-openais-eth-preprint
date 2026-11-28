
import J6R51PeakInstallTrace
import J6R50SourceProducerScope

/-! Put the concrete checked-header trace on the same job built
by the original local producer and passed to the scoped child.
Page build and entry creation appear once in the existing publish
bill.  The trace does not generate a replacement child. -/
namespace J6R51Peak
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree J6R34ChildPath
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R50SourceProducer

open J6R48RawRoute

set_option autoImplicit false
set_option maxHeartbeats 14000000
set_option maxRecDepth 3400

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable (X : StoredSite T v key prec tw bw page)
variable {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q}
variable {H : Replayed X.site w q U}
variable (W : NativeEventOnly H) (D : LocalDirectory X W)
local notation "L" => PageBank f ell key prec tw bw page
local notation "J" => PageJob f ell key prec tw bw page

theorem paid_visit_has_same_physical_header_and_mount {A : Type}
    (retire : J→ℕ)
    (child : StoredSite T (successorTicket v w) key prec tw bw page→SM L A)
    (fallback : Meter A) (registry : L) (sync : registry.synced)
    (fresh : ∀ e∈registry.headers,e.id≠W.issued.result) :
    let made := prepareOnlineAdvance X W D
    let B := made.next.birth
    let j := B.job
    let o := observeCheckedInstall j.entry registry.headers
    let out := child made.next (afterOne registry j)
    o.before=registry.headers.map (headerReadEvent j.identifier) ∧
    o.written=some j.entry.result.bytes ∧
    o.after=[headerReadEvent j.identifier j.entry.result] ∧
    o.run=⟨(j.entry.result::registry.headers,some j.entry.result.bytes),
      installFee j.entry registry.headers⟩ ∧
    (loadAt prec j.offset j.entry.result.bytes).result=some j.birth ∧
    directoryBits (j.install registry).result.1=directoryBits registry+insertionBits j ∧
    visitWithActualLoad X W D retire child fallback registry=
      ⟨(out.result.1,registry),publishFee registry j.entry j.offset
        ⟨some ⟨B.shape,B.rows⟩,B.compilePages.steps+shapeFrameFee prec⟩+
        out.steps+retire j+4⟩ := by
  let made := prepareOnlineAdvance X W D
  let B := made.next.birth
  let j := B.job
  have label : j.identifier=W.issued.result := (J6R34RootAtlas.occurrence_identity (localEventInput W)).1
  have newId : ∀ e∈registry.headers,e.id≠j.identifier := by
    rw [label]
    exact fresh
  have scan := actual_fresh_install_has_exact_trace j.entry registry.headers newId
  have op := paid_job_mounts_the_same_selected_directory registry j sync newId
  have valid := congrArg Meter.result j.validTag
  have fee := paid_actual_visit_is_one_scope_transaction X W D retire child fallback registry sync fresh
  change visitWithActualLoad X W D retire child fallback registry =
    ⟨((child made.next (j.install registry).result.1).result.1,registry),
      publishFee registry j.entry j.offset
        ⟨some ⟨B.shape,B.rows⟩,B.compilePages.steps+shapeFrameFee prec⟩+
        (child made.next (j.install registry).result.1).steps+retire j+4⟩ at fee
  rw [op.1] at fee
  exact ⟨scan.2.1,scan.2.2.1,scan.2.2.2,scan.1,valid,op.2,fee⟩

def chosenParseFields {key prec tw bw : ℕ} {A : Type}
    (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) A) : List Bool :=
  headerFields j.entry.result ++ headerFields j.entry.result ++ j.entry.result.bytes ++
    ((loadAt prec j.offset j.entry.result.bytes).result.toList.flatMap Word.bits)

theorem readback_precision_fields_exact {key prec tw bw : ℕ} {A : Type}
    (j : Job (key:=key) (prec:=prec) (tw:=tw) (bw:=bw) A) :
    (chosenParseFields j).length=2*key+3*j.entry.result.bytes.length+prec ∧
      (loadAt prec j.offset j.entry.result.bytes).steps=headerReadFee prec j.offset := by
  have actual := j.validTag
  constructor
  · rw [chosenParseFields,actual]
    simp only [Option.toList_some,List.flatMap_cons,List.flatMap_nil,List.append_nil,
      List.length_append,exact_header_encoding,j.birth.size]
    omega
  · exact congrArg Meter.steps actual

#print axioms paid_visit_has_same_physical_header_and_mount
#print axioms readback_precision_fields_exact
end J6R51Peak
