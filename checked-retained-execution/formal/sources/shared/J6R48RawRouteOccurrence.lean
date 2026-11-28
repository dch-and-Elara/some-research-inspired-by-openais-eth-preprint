import J6R34RootAtlasOccurrence
import J6R41StructuredAllPathsKeys

/-! The original descriptor compiler can be fed the newly written
physical file. Receiving precision, actual ticket, native modes,
page width, coordinate bytes, and immutable creator remain unchanged. -/
namespace J6R48RawRoute
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34RootAtlas J6R33StatefulArithmeticPage
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 2800
set_option maxHeartbeats 13000000
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {newWidth w ee dd tc tz tm : ℕ}
abbrev PhysicalFile (T : Prepared cfg sel r hf) (v : Ticket sel r) (w : ℕ) :=
  PhysicalPorts sel (ticketReady T v) v.centerAt w

def replaceJobPhysical (J : NativeJob T v w ee dd prec tc tz tm)
    (new : PhysicalFile T v newWidth) : NativeJob T v newWidth ee dd prec tc tz tm :=
  ⟨J.tWord,J.zWord,J.mWord,J.gWord,J.tExact,J.zExact,J.mExact,J.gExact,
    J.oldDepth,J.depthExact,J.depthPos,J.depthFit,J.receiving,J.receiveExact,
    J.edgePos,J.edgeFit,new⟩

theorem exact_job_site_replacement (J : NativeJob T v w ee dd prec tc tz tm)
    (new : PhysicalFile T v newWidth) :
    let K := replaceJobPhysical J new
    K.coordinates=J.coordinates ∧ K.gWord=J.gWord ∧ K.receiving=J.receiving ∧
      K.oldDepth=J.oldDepth ∧ K.physical.raw=new.raw :=
  ⟨rfl,rfl,rfl,rfl,rfl⟩

def replaceOccurrencePhysical (I : OccurrenceInput T v key prec tw bw page)
    (new : Meter (PhysicalFile T v newWidth)) :
    OccurrenceInput T v key prec tw bw page :=
  { I with
    port:=newWidth
    native:=⟨replaceJobPhysical I.native.result new.result,I.native.steps+new.steps+4⟩ }

theorem exact_occurrence_replacement (I : OccurrenceInput T v key prec tw bw page)
    (new : Meter (PhysicalFile T v newWidth)) :
    let K := replaceOccurrencePhysical I new
    K.native.result.physical=new.result ∧
    K.native.steps=I.native.steps+new.steps+4 ∧
    K.native.result.coordinates=I.native.result.coordinates ∧
    K.issued=I.issued ∧ K.physical=I.physical ∧ K.words=I.words :=
  ⟨rfl,rfl,rfl,rfl,rfl,rfl⟩

def birthPhysical (B : Birth T v key prec tw bw page) : Σ w,PhysicalFile T v w :=
  ⟨B.port,B.native.physical⟩

theorem page_cast_keeps_native_port_file {a b : ℕ} (e : a=b) (B : Birth T v key prec tw bw a) :
    birthPhysical (e ▸ B : Birth T v key prec tw bw b)=birthPhysical B := by
  subst b
  rfl

theorem compileOccurrence_native_file (I : OccurrenceInput T v key prec tw bw page) :
    birthPhysical (compileOccurrence I)=⟨I.port,I.native.result.physical⟩ := by
  unfold compileOccurrence
  exact page_cast_keeps_native_port_file I.width _

theorem generated_occurrence_has_no_old_physical_input
    (I : OccurrenceInput T v key prec tw bw page) (new : Meter (PhysicalFile T v newWidth)) :
    let out := compileOccurrence (replaceOccurrencePhysical I new)
    birthPhysical out=⟨newWidth,new.result⟩ ∧
      out.job.identifier=I.issued.result ∧
      out.job.immutable.payload.stamp.created.val=v.child.prec ∧
      out.issuance.steps=I.issued.steps+
        (I.native.steps+new.steps+4+I.physical.steps+I.words.steps+4) := by
  let rep := replaceOccurrencePhysical I new
  have id := occurrence_identity rep
  exact ⟨compileOccurrence_native_file rep,id.1,id.2.1,id.2.2⟩

theorem compiled_replaced_row_body
    (I : OccurrenceInput T v key prec tw bw page) (new : Meter (PhysicalFile T v newWidth))
    (x : Port v.parent.host.Edge) :
    ((compileOccurrence (replaceOccurrencePhysical I new)).native.physical.record x).body =
      (new.result.record x).body :=
  congrArg (fun u : Σ w,PhysicalFile T v w=>(u.2.record x).body)
    (compileOccurrence_native_file (replaceOccurrencePhysical I new))

#print axioms exact_job_site_replacement
#print axioms exact_occurrence_replacement
#print axioms page_cast_keeps_native_port_file
#print axioms compileOccurrence_native_file
#print axioms generated_occurrence_has_no_old_physical_input
#print axioms compiled_replaced_row_body
end
end J6R48RawRoute

