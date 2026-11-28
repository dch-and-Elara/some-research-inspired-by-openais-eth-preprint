import J6R26DescriptorTreeOccurrence
import J6R26DescriptorTreeSchedule
import J6R25PreparedSupplyNativeChild
import Mathlib.Data.List.NodupEquivFin

/-! The job constructor records the *four* native address fields
and the true child header. Numeric keys are separate issuance IDs.
The raw prepared group/centre/probe/mode words are constrained by
the same finite lists that the paid arithmetic actually visits. -/
namespace J6R26DescriptorTree
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R25PreparedSupply
open J6ActiveRun J6ActiveSchedule J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R24MeteredRecursion

variable {f : ℤ[X]} {ell s C : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
variable (T : Prepared cfg sel r hf)
variable (v : Ticket sel r)

abbrev ticketReady := ready_reachable cfg sel v.path T.rootStable v.slot.property
abbrev ticketActive := T.active v.parent v.path v.slot.property
abbrev Ticket.centerAt := v.slot.val.1
abbrev Ticket.probeAt := v.slot.val.2.1
abbrev Ticket.modeAt := v.slot.val.2.2.1
abbrev Ticket.groupAt := v.slot.val.2.2.2

noncomputable def centerOrdinal : ℕ :=
  let G := ticketActive T v
  ((List.Nodup.getEquivOfForallMemList G.centres G.centreUnique G.centreComplete).symm v.centerAt).val

noncomputable def modeOrdinal : ℕ := by
  classical
  let G := (ticketActive T v).tape v.centerAt
  exact ((List.Nodup.getEquivOfForallMemList G.modes G.modeUnique G.modeComplete).symm v.modeAt).val

structure NativeJob (port edge dep prec tc tz tm : ℕ) where
  tWord : Word tc
  zWord : Word tz
  mWord : Word tm
  gWord : Word 6
  tExact : tWord.val=centerOrdinal T v
  zExact : zWord.val=v.probeAt.val
  mExact : mWord.val=modeOrdinal T v
  gExact : gWord.val=v.groupAt.val
  oldDepth : Word dep
  depthExact : oldDepth.val=v.parent.depth
  depthPos : 0<dep
  depthFit : v.parent.depth+1<2^dep
  receiving : Word prec
  receiveExact : receiving.val=v.child.prec
  edgePos : 0<edge
  edgeFit : v.child.edges<2^edge
  physical : PhysicalPorts sel (ticketReady T v) v.centerAt port

variable {T v} {port edge dep prec tc tz tm : ℕ}
variable (D : NativeJob T v port edge dep prec tc tz tm)

def NativeJob.coordinates : List Bool :=
  (joinKey D.tWord (joinKey D.zWord (joinKey D.mWord D.gWord))).bits

def NativeJob.job : Job port edge dep prec :=
  ⟨D.coordinates,D.gWord,D.receiving,D.oldDepth,D.physical.raw⟩

set_option maxHeartbeats 3700000 in
theorem NativeJob.literal_bytes {key : ℕ} (issued : Meter (Word key)) :
    let wires := ((D.physical.physicalSelected v.groupAt).map D.physical.record).flatMap rowBytes
    (D.job.make issued).result.id=issued.result ∧
    (D.job.make issued).result.bytes=D.coordinates++
      childHeaderBytes (word (q:=prec) v.child.prec) (word (q:=dep) v.child.depth)
        (word (q:=edge) v.child.edges) wires := by
  let K := childStage (b:=edge) issued D.gWord D.receiving D.oldDepth D.physical.raw
  let literal := childStage (b:=edge) issued (word v.groupAt.val) D.receiving D.oldDepth D.physical.raw
  have hg : D.gWord=word v.groupAt.val :=
    (valued_word D.gWord).symm.trans (congrArg word D.gExact)
  have hk : K=literal := by dsimp only [K,literal]; rw [hg]
  obtain ⟨_,hBytes,_⟩ := acquired_native_child sel (ticketReady T v) v.centerAt
    D.physical v.probeAt v.modeAt v.groupAt issued [] D.receiving D.oldDepth
    D.receiveExact D.depthExact D.depthPos D.depthFit D.edgePos D.edgeFit
    (by intro x h; cases h)
  have exactB : literal.result.bytes=childHeaderBytes (word (q:=prec) v.child.prec)
      (word (q:=dep) v.child.depth) (word (q:=edge) v.child.edges)
      (((D.physical.physicalSelected v.groupAt).map D.physical.record).flatMap rowBytes) := by
    have e := acquired_literal_child literal [] (by intro x h; cases h)
    have q := congrArg Prod.snd (e.1.symm.trans hBytes)
    exact Option.some.inj q
  refine ⟨D.job.make_id issued,?_⟩
  rw [D.job.make_bytes]
  change D.coordinates++K.result.bytes=_
  rw [hk,exactB]

theorem NativeJob.address_field_width : D.coordinates.length=tc+(tz+(tm+6)) :=
  (joinKey D.tWord (joinKey D.zWord (joinKey D.mWord D.gWord))).size

#print axioms NativeJob.literal_bytes
#print axioms NativeJob.address_field_width
end J6R26DescriptorTree


