import J6R48RawRouteAdjacent

/-! Genuinely omit the external old raw file. Only the non-routing
words and the independently measured resident geometry are inputs to
this constructor; its physical half-ports come from the prior writer. -/
namespace J6R48RawRoute
open scoped Polynomial Classical
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R34RootAtlas J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6R32ChildResidentTransfer J6R33GeneratedChildSite J6R16ModeCost
open J6ActiveRun P11FullPacking J6R9PacketScopes
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3100
set_option maxHeartbeats 8500000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {ticket : Ticket sel r}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)

structure NativeWordsOnly (T : Prepared cfg sel r hf) (ticket : Ticket sel r)
    (edge dep prec tc tz tm : ℕ) where
  tWord : Word tc
  zWord : Word tz
  mWord : Word tm
  gWord : Word 6
  tExact : tWord.val=centerOrdinal T ticket
  zExact : zWord.val=ticket.probeAt.val
  mExact : mWord.val=modeOrdinal T ticket
  gExact : gWord.val=ticket.groupAt.val
  oldDepth : Word dep
  depthExact : oldDepth.val=ticket.parent.depth
  depthPos : 0<dep
  depthFit : ticket.parent.depth+1<2^dep
  receiving : Word prec
  receiveExact : receiving.val=ticket.child.prec
  edgePos : 0<edge
  edgeFit : ticket.child.edges<2^edge

def NativeWordsOnly.bind {edge dep tc tz tm w : ℕ}
    (U : NativeWordsOnly T ticket edge dep prec tc tz tm) (P : PhysicalFile T ticket w) :
    NativeJob T ticket w edge dep prec tc tz tm :=
  ⟨U.tWord,U.zWord,U.mWord,U.gWord,U.tExact,U.zExact,U.mExact,U.gExact,
    U.oldDepth,U.depthExact,U.depthPos,U.depthFit,U.receiving,U.receiveExact,
    U.edgePos,U.edgeFit,P⟩

structure OccurrenceWordsOnly (T : Prepared cfg sel r hf) (ticket : Ticket sel r)
    (key prec tw bw page : ℕ) where
  edge : ℕ
  dep : ℕ
  tc : ℕ
  tz : ℕ
  tm : ℕ
  q : ℕ
  code : ℕ
  native : Meter (NativeWordsOnly T ticket edge dep prec tc tz tm)
  issued : Meter (Word key)
  fw : List (A1R10.Word (registerPrecision SP ticket.parent ticket.centerAt))
  hOld : 0<fw.length
  hMod : A1R10.Modulus (registerPrecision SP ticket.parent ticket.centerAt)
    (register_positive (ticketReady T ticket) ticket.centerAt) fw=
      NativeProbeRing.liftPoly (registerPrecision SP ticket.parent ticket.centerAt) f
  physical : Meter (ChildResidents ((SP).levelBits ticket.parent.depth) q)
  geometry : ResidentReceipt (packing sel (ticketReady T ticket))
    (centerIndex (ticketReady T ticket) ticket.centerAt)
    (registerPrecision SP ticket.parent ticket.centerAt) physical.result
  words : Meter (ActiveWords fw (q+1) tw bw)
  group : words.result.group=native.result.gWord
  clock : words.result.axis.length=(centerIndex (ticketReady T ticket) ticket.centerAt).val
  centre : words.result.context.center=ticket.centerAt.val
  codeExact : words.result.context.codeWidth.val=code
  codePos : 0<code
  codeFit : 1+geometry.modes.length<2^code
  acted : words.result.exponents.map Word.val=geometry.modes.map
    (fun m=>siteTuple sel (ticketReady T ticket) ticket.slot.val
      ((packet_mode_equiv (packing sel (ticketReady T ticket)).mask
        (centerIndex (ticketReady T ticket) ticket.centerAt)
        (registerPrecision SP ticket.parent ticket.centerAt)).symm m))
  outerPos : 0<ell
  fit : (centerIndex (ticketReady T ticket) ticket.centerAt).val+1≤q+1
  probe : words.result.coordinates.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree
    (realProbeCount (S:=SP) (c:=ticket.parent)) (ticketReady T ticket).fit ticket.probeAt)
  width : (q-(SP).levelBits ticket.parent.depth)+13*(SP).levelBits ticket.parent.depth=page

def OccurrenceWordsOnly.bind {w : ℕ} (U : OccurrenceWordsOnly T ticket key prec tw bw page)
    (P : Meter (PhysicalFile T ticket w)) : OccurrenceInput T ticket key prec tw bw page where
  port := w
  edge := U.edge
  dep := U.dep
  tc := U.tc
  tz := U.tz
  tm := U.tm
  q := U.q
  code := U.code
  native := ⟨U.native.result.bind P.result,U.native.steps+P.steps+4⟩
  issued := U.issued
  fw := U.fw
  hOld := U.hOld
  hMod := U.hMod
  physical := U.physical
  geometry := U.geometry
  words := U.words
  group := U.group
  clock := U.clock
  centre := U.centre
  codeExact := U.codeExact
  codePos := U.codePos
  codeFit := U.codeFit
  acted := U.acted
  outerPos := U.outerPos
  fit := U.fit
  probe := U.probe
  width := U.width

theorem generated_without_any_old_raw_file {w : ℕ}
    (U : OccurrenceWordsOnly T ticket key prec tw bw page)
    (P : Meter (PhysicalFile T ticket w)) :
    let born := compileOccurrence (U.bind P)
    birthPhysical born=⟨w,P.result⟩ ∧ born.job.identifier=U.issued.result ∧
      born.job.immutable.payload.stamp.created.val=ticket.child.prec ∧
      born.issuance.steps=U.issued.steps+
        (U.native.steps+P.steps+4+U.physical.steps+U.words.steps+4) :=
  let e := occurrence_identity (U.bind P)
  ⟨compileOccurrence_native_file (U.bind P),e.1,e.2.1,e.2.2⟩

variable {v : Ticket sel r} {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}

theorem next_source_words_realize_adjacent_route {k : ℕ} {S : SiteInputs Q previous}
    {u : (Plan sel).Slot v.child} (D : LiteralAdjacent S u k)
    (U : OccurrenceWordsOnly T (successorTicket v u) key prec tw bw page)
    (x : Port v.child.host.Edge) :
    ((compileOccurrence (U.bind D.generated)).native.physical.record x).body=
      (S.issuedLane (childHalves T v (edge x)) (side x)).body := by
  exact congrArg (fun a : Σ w,PhysicalFile T (successorTicket v u) w=>(a.2.record x).body)
    (generated_without_any_old_raw_file U D.generated).1

theorem actual_path_body_from_source_words
    {born : Births T key prec tw bw page} {keys : PageKeys born}
    {rootTags : r.host.Row⊕r.host.Col→Origin key prec page}
    (files : SiteFiles born keys rootTags) (rootPorts : Port r.host.Edge→Payload key prec page)
    {c : Call (PhysicalHost f ell)} (p : J6R32StatefulArithmetic.Path sel r c)
    (w : (Plan sel).Slot c) (u : (Plan sel).Slot (p.ticket w).child) {k : ℕ}
    (D : LiteralAdjacent (files p w) u k)
    (U : OccurrenceWordsOnly T (successorTicket (p.ticket w) u) key prec tw bw page)
    (x : Port (p.ticket w).child.host.Edge) :
    ((compileOccurrence (U.bind D.generated)).native.physical.record x).body=
      (publishedPayload files rootPorts (.step p w) x).2 :=
  next_source_words_realize_adjacent_route D U x

#print axioms actual_path_body_from_source_words
#print axioms generated_without_any_old_raw_file
#print axioms next_source_words_realize_adjacent_route
end
end J6R48RawRoute

