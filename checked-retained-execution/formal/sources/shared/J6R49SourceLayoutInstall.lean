import J6R49SourceLayoutBind

/-! Bind the generated resident and generated physical row tapes to
the real occurrence compiler. The input carries only the original
non-layout words. In particular, there is no second resident table,
next-seat table, or previously installed physical file in it. -/
namespace J6R49SourceLayout
open scoped Classical Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor
open J6R25PreparedSupply J6R26DescriptorTree J6R34ChildPath J6R41StructuredAllPaths
open J6R33StatefulArithmeticPage J6R36ChildFramedRoute J6R27OriginalGate
open J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted J6R24MeteredRecursion
open J6ActiveRun P11FullPacking J6R9PacketScopes J6R11Repack
open J6R32ChildResidentTransfer J6R48RawRoute J6R33GeneratedChildSite
open J6R34RootAtlas J6R16ModeCost
set_option autoImplicit false
set_option warningAsError true
set_option maxRecDepth 3250
set_option maxHeartbeats 11300000
set_option maxSynthPendingDepth 12
set_option linter.unusedSectionVars false
set_option Elab.async false
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf} {v : Ticket sel r}
variable {Q : Birth T v key prec tw bw page}
variable {previous : v.parent.host.Row⊕v.parent.host.Col→Origin key prec page}
variable {S : SiteInputs Q previous}
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => (J6ActiveRun.Shape.levelBits (printedParams (f:=f) (ell:=ell) s) v.child.depth)
variable {q : ℕ} {u : (Plan sel).Slot v.child}
local notation "next" => (successorTicket v u)
local notation "d" => (ticketReady T (successorTicket v u))
local notation "t" => (Ticket.centerAt (successorTicket v u))
local notation "p" => (registerPrecision SP v.child t)
local notation "i" => (centerIndex d t)

def receiveResidents {a q : ℕ} (out : Meter (Option (PreparedSeats a q))) :
    Meter (Option (ChildResidents a q)) :=
  ⟨out.result.map PreparedSeats.native,out.steps+3⟩

theorem received_residents_are_the_compiler_input
    {out : Meter (Option (PreparedSeats ((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth) q))}
    (X : GeneratedChild (q:=q) S d t out) :
    receiveResidents out = ⟨some X.data.native,out.steps+3⟩ := by
  unfold receiveResidents
  rw [X.success]
  rfl

structure PreparedOccurrenceWords
    {out : Meter (Option (PreparedSeats ((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth) q))}
    (X : GeneratedChild (q:=q) S d t out) (chosen : X.chart=packing sel d) where
  edge : ℕ
  dep : ℕ
  tc : ℕ
  tz : ℕ
  tm : ℕ
  code : ℕ
  native : Meter (NativeWordsOnly T next edge dep prec tc tz tm)
  issued : Meter (Word key)
  fw : List (A1R10.Word p)
  hOld : 0<fw.length
  hMod : A1R10.Modulus p (register_positive d t) fw=NativeProbeRing.liftPoly p f
  words : Meter (ActiveWords fw (q+1) tw bw)
  group : words.result.group=native.result.gWord
  clock : words.result.axis.length=(i).val
  centre : words.result.context.center=(t).val
  codeExact : words.result.context.codeWidth.val=code
  codePos : 0<code
  codeFit : 1+(installed_chart_for_selector (q:=q) (u:=u) X chosen).modes.length<2^code
  acted : words.result.exponents.map Word.val=(installed_chart_for_selector (q:=q) (u:=u) X chosen).modes.map
    (fun m=>siteTuple sel d (next).slot.val ((packet_mode_equiv (packing sel d).mask i p).symm m))
  outerPos : 0<ell
  fit : (i).val+1≤q+1
  probe : words.result.coordinates.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree
    (realProbeCount (S:=SP) (c:=v.child)) (d).fit (next).probeAt)
  width : (q-A)+13*A=page

def bindPreparedWords
    {out : Meter (Option (PreparedSeats ((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth) q))}
    {X : GeneratedChild (q:=q) S d t out} {chosen : X.chart=packing sel d}
    (U : PreparedOccurrenceWords (q:=q) (u:=u) X chosen) :
    OccurrenceWordsOnly T next key prec tw bw page where
  edge := U.edge
  dep := U.dep
  tc := U.tc
  tz := U.tz
  tm := U.tm
  q := q
  code := U.code
  native := U.native
  issued := U.issued
  fw := U.fw
  hOld := U.hOld
  hMod := U.hMod
  physical := ⟨X.data.native,(receiveResidents out).steps⟩
  geometry := installed_chart_for_selector (q:=q) (u:=u) X chosen
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

theorem actual_successor_from_generated_resident_and_ports
    {out : Meter (Option (PreparedSeats ((printedParams (f:=f) (ell:=ell) s).levelBits v.child.depth) q))}
    (X : GeneratedChild (q:=q) S d t out) (chosen : X.chart=packing sel d)
    (U : PreparedOccurrenceWords (q:=q) (u:=u) X chosen)
    (h : Port v.child.host.Edge) :
    let D := adjacentOfGenerated (q:=q) (u:=u) X chosen
    let W := bindPreparedWords (q:=q) (u:=u) U
    let new := compileOccurrence (W.bind D.generated)
    (receiveResidents out).result=some X.data.native ∧
      (emitFromPrepared out S.write.result.framed).result=some D.generated.result.raw ∧
      (new.native.physical.record h).body=(S.issuedLane (childHalves T v (edge h)) (side h)).body ∧
      new.job.identifier=U.issued.result ∧ new.job.immutable.payload.stamp.created.val=(next).child.prec ∧
      new.issuance.steps=U.issued.steps+(U.native.steps+D.generated.steps+4+out.steps+3+U.words.steps+4) := by
  let D := adjacentOfGenerated (q:=q) (u:=u) X chosen
  let W := bindPreparedWords (q:=q) (u:=u) U
  let B := generated_without_any_old_raw_file W D.generated
  refine ⟨congrArg Meter.result (received_residents_are_the_compiler_input (u:=u) X),
    (emitted_from_the_actual_prepared_port_tape (u:=u) X chosen).1,
    generated_layout_birth_copies_same_predecessor_body (u:=u) X chosen W h,
    B.2.1,B.2.2.1,?_⟩
  have e := B.2.2.2
  dsimp only [W,bindPreparedWords,receiveResidents] at e
  exact e

#print axioms received_residents_are_the_compiler_input
#print axioms actual_successor_from_generated_resident_and_ports
end
end J6R49SourceLayout