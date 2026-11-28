import J6R51OnlineCore

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option maxHeartbeats 15500000
set_option maxRecDepth 3300
set_option linter.unusedSectionVars false

/-! An incoming shell contains no complete child, old mode ordinal,
group or exponent vector. Those four fields are materialized at the
addressed event. A physical chart receipt and the independent directory
inputs are explicit; nothing selects a different chart. -/
namespace J6R52Dispatch
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R16ModeCost J6R27OriginalGate
open P11FullPacking J6R9PacketScopes J6R10Repack J6R12CollisionEdges
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R26DescriptorTree J6R24MeteredRecursion J6R33GeneratedChildSite
open J6R34ChildPath J6R41StructuredAllPaths J6R48GeneratedAddons J6R48RawRoute
open J6R30ProducedGateRegistry J6R32ChildResidentTransfer J6R33StatefulArithmeticPage
open J6R49SourceLayout J6R50SourceProducer J6R51Online
open J6R21Ancestor J6R36ChildFramedRoute J6R34RootAtlas
noncomputable section

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root}
variable {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child} {q : ℕ}
variable {U : ExplicitSelectedWords X.site w q}
variable (R : Replayed X.site w q U)
local notation "SP" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => ((SP).levelBits v.child.depth)
local notation "nx" => (successorTicket v w)
local notation "d" => (ticketReady T (successorTicket v w))
local notation "t" => (Ticket.centerAt (successorTicket v w))
local notation "P" => (registerPrecision SP v.child t)

def liveExponentSpec : List ℕ :=
  R.certificate.modes.map (fun m=>siteTuple sel d (nx).slot.val
    ((packet_mode_equiv (packing sel d).mask (centerIndex d t) P).symm m))

structure PayloadShell where
  dep : ℕ
  edge : ℕ
  code : ℕ
  issued : Meter (Word key)
  oldDepth : Word dep
  depthExact : oldDepth.val=v.child.depth
  depthPos : 0<dep
  depthFit : v.child.depth+1<2^dep
  receiving : Word prec
  receiveExact : receiving.val=(nx).child.prec
  edgePos : 0<edge
  edgeFit : (nx).child.edges<2^edge
  fw : List (A1R10.Word P)
  hOld : 0<fw.length
  hMod : A1R10.Modulus P (register_positive d t) fw=NativeProbeRing.liftPoly P f
  context : CentreContext tw bw
  axis : List Bool
  coordinates : {bs : List Bool // bs.length=fw.length}
  clock : axis.length=(centerIndex d t).val
  centre : context.center=(t).val
  codeExact : context.codeWidth.val=code
  codePos : 0<code
  codeFit : 1+R.certificate.modes.length<2^code
  outerPos : 0<ell
  centreFit : (centerIndex d t).val+1≤q+1
  probe : coordinates.val=List.ofFn (NativeProbeRing.chosenRep f.natDegree
    (realProbeCount (S:=SP) (c:=v.child)) (d).fit (nx).probeAt)
  width : (q-A)+13*A=page

def shellPageWord (B : PayloadShell R) (k : PageAt T nx) : Word page :=
  B.width ▸ childPageKey (q-A) k

structure DirectorySeed (B : PayloadShell R) where
  k1 : ℕ
  k2 : ℕ
  ow : ℕ
  oldKey : v.child.host.Row⊕v.child.host.Col→Word ow
  owners : List (RefRow k1 (Word ow × Origin key prec page))
  seats : List (RefRow k2 (SeatField (dim nx) page))
  queries : Port v.child.host.Edge→Meter (Word k1 × Word k2 × Bool)
  fallback : Addon ow (dim nx) key prec page
  valid : NativeTables X.childOrigins oldKey (shellPageWord R B) owners seats queries

def eventFromShell (B : PayloadShell R)
    {tc tz tm : ℕ} (ct : Word tc) (zz : Word tz) (mm : Word tm) (gg : Word 6)
    (ht : ct.val=centerOrdinal T nx) (hz : zz.val=(nx).probeAt.val)
    (hm : mm.val=modeOrdinal T nx) (hg : gg.val=(nx).groupAt.val)
    (exponents : List (Word (q+1))) (acted : exponents.map Word.val=liveExponentSpec R) :
    NativeEventOnly R :=
  let old := copyFixed B.oldDepth
  let pr := copyFixed B.receiving
  let cent := copyContext B.context
  let ax := J6R21Ancestor.copyBytes B.axis
  let co := copyCoordinates (fw:=B.fw) B.coordinates
  let oldExact : old.result=B.oldDepth := congrArg Meter.result (copy_fixed_exact B.oldDepth)
  let prExact : pr.result=B.receiving := congrArg Meter.result (copy_fixed_exact B.receiving)
  let centExact : cent.result=B.context := congrArg Meter.result (copy_context_exact B.context)
  let axExact : ax.result=B.axis := congrArg Meter.result (J6R21Ancestor.copyBytes_exact B.axis)
  let coExact : co.result=B.coordinates := congrArg Meter.result (copy_coordinates_exact B.coordinates)
  { edge := B.edge
    dep := B.dep
    tc := tc
    tz := tz
    tm := tm
    code := B.code
    native := ⟨⟨ct,zz,mm,gg,ht,hz,hm,hg,old.result,
      oldExact.symm ▸ B.depthExact,B.depthPos,B.depthFit,pr.result,
      prExact.symm ▸ B.receiveExact,B.edgePos,B.edgeFit⟩,old.steps+pr.steps+8⟩
    issued := B.issued
    fw := B.fw
    hOld := B.hOld
    hMod := B.hMod
    words := ⟨⟨cent.result,ax.result,gg,exponents,co.result⟩,cent.steps+ax.steps+co.steps+8⟩
    group := rfl
    clock := axExact.symm ▸ B.clock
    centre := centExact.symm ▸ B.centre
    codeExact := centExact.symm ▸ B.codeExact
    codePos := B.codePos
    codeFit := B.codeFit
    acted := acted
    outerPos := B.outerPos
    fit := B.centreFit
    probe := coExact.symm ▸ B.probe
    width := B.width }

def loadFromShell (B : PayloadShell R) (D : DirectorySeed R B)
    {tc tz tm : ℕ} (ct : Word tc) (zz : Word tz) (mm : Word tm) (gg : Word 6)
    (ht : ct.val=centerOrdinal T nx) (hz : zz.val=(nx).probeAt.val)
    (hm : mm.val=modeOrdinal T nx) (hg : gg.val=(nx).groupAt.val)
    (exponents : List (Word (q+1))) (acted : exponents.map Word.val=liveExponentSpec R) :
    LocalLoad X w :=
  let ev := eventFromShell R B ct zz mm gg ht hz hm hg exponents acted
  let dir : LocalDirectory X ev :=
    ⟨D.k1,D.k2,D.ow,D.oldKey,D.owners,D.seats,D.queries,D.fallback,D.valid⟩
  ⟨q,U,R,ev,dir⟩

theorem shell_really_uses_input_fields (B : PayloadShell R) (D : DirectorySeed R B)
    {tc tz tm : ℕ} (ct : Word tc) (zz : Word tz) (mm : Word tm) (gg : Word 6)
    (ht : ct.val=centerOrdinal T nx) (hz : zz.val=(nx).probeAt.val)
    (hm : mm.val=modeOrdinal T nx) (hg : gg.val=(nx).groupAt.val)
    (exponents : List (Word (q+1))) (acted : exponents.map Word.val=liveExponentSpec R) :
    let ev := eventFromShell R B ct zz mm gg ht hz hm hg exponents acted
    let K := loadFromShell R B D ct zz mm gg ht hz hm hg exponents acted
    K.event.native.result.tWord=ct ∧ K.event.native.result.zWord=zz ∧
      K.event.native.result.mWord=mm ∧ K.event.native.result.gWord=gg ∧
      ev.words.result.exponents=exponents ∧ K.event.native.steps=(3*B.dep+1)+(3*prec+1)+8 ∧
      K.event.words.steps=contextCopyFee tw bw+(3*B.axis.length+1)+(3*B.fw.length+1)+8 := by
  refine ⟨rfl,rfl,rfl,rfl,rfl,?_,?_⟩
  · change (copyFixed B.oldDepth).steps+(copyFixed B.receiving).steps+8=_
    simp only [copy_fixed_exact]
  · change (copyContext B.context).steps+(J6R21Ancestor.copyBytes B.axis).steps+
      (copyCoordinates (fw:=B.fw) B.coordinates).steps+8=_
    simp only [copy_context_exact,J6R21Ancestor.copyBytes_exact,copy_coordinates_exact]

#print axioms liveExponentSpec
#print axioms eventFromShell
#print axioms loadFromShell
#print axioms shell_really_uses_input_fields
end
end J6R52Dispatch

