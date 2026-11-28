import J6R65LeafRateEntry
import J6R62LeafReader
import J1PPrintedDepth

/-! Uniform arithmetic and scan prefactor of a fetched created packet.
The inputs are published byte/field dimensions, not the fees of a
supplied evaluator. The only growing-base power is the grid size. -/
namespace J6R82LeafTime
open scoped Polynomial
open AOracleMachineTime A1R10 A1R11 A1R12 J6R21Ancestor J6R20Ancestor
open J6R18ChildWrite J6R19Retained J6R30ProducedGateRegistry J6R33StatefulArithmeticPage
open J6R48Leaf J6R65LeafRate J6R62Leaf J6R21Leaf
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option Elab.async false
set_option maxHeartbeats 30000000
set_option maxRecDepth 5500

variable {f : ℤ[X]} {ell key prec tw bw page : ℕ}
local notation "Bank" => (PageBank f ell key prec tw bw page)
local notation "Rec" => (Stored key prec tw bw (PagedEnvelope f ell prec page))

def uniformPacketPrefix (ell key prec tw bw page A K : ℕ) (hK : 0<K) : ℕ :=
  (locateFee key K+locateFee page K+
    K*(3*K+4*K+(K+A+2)+12)+traceRouteFee A K K K K+
    boxFee K ell K K+invokeStampFee key prec tw bw+18)+
  packetNonTreeFee A K ell K A K K K K K hK+
  packetTreeScale K ell K K K K K hK+packetFramingFee K ell K K

def uniformGatePrefix (ell K : ℕ) : ℕ :=
  originalGateFee K K K+uvWidth K ell K+4

def rowPrefix (ell key prec tw bw page A K : ℕ) (hK : 0<K) : ℕ :=
  uniformGatePrefix ell K+uniformPacketPrefix ell key prec tw bw page A K hK

structure PacketLimits (B : Bank) (r : Rec) (d : pageFields r) (p dep : ℕ)
    (wires : List WireRead) (A K : ℕ) : Prop where
  bank : B.records.length≤K
  pages : r.payload.pages.length≤K
  axis : r.payload.shape.a≤A
  fieldDeg : r.payload.shape.old.length≤K
  create : r.payload.shape.p≤K
  countWidth : r.payload.shape.w≤K
  codeWidth : r.context.codeWidth.val≤K
  rows : d.rows.length≤K
  cols : d.cols.length≤K
  modes : d.modes.length≤K
  receive : p≤K
  retention : dep≤K
  numWires : wires.length≤K
  wire : rawWireFee (dep+r.payload.shape.a+2) wires≤K*(3*K+4*K+(K+A+2)+12)

private theorem packet_primitive_envelope
    {a e ell p i q b r c m A K : ℕ} (hp : 0<p) (hK : 0<K)
    (ha : a≤A) (he : e≤K) (w : p≤K) (idx : i≤A) (hq : q≤K) (hb : b≤K)
    (hr : r≤K) (hc : c≤K) (hm : m≤K) :
    packetNonTreeFee a e ell p i q b r c m hp+packetTreeScale e ell p m r b q hp+
      packetFramingFee e ell p q≤
    packetNonTreeFee A K ell K A K K K K K hK+packetTreeScale K ell K K K K K hK+
      packetFramingFee K ell K K := by
  unfold packetNonTreeFee packetTreeScale packetFramingFee rowWriteCap affineRowFee
    variableFee unsignedCap affineExtra columnFee sourcePowerFee momentFee tileFee powBitCap
    choiceFee leafFee A1R9.counterBudget crossingGenCap crossScaleCap crossPowerCap
    modularGenCap localHeadCap derivativeInverseCap oddProdCap normProdCap ratioProdCap
    gridFoldCap gridCap shiftCap ratioCap dyadicCap scaleCap oddCap correctionCap
    subCap addCap mulCap uvWidth uBudgetGates uBudget A1R10.lane
  simp only [wordOps]
  gcongr <;> decide

theorem actual_packet_prefactor_has_one_uniform_scalar
    (B : Bank) (r : Rec) (d : pageFields r) (p dep : ℕ) (wires : List WireRead)
    (A K : ℕ) (hK : 0<K) (limit : PacketLimits B r d p dep wires A K) :
    actualPacketPrefactor B r d p dep wires≤uniformPacketPrefix ell key prec tw bw page A K hK := by
  let S := r.payload.shape
  have idx : S.i.val≤A := S.i.isLt.le.trans limit.axis
  have packet := packet_primitive_envelope (ell:=ell) S.pPos hK limit.axis limit.fieldDeg
    limit.create idx limit.countWidth limit.codeWidth limit.rows limit.cols limit.modes
  have bank := limit.bank
  have pages := limit.pages
  have mesh := limit.axis
  have field := limit.fieldDeg
  have newP := limit.receive
  have oldP := limit.create
  have depB := limit.retention
  have wiresB := limit.numWires
  have nr := limit.rows
  have nc := limit.cols
  have wiresFee := limit.wire
  have non :
      readerNonPacket B r d p dep wires≤
        locateFee key K+locateFee page K+K*(3*K+4*K+(K+A+2)+12)+
          traceRouteFee A K K K K+boxFee K ell K K+invokeStampFee key prec tw bw+18 := by
    unfold readerNonPacket locateFee traceRouteFee normalizeFee routeFee J6R20Ancestor.tapeFee
      portFee slotFee findFee boxFee scalarFee wordFee
    dsimp only
    gcongr
  let input := readerNonPacket B r d p dep wires
  let fixed := locateFee key K+locateFee page K+K*(3*K+4*K+(K+A+2)+12)+
    traceRouteFee A K K K K+boxFee K ell K K+invokeStampFee key prec tw bw+18
  let old := packetNonTreeFee S.a S.old.length ell S.p S.i.val S.w r.context.codeWidth.val
    d.rows.length d.cols.length d.modes.length S.pPos+
      packetTreeScale S.old.length ell S.p d.modes.length d.rows.length r.context.codeWidth.val S.w S.pPos+
      packetFramingFee S.old.length ell S.p S.w
  let top := packetNonTreeFee A K ell K A K K K K K hK+
    packetTreeScale K ell K K K K K hK+packetFramingFee K ell K K
  calc
    _ = input+old := by simp only [actualPacketPrefactor,input,old,S,Nat.add_assoc]
    _ ≤ fixed+top := Nat.add_le_add non packet
    _ = _ := by simp only [uniformPacketPrefix,fixed,top,Nat.add_assoc]

theorem true_gate_fits_the_same_uniform_scalar (B : Bank) (e p edges b : ℕ)
    (g : J6R27OriginalGate.CodeGate (J6R15ModeCost.Word b)) (A K : ℕ) (hK : 0<K)
    (width : e≤K) (receiver : p≤K) (clock : edges≤K) (addr : b≤K) (arity : gatePorts g≤K) :
    readCmdFee B e p edges (.gate b g)≤rowPrefix ell key prec tw bw page A K hK := by
  refine Nat.le_trans ?_ (Nat.le_add_right _ _)
  change originalGateFee edges b (gatePorts g)+uvWidth e ell p+4≤uniformGatePrefix ell K
  unfold uniformGatePrefix originalGateFee addressFee uvWidth
  gcongr

theorem printed_axis_fits_logarithmic_uniform_prefactor (s depth : ℕ) :
    J1PPrinted.stepA (Nat.clog 2 s) depth≤Nat.clog 2 s := by
  have cap := J1PPrinted.stepA_bound (Nat.clog 2 s) depth
  have base := (J9PrintedSchedule.rootU_range (Nat.clog 2 s)).1
  omega

theorem one_uniform_wire_tariff
    {n U dep a A K : ℕ} (ws : List WireRead) (nK : n≤K) (uK : U≤K) (aA : a≤A)
    (raw : rawWireFee (dep+a+2) ws≤n*(3*U+4*n+(U+a+2)+12)) :
    rawWireFee (dep+a+2) ws≤K*(3*K+4*K+(K+A+2)+12) := by
  refine raw.trans ?_
  gcongr

#print axioms actual_packet_prefactor_has_one_uniform_scalar
#print axioms true_gate_fits_the_same_uniform_scalar
#print axioms printed_axis_fits_logarithmic_uniform_prefactor
#print axioms one_uniform_wire_tariff
end J6R82LeafTime
