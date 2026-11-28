import J6R57ScopeFeeAtlas

/-! An explicit polynomial upper expression for the complete R33
atlas tariff as a function of actual finite field widths, page menu
dimensions and resident table lengths. A raw coefficient producer
is not covered merely because its result fits this footprint. -/
namespace J6R57ScopeFee
open scoped Polynomial BigOperators Classical
open Polynomial AOracleMachineTime A1R12 J6R15ModeCost J6R21Ancestor J6R25PreparedSupply J6R26DescriptorTree
open J6ActiveRun J6ActiveSchedule J6R12Blueprint J6R11Blueprint J1PPrinted J6R16ModeCost
open J6R10Repack J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage
open J6R34RootAtlas J6R33GeneratedChildSite J6R33PageIndexedBirth
open J6R17ModeTape J6R14LayoutCost J6R31RootResidentTables J6R32ChildResidentTransfer J6R27OriginalGate A1R11
set_option autoImplicit false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxHeartbeats 24000000
set_option maxRecDepth 4800
set_option Elab.async false
noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic}
variable {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)
local notation "L" => (PageBank f ell key prec tw bw page)
local notation "J" => (PageJob f ell key prec tw bw page)

def headerSweepCeiling (U : ℕ) : ℕ :=
  (16*(6*U+1)*U+U*((8*(6*U)+22)*U+4)+4)+(206*U+6+18)*(U*U)+4

def requestsGeometryCeiling (U : ℕ) : ℕ :=
  headerSweepCeiling U+spanFee U U+(U*U)*((2*requestFee U U U+6)*U+8)+4

def atlasWordGeometryCeiling (U : ℕ) : ℕ :=
  prepareSiteFee U U U U U U U U+requestsGeometryCeiling U+
    (U*U*U)*(framePayloadFee U U U U U U U U U U (U*U*U)+onePageFee U+5)+15

theorem header_enumeration_paid_by_side_count {a U : ℕ} (hA : a≤U) (cellSide : 2^(6*a)≤U) :
    headerBankFee a≤headerSweepCeiling U := by
  unfold headerBankFee headerSweepCeiling allPairsCap headerCap
  gcongr

theorem requests_counted_from_actual_header_side {a q b U : ℕ}
    (ha : a≤U) (hQ : q+1≤U) (hc : 2^(6*a)≤U) (hb : b≤U) :
    requestsFee a (q-a) (q+1) b≤requestsGeometryCeiling U := by
  have hs := header_enumeration_paid_by_side_count ha hc
  have hW : q-a≤U := (Nat.sub_le q a).trans ((Nat.le_succ q).trans hQ)
  unfold requestsFee requestsGeometryCeiling spanFee requestFee
  gcongr

theorem native_frame_fee_from_dimensions {p ell deg a coord q code page edges modes pages U : ℕ}
    (pFit : p≤U) (ellFit : ell≤U) (degreeFit : deg≤U)
    (aFit : a≤U) (coordFit : coord≤U) (qFit : q≤U) (codeFit : code≤U)
    (pageFit : page≤U) (edgeFit : edges≤U) (modeFit : modes≤U) (pagesFit : pages≤U*U*U) :
    framePayloadFee p ell deg a coord q code page edges modes pages≤
      framePayloadFee U U U U U U U U U U (U*U*U) := by
  unfold framePayloadFee uvWidth probeCopyFee slotStride pipelineFee denseRecordFee
    modeBindingFee maskSearchStride recordStride buildModeInputCap
  gcongr

variable {v : Ticket sel r}
structure AtlasFootprint (I : OccurrenceInput T v key prec tw bw page) (U : ℕ) : Prop where
  dim : (printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth≤U
  cells : 2^(6*(printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth)≤U
  q : I.q+1≤U
  copies : (packing sel (ticketReady T v)).copies≤U
  prec : registerPrecision (printedParams (f:=f) (ell:=ell) s) v.parent v.centerAt≤U
  outer : ell≤U
  deg : I.fw.length≤U
  code : I.code≤U
  page : page≤U
  edgeCount : I.geometry.edges.length≤U
  modeCount : I.geometry.modes.length≤U
  timeWord : tw≤U
  codeWord : bw≤U

theorem literal_atlas_tariff_from_finite_footprint
    (I : OccurrenceInput T v key prec tw bw page) (U : ℕ) (F : AtlasFootprint I U) :
    literalAtlasTariff I≤atlasWordGeometryCeiling U := by
  let a := (printedParams (f:=f) (ell:=ell) s).levelBits v.parent.depth
  let i := (centerIndex (ticketReady T v) v.centerAt).val
  let b := (packing sel (ticketReady T v)).copies
  let p := registerPrecision (printedParams (f:=f) (ell:=ell) s) v.parent v.centerAt
  have ha : a≤U := F.dim
  have hi : i≤U := (centerIndex (ticketReady T v) v.centerAt).isLt.le.trans ha
  have hq : I.q≤U := (Nat.le_succ I.q).trans F.q
  have hb : b≤U := F.copies
  have hc : 2^(6*a)≤U := F.cells
  have hPageWidth : (I.q-a)+13*a≤U := by
    calc
      _ = page := I.width
      _ ≤ U := F.page
  have hp : pagesCount a b≤U*U*U := Nat.mul_le_mul (Nat.mul_le_mul hc hc) hb
  have hp' : (orderedChildPages a b).length≤U*U*U := by
    rw [(child_pages_complete a b).2.2]
    exact hp
  have requests := requests_counted_from_actual_header_side ha F.q hc hb
  have fr := native_frame_fee_from_dimensions F.prec F.outer F.deg ha hi F.q F.code hPageWidth F.edgeCount F.modeCount hp'
  have append : onePageFee ((I.q-a)+13*a)≤onePageFee U := by
    unfold onePageFee
    omega
  have common :
      prepareSiteFee a I.q i I.fw.length I.code tw bw I.geometry.modes.length≤
        prepareSiteFee U U U U U U U U := by
    unfold prepareSiteFee dispatchStride recordStride contextCopyFee
    have mode := F.modeCount
    have hd := F.deg
    have code := F.code
    have time := F.timeWord
    have width := F.codeWord
    gcongr
  have pageLoop :
      pagesCount a b*(framePayloadFee p ell I.fw.length a i (I.q+1) I.code ((I.q-a)+13*a)
        I.geometry.edges.length I.geometry.modes.length (orderedChildPages a b).length+
        onePageFee ((I.q-a)+13*a)+5)≤
      (U*U*U)*(framePayloadFee U U U U U U U U U U (U*U*U)+onePageFee U+5) :=
    Nat.mul_le_mul hp (Nat.add_le_add_right (Nat.add_le_add fr append) 5)
  change prepareSiteFee a I.q i I.fw.length I.code tw bw I.geometry.modes.length+
    requestsFee a (I.q-a) (I.q+1) b+
    pagesCount a b*(framePayloadFee p ell I.fw.length a i (I.q+1) I.code ((I.q-a)+13*a)
      I.geometry.edges.length I.geometry.modes.length (orderedChildPages a b).length+
      onePageFee ((I.q-a)+13*a)+5)+12+3≤_
  unfold atlasWordGeometryCeiling
  have together := Nat.add_le_add (Nat.add_le_add common requests) pageLoop
  omega

theorem printed_literal_header_side_is_polynomial
    (d : ℕ) (hs : 1<s) :
    2^(6*(printedParams (f:=f) (ell:=ell) s).levelBits d)≤(2*s)^6 := by
  let l := Nat.clog 2 s
  have pos : 0<l := (Nat.lt_clog_iff_pow_lt (by decide : 1<2)).mpr (by simpa using hs)
  have low : 2^(l-1)<s := Nat.pow_pred_clog_lt_self (by decide : 1<2) hs
  have next : l=l-1+1 := by omega
  have high : 2^l≤2*s := by
    calc
      2^l=2^(l-1)*2 := by
        conv_lhs => rw [next]
        rw [pow_succ]
      _≤2*s := by
        rw [Nat.mul_comm _ 2]
        exact Nat.mul_le_mul_left 2 low.le
  have a : (printedParams (f:=f) (ell:=ell) s).levelBits d≤l := bits_le_lam _ _
  calc
    _≤2^(6*l) := Nat.pow_le_pow_right (by decide) (Nat.mul_le_mul_left 6 a)
    _=(2^l)^6 := by rw [←pow_mul,Nat.mul_comm l 6]
    _≤_ := Nat.pow_le_pow_left high 6

end
#print axioms printed_literal_header_side_is_polynomial
#print axioms header_enumeration_paid_by_side_count
#print axioms requests_counted_from_actual_header_side
#print axioms native_frame_fee_from_dimensions
#print axioms literal_atlas_tariff_from_finite_footprint
end J6R57ScopeFee
