
import J6R23PaddingCensusNative
import J6R23PaddingCensusCodec

/-! Retain the two exact original assigned seats as data, then export
their concrete page key and ordinal words. The input is a positioned
layout, not the older nonconstructive choice of an order from the mask. -/
namespace J6R23PaddingCensus
open scoped BigOperators Classical
open P11FullPacking J6Mesh J6OrientedHost J6RecursiveOrientation
open A1R10 A1R12 AOracleMachineTime AOracleMachineTimeTape
set_option maxHeartbeats 13000000
set_option linter.unusedSectionVars false

abbrev PositionedPad (a b : ℕ) :=
  Physical a b (Fin 64) × Physical a b (Fin 64)

def bothPorts {a b : ℕ} (p : PositionedPad a b) : Bool→Physical a b (Fin 64)
  | false => p.1
  | true => p.2

def exportFee (a width : ℕ) :=
  16*width+2400*a+80

def exportActualLayout {a b : ℕ} (width : ℕ) :
    List (PositionedPad a b)→Meter (List (PadColumnWord (width+13*a) (a+1)))
  | [] => ⟨[],4⟩
  | p::ps =>
    let rest := exportActualLayout width ps
    let q := serializeColumn width (bothPorts p)
    ⟨q::rest.result,rest.steps+exportFee a width⟩

theorem export_actual_layout_receipt {a b : ℕ} (width : ℕ) (xs : List (PositionedPad a b)) :
    (exportActualLayout width xs).result=xs.map (fun p=>serializeColumn width (bothPorts p)) ∧
    (exportActualLayout width xs).steps=4+xs.length*exportFee a width := by
  induction xs with
  | nil => simp [exportActualLayout]
  | cons p ps ih =>
    refine ⟨by simp only [exportActualLayout,List.map_cons,ih.1],?_⟩
    simp only [exportActualLayout,ih.2,List.length_cons,Nat.add_mul,one_mul]
    omega

def positionedLayout (m l : ℕ) (mask : MaskFamily (a m) (K m) (Fin 64))
    (w : Fin (a m)→Fin 64) (hm : m≤K m) (hL : 2*l=L m)
    (positions : List (PositionedPad (a m) (K m))) (order : List (NativePad m l w)) : Prop :=
  List.Forall₂ (fun p d =>
    p.1=oriented mask w m l hm hL (.inr (d,false)) ∧
    p.2=oriented mask w m l hm hL (.inr (d,true))) positions order

theorem exported_actual_layout_chart (m l width : ℕ) (mask : MaskFamily (a m) (K m) (Fin 64))
    (w : Fin (a m)→Fin 64) (hm : m≤K m) (hL : 2*l=L m)
    (positions : List (PositionedPad (a m) (K m))) (order : List (NativePad m l w))
    (matchesLayout : positionedLayout m l mask w hm hL positions order) :
    realizesLayout m l mask w hm hL (pageCode width) (exportActualLayout width positions).result order ∧
    (exportActualLayout width positions).steps=4+order.length*exportFee (a m) width := by
  obtain ⟨r,s⟩ := export_actual_layout_receipt width positions
  refine ⟨?_,s.trans (by rw [(show List.Forall₂ _ positions order from matchesLayout).length_eq])⟩
  unfold realizesLayout
  rw [r]
  clear r s
  induction matchesLayout with
  | nil => exact .nil
  | cons E F ih =>
    rename_i p d ps ds
    have H : bothPorts p=(fun side=>oriented mask w m l hm hL (.inr (d,side))) := by
      funext side
      cases side
      · exact E.1
      · exact E.2
    apply List.Forall₂.cons _ ih
    simp only [H]
    exact serialize_column_exact width _

theorem actual_census_from_positioned_layout (m l width : ℕ) (mask : MaskFamily (a m) (K m) (Fin 64))
    (w : Fin (a m)→Fin 64) (hm : m≤K m) (hL : 2*l=L m)
    (positions : List (PositionedPad (a m) (K m))) (order : List (NativePad m l w))
    (nodup : order.Nodup) (all : order.toFinset=Finset.univ)
    (matchesLayout : positionedLayout m l mask w hm hL positions order)
    (fits : K m≤2^width) (i : J6Recovery.Addr m) :
    let raw := exportActualLayout width positions
    let out := censusAt m i raw.result
    List.Forall₂ (fun k d=>k.val=J6PhysicalInteger.loads m l mask w hm hL i d) out.result order ∧
    raw.steps+out.steps≤4+order.length*exportFee (a m) width+censusBudget (width+13*a m) m order.length := by
  obtain ⟨chart,bill⟩ := exported_actual_layout_chart m l width mask w hm hL positions order matchesLayout
  have C := census_at_exact m l mask w hm hL (pageCode width) (page_code_injective width fits)
    (exportActualLayout width positions).result order nodup all chart i
  refine ⟨C.1,?_⟩
  rw [bill]
  exact Nat.add_le_add_left C.2 _

#print axioms export_actual_layout_receipt
#print axioms exported_actual_layout_chart
#print axioms actual_census_from_positioned_layout
end J6R23PaddingCensus
