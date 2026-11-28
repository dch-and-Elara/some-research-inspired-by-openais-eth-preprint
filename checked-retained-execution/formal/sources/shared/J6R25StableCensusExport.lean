
import J6R25StableCensusGeometry
import J6R23PaddingCensusExport

/-! Two actual assigned padding port positions are serialized with the
original canonical key word; this operation is independent of which
legal chart supplied them. -/
namespace J6R25StableCensus
open scoped Classical BigOperators
open P11FullPacking J6Mesh J6OrientedHost J6R23PaddingCensus
open AOracleMachineTime
set_option maxHeartbeats 13000000
set_option linter.unusedSectionVars false

def legallyPositioned (m l : ℕ) (w : Fin (a m)→Fin 64) (hm : m≤K m) (hL : 2*l=L m)
    (C : LegalRootChart w hm hL)
    (positions : List (PositionedPad (a m) (K m))) (order : List (NativePad m l w)) : Prop :=
  List.Forall₂ (fun port d=>port.1=C.seats (.inr (d,false)) ∧ port.2=C.seats (.inr (d,true)))
    positions order

theorem export_legal_positions (m l width : ℕ) (w : Fin (a m)→Fin 64)
    (hm : m≤K m) (hL : 2*l=L m) (C : LegalRootChart w hm hL)
    (positions : List (PositionedPad (a m) (K m))) (order : List (NativePad m l w))
    (matched : legallyPositioned m l w hm hL C positions order) :
    realizesLegalLayout m l w hm hL C (pageCode width) (exportActualLayout width positions).result order ∧
    (exportActualLayout width positions).steps=4+order.length*exportFee (a m) width := by
  obtain ⟨r,s⟩ := export_actual_layout_receipt width positions
  refine ⟨?_,s.trans (by rw [(show List.Forall₂ _ positions order from matched).length_eq])⟩
  unfold realizesLegalLayout
  rw [r]
  clear r s
  induction matched with
  | nil => exact .nil
  | cons E F ih =>
    rename_i p d ps ds
    have H : bothPorts p=(fun side=>C.seats (.inr (d,side))) := by
      funext side
      cases side
      · exact E.1
      · exact E.2
    apply List.Forall₂.cons _ ih
    simp only [H]
    exact serialize_column_exact width _

#print axioms export_legal_positions
end J6R25StableCensus
