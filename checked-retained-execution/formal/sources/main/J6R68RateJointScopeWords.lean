import J6R57ScopeFeeAtlas
import J6R51OnlineCore
import J6R50SourceProducerKeyed
import J6R48RawRouteLiteral

/-! The true descendant scope's paid source-word traffic: separate the
literal retained frame route and keyed replay from the primitive
event issuers. No supplied whole occurrence word-price or fee list. -/
namespace J6R68RateJoint
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R26DescriptorTree J6R34ChildPath J6R36ChildFramedRoute J6R48RawRoute
open J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R34RootAtlas
open J6R24MeteredRecursion J6R10Repack J6R11Blueprint J6R12Blueprint J1PPrinted
open J6ActiveRun J6ActiveSchedule J6R50SourceProducer J6R51Online J6R57ScopeFee J6R49SourceLayout
open J6R32ChildResidentTransfer J6R19Retained J6R17ModeTape J6R27OriginalGate

set_option autoImplicit false
set_option quotPrecheck false
set_option warningAsError true
set_option linter.unusedSectionVars false
set_option maxRecDepth 3700
set_option maxHeartbeats 23000000
set_option Elab.async false

noncomputable section
variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
variable {v : Ticket sel r}
variable {X : StoredSite T v key prec tw bw page} {w : (Plan sel).Slot v.child}
local notation "S" => (printedParams (f:=f) (ell:=ell) s)
local notation "A" => ((S).levelBits v.child.depth)
local notation "Vt" => (successorTicket v w)
local notation "Dr" => (ticketReady T Vt)
local notation "Ci" => (centerIndex Dr (Vt).centerAt)
local notation "Pr" => (registerPrecision S v.child (Vt).centerAt)
local notation "Bks" => (childOrder X.site)

/-- Exactly the word traffic of the original adjacent source writer.
The sum is over the actual retained file's edge order. -/
def nextPortWordsTariff (q : ℕ) : ℕ :=
  6+((Bks).map (fun e=>framedCopiesFee (frameOf X.site e)+3*A+3*((q-A)+13*A)+8)).sum

/-- No fee supplied for the selected replay: scans and copies of the
actual rows, masks, keyed seats and ancestral frames are exposed. -/
def selectedResidentWordsTariff (U : ExplicitSelectedWords X.site w q) : ℕ :=
  (3+(((Bks).map (frameOf X.site)).map
    (fun x=>3*X.birth.port+5+framedIncidenceFee x)).sum)+
  (4+(Bks).length*(locateFee X.birth.port U.rows.length+3*(A+((q-A)+13*A))+54))+
  selectedReplayFee A q (Ci).val (packing sel Dr).copies Pr
    ((U.masks.map (fun x=>copiedMaskFee x+5)).sum) (Bks).length+7

theorem actual_adjacent_port_word_copy_fee
    {U : ExplicitSelectedWords X.site w q} (Y : Replayed X.site w q U) :
    (selectedAdjacent Y).generated.steps=nextPortWordsTariff (X:=X) q := by
  let D := selectedAdjacent Y
  change (actualNextPhysical X.site Dr (Vt).centerAt D.code D.raw D.exact).steps=_
  exact (emit_next_exact X.site (rawLiteralNextSeats X.site Dr (Vt).centerAt D.code D.raw D.exact)).2

theorem actual_selected_resident_words_fee (U : ExplicitSelectedWords X.site w q) :
    (replayChild X.site w q U).steps≤selectedResidentWordsTariff (X:=X) (w:=w) U := by
  obtain ⟨_,paid⟩ := replay_actual_selected_from_parent_frames X.site w q U
  exact paid

theorem actual_local_load_source_words_split (K : LocalLoad X w) :
    measuredWordProducers K.advance.next.input=
      K.event.issued.steps+K.event.native.steps+nextPortWordsTariff (X:=X) K.rankWidth+
        (replayChild X.site w K.rankWidth K.selectedWords).steps+K.event.words.steps+8 := by
  change K.event.issued.steps+
    (K.event.native.steps+(selectedAdjacent K.replay).generated.steps+4+
      (replayChild X.site w K.rankWidth K.selectedWords).steps+K.event.words.steps+4)=_
  rw [actual_adjacent_port_word_copy_fee K.replay]
  omega

theorem actual_local_load_source_words_from_paid_parts (K : LocalLoad X w) :
    measuredWordProducers K.advance.next.input≤
      K.event.issued.steps+K.event.native.steps+nextPortWordsTariff (X:=X) K.rankWidth+
        selectedResidentWordsTariff (X:=X) (w:=w) K.selectedWords+K.event.words.steps+8 := by
  rw [actual_local_load_source_words_split K]
  exact Nat.add_le_add_right (Nat.add_le_add_right
    (Nat.add_le_add_left (actual_selected_resident_words_fee K.selectedWords) _) _) _

variable {rate : ℕ} {c : Call (PhysicalHost f ell)}

theorem real_descendant_source_words_from_actual_scope
    (M : OnlineMachine T key prec tw bw page rate) (p : Path sel r c)
    (u : (Plan sel).Slot c) (j : (Plan sel).Slot ((Plan sel).child c u)) :
    let Y := sourceState M p u
    let K := (M.demand Y j).result
    measuredWordProducers (sourceState M (.step p u) j).input≤
      K.event.issued.steps+K.event.native.steps+nextPortWordsTariff (X:=Y) K.rankWidth+
        selectedResidentWordsTariff (X:=Y) (w:=j) K.selectedWords+K.event.words.steps+8 :=
  actual_local_load_source_words_from_paid_parts (M.demand (sourceState M p u) j).result

#print axioms actual_adjacent_port_word_copy_fee
#print axioms actual_selected_resident_words_fee
#print axioms actual_local_load_source_words_split
#print axioms actual_local_load_source_words_from_paid_parts
#print axioms real_descendant_source_words_from_actual_scope
end
end J6R68RateJoint
