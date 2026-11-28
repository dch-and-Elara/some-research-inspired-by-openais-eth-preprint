import J6R55PublicDemand
import J6R52PeakModePath

/-! The successful actual request carries one dense exponent vector.
Its current literal implementation also passes the legacy full legal
mode catalogue to the ordinal scan. We count those two actual payloads
separately; a streamed arithmetic cursor does not remove the latter. -/
namespace J6R57LiveSpace
open scoped Polynomial
open Polynomial AOracleMachineTime J6R15ModeCost J6R17ModeTape J6R25PreparedSupply
open J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J1PPrinted
open J6R16ModeCost J6R26DescriptorTree J6R24MeteredRecursion
open J6R32ChildResidentTransfer J6R33GeneratedChildSite J6R33StatefulArithmeticPage
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R48DFS
open J6R50SourceProducer J6R51Online J6R51Dispatch J6R52Dispatch J6R53Dispatch
open J6R54Dispatch J6R55Public J6R52Peak

set_option autoImplicit false
set_option quotPrecheck false
set_option maxRecDepth 4100
set_option maxHeartbeats 25000000
set_option maxSynthPendingDepth 12
set_option Elab.async false
noncomputable section

def denseRequestBits {w : ℕ} (raw : List (Word w)) : ℕ :=
  (raw.flatMap Word.bits).length

def ordinalTableBits {w : ℕ} (file : List (List (Word w))) : ℕ :=
  (file.flatMap (fun row=>row.flatMap Word.bits)).length

theorem constant_dense_rows_width {A : Type*} {w : ℕ} (rows : List A) (words : A→List (Word w))
    (width : ℕ) (fit : ∀ a,(words a).length=width) :
    ordinalTableBits (rows.map words)=rows.length*(width*w) := by
  induction rows with
  | nil => simp [ordinalTableBits]
  | cons u us ih =>
    change ((words u).flatMap Word.bits++(us.map words).flatMap
      (fun row=>row.flatMap Word.bits)).length=(us.length+1)*(width*w)
    rw [List.length_append,fixed_weight_words_width,fit]
    change width*w+ordinalTableBits (us.map words)=_
    rw [ih,Nat.add_mul,Nat.one_mul,Nat.add_comm]

variable {f : ℤ[X]} {ell s C key prec tw bw page : ℕ} {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {root : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel root hf}
variable {v : Ticket sel root} {X : StoredSite T v key prec tw bw page}
variable {u : (Plan sel).Slot v.child}
local notation "nx" => (J6R48RawRoute.successorTicket v u)

theorem exact_ordinal_bytes_of_the_actual_mode_table {w : ℕ}
    (I : SiteTape sel (ticketReady T nx) (nx).centerAt w) :
    ordinalTableBits (frozenCatalogueBytes T nx I)=
      ((ticketActive T nx).tape (nx).centerAt).modes.length*(I.modes.length*w) := by
  unfold frozenCatalogueBytes
  apply constant_dense_rows_width
  intro β
  simp only [List.length_map,vectorKey]

theorem successful_real_request_counts_current_and_full_ordinal_words
    (input : Meter (FixedRequest X u)) :
    let Q := input.result
    let pick := Q.find Q.raw Q.group
    let F := (pick.result.get Q.hit).val
    denseRequestBits Q.raw=F.tape.modes.length*(Q.q+1) ∧
    ordinalTableBits F.catalogue=
      ((ticketActive T nx).tape (nx).centerAt).modes.length*
        (Q.replay.certificate.modes.length*(Q.q+1)) ∧
    (F.centre.bits++F.probe.bits++F.group.bits).length=F.tc+F.tz+6 := by
  let Q := input.result
  let pick := Q.find Q.raw Q.group
  let F := (pick.result.get Q.hit).val
  have count : Q.raw.length=F.tape.modes.length := by
    have eq := congrArg List.length F.exponents
    simpa only [List.length_map,vectorKey] using eq
  refine ⟨(fixed_weight_words_width Q.raw).trans (congrArg (·*(Q.q+1)) count),?_,?_⟩
  · change ordinalTableBits F.catalogue=_
    rw [F.catalogueExact]
    exact exact_ordinal_bytes_of_the_actual_mode_table _
  · change (F.centre.bits++F.probe.bits++F.group.bits).length=F.tc+F.tz+6
    rw [List.length_append,List.length_append,F.centre.size,F.probe.size,F.group.size,Nat.add_assoc]

#print axioms constant_dense_rows_width
#print axioms exact_ordinal_bytes_of_the_actual_mode_table
#print axioms successful_real_request_counts_current_and_full_ordinal_words
end
end J6R57LiveSpace
