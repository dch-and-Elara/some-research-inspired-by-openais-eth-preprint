import J6R54PeakInputPath

/-! Separate selected states during raw emission and index installation.
The new complete raw field is counted once in the second state.
A raw prefix still being emitted is not added to some preexisting
complete copy of that same field. -/
namespace J6R54PeakInput
open scoped Polynomial
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R26DescriptorTree
open J1PPrinted J6ActiveRun J6R10Reachable J6R11Blueprint J6R12Blueprint J6R24MeteredRecursion
open J6R30ProducedGateRegistry J6R32StatefulArithmetic J6R33StatefulArithmeticPage J6R48DFS
open J6R16ModeCost J6R36ChildFramedRoute J6R41StructuredAllPaths J6R50SourceProducer
open J6R51Peak J6R51Online J6R51ParentFrames J6R52Peak J6R52CacheWhole J6R53PeakAddon

set_option autoImplicit false
set_option maxRecDepth 3650
set_option maxHeartbeats 16500000
noncomputable section

theorem encoded_take_le_full {A : Type*} (source : List A) (enc : A→List Bool) (n : ℕ) :
    ((source.take n).flatMap enc).length≤(source.flatMap enc).length := by
  have fact : ((source.take n).flatMap enc).length+((source.drop n).flatMap enc).length=
      (source.flatMap enc).length := by
    rw [←List.length_append,←List.flatMap_append,List.take_append_drop]
  exact (Nat.le_add_right _ _).trans_eq fact

variable {f : ℤ[X]} {ell s C key prec tw bw page q : ℕ}
variable {cfg : RootBounds s C f}
variable {sel : Selector (printedParams (f:=f) (ell:=ell) s) (sourceDelta s)}
variable {r c : Call (PhysicalHost f ell)} {hf : f.Monic} {T : Prepared cfg sel r hf}
local notation "P" => (Plan sel)

def selectedAncestralIngress (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c) : ℕ :=
  rawStackBits M p+addonStackBits M p+cacheStackBits M p

def emittedPrefixBits (M : OnlineMachine T key prec tw bw page q)
    (p : Path sel r c) (w : (P).Slot c) (n : ℕ) : ℕ :=
  (rawWords ((sourceState M p w).site.input.take n)).length

def installedPrefixBits (M : OnlineMachine T key prec tw bw page q)
    (p : Path sel r c) (w : (P).Slot c) (n : ℕ) : ℕ :=
  (((sourceBankAt M p w).result.rows.take n).flatMap indexedAddonBits).length

theorem phase_does_not_double_count_the_stored_raw_input
    (M : OnlineMachine T key prec tw bw page q) (p : Path sel r c) (w : (P).Slot c) (n : ℕ) :
    selectedAncestralIngress M p+emittedPrefixBits M p w n≤
       selectedAncestralIngress M (.step p w) ∧
    selectedAncestralIngress M p+
       (storedRawBits (sourceState M p w)).length+installedPrefixBits M p w n≤
       selectedAncestralIngress M (.step p w) := by
  have emitFit : emittedPrefixBits M p w n≤(storedRawBits (sourceState M p w)).length :=
    encoded_take_le_full (sourceState M p w).site.input addonWords n
  have indexFit : installedPrefixBits M p w n≤
      (residentAddonPayload (sourceBankAt M p w).result).length :=
    encoded_take_le_full (sourceBankAt M p w).result.rows indexedAddonBits n
  constructor
  · simp only [selectedAncestralIngress,rawStackBits,addonStackBits,cacheStackBits]
    omega
  · simp only [selectedAncestralIngress,rawStackBits,addonStackBits,cacheStackBits]
    omega

theorem actual_install_focus_has_a_named_live_path_reserve
    (M : OnlineMachine T key prec tw bw page q) (fixed addr seed owner : ℕ)
    (sizes : EntryWidths M fixed addr) (boot : BootBodyWidth M seed)
    (owners : OwnerWidth M owner) (p : Path sel r c) (w : (P).Slot c) (n : ℕ) :
    selectedAncestralIngress M p+
       (storedRawBits (sourceState M p w)).length+installedPrefixBits M p w n≤
     2*((32*r.edges/29)-((P).child c w).edges)*rawAndIndexedRowCap s addr owner key prec page+
        (3*r.edges/29)*cachedRowCap addr owner key prec page (Nat.clog 2 s) (sourceBodyCap s C seed) :=
  (phase_does_not_double_count_the_stored_raw_input M p w n).2.trans
    (actual_raw_indexed_and_frame_reserves_same_stack M fixed addr seed owner sizes boot owners (.step p w))

#print axioms encoded_take_le_full
#print axioms phase_does_not_double_count_the_stored_raw_input
#print axioms actual_install_focus_has_a_named_live_path_reserve
end
end J6R54PeakInput
