import J6R55SelectedPeakWords

/-! Each selected owner payload bit appearing at the successful original
read can be charged to the same real source's actual copies. Lookup
search and option/address overhead are additional, not free. This is
a local consistency check between the memory projection and Meter. -/
namespace J6R55SelectedPeak
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R27OriginalGate
open J6R36ChildFramedRoute J6R51Peak J6R53OldOwner

set_option autoImplicit false
set_option maxRecDepth 3100
set_option maxHeartbeats 14500000

theorem selected_owner_data_bits_are_paid_at_copy
    {gate key prec page : ℕ} (x : OwnerData gate key prec page) :
    (ownerPayload x).length≤(copyOwnerData x).steps := by
  have originPart : (originWords x.origin).length+1≤originFee key prec page x.origin.pageKey.isSome := by
    rw [origin_words_exact,originFee]
    cases x.origin.pageKey.isSome <;> simp <;> omega
  have scaled (n : ℕ) : n*gate≤(3*gate+5)*n := by
    rw [Nat.mul_comm n gate]
    exact Nat.mul_le_mul_right n (by omega)
  have gatePart : (x.gateCode.toList.flatMap ownerGatePayload).length≤optGateFee x.gateCode := by
    cases h : x.gateCode with
    | none => simp
    | some ob =>
      cases ob with
      | free => simp [ownerGatePayload,optGateFee,gateCopyFee]
      | equal xs =>
        have fee := scaled xs.length
        simp [ownerGatePayload,optGateFee,gateCopyFee,selected_word_tape_width]
        omega
      | clause xs ss =>
        have fee := scaled xs.length
        simp [ownerGatePayload,optGateFee,gateCopyFee,selected_word_tape_width]
        omega
  rw [copy_owner_data_exact]
  change (originWords x.origin++[x.gateCode.isSome]++x.gateCode.toList.flatMap ownerGatePayload).length≤_
  simp only [List.length_append,List.length_cons,List.length_nil, Nat.zero_add]
  exact (Nat.add_le_add originPart gatePart).trans (Nat.le_add_right _ 5)

theorem actual_owner_copies_cover_all_selected_read_bits {U : Type} {own gate key prec page : ℕ}
    (roster : RawRoster own gate key prec page) (name : U→Word own)
    (data : U→OwnerData gate key prec page) (order : List U)
    (fetches : ∀ u∈order,(locate (name u) roster).result=some (data u)) :
    let read := gatherOwners roster (order.map name)
    read.result=some (order.map data) ∧ (ownerTape (order.map data)).length≤read.steps := by
  have evaluated : gatherOwners roster (order.map name)=
      ⟨some (order.map data),3+(order.map (fun u=>(locate (name u) roster).steps+ownerDataFee (data u)+8)).sum⟩ :=
    gather_owner_words_exact roster name data order fetches
  dsimp only
  rw [evaluated]
  refine ⟨rfl,?_⟩
  change (ownerTape (order.map data)).length≤
    3+(order.map (fun u=>(locate (name u) roster).steps+ownerDataFee (data u)+8)).sum
  clear evaluated
  induction order with
  | nil => exact Nat.zero_le _
  | cons u us ih =>
    have k := selected_owner_data_bits_are_paid_at_copy (data u)
    rw [copy_owner_data_exact] at k
    change (ownerPayload (data u)).length≤ownerDataFee (data u) at k
    change (ownerPayload (data u)++ownerTape (us.map data)).length≤
      3+((locate (name u) roster).steps+ownerDataFee (data u)+8+
        (us.map (fun v=>(locate (name v) roster).steps+ownerDataFee (data v)+8)).sum)
    rw [List.length_append]
    have next := ih (fun v mem=>fetches v (List.mem_cons_of_mem _ mem))
    omega

#print axioms selected_owner_data_bits_are_paid_at_copy
#print axioms actual_owner_copies_cover_all_selected_read_bits
end J6R55SelectedPeak
