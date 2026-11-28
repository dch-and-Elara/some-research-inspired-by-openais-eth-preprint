import J6R94HeldOwnerProviderUniform
import J6R62LeafPrepBounds

/-! Costs of the actual finite R53/R58 scan loops, including the
backing-table lookup and immutable Gate and Origin word copies. -/
namespace J6R114RetainedScopeTariff
open scoped Polynomial Classical
open AOracleMachineTime J6R15ModeCost J6R21Ancestor J6R53OldOwner
open J6R58RequestSource J6R57PublicRequest J6R62Leaf J6R26DescriptorTree
set_option autoImplicit false
set_option warningAsError true
set_option Elab.async false
set_option maxHeartbeats 12000000

theorem actual_owner_lookup_scan_cap {own gate key prec page : ℕ}
    (raw : RawRoster own gate key prec page) (d : ℕ)
    (fit : ∀ row∈raw,∀ g,row.payload.gateCode=some g→GateFit d g)
    (keys : List (Word own)) :
    (gatherOwners raw keys).steps≤3+keys.length*
      (locateFee own raw.length+ownerDataCap gate key prec page d+8) := by
  let unit := locateFee own raw.length+ownerDataCap gate key prec page d+8
  change (gatherOwners raw keys).steps≤3+keys.length*unit
  induction keys with
  | nil => simp [gatherOwners]
  | cons k ks ih =>
    have l := locate_bound k raw
    cases e : (locate k raw).result with
    | none =>
      have h : (gatherOwners raw (k::ks)).steps=(locate k raw).steps+7 := by
        simp only [gatherOwners,paidOwnerLookup,e]
      have cap : (locate k raw).steps+7≤unit := by dsimp [unit]; omega
      rw [h,List.length_cons,Nat.add_mul,one_mul]
      omega
    | some value =>
      obtain ⟨row,mem,same⟩ := locate_returns_actual_row k raw value e
      have cp := actual_gate_roster_payload_cap row.payload (fit row mem)
      have p : ownerDataFee value≤ownerDataCap gate key prec page d := same ▸ cp
      have h : (gatherOwners raw (k::ks)).steps=(locate k raw).steps+ownerDataFee value+4+
          (gatherOwners raw ks).steps+4 := by
        simp only [gatherOwners,paid_owner_lookup_exact raw k value e]
      have cap : (locate k raw).steps+ownerDataFee value+8≤unit := by dsimp [unit]; omega
      rw [h,List.length_cons,Nat.add_mul,one_mul]
      omega

theorem actual_born_owner_copy_cap {gate key prec page : ℕ}
    (stamp : Stamp key prec) (keys : List (Word page)) (d : ℕ) :
    (writeFreshOwners (gate:=gate) stamp keys).steps≤3+keys.length*
        (ownerDataCap gate key prec page d+4) := by
  rw [write_fresh_owners_exact]
  dsimp only
  apply Nat.add_le_add_left
  apply sum_map_cap
  intro k _
  apply Nat.add_le_add_right
  apply actual_gate_roster_payload_cap
  intro g h
  cases h

theorem actual_tagged_owner_copy_cap {own page : ℕ}
    (rows : List (Word own)) (cols : List (Word page)) :
    (tagOwnerWords rows cols).steps≤10+(rows.length+cols.length)*
      (4*(own+page)+6*(1+(own+page))+14) := by
  let tagL := fun x : Word own => writeTaggedName (page:=page) (.inl x)
  let tagR := fun x : Word page => writeTaggedName (own:=own) (.inr x)
  let L := emitRows tagL rows
  let R := emitRows tagR cols
  let U := 4*(own+page)+6*(1+(own+page))+11
  have hcL (x : Word own) : (tagL x).steps+4≤U := by
    dsimp only [tagL]
    rw [actual_tagged_write_exact]
    dsimp only [U,tagFieldFee]
    omega
  have hcR (x : Word page) : (tagR x).steps+4≤U := by
    dsimp only [tagR]
    rw [actual_tagged_write_exact]
    dsimp only [U,tagFieldFee]
    omega
  have bL : L.steps≤2+rows.length*U := (emitted_rows_exact tagL rows).2.trans_le
    (Nat.add_le_add_left (sum_map_cap rows (fun x=>(tagL x).steps+4) U (fun x _=>hcL x)) _)
  have bR : R.steps≤2+cols.length*U := (emitted_rows_exact tagR cols).2.trans_le
    (Nat.add_le_add_left (sum_map_cap cols (fun x=>(tagR x).steps+4) U (fun x _=>hcR x)) _)
  have len : L.result.length=rows.length := by rw [(emitted_rows_exact tagL rows).1,List.length_map]
  change L.steps+R.steps+(prependRows R.result L.result).steps+4≤_
  rw [prepend_rows_exact]
  dsimp only
  rw [len]
  calc
    _ ≤ (2+rows.length*U)+(2+cols.length*U)+(3*rows.length+2)+4 := by omega
    _ ≤ _ := by
      change _≤10+(rows.length+cols.length)*(U+3)
      rw [Nat.mul_add (rows.length+cols.length) U 3,
        Nat.add_mul rows.length cols.length U, Nat.add_mul rows.length cols.length 3,
        Nat.mul_comm rows.length 3]
      omega

#print axioms actual_owner_lookup_scan_cap
#print axioms actual_born_owner_copy_cap
#print axioms actual_tagged_owner_copy_cap
end J6R114RetainedScopeTariff
