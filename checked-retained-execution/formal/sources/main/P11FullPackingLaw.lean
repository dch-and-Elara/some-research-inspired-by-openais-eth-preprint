import P11FullPackingPlacement

/-!
Endpoint cardinalities in the same fixed address chart used for the full
cell permutation. Conditioning on its unique eligible orientation, this
instantiates the previously verified single- and double-draw laws.
-/
namespace P11FullPacking
open scoped BigOperators

variable {K : Type*} [LinearOrder K] {a b : ℕ}

noncomputable def endpointAddresses (m : ∀ k : Key (Fin a) K, Orient k)
    (k : Key (Fin a) K) (c : Orient k) (right : Bool) : Finset (Fin (b*2^a)) := by
  classical
  exact Finset.univ.filter fun q =>
    ((addressInCell (b:=b) (commonMask m) k c).symm q).2.val = endpointIndex a right

theorem mem_endpointAddresses (m : ∀ k : Key (Fin a) K, Orient k)
    (k : Key (Fin a) K) (c : Orient k) (right : Bool) (q : Fin (b*2^a)) :
    q ∈ endpointAddresses m k c right ↔
      ((addressInCell (b:=b) (commonMask m) k c).symm q).2.val = endpointIndex a right := by
  classical
  simp [endpointAddresses]

noncomputable def endpointAddressesEquiv (m : ∀ k : Key (Fin a) K, Orient k)
    (k : Key (Fin a) K) (c : Orient k) (right : Bool) :
    ↥(endpointAddresses (b:=b) m k c right) ≃ endSeats (b:=b) m k c right where
  toFun q := ⟨(addressInCell (commonMask m) k c).symm q.val,
    (mem_endpointAddresses m k c right q.val).mp q.prop⟩
  invFun z := ⟨addressInCell (commonMask m) k c z.val,
    (mem_endpointAddresses m k c right _).mpr (by
      rw [Equiv.symm_apply_apply]
      exact z.prop)⟩
  left_inv q := Subtype.ext ((addressInCell (commonMask m) k c).apply_symm_apply q.val)
  right_inv z := Subtype.ext ((addressInCell (commonMask m) k c).symm_apply_apply z.val)

theorem chosen_cell_end_count (m : ∀ k : Key (Fin a) K, Orient k)
    (k : Key (Fin a) K) (right : Bool) :
    (endpointAddresses (b:=b) m k (GuardedPacking.endMask right (m k)) right).card =
      b*2^Nat.card (Hot k) := by
  classical
  rw [← Fintype.card_coe, ← Nat.card_eq_fintype_card, Nat.card_congr (endpointAddressesEquiv ..),
    eligible_end_card]

theorem other_cell_has_no_end (m : ∀ k : Key (Fin a) K, Orient k)
    (k : Key (Fin a) K) (c : Orient k) (right : Bool)
    (hne : GuardedPacking.endMask right (m k) ≠ c) :
    endpointAddresses (b:=b) m k c right = ∅ := by
  apply Finset.eq_empty_iff_forall_notMem.mpr
  intro q hq
  exact (ineligible_end_empty (b:=b) m k c right hne).false
    (endpointAddressesEquiv m k c right ⟨q,hq⟩)

theorem address_unpack_position (m : ∀ k : Key (Fin a) K, Orient k)
    (k : Key (Fin a) K) (c : Orient k) (q : Fin (b*2^a)) :
    ((fullSlotChart (b:=b) (commonMask m)).symm (cell k c,q)).2 =
      ((addressInCell (b:=b) (commonMask m) k c).symm q).2.val := by
  let z := (addressInCell (b:=b) (commonMask m) k c).symm q
  let d : Σ d' : (Σ k' : Key (Fin a) K, Orient k'), TypeCellFiber (b:=b) (commonMask m) d'.1 d'.2 :=
    ⟨⟨k,c⟩,z⟩
  have hh : (fullSlotChart (b:=b) (commonMask m)).symm (cell k c,q) =
      (physicalSplit (b:=b) (commonMask m)).symm d := by
    apply (fullSlotChart (b:=b) (commonMask m)).injective
    rw [Equiv.apply_symm_apply]
    unfold fullSlotChart
    simp only [Equiv.trans_apply, Equiv.apply_symm_apply]
    change (cell k c,q) = (cell k c,addressInCell (commonMask m) k c z)
    rw [(addressInCell (b:=b) (commonMask m) k c).apply_symm_apply]
  exact congrArg Prod.snd hh

/-- Exactly the addressed seats of this cell are the actual occupied
packet endpoints; this uses the same fixed slot chart as seatReal. -/
theorem actual_endpoint_address {W : Type*} [Fintype W]
    (m : ∀ k : Key (Fin a) K, Orient k) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (order : CellOrder a b K)
    (w : W) (k : Key (Fin a) K) (c : Orient k) (hcell : f w=cell k c)
    (right : Bool) :
    (seatReal (commonMask m) f cap order w).2 = endpointIndex a right ↔
    order (f w) (initialIndex f cap (f w) ⟨w,rfl⟩) ∈ endpointAddresses m k c right := by
  rw [mem_endpointAddresses, ← address_unpack_position]
  have hs : seatReal (commonMask m) f cap order w =
      (fullSlotChart (commonMask m)).symm
        (cell k c,order (f w) (initialIndex f cap (f w) ⟨w,rfl⟩)) := by
    apply (fullSlotChart (commonMask m)).injective
    rw [Equiv.apply_symm_apply, seatReal_address]
    exact Prod.ext hcell rfl
  rw [hs]

/-- Same-type, same-cell probability with the source-computed endpoint
count, and the given pair fixed before the full cell permutation. -/
theorem actual_cell_pair_lower (m : ∀ k : Key (Fin a) K, Orient k)
    (k : Key (Fin a) K) (right : Bool) (hb : 0<b) (hH : 1<b*2^a)
    (eligible : Fin (2^Nat.card (Hot k))) (p : RandomEndpoint.DistinctPair (Fin (b*2^a))) :
    let E := endpointAddresses (b:=b) m k (GuardedPacking.endMask right (m k)) right
    (1-1/(b:ℚ))/((2^a:ℕ):ℚ)^2 ≤
      (Nat.card {ω : Fin (2^Nat.card (Hot k)) × Equiv.Perm (Fin (b*2^a)) //
        ω.1=eligible ∧ ω.2 p.val.1∈E ∧ ω.2 p.val.2∈E}:ℚ) /
      (Nat.card (Fin (2^Nat.card (Hot k)) × Equiv.Perm (Fin (b*2^a))):ℚ) := by
  dsimp
  exact P11SourceGeometry.physical_sameType_lower eligible p _ hb (by positivity) hH
    (chosen_cell_end_count m k right)

#print axioms mem_endpointAddresses
#print axioms chosen_cell_end_count
#print axioms other_cell_has_no_end
#print axioms address_unpack_position
#print axioms actual_endpoint_address
#print axioms actual_cell_pair_lower

end P11FullPacking