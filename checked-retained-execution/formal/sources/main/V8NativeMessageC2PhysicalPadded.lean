import V8NativeMessageC2PhysicalPrinted

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 2600000

/-! Independent strengthening for this count-only graph. The original
legal padded chart's 3M budget already balances the availability
vertices. This does not manufacture a valid packing or prove a uniform
variance statement for a different label choice. -/
namespace V8NativeMessage.C2Physical
open scoped Classical BigOperators
open V8PooledRange V8PooledRange.NativeOrigin V8PooledMenu.FiveCopy V8NativeMessage.Five
open J6R10Repack P11FullPacking
noncomputable section

variable {V E : Type} [Fintype V] [Fintype E] {G : Graph V E} {p : ThreePorts G}

omit [Fintype E] in
theorem switchWire_seat_group (P : Packing G p) (i : Fin (rootA V)) (v : V) (b : Bool) :
    atEnd i false (physicalCell P.mask (P.seat (switchWire (E:=E) v b)))=switchGroup P i v := by
  rw [P.exactCell (switchWire (E:=E) v b)]
  exact switchWire_side P i v b

theorem occupied_side_padded (P : Packing G p) (i : Fin (rootA V)) (g : Fin 64) :
    64*Nat.card (SideWires P i g)≤3*wireSize V := by
  let T := {w : Edge V E // atEnd i false (physicalCell P.mask (P.seat w))=g}
  have hc : Nat.card (SideWires P i g)=Nat.card T := by
    apply Nat.card_congr
    exact Equiv.subtypeEquivRight (fun w => by
      rw [P.exactCell w]
      rfl)
  have h : Nat.card T≤3*wireSize V/64 := by
    have h' := physical_side_cap P (by simp) i false g
    rw [Nat.card_eq_fintype_card (α:=Edge V E),wires_card G p] at h'
    exact h'
  rw [hc]
  apply (Nat.mul_le_mul_left 64 h).trans
  rw [Nat.mul_comm]
  exact Nat.div_mul_le_self _ _

theorem padded_switch_cap (P : Packing G p) (i : Fin (rootA V)) (g : Fin 64) :
    128*Nat.card (Switches P i g)≤3*wireSize V := by
  have h := (Nat.mul_le_mul_left 64 (both_switch_ports P i g)).trans
    (occupied_side_padded P i g)
  simpa only [← Nat.mul_assoc] using h

include p in
omit [Fintype E] in
theorem at_least_two_vertices (hN : 0<Fintype.card V) (hloop : ∀ e, G e false≠G e true) :
    2≤Fintype.card V := by
  letI : Nonempty V := Fintype.card_pos_iff.mp hN
  let v : V := Classical.choice inferInstance
  let e := ((p v).symm 0).val.1
  have hinj : Function.Injective (G e) := by
    intro a b h
    have hne := hloop e
    cases a <;> cases b <;> simp_all
  simpa only [Fintype.card_bool] using Fintype.card_le_of_injective (G e) hinj

theorem balanced_union_padded (P : Packing G p) (i : Fin (rootU V))
    (hloop : ∀ e, G e false≠G e true) :
    ∃ T : Finset (Fin 64), Fintype.card V≤4*min (switchUnion P i T).card
      (Fintype.card V-(switchUnion P i T).card) := by
  let hN := printed_root_has_vertices i
  letI : Nonempty V := Fintype.card_pos_iff.mp hN
  have h2 := at_least_two_vertices (p:=p) hN hloop
  have hcap (g : Fin 64) :
      (SourceDensity.fiberCount (switchGroup P (physIndex i)) g : ℚ) ≤
        (3/4:ℚ)*Fintype.card V := by
    have h := padded_switch_cap P (physIndex i) g
    have hc : Nat.card (Switches P (physIndex i) g)=
        SourceDensity.fiberCount (switchGroup P (physIndex i)) g := by
      rw [Nat.card_eq_fintype_card,Fintype.card_subtype]
      rfl
    have hnat : 4*SourceDensity.fiberCount (switchGroup P (physIndex i)) g≤3*Fintype.card V := by
      rw [hc] at h
      unfold wireSize at h
      omega
    have hcast : 4*(SourceDensity.fiberCount (switchGroup P (physIndex i)) g:ℚ)≤3*Fintype.card V := by
      exact_mod_cast hnat
    linarith only [hcast]
  obtain ⟨T,hT⟩ := BalancedUnion.exists_balanced_vertex_union (switchGroup P (physIndex i)) hcap
  refine ⟨T,?_⟩
  exact_mod_cast (show (Fintype.card V:ℚ)≤
    4*(min (switchUnion P i T).card (Fintype.card V-(switchUnion P i T).card):ℕ) by
      unfold switchUnion
      linarith only [hT])

variable {K : Type*} [Field K] [LinearOrder K] [IsStrictOrderedRing K]

theorem native_cut_from_legal_padded_layout (P : Packing G p) (i : Fin (rootU V)) (γ : K)
    (hγ : 0≤γ) (hE : ExpansionOn G γ) (hloop : ∀ e, G e false≠G e true) :
    Nonempty (NativeCut P i γ) := by
  obtain ⟨T,ht⟩ := balanced_union_padded P i hloop
  exact native_cut_of_balanced P i γ hγ hE hloop T ht

#print axioms switchWire_seat_group
#print axioms occupied_side_padded
#print axioms padded_switch_cap
#print axioms at_least_two_vertices
#print axioms balanced_union_padded
#print axioms native_cut_from_legal_padded_layout
end
end V8NativeMessage.C2Physical
