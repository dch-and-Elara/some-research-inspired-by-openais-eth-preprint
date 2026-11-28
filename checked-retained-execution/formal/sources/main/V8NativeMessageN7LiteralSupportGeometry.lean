import V8NativeMessageN7PublicShift

/-! Same real seat injection as the N7 received slot. There is no
wraparound, no substitute column and no extra real port in padding. -/
namespace V8NativeMessage.N7LiteralSupport
open scoped Classical BigOperators
open P1DyadicGrid P11FullPacking J6R10Repack J6R9PacketScopes
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 6000000

variable {E A B G : Type} [LinearOrder G] [Fintype G] {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G)

def Matches (t : ℤ) (r q : E) : Prop :=
  (P.seat q).1=(P.seat r).1 ∧ ((P.seat q).2.val:ℤ)-(P.seat r).2.val=t

abbrev Matching (t : ℤ) := {x : E×E // Matches P t x.1 x.2}

theorem match_unique_col {t : ℤ} {r q q' : E} (h : Matches P t r q) (h' : Matches P t r q') : q=q' :=
  V8NativeMessage.N7.shifted_col_unique P (P.seat r) q q' h.1 h'.1 h.2 h'.2

theorem match_unique_row {t : ℤ} {r r' q : E} (h : Matches P t r q) (h' : Matches P t r' q) : r=r' := by
  apply P.seat.injective
  refine Prod.ext (h.1.symm.trans h'.1) (Fin.ext ?_)
  have x := h.2
  have y := h'.2
  omega

theorem actual_match_is_group_local (i : Fin a) {t : ℤ} (ht : t≠0)
    (hv : padicValInt 2 t=i.val) {r q : E} (h : Matches P t r q) :
    rowGroup P.mask i (P.seat r)=colGroup P.mask i (P.seat q) := by
  by_contra wrong
  have e : ((P.seat r).1,(P.seat q).2)=P.seat q := Prod.ext h.1.symm rfl
  have same := different_groups_same_bit P.mask (P.seat r).1 i (P.seat r).2 (P.seat q).2
    (fun e0=>wrong (by simpa only [Prod.eta,e] using e0))
  have flip := shifted_bit_flip ht hv h.2
  cases H : (P.seat r).2.val.testBit i.val <;> simp_all

def earlierSlot (t : ℤ) (m : Matching P t) : ℕ :=
  if 0≤t then (P.seat m.val.1).2.val else (P.seat m.val.2).2.val

theorem earlier_slot_lt (t : ℤ) (m : Matching P t) :
    earlierSlot P t m < 2^a-t.natAbs := by
  have row := (P.seat m.val.1).2.isLt
  have col := (P.seat m.val.2).2.isLt
  have Eq := m.property.2
  by_cases s : 0≤t
  · have k : (t.natAbs:ℤ)=t := Int.natAbs_of_nonneg s
    rw [earlierSlot,if_pos s]
    omega
  · have k : (t.natAbs:ℤ)=-t := by
      rw [←Int.natAbs_neg]
      exact Int.natAbs_of_nonneg (by omega)
    rw [earlierSlot,if_neg s]
    omega

def matchEmbedding (t : ℤ) : Matching P t ↪ Page a P.copies G × Fin (2^a-t.natAbs) where
  toFun m := ((P.seat m.val.1).1,⟨earlierSlot P t m,earlier_slot_lt P t m⟩)
  inj' := by
    intro m n same
    have page := congrArg Prod.fst same
    have slot := congrArg (fun x : Page a P.copies G × Fin (2^a-t.natAbs)=>x.2.val) same
    change earlierSlot P t m=earlierSlot P t n at slot
    by_cases s : 0≤t
    · simp only [earlierSlot,if_pos s] at slot
      have E : m.val.1=n.val.1 := P.seat.injective (Prod.ext page (Fin.ext slot))
      apply Subtype.ext
      exact Prod.ext E (match_unique_col P m.property (by rw [E]; exact n.property))
    · simp only [earlierSlot,if_neg s] at slot
      have p' : (P.seat m.val.2).1=(P.seat n.val.2).1 :=
        m.property.1.trans (page.trans n.property.1.symm)
      have E : m.val.2=n.val.2 := P.seat.injective (Prod.ext p' (Fin.ext slot))
      apply Subtype.ext
      exact Prod.ext (match_unique_row P m.property (by rw [E]; exact n.property)) E

theorem actual_matches_at_most_padded_range [Fintype E] (t : ℤ) :
    Nat.card (Matching P t)≤(3*Fintype.card E/2^a)*(2^a-t.natAbs) := by
  have c := Nat.card_le_card_of_injective _ (matchEmbedding P t).injective
  rw [Nat.card_prod,Nat.card_fin] at c
  have cap : Nat.card (Page a P.copies G)≤3*Fintype.card E/2^a := by
    apply (Nat.le_div_iff_mul_le (by positivity)).mpr
    simpa only [Nat.card_eq_fintype_card] using physical_packet_count P
  exact c.trans (Nat.mul_le_mul_right _ cap)

theorem all_required_rows_force_matched_capacity [Fintype E] {U : Type} [Fintype U]
    (pin : U↪E) (t : ℤ) (all : ∀ u,∃ q,Matches P t (pin u) q) :
    Fintype.card U≤(3*Fintype.card E/2^a)*(2^a-t.natAbs) := by
  classical
  choose q fit using all
  let read (u : U) : Matching P t := ⟨(pin u,q u),fit u⟩
  have injection : Function.Injective read := fun _ _ e=>
    pin.injective (congrArg (fun v : Matching P t=>v.val.1) e)
  have card := Nat.card_le_card_of_injective read injection
  rw [Nat.card_eq_fintype_card] at card
  exact card.trans (actual_matches_at_most_padded_range P t)

theorem all_required_columns_force_matched_capacity [Fintype E] {U : Type} [Fintype U]
    (pin : U↪E) (t : ℤ) (all : ∀ u,∃ r,Matches P t r (pin u)) :
    Fintype.card U≤(3*Fintype.card E/2^a)*(2^a-t.natAbs) := by
  classical
  choose r fit using all
  let read (u : U) : Matching P t := ⟨(r u,pin u),fit u⟩
  have injection : Function.Injective read := fun _ _ e=>
    pin.injective (congrArg (fun v : Matching P t=>v.val.2) e)
  have card := Nat.card_le_card_of_injective read injection
  rw [Nat.card_eq_fintype_card] at card
  exact card.trans (actual_matches_at_most_padded_range P t)

end V8NativeMessage.N7LiteralSupport
#print axioms V8NativeMessage.N7LiteralSupport.match_unique_col
#print axioms V8NativeMessage.N7LiteralSupport.match_unique_row
#print axioms V8NativeMessage.N7LiteralSupport.actual_match_is_group_local
#print axioms V8NativeMessage.N7LiteralSupport.earlier_slot_lt
#print axioms V8NativeMessage.N7LiteralSupport.matchEmbedding
#print axioms V8NativeMessage.N7LiteralSupport.actual_matches_at_most_padded_range
#print axioms V8NativeMessage.N7LiteralSupport.all_required_rows_force_matched_capacity
#print axioms V8NativeMessage.N7LiteralSupport.all_required_columns_force_matched_capacity
