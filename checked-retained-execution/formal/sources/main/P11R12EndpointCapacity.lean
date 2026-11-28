import P11R12Coverage

namespace P11R12EndpointCapacity
open scoped Classical BigOperators
open P11FullPacking P11R12Choice OuterNodePacking
variable {K W : Type*} [LinearOrder K] [Fintype W] {a b : ℕ}

omit [Fintype W] in
def packetFiber (k : Key (Fin a) K) :
    {q : Page a b K // q.1 = k} ≃ Packet b k where
  toFun q := q.property ▸ q.val.2
  invFun q := ⟨⟨k,q⟩,rfl⟩
  left_inv q := by rcases q with ⟨⟨k',q⟩,e⟩; dsimp at e; subst k'; rfl
  right_inv _ := rfl

theorem physical_key (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (w : W) :
    (seat ω f cap w).1.1 = key (f w) := by
  have h := congrArg key (labels_unchanged ω f cap w)
  simpa only [physicalCell,key_cell] using h

/-- A selected real leg of a fixed type and fixed orientation-right event
occupies the specified endpoint slot in exactly one physical packet.
Thus the sharp per-type cap is its number of packets, not its cell load
times the number of orientations. -/
theorem picked_le_packet_count (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a)
    (right : Bool) (k : Key (Fin a) K) :
    (picked ω f cap (fun _ => right) k).card ≤ Nat.card (Packet b k) := by
  classical
  let S := picked ω f cap (fun _ => right) k
  let p : S → {q : Page a b K // q.1 = k} := fun w =>
    ⟨(seat ω f cap w.val).1,
      (physical_key ω f cap w.val).trans (Finset.mem_filter.mp w.property).2.1⟩
  have hi : Function.Injective p := by
    intro x y h
    apply Subtype.ext
    apply (seat ω f cap).injective
    have hPage : (seat ω f cap x.val).1 = (seat ω f cap y.val).1 := congrArg Subtype.val h
    have hx : (seat ω f cap x.val).2 = endpointIndex a right := (Finset.mem_filter.mp x.property).2.2
    have hy : (seat ω f cap y.val).2 = endpointIndex a right := (Finset.mem_filter.mp y.property).2.2
    exact Prod.ext hPage (hx.trans hy.symm)
  have h := Fintype.card_le_of_injective ((packetFiber (b:=b) k) ∘ p)
    ((packetFiber k).injective.comp hi)
  rw [Fintype.card_coe, ← Nat.card_eq_fintype_card] at h
  exact h

theorem exact_total_packets [Fintype (Key (Fin a) K)]
    [∀ k : Key (Fin a) K, Fintype (Packet b k)] :
    (∑ k : Key (Fin a) K, Nat.card (Packet b k)) = Nat.card (Page a b K) := by
  simp only [Nat.card_eq_fintype_card, Fintype.card_sigma]

/-- Both deterministic cap hypotheses in the original variance argument. -/
theorem physical_packet_cap (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (k : Key (Fin a) K) (right : Bool) :
    (picked ω f cap (fun _ => right) k).card ≤ Nat.card (Packet b k) ∧
      Nat.card (Packet b k) ≤ b*2^a :=
  ⟨picked_le_packet_count ω f cap right k,packet_card_le_padding b k⟩

#print axioms physical_key
#print axioms picked_le_packet_count
#print axioms exact_total_packets
#print axioms physical_packet_cap
end P11R12EndpointCapacity
