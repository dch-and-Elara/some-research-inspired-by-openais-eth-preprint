import P11FullPackingChart

/-!
A real edge has one injective physical seat for both of its ends. A fixed
cell enumeration embeds real wires among the Hpad addresses; composing
with any permutation of the whole padded cell gives the printed ordering
rule (including padding). The location map is not restricted to a
separately chosen tuple of sampled ports.
-/
namespace P11FullPacking

open scoped BigOperators
open OuterNodePacking

variable {W K : Type*} [LinearOrder K] {a b : ℕ}
abbrev RealFiber (f : W → Cell (Fin a) K) (c : Cell (Fin a) K) :=
  {p : W // f p=c}

noncomputable def initialIndex [Fintype W] (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (c : Cell (Fin a) K) :
    RealFiber f c ↪ Fin (b*2^a) := by
  classical
  exact (Fintype.equivFin (RealFiber f c)).toEmbedding.trans
    (Fin.castLEEmb (by rw [← Nat.card_eq_fintype_card]; exact cap c))

abbrev CellOrder (a b : ℕ) (K : Type*) :=
  Cell (Fin a) K → Equiv.Perm (Fin (b*2^a))

noncomputable def seatReal [Fintype W] (m : MaskFamily a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (order : CellOrder a b K) :
    W ↪ Physical a b K :=
  ((Equiv.sigmaFiberEquiv f).symm.toEmbedding.trans
    ((Function.Embedding.refl _).sigmaMap (fun c => (initialIndex f cap c).trans (order c).toEmbedding))).trans
      ((Equiv.sigmaEquivProd _ _).toEmbedding.trans (fullSlotChart m).symm.toEmbedding)

theorem seatReal_address [Fintype W] (m : MaskFamily a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (order : CellOrder a b K) (w : W) :
    fullSlotChart m (seatReal m f cap order w) =
      (f w,order (f w) (initialIndex f cap (f w) ⟨w,rfl⟩)) := by
  change fullSlotChart m ((fullSlotChart m).symm
    (f w,order (f w) (initialIndex f cap (f w) ⟨w,rfl⟩))) = _
  exact Equiv.apply_symm_apply _ _

theorem seatReal_preserves [Fintype W] (m : MaskFamily a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (order : CellOrder a b K) (w : W) :
    physicalCell m (seatReal m f cap order w) = f w := by
  rw [← fullSlotChart_cell, seatReal_address]

theorem seatReal_injective [Fintype W] (m : MaskFamily a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (order : CellOrder a b K) :
    Function.Injective (seatReal m f cap order) :=
  Function.Embedding.injective _

/-- All capacity certificates can be stated on a largest *real* cell
load. Rounding up that load to a whole number of L-slot pages is exact. -/
def ceilCopies (L maxLoad : ℕ) : ℕ :=
  maxLoad/L + if maxLoad%L=0 then 0 else 1

theorem rounded_capacity (L maxLoad : ℕ) (hL : 0<L) :
    maxLoad ≤ ceilCopies L maxLoad * L ∧ ceilCopies L maxLoad * L < maxLoad+L := by
  have hm := Nat.mod_lt maxLoad hL
  have he := Nat.mod_add_div maxLoad L
  unfold ceilCopies
  by_cases h : maxLoad%L=0
  · rw [if_pos h, Nat.add_zero, Nat.mul_comm]
    rw [h, Nat.zero_add] at he
    omega
  · rw [if_neg h, Nat.add_mul, Nat.one_mul, Nat.mul_comm (maxLoad/L) L]
    omega

omit [LinearOrder K] in
theorem padded_real_cap [Fintype W] (f : W → Cell (Fin a) K) (maxLoad : ℕ)
    (load : ∀ c, Nat.card (RealFiber f c) ≤ maxLoad) :
    ∀ c, Nat.card (RealFiber f c) ≤ ceilCopies (2^a) maxLoad * 2^a :=
  fun c => (load c).trans (rounded_capacity _ _ (by positivity)).1

section Owners

variable {E : Type*}

/-- The Boolean predicate marking the exact occupied real slots. Padded
slots acquire neither a real row nor a real column, since each edge's
row and column ends use the same physical position. -/
noncomputable def realSlot (seat : E×Bool ↪ Physical a b K) (z : Physical a b K) : Bool :=
  by classical exact decide (∃ e : E×Bool, seat e=z)

noncomputable def vertexOwner [Nonempty E] (seat : E×Bool ↪ Physical a b K)
    (z : Physical a b K) : E :=
  by
    classical
    exact if h : ∃ e : E×Bool, seat e=z then (Classical.choose h).1 else Classical.arbitrary E

theorem realSlot_iff (seat : E×Bool ↪ Physical a b K) (z : Physical a b K) :
    realSlot seat z = true ↔ ∃ e : E×Bool, seat e=z := by
  simp [realSlot]

theorem realSlot_self (seat : E×Bool ↪ Physical a b K) (e : E×Bool) :
    realSlot seat (seat e) = true :=
  (realSlot_iff seat (seat e)).mpr ⟨e,rfl⟩

theorem owner_of_seat [Nonempty E] (seat : E×Bool ↪ Physical a b K) (e : E×Bool) :
    vertexOwner seat (seat e) = e.1 := by
  have h : ∃ p : E×Bool, seat p=seat e := ⟨e,rfl⟩
  unfold vertexOwner
  rw [dif_pos h]
  exact congrArg Prod.fst (seat.injective (Classical.choose_spec h))

/-- Explicitly instantiate the coverage chart required by P11SourceGeometry.
No other real port of a degree-two equality has been ignored. -/
theorem real_fullPortFiber [Fintype E] [Nonempty E] (seat : E×Bool ↪ Physical a b K) :
    P11SourceGeometry.fullPortFiber Finset.univ (fun e p => seat (e,p))
      (realSlot seat) (vertexOwner seat) := by
  intro e _ z hreal hown
  obtain ⟨p,hp⟩ := (realSlot_iff seat z).mp hreal
  have he : p.1=e := by
    rw [← hown,←hp,owner_of_seat]
  exact ⟨p.2,by rw [← he]; exact hp⟩

/-- For every permutation of the real-and-padding cell addresses, endpoints
are genuine physical seats of the graph and the no-predecessor theorem
applies at *every* nonzero integer shift. -/
theorem real_all_shifts [Fintype E] [Nonempty E] [DecidableEq E]
    [DecidableEq (Page a b K)] (m : MaskFamily a b K)
    (f : E×Bool → Cell (Fin a) K) (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a)
    (order : CellOrder a b K) (t : ℤ) (ht : t≠0) [Fintype K]
    (packets : Finset (Page a b K)) :
    min (P11SourceGeometry.seated Finset.univ
      (fun e p => seatReal m f cap order (e,p)) false).card
      (P11SourceGeometry.seated Finset.univ
        (fun e p => seatReal m f cap order (e,p)) true).card ≤
     (untouched Finset.univ (vertexOwner (seatReal m f cap order))
       (matchedColumns packets (realSlot (seatReal m f cap order))
         (realSlot (seatReal m f cap order)) t)).card := by
  exact P11SourceGeometry.both_endpoint_counts_le_every_shift _ packets
     _ _ _ _ (real_fullPortFiber (seatReal m f cap order)) t ht

end Owners

#print axioms seatReal_address
#print axioms seatReal_preserves
#print axioms seatReal_injective
#print axioms rounded_capacity
#print axioms padded_real_cap
#print axioms realSlot_iff
#print axioms owner_of_seat
#print axioms real_fullPortFiber
#print axioms real_all_shifts

end P11FullPacking