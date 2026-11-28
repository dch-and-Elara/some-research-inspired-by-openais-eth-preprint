import P11FullPackingLaw

namespace P11R12Choice
open scoped Classical BigOperators
open P11FullPacking OuterNodePacking
variable {K W : Type*} [LinearOrder K] [Fintype W] {a b : ℕ}

/-- Original local sample: one mask for the unordered type, then
one whole-cell permutation for each of its ordered orientations. -/
abbrev TypeDraw (b : ℕ) (k : Key (Fin a) K) :=
  Orient k × (Orient k → Equiv.Perm (Fin (b*2^a)))

abbrev Draw (a b : ℕ) (K : Type*) [LinearOrder K] :=
  ∀ k : Key (Fin a) K, TypeDraw b k

omit [Fintype W] in
def masks (ω : Draw a b K) (k : Key (Fin a) K) : Orient k := (ω k).1

omit [Fintype W] in
def orders (ω : Draw a b K) : CellOrder a b K :=
  fun c => (ω (key c)).2 (orientation c)

/-- The actual sampled seat of each real leg, in the full chart including
the padding. No fan-out or independently sampled pair of seats is used. -/
noncomputable def seat (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) : W ↪ Physical a b K :=
  seatReal (commonMask (masks ω)) f cap (orders ω)

theorem actual_cell_seat (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (w : W) :
    (fullSlotChart (commonMask (masks ω))) (seat ω f cap w) =
      (f w, (ω (key (f w))).2 (orientation (f w)) (initialIndex f cap (f w) ⟨w,rfl⟩)) :=
  seatReal_address (commonMask (masks ω)) f cap (orders ω) w

theorem labels_unchanged (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (w : W) :
    physicalCell (commonMask (masks ω)) (seat ω f cap w) = f w :=
  seatReal_preserves (commonMask (masks ω)) f cap (orders ω) w

theorem actual_endpoint_event (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a) (w : W) (right : Bool) :
    (seat ω f cap w).2 = endpointIndex a right ↔
       (ω (key (f w))).2 (orientation (f w)) (initialIndex f cap (f w) ⟨w,rfl⟩) ∈
         endpointAddresses (masks ω) (key (f w)) (orientation (f w)) right :=
  actual_endpoint_address (masks ω) f cap (orders ω) w _ _ (cell_decode _).symm right

noncomputable def picked (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a)
    (side : W → Bool) (k : Key (Fin a) K) : Finset W :=
  Finset.univ.filter fun w => key (f w) = k ∧ (seat ω f cap w).2 = endpointIndex a (side w)

theorem picked_exact (ω : Draw a b K) (f : W → Cell (Fin a) K)
    (cap : ∀ c, Nat.card (RealFiber f c) ≤ b*2^a)
    (side : W → Bool) (k : Key (Fin a) K) (w : W) :
    w ∈ picked ω f cap side k ↔ key (f w) = k ∧
      (ω (key (f w))).2 (orientation (f w)) (initialIndex f cap (f w) ⟨w,rfl⟩) ∈
        endpointAddresses (masks ω) (key (f w)) (orientation (f w)) (side w) := by
  simp only [picked, Finset.mem_filter, Finset.mem_univ,true_and,actual_endpoint_event]

#print axioms actual_cell_seat
#print axioms labels_unchanged
#print axioms actual_endpoint_event
#print axioms picked_exact
end P11R12Choice
