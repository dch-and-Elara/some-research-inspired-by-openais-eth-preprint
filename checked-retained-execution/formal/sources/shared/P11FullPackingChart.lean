import P11FullPacking
import P11SourceGeometry

/-! Uniform padded load and the complete finite slot address chart. -/
namespace P11FullPacking

open scoped BigOperators
open OuterNodePacking

variable {K : Type*} [LinearOrder K] {a : ℕ}

abbrev Packet (b : ℕ) (k : Key (Fin a) K) := Fin b × Orient k
abbrev Page (a b : ℕ) (K : Type*) [LinearOrder K] :=
  Σ k : Key (Fin a) K, Packet b k
abbrev Physical (a b : ℕ) (K : Type*) [LinearOrder K] := Slot (Page a b K) (2^a)
abbrev MaskFamily (a b : ℕ) (K : Type*) [LinearOrder K] :=
  ∀ k : Key (Fin a) K, Packet b k → Orient k

theorem packet_card (b : ℕ) (k : Key (Fin a) K) :
    Nat.card (Packet b k) = b * 2^Nat.card (Hot k) := by
  rw [Nat.card_prod, Nat.card_fin, Nat.card_fun]
  rw [Nat.card_eq_fintype_card (α:=Bool), Fintype.card_bool]

theorem packet_card_le_padding (b : ℕ) (k : Key (Fin a) K) :
    Nat.card (Packet b k) ≤ b * 2^a := by
  rw [packet_card]
  have h := hot_cold_card k
  exact Nat.mul_le_mul_left b (Nat.pow_le_pow_right (by decide) (by omega))

def physicalCell {b : ℕ} (m : MaskFamily a b K) (z : Physical a b K) : Cell (Fin a) K :=
  cell z.1.1 (slotOrient z.1.1 (m z.1.1 z.1.2) z.2)

abbrev TypeCellFiber {b : ℕ} (m : MaskFamily a b K)
    (k : Key (Fin a) K) (c : Orient k) :=
  Σ p : Packet b k, LocalFiber k (m k p) c

theorem type_cell_card {b : ℕ} (m : MaskFamily a b K) (k : Key (Fin a) K) (c : Orient k) :
    Nat.card (TypeCellFiber m k c) = b * 2^a := by
  classical
  let r := Nat.card (Hot k)
  have hd : r ≤ a := by
    have e := hot_cold_card k
    change r+Nat.card (Cold k)=a at e
    omega
  have hh (p : Packet b k) :
      Fintype.card (LocalFiber k (m k p) c) = 2^(a-r) := by
    rw [← Nat.card_eq_fintype_card]
    exact local_fiber_card k (m k p) c
  rw [Nat.card_eq_fintype_card, Fintype.card_sigma]
  simp only [hh, Finset.sum_const, Finset.card_univ, nsmul_eq_mul]
  rw [← Nat.card_eq_fintype_card, packet_card]
  change b*2^r*2^(a-r) = b*2^a
  rw [mul_assoc, ← pow_add, Nat.add_sub_of_le hd]

private def pairFiberEquiv {P X Y : Type*} (f : P → X → Y) (y : Y) :
    {z : P×X // f z.1 z.2=y} ≃ (Σ p : P, {x : X // f p x=y}) where
  toFun z := ⟨z.val.1,⟨z.val.2,z.prop⟩⟩
  invFun z := ⟨(z.1,z.2.val),z.2.prop⟩
  left_inv := by rintro ⟨⟨p,x⟩,h⟩; rfl
  right_inv := by rintro ⟨p,⟨x,h⟩⟩; rfl

def physicalSplit {b : ℕ} (m : MaskFamily a b K) :
    Physical a b K ≃ (Σ d : (Σ k : Key (Fin a) K, Orient k), TypeCellFiber m d.1 d.2) :=
  (Equiv.sigmaProdDistrib (fun k : Key (Fin a) K => Packet b k) (Fin (2^a))).trans
    ((Equiv.sigmaCongrRight fun k =>
      (Equiv.sigmaFiberEquiv (fun z : Packet b k × Fin (2^a) => slotOrient k (m k z.1) z.2)).symm.trans
        (Equiv.sigmaCongrRight fun c => pairFiberEquiv (fun p x => slotOrient k (m k p) x) c)).trans
      (Equiv.sigmaAssoc (fun k c => TypeCellFiber m k c)).symm)

noncomputable def addressInCell {b : ℕ} (m : MaskFamily a b K)
    (k : Key (Fin a) K) (c : Orient k) : TypeCellFiber m k c ≃ Fin (b*2^a) := by
  classical
  apply Fintype.equivOfCardEq
  rw [← Nat.card_eq_fintype_card, Fintype.card_fin, type_cell_card]

/-- All physical positions, not only the real wires, are enumerated once
in their correct ordered cells, each of size Hpad=bL. -/
noncomputable def fullSlotChart {b : ℕ} (m : MaskFamily a b K) :
    Physical a b K ≃ Cell (Fin a) K × Fin (b*2^a) :=
  (physicalSplit m).trans
    ((Equiv.sigmaCongrRight (fun d => addressInCell m d.1 d.2)).trans
      (Equiv.sigmaEquivProd _ _ |>.trans (Equiv.prodCongr cellChart (Equiv.refl _))))

theorem fullSlotChart_cell {b : ℕ} (m : MaskFamily a b K) (z : Physical a b K) :
    (fullSlotChart m z).1 = physicalCell m z := rfl

/-- Each physical packet contributes L positions and every ordered cell
contributes Hpad positions. This is exactly PL=Hpad*D_arr. -/
theorem total_slots [Fintype K] {b : ℕ} (m : MaskFamily a b K) :
    Nat.card (Page a b K) * 2^a = Nat.card (Cell (Fin a) K) * (b * 2^a) := by
  have h := Nat.card_congr (fullSlotChart m)
  rwa [Nat.card_prod, Nat.card_prod, Nat.card_fin, Nat.card_fin] at h

theorem total_packets [Fintype K] {b : ℕ} (m : MaskFamily a b K) :
    Nat.card (Page a b K) = Nat.card (Cell (Fin a) K) * b := by
  have h := total_slots m
  rw [← mul_assoc] at h
  exact Nat.eq_of_mul_eq_mul_right (by positivity) h

omit [LinearOrder K] in
theorem total_cells [Fintype K] : Nat.card (Cell (Fin a) K) = (Fintype.card K)^(2*a) := by
  classical
  rw [Nat.card_fun, Nat.card_prod, Nat.card_fin, Nat.card_eq_fintype_card (α:=K), pow_mul, pow_two]

def endpointIndex (a : ℕ) (right : Bool) : Fin (2^a) :=
  ⟨GuardedPacking.endpoint (2^a) right, by
    have hp : 0 < (2:ℕ)^a := by positivity
    cases right <;> simp [GuardedPacking.endpoint, hp]⟩

def commonMask {b : ℕ} (m : ∀ k : Key (Fin a) K, Orient k) : MaskFamily a b K :=
  fun k _ => m k

/-- Under the P11 convention, all packets of the type share the same mask.
For the unique eligible ordered cell every packet supplies one end seat,
and no packet supplies an end seat in any other cell. -/
def endSeats {b : ℕ} (m : ∀ k : Key (Fin a) K, Orient k)
    (k : Key (Fin a) K) (c : Orient k) (right : Bool) :=
  {z : TypeCellFiber (b:=b) (commonMask m) k c //
      z.2.val = endpointIndex a right}

def endSeatsEquiv {b : ℕ} (m : ∀ k : Key (Fin a) K, Orient k)
    (k : Key (Fin a) K) (right : Bool) :
    endSeats (b:=b) m k (GuardedPacking.endMask right (m k)) right ≃ Packet b k where
  toFun z := z.val.1
  invFun p := ⟨⟨p,⟨endpointIndex a right,slotOrient_endpoint k (m k) right (endpointIndex a right) rfl⟩⟩,rfl⟩
  left_inv := by
    rintro ⟨⟨p,⟨x,hx⟩⟩,he⟩
    change x = endpointIndex a right at he
    subst x
    rfl
  right_inv := fun _ => rfl

theorem eligible_end_card {b : ℕ} (m : ∀ k : Key (Fin a) K, Orient k)
    (k : Key (Fin a) K) (right : Bool) :
    Nat.card (endSeats (b:=b) m k (GuardedPacking.endMask right (m k)) right)
      = b*2^Nat.card (Hot k) := by
  rw [Nat.card_congr (endSeatsEquiv (b:=b) m k right), packet_card]

theorem ineligible_end_empty {b : ℕ} (m : ∀ k : Key (Fin a) K, Orient k)
    (k : Key (Fin a) K) (c : Orient k) (right : Bool)
    (hc : GuardedPacking.endMask right (m k) ≠ c) :
    IsEmpty (endSeats (b:=b) m k c right) := by
  refine ⟨fun z => hc ?_⟩
  have hz := z.val.2.prop
  change slotOrient k (m k) z.val.2.val = c at hz
  rw [z.prop] at hz
  exact (slotOrient_endpoint k (m k) right (endpointIndex a right) rfl).symm.trans hz

#print axioms packet_card
#print axioms packet_card_le_padding
#print axioms type_cell_card
#print axioms fullSlotChart
#print axioms fullSlotChart_cell
#print axioms total_slots
#print axioms total_packets
#print axioms total_cells
#print axioms eligible_end_card
#print axioms ineligible_end_empty

end P11FullPacking