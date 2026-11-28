import J7R13Physical
import J7PrintedParamsGraph

/-! The genuine two-legged old columns, rather than arbitrary pairs of
wire labels, satisfy the P11 common-column and physical cap interfaces. -/
open scoped Classical BigOperators
namespace J7R13
open J7SourceLabels J7PrintedParamsGraph J7ToJ8Layout J7SeatSource J7SeatPacking P11FullPacking
noncomputable section

variable {A Pair G : Type*} [LinearOrder A] [AddCommGroup A] [Fintype A]
variable [Fintype Pair] [Fintype G] {t b : ℕ}

def binaryLegs (Pair G : Type*) :
    Binary Pair G × Bool ↪ Wire Pair (OrdinaryWire Pair G) where
  toFun x := .inr (x,false)
  inj' _ _ h := congrArg Prod.fst (Sum.inr.inj h)

def binaryCell (ends : G × Bool ≃ Pin Pair × Fin 3)
    (z : DState A Pair (OrdinaryRow Pair G) (OldNonPrivate Pair G) t) :
    Binary Pair G × Bool → Cell (Fin (t+1)) A :=
  fun x => wordLabel Prod.fst (column ends cycle) z (binaryLegs Pair G x)

omit [LinearOrder A] [AddCommGroup A] [Fintype A] [Fintype Pair] [Fintype G] in
theorem binary_common_column (ends : G × Bool ≃ Pin Pair × Fin 3)
    (z : DState A Pair (OrdinaryRow Pair G) (OldNonPrivate Pair G) t)
    (c : Binary Pair G) (i : Fin (t+1)) :
    (binaryCell ends z (c,false) i).2 = (binaryCell ends z (c,true) i).2 :=
  same_column_words Prod.fst (column ends cycle) z
    (x:=binaryLegs Pair G (c,false)) (y:=binaryLegs Pair G (c,true))
    (by rcases c with g|⟨p,j⟩ <;> rfl) i

omit [AddCommGroup A] [Fintype Pair] [Fintype G] in
theorem binary_cell_cap (ends : G × Bool ≃ Pin Pair × Fin 3)
    (z : DState A Pair (OrdinaryRow Pair G) (OldNonPrivate Pair G) t)
    (j : Wire Pair (OrdinaryWire Pair G) ↪ Physical (t+1) b A)
    (preserve : ∀ w, physicalCell (balancedMask (t+1) b) (j w) =
      wordLabel Prod.fst (column ends cycle) z w)
    (c : Cell (Fin (t+1)) A) :
    Nat.card {x : Binary Pair G × Bool // binaryCell ends z x = c} ≤ b*2^(t+1) := by
  let m : {x : Binary Pair G × Bool // binaryCell ends z x = c} ↪ SlotFiber (b:=b) c :=
    ⟨fun x => ⟨j (binaryLegs Pair G x.val),(preserve _).trans x.prop⟩,
      fun x y h => Subtype.ext ((binaryLegs Pair G).injective (j.injective (congrArg Subtype.val h)))⟩
  exact (Nat.card_le_card_of_injective m m.injective).trans_eq (card_slots (b:=b) c)

#print axioms binaryLegs
#print axioms binaryCell
#print axioms binary_common_column
#print axioms binary_cell_cap
end
end J7R13
