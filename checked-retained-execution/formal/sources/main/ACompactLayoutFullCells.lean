import ACompactLayoutIncidence
import P11FullPackingChart

/-! Connect the explicitly ordered planted diagonal with the complete
source packet geometry. Every physical seat is real; the nonplanted
cells are filled by pairs in one ordered cell, never by mixing labels. -/

namespace ACompactLayout
open P11FullPacking

abbrev Alphabet := Fin 64

def diagonalCell (a : ℕ) : Cell (Fin a) Alphabet := fun _ => (0,0)
def diagonalKey (a : ℕ) : Key (Fin a) Alphabet :=
  ⟨diagonalCell a,fun _ => le_rfl⟩
def constantConvention (a b : ℕ) : MaskFamily a b Alphabet := fun _ _ _ => false

def plantPage (a b : ℕ) (j : Fin b) : Page a b Alphabet :=
  ⟨diagonalKey a,(j,fun _ => false)⟩

def placeDiagonal {a b t pad : ℕ} (eq : 3*t+pad=b*2^a)
    (w : DiagonalWire t pad) : Physical a b Alphabet :=
  let p := diagonalSeat eq w
  (plantPage a b p.1,p.2)

theorem placeDiagonal_injective {a b t pad : ℕ} (eq : 3*t+pad=b*2^a) :
    Function.Injective (placeDiagonal (a:=a) eq) := by
  intro x y h
  apply (diagonalSeat eq).injective
  refine Prod.ext ?_ ?_
  · have he := congrArg (fun p : Physical a b Alphabet => p.1.2.1) h
    exact he
  · have he := congrArg (fun p : Physical a b Alphabet => p.2) h
    exact he

theorem placeDiagonal_cell {a b t pad : ℕ} (eq : 3*t+pad=b*2^a)
    (w : DiagonalWire t pad) :
    physicalCell (constantConvention a b) (placeDiagonal (a:=a) eq w)=diagonalCell a := by
  funext i
  simp [physicalCell,placeDiagonal,plantPage,cell,diagonalKey,diagonalCell]

theorem placeDiagonal_predecessor {a b t pad : ℕ} (eq : 3*t+pad=b*2^a)
    (even : Even ((2:ℕ)^a)) (i : Fin t) :
    AAcquisitionCost.wirePred (Equiv.refl (Physical a b Alphabet))
      (placeDiagonal eq (.inl (i,true))) = some (placeDiagonal eq (.inl (i,false))) := by
  have h := planted_predecessor eq (Nat.pow_pos (by decide)) even i
  have hs := (AAcquisitionCost.wirePred_spec _ _ _).1 h
  apply (AAcquisitionCost.wirePred_spec _ _ _).2
  refine ⟨?_,hs.2⟩
  exact congrArg (plantPage a b) hs.1

abbrev OccupiedCell (a b : ℕ) (c : Cell (Fin a) Alphabet) :=
  {z : Physical a b Alphabet // physicalCell (constantConvention a b) z = c}

noncomputable def fullCellAddress {a b : ℕ} (c : Cell (Fin a) Alphabet) :
    OccupiedCell a b c ≃ Fin (b*2^a) := by
  let f := fullSlotChart (constantConvention a b)
  refine
    { toFun := fun z => (f z.1).2
      invFun := fun i => ⟨f.symm (c,i),?_⟩
      left_inv := ?_
      right_inv := ?_ }
  · rw [← fullSlotChart_cell,Equiv.apply_symm_apply]
  · intro z
    apply Subtype.ext
    apply f.injective
    rw [Equiv.apply_symm_apply]
    have hz : (f z.1).1 = c := (fullSlotChart_cell _ _).trans z.2
    exact Prod.ext hz.symm rfl
  · intro i
    simp

theorem fullCell_exact_load {a b : ℕ} (c : Cell (Fin a) Alphabet) :
    Nat.card (OccupiedCell a b c) = b*2^a := by
  rw [Nat.card_congr (fullCellAddress c),Nat.card_fin]

/-- No padding is left unoccupied in the A4 construction; the source's
same ordered classes all have equal common load. -/
theorem printed_full_padding (w : ℕ) :
    (∀ c : Cell (Fin (exponent w)) Alphabet,
      Nat.card (OccupiedCell (exponent w) (packetCopies w) c) = perCell w) ∧
    Nat.card (Page (exponent w) (packetCopies w) Alphabet) * packetLength w = total w := by
  refine ⟨fun c => (fullCell_exact_load c).trans (common_load w).2.1.symm,?_⟩
  change Nat.card (Page (exponent w) (packetCopies w) Alphabet) * (2^exponent w) = _
  rw [total_slots (constantConvention _ _),total_cells]
  change cells w * (packetCopies w * packetLength w) = total w
  rw [← (common_load w).2.1,(common_load w).1]

/-- An unplanted unary-padding clause uses two positions in exactly the
same ordered cell. Their endpoints can be given one common right label
and one common left label, as required by literal subdivision. -/
noncomputable def pairFill {a b p : ℕ} (c : Cell (Fin a) Alphabet)
    (eq : p*2=b*2^a) : Fin p × Bool ≃ OccupiedCell a b c :=
  ((Equiv.prodCongr (Equiv.refl _) finTwoEquiv.symm).trans finProdFinEquiv).trans
    ((finCongr eq).trans (fullCellAddress c).symm)

theorem pairFill_cell {a b p : ℕ} (c : Cell (Fin a) Alphabet)
    (eq : p*2=b*2^a) (j : Fin p) (v : Bool) :
    physicalCell (constantConvention a b) (pairFill c eq (j,v)).1=c :=
  (pairFill c eq (j,v)).2

theorem fillers_disjoint_from_planted {a b p t pad : ℕ}
    (c : Cell (Fin a) Alphabet) (hc : c ≠ diagonalCell a)
    (eq : p*2=b*2^a) (fit : 3*t+pad=b*2^a)
    (j : Fin p) (v : Bool) (z : DiagonalWire t pad) :
    (pairFill c eq (j,v)).1 ≠ placeDiagonal fit z := by
  intro h
  have h' := congrArg (physicalCell (constantConvention a b)) h
  rw [pairFill_cell,placeDiagonal_cell] at h'
  exact hc h'

#print axioms placeDiagonal_injective
#print axioms placeDiagonal_cell
#print axioms placeDiagonal_predecessor
#print axioms printed_full_padding
#print axioms pairFill_cell
#print axioms fillers_disjoint_from_planted

end ACompactLayout
