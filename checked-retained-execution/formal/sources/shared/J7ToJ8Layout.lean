import J7ToJ8Incidence

/-! # Compile the actual J7 seating to the physical J8 contraction layout -/
open scoped BigOperators Classical

namespace J7ToJ8Layout
open J7SourceLabels J7SeatSource J7SeatPacking J7ToJ8Incidence
open J7FullWordCells J7FullWordLaw J7FullWordAssembly P11FullPacking

noncomputable section
set_option maxHeartbeats 1200000

variable {A Pair Row Col W : Type*} [LinearOrder A] {t b : ℕ}

abbrev DState (A Pair Row Col : Type*) (t : ℕ) := State A (Fin t → A) Pair Row Col

def subdivisionHead (z : DState A Pair Row Col t) : Subdivision Pair Row → A
  | .inl (p,s) => (gadget (z (.inl p)).1 s).1
  | .inr r => (z (.inr (.inl r))).1.1

def pinHead (z : DState A Pair Row Col t) (p : Pin Pair) : A := (z (.inl p.1)).1.1

def columnHead (z : DState A Pair Row Col t) : OrdinaryColumn Pair Col → A
  | .inl (p,s) => (gadget (z (.inl p)).1 s).2
  | .inr c => (z (.inr (.inr c))).1.1

omit [LinearOrder A] in
theorem label_head (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (z : DState A Pair Row Col t) (e : Wire Pair W) :
    wordLabel row col z e 0 =
      (subdivisionHead z (rowNode row e), Sum.elim (pinHead z) (columnHead z) (colNode col e)) := by
  unfold wordLabel
  rw [cellChart_head]
  rcases e with ⟨⟨p,s⟩,b⟩ | w
  · cases b <;> simp [fullCell,chosenCell,rowNode,colNode,subdivisionHead,pinHead,columnHead]
  · cases hw : col w with
    | inl p =>
      obtain ⟨q,s⟩ := p
      simp [fullCell,chosenCell,rowNode,colNode,subdivisionHead,columnHead,hw]
    | inr o => simp [fullCell,chosenCell,rowNode,colNode,subdivisionHead,columnHead,hw]

def baseHead (p : Page (t+1) b A) : A × A := P11FullPacking.cell p.1 p.2.2 0

/-- The first coordinate is precisely the packet's even/odd orientation;
equal coordinates introduce no artificial alternation. -/
theorem physical_head (p : Page (t+1) b A) (x : Fin (2^(t+1))) :
    physicalCell (balancedMask (t+1) b) (p,x) 0 =
      if x.val % 2 = 0 then baseHead p else (baseHead p).swap := by
  change P11FullPacking.cell p.1 (slotOrient p.1 p.2.2 x) 0 = _
  by_cases hp : x.val % 2 = 0
  · rw [if_pos hp]
    have hzero : bits (t+1) x 0 = false := Nat.mod_two_eq_zero_iff_testBit_zero.mp hp
    unfold baseHead P11FullPacking.cell
    by_cases he : ((p.1.val 0).1 ≠ (p.1.val 0).2)
    · simp [he,slotOrient,shiftMask,hzero]
    · simp [he]
  · rw [if_neg hp]
    have hp' : x.val % 2 = 1 := by omega
    have hone : bits (t+1) x 0 = true := Nat.mod_two_eq_one_iff_testBit_zero.mp hp'
    unfold baseHead P11FullPacking.cell
    by_cases ht : ((p.1.val 0).1 ≠ (p.1.val 0).2)
    · cases hm : p.2.2 ⟨0,ht⟩ <;> simp [ht,slotOrient,shiftMask,hone,hm,Prod.swap]
    · have ht' : (p.1.val 0).1 = (p.1.val 0).2 := not_not.mp ht
      simp only [dif_neg ht]
      exact Prod.ext ht' ht'.symm

abbrev PhysicalLayout (col : W → OrdinaryColumn Pair Col) (A Row : Type*)
    [LinearOrder A] (t b : ℕ) :=
  J8Physical.Layout (Page (t+1) b A) (Subdivision Pair Row) (Pin Pair)
    (OrdinaryColumn Pair Col) A (Ports col) (2^(t+1))

def physicalLayout (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (two : ∀ v, Nat.card {w : W // row w = v} = 2) (z : DState A Pair Row Col t)
    (seat : Wire Pair W ↪ Physical (t+1) b A)
    (preserves : ∀ w, physicalCell (balancedMask (t+1) b) (seat w) = wordLabel row col z w) :
    PhysicalLayout col A Row t b := by
  let e := rowWire (Pair:=Pair) row two
  let f := colWire col
  have all (w : J8Physical.Wire (Subdivision Pair Row)) :
      (subdivisionHead z w.1, Sum.elim (pinHead z) (columnHead z) (Sum.map id Sigma.fst (f.symm (e w)))) =
      if (seat (e w)).2.val % 2 = 0 then baseHead (seat (e w)).1 else (baseHead (seat (e w)).1).swap := by
    have hp := congrFun (preserves (e w)) 0
    rw [label_head, rowWire_owner row two] at hp
    have hc := colWire_owner col (f.symm (e w))
    change colNode col (f (f.symm (e w))) = _ at hc
    rw [f.apply_symm_apply] at hc
    rw [hc] at hp
    have hhead := physical_head (seat (e w)).1 (seat (e w)).2
    exact hp.symm.trans hhead
  refine
    { seat := e.toEmbedding.trans seat
      column := e.trans f.symm
      rowLabel := subdivisionHead z
      pinLabel := pinHead z
      colLabel := columnHead z
      packetLabels := baseHead
      rowOrientation := fun w => ?_
      columnOrientation := fun w => ?_ }
  · have hh := congrArg Prod.fst (all w)
    change subdivisionHead z w.1 =
      if (seat (e w)).2.val % 2 = 0 then (baseHead (seat (e w)).1).1 else (baseHead (seat (e w)).1).2
    by_cases h : (seat (e w)).2.val % 2 = 0 <;> simpa only [h,if_true,if_false] using hh
  · have hh := congrArg Prod.snd (all w)
    have hleft : (Sum.elim (pinHead z) (fun p : Sigma (Ports col) => columnHead z p.1) (f.symm (e w))) =
        Sum.elim (pinHead z) (columnHead z) (Sum.map id Sigma.fst (f.symm (e w))) := by
      cases f.symm (e w) <;> rfl
    change Sum.elim (pinHead z) (fun p : Sigma (Ports col) => columnHead z p.1) (f.symm (e w)) =
      if (seat (e w)).2.val % 2 = 0 then (baseHead (seat (e w)).1).2 else (baseHead (seat (e w)).1).1
    rw [hleft]
    by_cases h : (seat (e w)).2.val % 2 = 0 <;> simpa only [h,if_true,if_false] using hh

theorem owner_layout (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (two : ∀ v, Nat.card {w : W // row w = v} = 2) (z : DState A Pair Row Col t)
    (seat : Wire Pair W ↪ Physical (t+1) b A)
    (preserves : ∀ w, physicalCell (balancedMask (t+1) b) (seat w) = wordLabel row col z w)
    (w : J8Physical.Wire (Subdivision Pair Row)) :
    J8Physical.colOwner (physicalLayout row col two z seat preserves) w =
      colNode col (rowWire row two w) := by
  unfold J8Physical.colOwner
  have hh := colWire_owner col ((colWire col).symm (rowWire row two w))
  rw [Equiv.apply_symm_apply] at hh
  exact hh.symm

/-- Transport the real endpoint matching from the J7 placement to the
very same wires and vertices used by J8Physical's shift. -/
def endpointLayout (row : W → Row) (col : W → OrdinaryColumn Pair Col)
    (two : ∀ v, Nat.card {w : W // row w = v} = 2) (z : DState A Pair Row Col t)
    (seat : Wire Pair W ↪ Physical (t+1) b A)
    (preserves : ∀ w, physicalCell (balancedMask (t+1) b) (seat w) = wordLabel row col z w)
    (hR : Set.InjOn (rowNode row) {w | isEnd (seat w)})
    (hC : Set.InjOn (colNode col) {w | isEnd (seat w)})
    (hP : ∀ p, ¬ isEnd (seat (pinEmbed Pair W p))) :
    J8Physical.EndpointSeating (physicalLayout row col two z seat preserves) := by
  let e := rowWire (Pair:=Pair) row two
  refine ⟨{w | isEnd (seat (e w))},fun w h => h,?_ ,?_ ,?_⟩
  · intro x hx y hy h
    apply e.injective
    apply hR hx hy
    change rowNode row (rowWire row two x) = rowNode row (rowWire row two y)
    rw [rowWire_owner, rowWire_owner, h]
  · intro x hx y hy h
    apply e.injective
    apply hC hx hy
    rw [owner_layout, owner_layout] at h
    exact h
  · intro x hx
    cases he : (colWire col).symm (e x) with
    | inl p =>
      have hh : e x = pinEmbed Pair W p :=
        ((colWire col).apply_symm_apply (e x)).symm.trans (congrArg (colWire col) he)
      exact (hP p (hh ▸ hx)).elim
    | inr v => exact ⟨v,he⟩

omit [LinearOrder A] in
theorem pin_tie (z : DState A Pair Row Col t) (p : Pair) (s s' : Fin 2) :
    pinHead z (p,s) = pinHead z (p,s') := rfl

#print axioms label_head
#print axioms physical_head
#print axioms physicalLayout
#print axioms endpointLayout
#print axioms pin_tie

end
end J7ToJ8Layout
