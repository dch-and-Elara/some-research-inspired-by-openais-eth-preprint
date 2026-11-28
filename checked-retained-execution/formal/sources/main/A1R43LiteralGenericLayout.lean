import A1R43LiteralPairs
import J6R10RepackRounded

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12500000
set_option maxRecDepth 1700

/-! Shared A1/A2 physical layout builder. This component constructs
the actual full star host for any bounded simulated bipartite instance;
it takes the smaller-cell load cap, not the final chart or its value. -/
namespace A1R43Literal.General
open scoped Classical BigOperators
open P11FullPacking J6R10Repack
noncomputable section

variable {U A B : Type} [Fintype U] (T : Network U A B)
variable {a b : ℕ}

abbrev SplitWire (U Pad : Type) := (U × Bool) ⊕ Pad
abbrev SplitRow (U A Pad : Type) := A ⊕ (U ⊕ Pad)
abbrev SplitCol (U B Pad : Type) := B ⊕ (U ⊕ Pad)

def evenWire (U Pad : Type) (u : U) : SplitWire U Pad := .inl (u,false)
def oddWire (U Pad : Type) (u : U) : SplitWire U Pad := .inl (u,true)

def splitNetwork (Pad : Type) : Network (SplitWire U Pad) (SplitRow U A Pad) (SplitCol U B Pad) where
  row
    | .inl (u,false) => .inr (.inl u)
    | .inl (u,true) => .inl (T.row u)
    | .inr z => .inr (.inr z)
  col
    | .inl (u,false) => .inl (T.col u)
    | .inl (u,true) => .inr (.inl u)
    | .inr z => .inr (.inr z)

def simulatedCell (r : A→Fin a→Sym) (c : B→Fin a→Sym) (u : U) : Cell (Fin a) Sym :=
  fun i=>(r (T.row u) i,c (T.col u) i)

structure PairPlan (a b : ℕ) where
  shared : Sym
  row : A→Fin a→Sym
  col : B→Fin a→Sym
  capacity : ∀ c, Nat.card (Fiber (simulatedCell T row col) c) ≤ b*2^a

variable (W : PairPlan T a b)

def shortSeat : U ↪ Physical a b Sym :=
  seatReal (zeroMask a b) (simulatedCell T W.row W.col) W.capacity (fun _=>Equiv.refl _)

def pairSeat : U × Bool ↪ Physical (a+1) b Sym where
  toFun z := doublePhysical W.shared (shortSeat T W z.1) z.2
  inj' := by
    intro x y e
    have h : (shortSeat T W x.1,x.2)=(shortSeat T W y.1,y.2) :=
      doublePhysical_injective (a:=a) (b:=b) W.shared e
    exact Prod.ext ((shortSeat T W).injective (congrArg (fun z : Physical a b Sym×Bool=>z.1) h))
      (congrArg (fun z : Physical a b Sym×Bool=>z.2) h)

theorem pairSeat_cell (u : U) (right : Bool) :
    physicalCell (zeroMask (a+1) b) (pairSeat T W (u,right)) =
      coldExtend W.shared (simulatedCell T W.row W.col u) := by
  change physicalCell (zeroMask (a+1) b) (doublePhysical W.shared (shortSeat T W u) right)=_
  rw [physicalCell_double,shortSeat,seatReal_preserves]

abbrev Spare := ((Set.range (pairSeat T W))ᶜ : Set (Physical (a+1) b Sym))

def fullSeat : SplitWire U (Spare T W) ≃ Physical (a+1) b Sym :=
  (Equiv.sumCongr (Equiv.ofInjective (pairSeat T W) (pairSeat T W).injective)
    (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range (pairSeat T W)))

theorem fullSeat_pair (z : U×Bool) : fullSeat T W (.inl z)=pairSeat T W z := rfl

theorem fullSeat_fill (z : Spare T W) : fullSeat T W (.inr z)=z.val := rfl

def rowWord : SplitRow U A (Spare T W)→Fin (a+1)→Sym
  | .inl e=>Fin.cases W.shared (W.row e)
  | .inr (.inl u)=>Fin.cases W.shared (W.row (T.row u))
  | .inr (.inr z)=>fun i=>(physicalCell (zeroMask (a+1) b) z.val i).1

def colWord : SplitCol U B (Spare T W)→Fin (a+1)→Sym
  | .inl v=>Fin.cases W.shared (W.col v)
  | .inr (.inl u)=>Fin.cases W.shared (W.col (T.col u))
  | .inr (.inr z)=>fun i=>(physicalCell (zeroMask (a+1) b) z.val i).2

local notation "N" => splitNetwork T (Spare T W)

theorem fullSeat_cell (w : SplitWire U (Spare T W)) :
    physicalCell (zeroMask (a+1) b) (fullSeat T W w) =
      declaredCell N (rowWord T W) (colWord T W) w := by
  rcases w with ⟨u,d⟩|z
  · rw [fullSeat_pair,pairSeat_cell]
    cases d <;> funext i <;> cases i using Fin.cases <;> rfl
  · funext i
    exact Prod.eta _

theorem full_wire_count :
    Nat.card (SplitWire U (Spare T W)) = Nat.card (Cell (Fin (a+1)) Sym)*(b*2^(a+1)) := by
  rw [Nat.card_congr (fullSeat T W),Nat.card_prod,Nat.card_fin,total_slots (zeroMask (a+1) b)]

def fullPacking : PhysicalPacking N (a+1) Sym where
  rowLabel := rowWord T W
  colLabel := colWord T W
  copies := b
  mask := zeroMask (a+1) b
  seat := (fullSeat T W).toEmbedding
  exactCell := fullSeat_cell T W
  paddedBudget := by rw [← full_wire_count T W]; omega

theorem full_seat_predecessor (u : U) :
    ((fullPacking T W).seat (oddWire U (Spare T W) u)).1 =
      ((fullPacking T W).seat (evenWire U (Spare T W) u)).1 ∧
    ((fullPacking T W).seat (evenWire U (Spare T W) u)).2.val+1 =
      ((fullPacking T W).seat (oddWire U (Spare T W) u)).2.val :=
  doublePhysical_step W.shared (shortSeat T W u)

def cellSeat (c : Cell (Fin (a+1)) Sym) :
    Fiber (declaredCell N (rowWord T W) (colWord T W)) c ≃ Fin (b*2^(a+1)) := by
  let e := (fullSeat T W).trans (fullSlotChart (zeroMask (a+1) b))
  have cell_eq (w : SplitWire U (Spare T W)) :
      (e w).1 = declaredCell N (rowWord T W) (colWord T W) w := by
    rw [←fullSeat_cell T W w]
    rfl
  refine {
    toFun := fun w=>(e w.val).2
    invFun := fun j=>⟨e.symm (c,j),?_⟩
    left_inv := ?_
    right_inv := ?_ }
  · rw [← cell_eq,e.apply_symm_apply]
  · intro w
    apply Subtype.ext
    apply e.injective
    rw [e.apply_symm_apply]
    exact Prod.ext (w.property.symm.trans (cell_eq w.val).symm) rfl
  · intro j
    exact congrArg Prod.snd (e.apply_symm_apply (c,j))

theorem full_cell_load (c : Cell (Fin (a+1)) Sym) :
    Nat.card (Fiber (declaredCell N (fullPacking T W).rowLabel (fullPacking T W).colLabel) c)
      = b*2^(a+1) := by
  change Nat.card (Fiber (declaredCell N (rowWord T W) (colWord T W)) c) = _
  rw [Nat.card_congr (cellSeat T W c),Nat.card_fin]

theorem full_minimum_rounded :
    (fullPacking T W).copies =
      ceilCopies (2^(a+1))
        (maxFiber (declaredCell N (fullPacking T W).rowLabel (fullPacking T W).colLabel)) := by
  obtain ⟨c,hc⟩ := attained_max
    (declaredCell N (fullPacking T W).rowLabel (fullPacking T W).colLabel)
  rw [←hc,full_cell_load,ceilCopies]
  have hp : 0 < (2:ℕ)^(a+1) := pow_pos (by decide) _
  change b = (b*2^(a+1))/2^(a+1) + if (b*2^(a+1))%2^(a+1)=0 then 0 else 1
  rw [Nat.mul_div_cancel b hp,Nat.mul_mod_left,if_pos rfl,Nat.add_zero]

theorem full_collision_zero :
    varianceScore (declaredCell N (fullPacking T W).rowLabel (fullPacking T W).colLabel)=0 := by
  have D : 0 < (Nat.card (Cell (Fin (a+1)) Sym):ℚ) := by
    rw [total_cells]
    positivity
  have hEq : (Nat.card (SplitWire U (Spare T W)):ℚ) =
      Nat.card (Cell (Fin (a+1)) Sym) * ((b*2^(a+1):ℕ):ℚ) := by
    exact_mod_cast full_wire_count T W
  unfold varianceScore
  simp only [full_cell_load,hEq,mul_comm (Nat.card (Cell (Fin (a+1)) Sym):ℚ),
    mul_div_cancel_right₀ _ D.ne',sub_self,zero_pow (by decide : (2:ℕ)≠0),Finset.sum_const_zero]

#print axioms pairSeat_cell
#print axioms fullSeat_cell
#print axioms full_wire_count
#print axioms full_seat_predecessor
#print axioms full_cell_load
#print axioms full_minimum_rounded
#print axioms full_collision_zero
end
end A1R43Literal.General
