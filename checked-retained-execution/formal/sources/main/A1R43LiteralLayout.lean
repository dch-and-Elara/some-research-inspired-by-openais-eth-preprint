import A1R43LiteralGraph
import A1R43LiteralPairs
import J6R10RepackRounded

set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 12500000
set_option maxRecDepth 1500

/-! Relative to the simulated incidence class-load capacity, build the
entire real packed host, including every dummy row and column. The
complete physical chart is filled, so loads are exactly equal in all
ordered classes and the minimum rounded packet count is verified. -/
namespace A1R43Literal
open scoped Classical BigOperators
open P11FullPacking J6R10Repack
noncomputable section

variable {V : Type}
variable (F : Finset (V×V))
variable {a b : ℕ}

def simulatedCell (r : F→Fin a→Sym) (c : V→Fin a→Sym)
    (u : Occ F) : Cell (Fin a) Sym :=
  fun i=>(r u.1 i,c (endpoint F u) i)

structure PairPlan (a b : ℕ) where
  shared : Sym
  row : F→Fin a→Sym
  col : V→Fin a→Sym
  capacity : ∀ c, Nat.card (Fiber (simulatedCell F row col) c) ≤ b*2^a

variable (W : PairPlan F a b)

def shortSeat : Occ F ↪ Physical a b Sym :=
  seatReal (zeroMask a b) (simulatedCell F W.row W.col) W.capacity (fun _=>Equiv.refl _)

def pairSeat : Occ F × Bool ↪ Physical (a+1) b Sym where
  toFun z := doublePhysical W.shared (shortSeat F W z.1) z.2
  inj' := by
    intro x y e
    have h : (shortSeat F W x.1,x.2)=(shortSeat F W y.1,y.2) :=
      doublePhysical_injective (a:=a) (b:=b) W.shared e
    exact Prod.ext ((shortSeat F W).injective (congrArg (fun z : Physical a b Sym×Bool=>z.1) h))
      (congrArg (fun z : Physical a b Sym×Bool=>z.2) h)

theorem pairSeat_cell (u : Occ F) (right : Bool) :
    physicalCell (zeroMask (a+1) b) (pairSeat F W (u,right)) =
      coldExtend W.shared (simulatedCell F W.row W.col u) := by
  change physicalCell (zeroMask (a+1) b) (doublePhysical W.shared (shortSeat F W u) right)=_
  rw [physicalCell_double,shortSeat,seatReal_preserves]

abbrev Spare := ((Set.range (pairSeat F W))ᶜ : Set (Physical (a+1) b Sym))

def fullSeat : Wire F (Spare F W) ≃ Physical (a+1) b Sym :=
  (Equiv.sumCongr (Equiv.ofInjective (pairSeat F W) (pairSeat F W).injective)
    (Equiv.refl _)).trans (Equiv.Set.sumCompl (Set.range (pairSeat F W)))

theorem fullSeat_pair (z : Occ F×Bool) : fullSeat F W (.inl z)=pairSeat F W z := rfl

theorem fullSeat_fill (z : Spare F W) : fullSeat F W (.inr z)=z.val := rfl

def rowWord : Row F (Spare F W)→Fin (a+1)→Sym
  | .inl e=>Fin.cases W.shared (W.row e)
  | .inr (.inl u)=>Fin.cases W.shared (W.row u.1)
  | .inr (.inr z)=>fun i=>(physicalCell (zeroMask (a+1) b) z.val i).1

def colWord : Col F (Spare F W)→Fin (a+1)→Sym
  | .inl v=>Fin.cases W.shared (W.col v)
  | .inr (.inl u)=>Fin.cases W.shared (W.col (endpoint F u))
  | .inr (.inr z)=>fun i=>(physicalCell (zeroMask (a+1) b) z.val i).2

local notation "N" => network F (Spare F W)

theorem fullSeat_cell (w : Wire F (Spare F W)) :
    physicalCell (zeroMask (a+1) b) (fullSeat F W w) =
      declaredCell N (rowWord F W) (colWord F W) w := by
  rcases w with ⟨u,d⟩|z
  · rw [fullSeat_pair,pairSeat_cell]
    cases d <;> funext i <;> cases i using Fin.cases <;> rfl
  · funext i
    exact Prod.eta _

theorem full_wire_count :
    Nat.card (Wire F (Spare F W)) = Nat.card (Cell (Fin (a+1)) Sym)*(b*2^(a+1)) := by
  rw [Nat.card_congr (fullSeat F W),Nat.card_prod,Nat.card_fin,total_slots (zeroMask (a+1) b)]

def fullPacking : PhysicalPacking N (a+1) Sym where
  rowLabel := rowWord F W
  colLabel := colWord F W
  copies := b
  mask := zeroMask (a+1) b
  seat := (fullSeat F W).toEmbedding
  exactCell := fullSeat_cell F W
  paddedBudget := by rw [← full_wire_count F W]; omega

theorem full_seat_predecessor (u : Occ F) :
    ((fullPacking F W).seat (oddWire F (Spare F W) u)).1 =
      ((fullPacking F W).seat (evenWire F (Spare F W) u)).1 ∧
    ((fullPacking F W).seat (evenWire F (Spare F W) u)).2.val+1 =
      ((fullPacking F W).seat (oddWire F (Spare F W) u)).2.val :=
  doublePhysical_step W.shared (shortSeat F W u)

def cellSeat (c : Cell (Fin (a+1)) Sym) :
    Fiber (declaredCell N (rowWord F W) (colWord F W)) c ≃ Fin (b*2^(a+1)) := by
  let e := (fullSeat F W).trans (fullSlotChart (zeroMask (a+1) b))
  have cell_eq (w : Wire F (Spare F W)) :
      (e w).1 = declaredCell N (rowWord F W) (colWord F W) w := by
    rw [←fullSeat_cell F W w]
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
    Nat.card (Fiber (declaredCell N (fullPacking F W).rowLabel (fullPacking F W).colLabel) c)
      = b*2^(a+1) := by
  change Nat.card (Fiber (declaredCell N (rowWord F W) (colWord F W)) c) = _
  rw [Nat.card_congr (cellSeat F W c),Nat.card_fin]

theorem full_minimum_rounded :
    (fullPacking F W).copies =
      ceilCopies (2^(a+1))
        (maxFiber (declaredCell N (fullPacking F W).rowLabel (fullPacking F W).colLabel)) := by
  obtain ⟨c,hc⟩ := attained_max
    (declaredCell N (fullPacking F W).rowLabel (fullPacking F W).colLabel)
  rw [←hc,full_cell_load,ceilCopies]
  have hp : 0 < (2:ℕ)^(a+1) := pow_pos (by decide) _
  change b = (b*2^(a+1))/2^(a+1) + if (b*2^(a+1))%2^(a+1)=0 then 0 else 1
  rw [Nat.mul_div_cancel b hp,Nat.mul_mod_left,if_pos rfl,Nat.add_zero]

theorem full_collision_zero :
    varianceScore (declaredCell N (fullPacking F W).rowLabel (fullPacking F W).colLabel)=0 := by
  have D : 0 < (Nat.card (Cell (Fin (a+1)) Sym):ℚ) := by
    rw [total_cells]
    positivity
  have hEq : (Nat.card (Wire F (Spare F W)):ℚ) =
      Nat.card (Cell (Fin (a+1)) Sym) * ((b*2^(a+1):ℕ):ℚ) := by
    exact_mod_cast full_wire_count F W
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
end A1R43Literal
