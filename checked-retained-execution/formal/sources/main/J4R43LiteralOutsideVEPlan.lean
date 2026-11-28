import J4R43LiteralOutsideVETable

/-! Complete finite order, including the real bucket tables. The proof
checks the width of every intermediate bucket, not just the original
bounded degree. Width remains a condition on the supplied order. -/
namespace J4R43LiteralOutside.VE
open scoped Classical BigOperators
noncomputable section
set_option linter.unusedSectionVars false
set_option linter.unusedSimpArgs false
set_option maxHeartbeats 5500000

variable {V R : Type} [Fintype V] [DecidableEq V] [CommRing R]

inductive LegalOrder (w : ℕ) :
    Finset V→List (Factor V R)→List V→Prop
  | stop (fs) : LegalOrder w ∅ fs []
  | next {active fs order v} (mem : v∈active)
      (width : (bucketScope v fs).card≤w)
      (rest : LegalOrder w (active.erase v) (eliminateStored v fs) order) :
      LegalOrder w active fs (v::order)

def finalFactors (fs : List (Factor V R)) : List V→List (Factor V R)
  | [] => fs
  | v::vs => finalFactors (eliminateStored v fs) vs

def orderCost (fs : List (Factor V R)) : List V→ℕ
  | [] => fs.length
  | v::vs => bucketArithmetic v fs+orderCost (eliminateStored v fs) vs

theorem final_product (fs : List (Factor V R)) :
    activeSum ∅ fs=prodAt fs (fun _=>false) := by
  let z : (∅ : Finset V)→Bool := fun _=>false
  have K (x : (∅ : Finset V)→Bool) : x=z := by
    funext u
    exact (Finset.notMem_empty u.val u.property).elim
  unfold activeSum
  rw [Finset.sum_eq_single z]
  · congr 1
  · exact fun x _ n => (n (K x)).elim
  · intro missing
    exact (missing (Finset.mem_univ z)).elim

theorem actual_order_returns_value {w : ℕ} {active : Finset V} {fs : List (Factor V R)}
    {order : List V} (legal : LegalOrder w active fs order) :
    prodAt (finalFactors fs order) (fun _=>false) = activeSum active fs := by
  induction legal with
  | stop fs => exact (final_product fs).symm
  | @next act fs order v mem width rest ih =>
    change prodAt (finalFactors (eliminateStored v fs) order) (fun _=>false) = _
    rw [ih,stored_elimination_exact]
    exact (active_eliminate_exact act v mem fs).symm

theorem stored_arity (v : V) (fs : List (Factor V R)) :
    (eliminateStored v fs).length≤fs.length+1 := by
  unfold eliminateStored outside
  simp only [List.length_cons]
  exact Nat.succ_le_succ (List.length_filter_le _ _)

theorem actual_order_cost {w : ℕ} {active : Finset V} {fs : List (Factor V R)}
    {order : List V} (legal : LegalOrder w active fs order) :
    orderCost fs order≤
      order.length*2^w*(2*(fs.length+order.length)+1)+fs.length+order.length := by
  induction legal with
  | stop fs => simp [orderCost]
  | @next act fs order v mem width rest ih =>
    let q := (2:ℕ)^w*(2*(fs.length+(order.length+1))+1)
    let new := eliminateStored v fs
    have len : new.length+order.length≤fs.length+(order.length+1) := by
      have r := stored_arity v fs
      change new.length≤fs.length+1 at r
      omega
    have unit : bucketArithmetic v fs≤q := by
      exact (bounded_bucket_arithmetic v fs w width).trans
        (Nat.mul_le_mul_left _ (by omega))
    change orderCost new order≤_ at ih
    have oth : orderCost new order≤order.length*q+fs.length+(order.length+1) := by
      refine ih.trans ?_
      calc
        _ = order.length*2^w*(2*(new.length+order.length)+1) +
            (new.length+order.length) := by simp only [new,Nat.add_assoc]
        _ ≤ order.length*2^w*(2*(fs.length+(order.length+1))+1)
            + (fs.length+(order.length+1)) := by
              refine Nat.add_le_add ?_ len
              apply Nat.mul_le_mul_left
              omega
        _ = _ := by unfold q; ring
    have both := Nat.add_le_add unit oth
    change bucketArithmetic v fs+orderCost new order≤_
    refine both.trans_eq ?_
    simp only [List.length_cons,q]
    ring

#print axioms final_product
#print axioms actual_order_returns_value
#print axioms actual_order_cost
end
end J4R43LiteralOutside.VE

