import J6R57PublicRequestSuccess

/-! Explicit bounds on the input catalogue alone (not the recursion
behind a successful native query). The exact finite-domain converse
also rules out an even or out-of-range centre at this public layer. -/
namespace J6R57PublicRequest
open scoped Classical
open AOracleMachineTime J6R15ModeCost J6R34RootAtlas J6R52FreshExterior
open J6R54PublicFamily J6R14ZeroMode J6Mesh
set_option autoImplicit false
set_option warningAsError true
set_option maxHeartbeats 11000000
set_option maxRecDepth 3000

theorem printed_positive_odd_domain {tc tj : ℕ} (m n : ℕ) (raw : OccurrenceAddress tc tj) :
    LegalAddress m n raw ↔
      Odd raw.centre.val ∧ raw.centre.val≤2*m+1 ∧ raw.sample.val≤literalDegree m n := by
  constructor
  · rintro ⟨⟨⟨i,j⟩,g⟩,tc,jc,_⟩
    have h : raw.centre.val=2*i.val+1 := tc
    have hi := i.isLt
    have jj := j.isLt
    exact ⟨⟨i.val,h⟩,by omega,by omega⟩
  · rintro ⟨⟨i,hi⟩,tc,jc⟩
    have it : i<m+1 := by omega
    let c : J6Recovery.Addr m := ⟨i,it⟩
    let j : Fin (literalDegree m n+1) := ⟨raw.sample.val,Nat.lt_succ_of_le jc⟩
    let g : Fin 64 := ⟨raw.group.val,val_lt raw.group⟩
    exact ⟨((c,j),g),hi,rfl,rfl⟩

theorem sum_row_fees {A : Type*} (xs : List A) (fee : A→ℕ) (cap : ℕ)
    (fit : ∀ x∈xs,fee x≤cap) :
    (xs.map fee).sum≤xs.length*cap := by
  induction xs with
  | nil => simp
  | cons x xs ih =>
    have h := fit x List.mem_cons_self
    have tail := ih (fun y hy=>fit y (List.mem_cons_of_mem x hy))
    simp only [List.map_cons,List.sum_cons,List.length_cons,Nat.add_mul,Nat.one_mul]
    omega

theorem ordinal_fee_monotone (w : ℕ) : Monotone (ordinalFee w) := by
  intro a b h
  unfold ordinalFee
  exact Nat.add_le_add_left (Nat.mul_le_mul_right (13*w+7) h) _

variable {m n kp tc tj tw edgew : ℕ}
variable (W : Widths m n tc tj tw edgew) (mark : Word kp)

def headRoof (m n tc tj tw : ℕ) :=
  ordinalFee tc (2*m+1)+ordinalFee tj (literalDegree m n)+(2*tc+4*tw+5)+6

def groupRoof (key : ℕ) := 64*(ordinalFee 6 63+6*key+21)

theorem catalogue_construction_roof :
    (emitCatalogue W mark).steps≤
      2+((m+1)*(literalDegree m n+1))*(headRoof m n tc tj tw+203+groupRoof (KeyWidth kp tc tj)) := by
  let groupFees := ((List.finRange 64).map fun g=>ordinalFee 6 g.val+6*KeyWidth kp tc tj+21).sum
  have group : groupFees≤groupRoof (KeyWidth kp tc tj) := by
    have h := sum_row_fees (List.finRange 64)
      (fun g=>ordinalFee 6 g.val+6*KeyWidth kp tc tj+21)
      (ordinalFee 6 63+6*KeyWidth kp tc tj+21) (by
        intro g _
        have p := ordinal_fee_monotone 6 (Nat.le_of_lt_succ g.isLt)
        change ordinalFee 6 g.val+6*KeyWidth kp tc tj+21≤ordinalFee 6 63+6*KeyWidth kp tc tj+21
        omega)
    rw [List.length_finRange] at h
    exact h
  have heads : (orderedHeads m n).length=(m+1)*(literalDegree m n+1) := by
    calc
      _ = (List.finRange (m+1)).length*(List.finRange (literalDegree m n+1)).length :=
        List.length_product _ _
      _ = _ := by simp only [List.length_finRange]
  have bound := sum_row_fees (orderedHeads m n)
    (fun ij=>(prepareHead W ij.1 ij.2).steps+203+groupFees)
    (headRoof m n tc tj tw+203+groupRoof (KeyWidth kp tc tj)) (by
      intro ij _
      change (prepareHead W ij.1 ij.2).steps+203+groupFees≤_
      rw [query_head_exact_fee W ij.1 ij.2,headRoof]
      have t := ij.1.isLt
      have u : index m ij.1≤2*m+1 := by unfold index; omega
      have v := Nat.le_of_lt_succ ij.2.isLt
      have h := ordinal_fee_monotone tc u
      have l := ordinal_fee_monotone tj v
      omega)
  rw [heads] at bound
  rw [(catalogue_exact_order_and_bill W mark).2.2]
  exact Nat.add_le_add_left bound 2

#print axioms printed_positive_odd_domain
#print axioms catalogue_construction_roof
end J6R57PublicRequest
