import J6R14LayoutCostUnique

/-! Literal rank arithmetic for the planted equal-word template.
Consecutive ranks p*L through p*L+L-1 occupy exactly page p,
slots 0,...,L-1 in numeric order; arbitrary source tie-breaks are
not required to agree with this chosen ordering. -/
namespace J6R14LayoutCost
open AOracleMachineTime AOracleMachineTimeTape P11FullPacking

def diagonalCell {a : ℕ} (w : Fin a→Fin 64) : Cell (Fin a) (Fin 64) :=
  fun i => (w i,w i)

theorem diagonal_marks {a : ℕ} (w : Fin a→Fin 64) :
    marksOf (diagonalCell w)=List.replicate a (false,false) := by
  simp [marksOf,diagonalCell,List.ofFn_const]

theorem cold_slot (a : ℕ) (r : List Bool) (h : a≤r.length) :
    (seatWords (List.replicate a (false,false)) r).result.slot=r.take a := by
  change (weave false Prod.snd (List.replicate a (false,false)) r).result.1=_
  induction a generalizing r with
  | zero => rfl
  | succ a ih =>
    cases r with
    | nil => simp at h
    | cons u us =>
      have hU : a≤us.length := by simpa using h
      simp [List.replicate_succ,weave,ih us hU]

theorem encode_getD (q n j : ℕ) (h : j<q) :
    (encodeBits q n).getD j false=n.testBit j := by
  induction q generalizing n j with
  | zero => omega
  | succ q ih =>
    cases j with
    | zero => simp [encodeBits]
    | succ j =>
      have H : j<q := by omega
      rw [encodeBits,List.getD_cons_succ,Nat.testBit_succ]
      exact ih _ _ H

theorem diagonal_address_exact {a b q : ℕ} (w : Fin a→Fin 64) (r : ℕ)
    (ha : a≤q) (hr : r<2^q) (hP : r<b*2^a) :
    let c := diagonalCell w
    let t := seatWords (marksOf c) (encodeBits q r)
    let hp : bitsValue t.result.page<b :=
      page_in_range (marksOf c) (encodeBits q r) (by rw [marksOf_len,encodeBits_length]; exact ha) b
        (by rw [marksOf_len,encodeBits_exact _ _ hr]; exact hP)
    let p := decodePhysical c t.result hp
    p.2.val=r%2^a ∧ pageNo p=r/2^a := by
  let c := diagonalCell w
  let t := seatWords (marksOf c) (encodeBits q r)
  have hT : (marksOf c).length≤(encodeBits q r).length := by
    rw [marksOf_len,encodeBits_length]
    exact ha
  have hslot : t.result.slot=(encodeBits q r).take a := by
    change (seatWords (marksOf (diagonalCell w)) (encodeBits q r)).result.slot=_
    rw [diagonal_marks]
    exact cold_slot a (encodeBits q r) (by rwa [encodeBits_length])
  have H := (seatWords_exact (marksOf c) (encodeBits q r) hT).2.2.2.2.1
  have hPage : bitsValue t.result.page=r/2^a := by
    change t.result.page=_ at H
    rw [H,marksOf_len,drop_value,encodeBits_exact _ _ hr]
  refine ⟨?_,hPage⟩
  let f : Fin a→Bool := fun j => t.result.slot.getD j.val false
  change ((bitsChart a).symm f).val=_
  let x : Fin (2^a) := ⟨r%2^a,Nat.mod_lt _ (by positivity)⟩
  have Z : (bitsChart a).symm f=x := by
    apply (bitsChart a).injective
    rw [Equiv.apply_symm_apply]
    funext i
    change t.result.slot.getD i.val false=(r%2^a).testBit i.val
    have hi : i.val<a := i.isLt
    have hq : i.val<q := hi.trans_le ha
    rw [hslot,List.getD_eq_getElem?_getD,List.getElem?_take]
    simp only [hi,if_true]
    rw [← List.getD_eq_getElem?_getD,encode_getD _ _ _ hq]
    simp [hi]
  exact congrArg Fin.val Z

theorem diagonal_planted_rank {a b q : ℕ} (w : Fin a→Fin 64) (p j : ℕ)
    (ha : a≤q) (hfit : p*2^a+j<2^q) (hp : p<b) (hj : j<2^a) :
    let r := p*2^a+j
    let c := diagonalCell w
    let t := seatWords (marksOf c) (encodeBits q r)
    let hb : bitsValue t.result.page<b :=
      page_in_range (marksOf c) (encodeBits q r) (by rw [marksOf_len,encodeBits_length]; exact ha) b
        (by
          rw [marksOf_len,encodeBits_exact _ _ hfit]
          exact lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by
            rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hp)))
    let x := decodePhysical c t.result hb
    x.2.val=j ∧ pageNo x=p := by
  have hP : p*2^a+j<b*2^a :=
    lt_of_lt_of_le (Nat.add_lt_add_left hj _) (by
      rw [← Nat.succ_mul]; exact Nat.mul_le_mul_right _ (Nat.succ_le_of_lt hp))
  obtain ⟨H₁,H₂⟩ := diagonal_address_exact w (p*2^a+j) ha hfit hP
  rw [Nat.mul_add_mod_self_right,Nat.mod_eq_of_lt hj] at H₁
  have hdiv : (p*2^a+j)/2^a=p := by
    rw [Nat.mul_comm p,Nat.mul_add_div (by positivity),Nat.div_eq_of_lt hj,Nat.add_zero]
  exact ⟨H₁,H₂.trans hdiv⟩

#print axioms encode_getD
#print axioms diagonal_address_exact
#print axioms diagonal_planted_rank
end J6R14LayoutCost



