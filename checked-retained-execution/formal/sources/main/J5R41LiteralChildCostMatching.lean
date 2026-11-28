import J5R41LiteralChildCostFactors

/-! The J5 boundary words really are the occupied columns reached
at an actual integer shift in the unchanged child. The same
partial matching supplies every row argument in the DP. -/
namespace J5R41LiteralChildCost
open scoped Classical BigOperators Polynomial
open Polynomial P11FullPacking J6R10Repack J6R9Recursive OuterNodePacking
open J6R9PacketScopes J6R9PacketChild J6R9PacketTiles J6R9PacketCoeff J6R10RowAffine
noncomputable section
set_option linter.unusedSectionVars false
set_option maxHeartbeats 2200000

variable {E A B G : Type} [Fintype E] [LinearOrder G] [Fintype G]
variable {a : ℕ} {N : Network E A B}
variable (P : PhysicalPacking N a G) (i : Fin a) (g : G) (t : ℤ)

abbrev Boundary := ↥(matched P i g t)

def shift (r : RowHalf P i g) (q : ColHalf P i g) : Prop :=
  (P.seat r.val).1=(P.seat q.val).1 ∧
    ((P.seat r.val).2.val:ℤ)+t=((P.seat q.val).2.val:ℤ)

theorem shift_unique (r : RowHalf P i g) (q q' : ColHalf P i g)
    (h : shift P i g t r q) (h' : shift P i g t r q') : q=q' := by
  apply Subtype.ext
  apply P.seat.injective
  apply Prod.ext (h.1.symm.trans h'.1)
  apply Fin.ext
  have h₀ := h.2
  have h₁ := h'.2
  omega

theorem slot_of_shift (r : RowHalf P i g) (q : ColHalf P i g)
    (h : shift P i g t r q) : P.seat q.val∈matched P i g t := by
  apply (mem_matchedColumns _ _ _ _ _).2
  refine ⟨Finset.mem_univ _,?_,(P.seat r.val).2,?_,h.2⟩
  · simp only [colReal,decide_eq_true_eq]
    exact ⟨q.val,rfl,q.prop⟩
  · simp only [rowReal,decide_eq_true_eq]
    have e : ((P.seat q.val).1,(P.seat r.val).2)=P.seat r.val :=
      Prod.ext h.1.symm rfl
    rw [e]
    exact ⟨r.val,rfl,r.prop⟩

private theorem column_exists (q : Boundary P i g t) :
    ∃ e : E, P.seat e=q.val ∧ colGroup P.mask i q.val=g := by
  have h := ((mem_matchedColumns _ _ _ _ _).1 q.prop).2.1
  exact of_decide_eq_true h

def boundaryCol (q : Boundary P i g t) : ColHalf P i g :=
  ⟨Classical.choose (column_exists P i g t q),
    (congrArg (colGroup P.mask i) (Classical.choose_spec (column_exists P i g t q)).1).trans
      (Classical.choose_spec (column_exists P i g t q)).2⟩

theorem boundary_column_address (q : Boundary P i g t) :
    P.seat (boundaryCol P i g t q).val=q.val :=
  (Classical.choose_spec (column_exists P i g t q)).1

theorem boundaryCol_injective : Function.Injective (boundaryCol P i g t) := by
  intro x y he
  apply Subtype.ext
  exact (boundary_column_address P i g t x).symm.trans
    ((congrArg (fun q : ColHalf P i g=>P.seat q.val) he).trans (boundary_column_address P i g t y))

def rowLink (r : RowHalf P i g) : Option (Boundary P i g t) :=
  if h : ∃ q : ColHalf P i g,shift P i g t r q then
    some ⟨P.seat (Classical.choose h).val,slot_of_shift P i g t r _ (Classical.choose_spec h)⟩
  else none

theorem link_at_shift (r : RowHalf P i g) (q : ColHalf P i g) (h : shift P i g t r q) :
    rowLink P i g t r=some ⟨P.seat q.val,slot_of_shift P i g t r q h⟩ := by
  have e : ∃ q, shift P i g t r q := ⟨q,h⟩
  rw [rowLink,dif_pos e]
  congr 1
  apply Subtype.ext
  exact congrArg (fun q : ColHalf P i g=>P.seat q.val)
    (shift_unique P i g t r _ q (Classical.choose_spec e) h)

variable {f : ℤ[X]} {ell : ℕ} (p : ℕ) (hnil : (2:Residue f ell p)^p=0)

def centreUnit : Residue f ell p := J6ZeroTransport.reduceAt p hnil (rho a t)

theorem group_base_boundary_wire (v : PhysicalState P i g) (r : RowHalf P i g) :
    groupBase (fun e=>P.seat e) (fun e=>P.seat e) P.mask i t p hnil 0 g v r.val =
      JointContraction.wiredInput (centreUnit (a:=a) t p hnil)
        (fun q=>v.2 (boundaryCol P i g t q)) (rowLink P i g t r) := by
  unfold groupBase
  rw [dif_pos r.prop]
  unfold localValue
  let e : {q : E // colGroup P.mask i (P.seat q)=rowGroup P.mask i (P.seat r.val)} ≃
      ColHalf P i g := Equiv.subtypeEquivRight (fun _=>by rw [r.prop])
  let c := centreUnit (a:=a) t p hnil
  let F := fun q : ColHalf P i g=>if shift P i g t r q then c*bit (Residue f ell p) (v.2 q) else 0
  have value : (∑ q : {q : E // colGroup P.mask i (P.seat q)=rowGroup P.mask i (P.seat r.val)},
       if (P.seat q.val).1=(P.seat r.val).1 then
          (J6R9PacketLocal.W a t (((P.seat q.val).2.val:ℤ)-(P.seat r.val).2.val)).eval₂
             (J6ZeroTransport.reduceAt p hnil) 0 * bit (Residue f ell p) (v.2 ⟨q.val,q.prop.trans r.prop⟩)
       else 0) = ∑ q : ColHalf P i g,F q := by
    refine Fintype.sum_equiv e _ _ (fun q=>?_ )
    dsimp only [e,F]
    change (if (P.seat q.val).1=(P.seat r.val).1 then _ else _)=_
    by_cases hpage : (P.seat q.val).1=(P.seat r.val).1
    · rw [if_pos hpage,literal_W_zero]
      by_cases hd : ((P.seat q.val).2.val:ℤ)-(P.seat r.val).2.val=t
      · have hs : shift P i g t r (e q) := ⟨hpage.symm,by
          change ((P.seat r.val).2.val:ℤ)+t=(P.seat q.val).2.val
          omega⟩
        rw [if_pos hd,if_pos hs]
        rfl
      · have hs : ¬shift P i g t r (e q) := by
          intro hs
          apply hd
          have w := hs.2
          change ((P.seat r.val).2.val:ℤ)+t=(P.seat q.val).2.val at w
          omega
        rw [if_neg hd,if_neg hs,zero_mul]
    · have hs : ¬shift P i g t r (e q) := fun hs=>hpage hs.1.symm
      rw [if_neg hpage,if_neg hs]
  rw [value]
  by_cases h : ∃ q : ColHalf P i g,shift P i g t r q
  · obtain ⟨q,hq⟩ := h
    rw [link_at_shift P i g t r q hq]
    have same : boundaryCol P i g t ⟨P.seat q.val,slot_of_shift P i g t r q hq⟩=q := by
      apply Subtype.ext
      apply P.seat.injective
      exact boundary_column_address P i g t _
    rw [Finset.sum_eq_single q]
    · unfold F
      rw [if_pos hq]
      cases hv : v.2 q <;> simp [JointContraction.wiredInput,same,bit,hv,c]
    · intro q' _ hn
      exact if_neg (fun hd=>hn (shift_unique P i g t r q' q hd hq))
    · simp
  · rw [rowLink,dif_neg h,JointContraction.wiredInput]
    exact Finset.sum_eq_zero (fun q _=>if_neg (fun hq=>h ⟨q,hq⟩))

theorem affine_at_boundary (v : PhysicalState P i g) (r : RowHalf P i g) :
    affineAt (t:=t) P i g p hnil v r =
      JointContraction.literal (v.1 r) (JointContraction.wiredInput (centreUnit (a:=a) t p hnil)
        (fun q=>v.2 (boundaryCol P i g t q)) (rowLink P i g t r)) := by
  unfold affineAt
  rw [group_base_boundary_wire P i g t p hnil]
  rfl

#print axioms shift_unique
#print axioms slot_of_shift
#print axioms boundaryCol_injective
#print axioms link_at_shift
#print axioms group_base_boundary_wire
#print axioms affine_at_boundary
end
end J5R41LiteralChildCost