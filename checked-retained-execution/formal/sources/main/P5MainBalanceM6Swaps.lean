import P5MainBalanceM6Walsh
import P5MainIteratorSourceLayout

/-! The physical swap matrices are the coordinate toggles on the
ordered-cell orbit chart. The weight/complete-swap actions are checked
on the actual measured Walsh vectors. -/
namespace P5MainBalance.M6
open P5MainIterator
open scoped BigOperators Classical

variable {Copy I B : Type*} [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]
abbrev SwapSlot (Copy I B : Type*) [LinearOrder B] := CopiedSlot Copy I B
abbrev Operator (Copy I B : Type*) [LinearOrder B] :=
  Matrix (SwapSlot Copy I B) (SwapSlot Copy I B) ℚ

variable {O J : Type*} [Fintype J] [DecidableEq J]

def flipOne (i : J) (w : J→Bool) (j : J) : Bool := if j=i then !w j else w j

noncomputable def flipAt (i : I) (s : SwapSlot Copy I B) : SwapSlot Copy I B :=
  ⟨s.1,fun j=>if j.val=i then !s.2 j else s.2 j⟩

def flipAll (s : SwapSlot Copy I B) : SwapSlot Copy I B :=
  ⟨s.1,fun j=>!s.2 j⟩

omit [DecidableEq J] in
theorem qWalsh_neg_all (r w : J→Bool) :
    qWalsh r (fun i=>!w i)=(-1:ℚ)^boolWeight r*qWalsh r w := by
  have h (j : J) : (if r j && !w j then (-1:ℚ) else 1)=
      (if r j then -1 else 1)*(if r j && w j then -1 else 1) := by
    cases r j <;> cases w j <;> norm_num
  unfold qWalsh boolWeight
  simp_rw [h,Finset.prod_mul_distrib]
  congr 1
  rw [← Finset.prod_filter]
  simp

omit [Fintype Copy] [Fintype B] in
theorem qRow_flipAll (r s : SwapSlot Copy I B) :
    qOrbitRow CoordFamily r (flipAll s)=(-1:ℚ)^boolWeight r.2*qOrbitRow CoordFamily r s := by
  rcases r with ⟨o,r⟩
  rcases s with ⟨p,s⟩
  by_cases h : o=p
  · subst p
    simpa only [flipAll,qOrbitRow,dif_pos rfl] using qWalsh_neg_all r s
  · simp [flipAll,qOrbitRow,h]

noncomputable def oddAt (r : SwapSlot Copy I B) (i : I) : Bool :=
  if h : (r.1.2 i).val.1 ≠ (r.1.2 i).val.2 then r.2 ⟨i,h⟩ else false

theorem qWalsh_toggle (p : J→Bool) (w : J→Bool) (i : J) :
    qWalsh p (flipOne i w)=(if p i then (-1:ℚ) else 1)*qWalsh p w := by
  have h (j : J) :
      (if p j && flipOne i w j then (-1:ℚ) else 1) =
        (if j=i then (if p i then -1 else 1) else 1) *
          (if p j && w j then -1 else 1) := by
    by_cases hj : j=i
    · subst j
      cases hp : p i <;> cases hw : w i <;> norm_num [flipOne,hp,hw]
    · simp [flipOne,hj]
  unfold qWalsh
  simp_rw [h,Finset.prod_mul_distrib]
  congr 1
  simp

omit [Fintype Copy] [Fintype B] in
theorem qRow_flipAt (r s : SwapSlot Copy I B) (i : I) :
    qOrbitRow CoordFamily r (flipAt i s)=
      (if oddAt r i then (-1:ℚ) else 1)*qOrbitRow CoordFamily r s := by
  rcases r with ⟨o,r⟩
  rcases s with ⟨p,s⟩
  by_cases h : o=p
  · subst p
    by_cases hi : (o.2 i).val.1≠(o.2 i).val.2
    · let j : CoordFamily o := ⟨i,hi⟩
      have H : (fun k : CoordFamily o=>if k.val=i then !s k else s k)=flipOne j s := by
        funext k
        have hK : (k.val=i) ↔ k=j := ⟨fun h=>Subtype.ext (by change k.val=i; exact h),fun h=>congrArg Subtype.val h⟩
        simp [flipOne,hK]
      simpa only [flipAt,qOrbitRow,dif_pos rfl,oddAt,dif_pos hi,H] using qWalsh_toggle r s j
    · have H : (fun k : CoordFamily o=>if k.val=i then !s k else s k)=s := by
        funext k
        have hne : k.val≠i := by intro he; apply hi; simpa only [←he] using k.property
        rw [if_neg hne]
      simp [flipAt,qOrbitRow,oddAt,hi,H]
  · simp [flipAt,qOrbitRow,h]

omit [Fintype Copy] [Fintype B] in
theorem card_oddAt (r : SwapSlot Copy I B) :
    (Finset.univ.filter (fun i=>oddAt r i)).card=boolWeight r.2 := by
  unfold boolWeight
  have hne (i : I) (hi : i∈Finset.univ.filter fun i=>oddAt r i) :
      (r.1.2 i).val.1 ≠ (r.1.2 i).val.2 := by
    by_contra h
    have hn := (Finset.mem_filter.mp hi).2
    simp [oddAt,h] at hn
  refine Finset.card_bij (fun i hi => ⟨i,hne i hi⟩) ?_ ?_ ?_
  · intro i hi
    have hn := (Finset.mem_filter.mp hi).2
    exact Finset.mem_filter.mpr ⟨Finset.mem_univ _,by simpa only [oddAt,dif_pos (hne i hi)] using hn⟩
  · intro i _ j _ h
    exact congrArg Subtype.val h
  · intro j hj
    refine ⟨j.val,Finset.mem_filter.mpr ⟨Finset.mem_univ _,?_⟩,rfl⟩
    simpa only [oddAt,dif_pos j.property] using (Finset.mem_filter.mp hj).2

noncomputable def permMat {Q : Type*} (f : Q→Q) : Matrix Q Q ℚ :=
  Matrix.of fun u v=>if v=f u then 1 else 0

theorem permMat_mulVec {Q : Type*} [Fintype Q] (f : Q→Q) (ζ : Q→ℚ) :
    (permMat f).mulVec ζ=ζ∘f := by
  funext s
  simp [permMat,Matrix.mulVec,dotProduct]

noncomputable def swapMatrix (i : I) : Operator Copy I B := permMat (flipAt i)
noncomputable def fullMatrix : Operator Copy I B := permMat flipAll

noncomputable def weightMatrix : Operator Copy I B :=
  (1/2:ℚ) • ∑ i : I,(1-swapMatrix i)

theorem full_eigen (r : SwapSlot Copy I B) :
    (fullMatrix : Operator Copy I B).mulVec (qOrbitRow CoordFamily r) =
      ((-1:ℚ)^boolWeight r.2) • qOrbitRow CoordFamily r := by
  rw [fullMatrix,permMat_mulVec]
  funext v
  exact qRow_flipAll r v

set_option maxHeartbeats 10000000 in
theorem weight_eigen (r : SwapSlot Copy I B) :
    (weightMatrix : Operator Copy I B).mulVec (qOrbitRow CoordFamily r) =
      (boolWeight r.2:ℚ) • qOrbitRow CoordFamily r := by
  unfold weightMatrix
  rw [Matrix.smul_mulVec,Matrix.sum_mulVec]
  funext v
  simp only [Pi.smul_apply,smul_eq_mul,Finset.sum_apply,Matrix.sub_mulVec,Matrix.one_mulVec,
    swapMatrix,permMat_mulVec,Pi.sub_apply,Function.comp_apply,qRow_flipAt]
  have h : (∑ i : I,(qOrbitRow CoordFamily r v -
      (if oddAt r i then (-1:ℚ) else 1)*qOrbitRow CoordFamily r v)) =
      (∑ i : I,if oddAt r i then (2:ℚ) else 0)*qOrbitRow CoordFamily r v := by
    rw [Finset.sum_mul]
    apply Finset.sum_congr rfl
    intro i _
    cases oddAt r i <;> simp [sub_neg_eq_add,two_mul]
  rw [h,←Finset.sum_filter]
  simp only [Finset.sum_const,nsmul_eq_mul,card_oddAt]
  ring

#print axioms qWalsh_neg_all
#print axioms qRow_flipAll
#print axioms qWalsh_toggle
#print axioms qRow_flipAt
#print axioms card_oddAt
#print axioms permMat_mulVec
#print axioms full_eigen
#print axioms weight_eigen
end P5MainBalance.M6
