import P5MainIteratorSource
import P5MainIteratorTrace

/-! Actual integer coordinate width and the finite upper bound for
visit-list size on separately variable-balanced layouts. The bound
counts iterator slots, not unrestricted execution of arithmetic. -/
namespace P5MainIterator
open scoped BigOperators Classical

variable {E V F Copy I B : Type*} [Fintype E] [Fintype V]
  [Fintype Copy] [Fintype I] [Fintype B] [LinearOrder B]

noncomputable def zWalsh {D : Type*} [Fintype D] (a x : D → Bool) : ℤ :=
  ∏ i, if a i && x i then (-1:ℤ) else 1

theorem zWalsh_cast {D : Type*} [Fintype D] (a x : D → Bool) :
    (zWalsh a x:ℚ)=qWalsh a x := by
  unfold zWalsh qWalsh
  rw [Int.cast_prod]
  apply Finset.prod_congr rfl
  intro i _
  by_cases h : (a i && x i)=true <;> simp [h]

theorem zWalsh_abs {D : Type*} [Fintype D] (a x : D → Bool) :
    |zWalsh a x|=1 := by
  unfold zWalsh
  rw [Finset.abs_prod]
  apply Finset.prod_eq_one
  intro i _
  by_cases h : (a i && x i)=true <;> simp [h]

variable {O : Type*} (A : O → Type*) [∀ o, Fintype (A o)]

noncomputable def zOrbitRow (r x : OrbitSlots A) : ℤ :=
  if h : r.1=x.1 then zWalsh r.2 (h.symm ▸ x.2) else 0

theorem zOrbitRow_cast (r x : OrbitSlots A) :
    (zOrbitRow A r x:ℚ)=qOrbitRow A r x := by
  by_cases h : r.1=x.1 <;> simp [zOrbitRow,qOrbitRow,h,zWalsh_cast]

theorem zOrbitRow_abs_le (r x : OrbitSlots A) :
    |zOrbitRow A r x|≤1 := by
  by_cases h : r.1=x.1 <;> simp [zOrbitRow,h,zWalsh_abs]

noncomputable def slotCount (L : SourceLayout E V F Copy I B) : ℕ :=
  ∑ v, (filled L.orbitPlacement v).card

omit [Fintype Copy] [Fintype I] [Fintype B] in
theorem occupied_slots_count (L : SourceLayout E V F Copy I B) :
    slotCount L=Fintype.card E := by
  unfold slotCount
  simp_rw [filled_card]
  change (∑ v : V, ((Finset.univ : Finset E).filter (fun e => L.placement.owner e=v)).card) = _
  have h := Finset.sum_card_fiberwise_eq_card_filter (Finset.univ : Finset E)
    (Finset.univ : Finset V) L.placement.owner
  simpa only [Finset.mem_univ,Finset.filter_true,Finset.card_univ] using h

noncomputable def integerCoordinate (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B)
    (t : I) (x : V→Bool) (g : B)
    (r : Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep) : ℤ :=
  ∑ v, ∑ s∈filled L.orbitPlacement v,
    if L.a v t=g ∧ x v = true then zOrbitRow CoordFamily r.val s else 0

theorem integerCoordinate_cast (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B)
    (t : I) (x : V→Bool) (g : B)
    (r : Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep) :
    (integerCoordinate keep L t x g r:ℚ)=sourceTuple keep L t x g r := by
  unfold integerCoordinate sourceTuple exceptionalMatrix
  rw [Int.cast_sum,Matrix.mulVec,dotProduct]
  apply Finset.sum_congr rfl
  intro v _
  rw [Int.cast_sum,rawMeasurement_apply,Finset.sum_mul]
  apply Finset.sum_congr rfl
  intro s _
  by_cases h : L.a v t=g <;> cases x v <;>
    simp [h,BooleanMeasurement.bit,zOrbitRow_cast]

omit [Fintype Copy] [Fintype B] in
theorem integerCoordinate_abs_le (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B)
    (t : I) (x : V→Bool) (g : B)
    (r : Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep) :
    |integerCoordinate keep L t x g r|≤(Fintype.card E:ℤ) := by
  rw [←occupied_slots_count L]
  unfold integerCoordinate slotCount
  rw [Nat.cast_sum]
  refine (Finset.abs_sum_le_sum_abs _ _).trans (Finset.sum_le_sum (fun v _ => ?_))
  refine (Finset.abs_sum_le_sum_abs _ _).trans ?_
  calc
    _ ≤ ∑ _s∈filled L.orbitPlacement v,(1:ℤ) := by
      apply Finset.sum_le_sum
      intro s _
      split
      · exact zOrbitRow_abs_le _ _ _
      · norm_num
    _ = _ := by simp

def signedCode (M : ℕ) (z : ℤ) (hz : |z|≤(M:ℤ)) : Fin (2*M+1) :=
  ⟨(z+(M:ℤ)).toNat, by
    have h := abs_le.mp hz
    omega⟩

theorem signedCode_inj (M : ℕ) (z w : ℤ) (hz : |z|≤(M:ℤ)) (hw : |w|≤(M:ℤ))
    (he : signedCode M z hz=signedCode M w hw) : z=w := by
  have h := congrArg Fin.val he
  change (z+(M:ℤ)).toNat=(w+(M:ℤ)).toNat at h
  have hz' := (abs_le.mp hz).1
  have hw' := (abs_le.mp hw).1
  omega

noncomputable def boxedTuple (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B)
    (t : I) (x : V→Bool) (g : B)
    (r : Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep) :
    Fin (2*Fintype.card E+1) :=
  signedCode _ (integerCoordinate keep L t x g r) (integerCoordinate_abs_le keep L t x g r)

theorem actual_attained_upper (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B) (t : I) :
    (Set.range (sourceTuple keep L t)).ncard ≤
      (2*Fintype.card E+1)^(Fintype.card B *
        Fintype.card (Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep)) := by
  let S := Set.range (sourceTuple keep L t)
  let X := Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep
  letI : Fintype S := (Set.finite_range _).fintype
  let f : S → B → X → Fin (2*Fintype.card E+1) :=
    fun y => boxedTuple keep L t (Classical.choose y.property)
  have hi : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    rw [←Classical.choose_spec y.property,←Classical.choose_spec z.property]
    funext g r
    rw [←integerCoordinate_cast,←integerCoordinate_cast]
    exact congrArg (fun a : ℤ => (a:ℚ))
      (signedCode_inj _ _ _ _ _ (congrFun (congrFun he g) r))
  have h := Fintype.card_le_of_injective f hi
  change S.ncard≤_
  rw [Set.ncard_eq_toFinset_card',Set.toFinset_card]
  simpa only [Fintype.card_fun,Fintype.card_fin,←pow_mul,Nat.mul_comm] using h

set_option maxHeartbeats 2400000 in
theorem actual_balanced_iterator_upper (keep : ℕ → Prop) (L : SourceLayout E V F Copy I B)
    (q b : ℕ) (hb : ∀ t g,Fintype.card {v : V // L.a v t=g}≤b) :
    (∑ t : I, ((TaylorList V q).card * (Set.range (sourceTuple keep L t)).ncard *
      ∑ g : B,2^Fintype.card {v : V // L.a v t=g})) ≤
      Fintype.card I * (TaylorList V q).card *
      (2*Fintype.card E+1)^(Fintype.card B *
        Fintype.card (Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep)) *
      Fintype.card B * 2^b := by
  let Y := (2*Fintype.card E+1)^(Fintype.card B *
    Fintype.card (Exceptional (CoordFamily (Copy:=Copy) (I:=I) (B:=B)) keep))
  calc
    _ ≤ ∑ _t : I, ((TaylorList V q).card*Y*(Fintype.card B*2^b)) := by
      apply Finset.sum_le_sum
      intro t _
      apply Nat.mul_le_mul (Nat.mul_le_mul_left _ (actual_attained_upper keep L t))
      calc
        _ ≤ ∑ _g : B, 2^b := Finset.sum_le_sum fun g _ => Nat.pow_le_pow_right (by decide) (hb t g)
        _ = _ := by simp
    _ = _ := by simp [Nat.mul_assoc,Y]

#print axioms zWalsh_cast
#print axioms zWalsh_abs
#print axioms occupied_slots_count
#print axioms integerCoordinate_cast
#print axioms integerCoordinate_abs_le
#print axioms signedCode_inj
#print axioms actual_attained_upper
#print axioms actual_balanced_iterator_upper
end P5MainIterator
