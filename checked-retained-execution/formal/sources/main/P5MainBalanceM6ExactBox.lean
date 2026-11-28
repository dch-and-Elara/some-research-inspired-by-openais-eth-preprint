import P5MainBalanceM6Scores
import P5MainIteratorBox

/-! Exact original integer measurement box. There are D ordered
cells in one physical copy. A kept row accesses that copy alone;
the unique occupied-seat condition bounds each read by D, not M. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator
open scoped BigOperators Classical

variable {E W F Copy I B : Type*} [Fintype E] [Fintype W] [Fintype Copy]
  [Fintype I] [Fintype B] [LinearOrder B]

noncomputable def sourceLegRead (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (i : I) (g : B) (x : W→Bool) (r : NativeRows keep Copy I B) (e : E) : ℤ :=
  if L.a (L.placement.owner e) i=g ∧ x (L.placement.owner e)=true then
    zOrbitRow CoordFamily r.val (L.orbitPlacement.slot e) else 0

set_option maxHeartbeats 4500000 in
omit [Fintype Copy] [Fintype B] in
theorem integer_coordinate_on_real_legs (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (i : I) (g : B) (x : W→Bool) (r : NativeRows keep Copy I B) :
    integerCoordinate keep L i x g r=∑ e,sourceLegRead keep L i g x r e := by
  unfold integerCoordinate
  calc
    _ = ∑ w : W, ∑ e∈incidences L.orbitPlacement w,sourceLegRead keep L i g x r e := by
      apply Finset.sum_congr rfl
      intro w _
      unfold filled
      rw [Finset.sum_image (fun _ _ _ _ h=>L.orbitPlacement.slot.injective h)]
      apply Finset.sum_congr rfl
      intro e he
      have h : L.placement.owner e=w := (Finset.mem_filter.mp he).2
      simp [sourceLegRead,h]
    _ = _ := Finset.sum_fiberwise (Finset.univ : Finset E) L.orbitPlacement.owner
      (sourceLegRead keep L i g x r)

noncomputable def inCopy (L : SourceLayout E W F Copy I B) (c : Copy) : Finset E :=
  Finset.univ.filter (fun e=>(L.placement.slot e).1=c)

omit [Fintype W] [Fintype Copy] in
theorem copy_incidence_limit (L : SourceLayout E W F Copy I B) (c : Copy) :
    (inCopy L c).card≤Fintype.card (WordCell I B) := by
  let f (e : E) := (L.placement.slot e).2
  have hi : Set.InjOn f (inCopy L c : Set E) := by
    intro e he e' he' hf
    apply L.placement.slot.injective
    have h₁ : (L.placement.slot e).1=c := (Finset.mem_filter.mp he).2
    have h₂ : (L.placement.slot e').1=c := (Finset.mem_filter.mp he').2
    exact Prod.ext (h₁.trans h₂.symm) hf
  rw [←Finset.card_image_of_injOn hi]
  exact Finset.card_le_univ _

omit [Fintype E] [Fintype W] [Fintype Copy] [Fintype B] in
theorem real_leg_off_copy (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (i : I) (g : B) (x : W→Bool) (r : NativeRows keep Copy I B) (e : E)
    (h : (L.placement.slot e).1≠r.val.1.1) :
    sourceLegRead keep L i g x r e=0 := by
  have hOff : r.val.1≠(L.orbitPlacement.slot e).1 := by
    intro he
    have hc : r.val.1.1=(L.placement.slot e).1 := congrArg Prod.fst he
    exact h hc.symm
  unfold sourceLegRead
  simp [zOrbitRow,hOff]

omit [Fintype E] [Fintype W] [Fintype Copy] [Fintype B] in
theorem real_leg_read_abs_le_one (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (i : I) (g : B) (x : W→Bool) (r : NativeRows keep Copy I B) (e : E) :
    |sourceLegRead keep L i g x r e|≤1 := by
  unfold sourceLegRead
  split
  · exact zOrbitRow_abs_le _ _ _
  · norm_num

omit [Fintype Copy] in
theorem integer_coordinate_exact_D (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (i : I) (g : B) (x : W→Bool) (r : NativeRows keep Copy I B) :
    |integerCoordinate keep L i x g r|≤(Fintype.card (WordCell I B):ℤ) := by
  rw [integer_coordinate_on_real_legs]
  have hSum : (∑ e,sourceLegRead keep L i g x r e)=
      ∑ e∈inCopy L r.val.1.1,sourceLegRead keep L i g x r e := by
    symm
    apply Finset.sum_subset (Finset.subset_univ _)
    intro e _ he
    exact real_leg_off_copy keep L i g x r e (fun heq=>he (Finset.mem_filter.mpr ⟨Finset.mem_univ _,heq⟩))
  rw [hSum]
  calc
    _ ≤ ∑ e∈inCopy L r.val.1.1,|sourceLegRead keep L i g x r e| :=
      Finset.abs_sum_le_sum_abs _ _
    _ ≤ ∑ _e∈inCopy L r.val.1.1,(1:ℤ) :=
      Finset.sum_le_sum (fun e _=>real_leg_read_abs_le_one keep L i g x r e)
    _ ≤ _ := by
      simp only [Finset.sum_const,nsmul_eq_mul,mul_one]
      exact_mod_cast copy_incidence_limit L r.val.1.1

noncomputable def exactBox (keep : ℕ→Prop) (_L : SourceLayout E W F Copy I B) : ℕ :=
  (2*Fintype.card (WordCell I B)+1)^
    (Fintype.card B*Fintype.card (NativeRows keep Copy I B))

set_option maxHeartbeats 4800000 in
theorem actualY_card_in_D_box (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B) (i : I) :
    Fintype.card (ActualY keep L i)≤exactBox keep L := by
  let D := Fintype.card (WordCell I B)
  let f : ActualY keep L i→B→NativeRows keep Copy I B→Fin (2*D+1) :=
    fun y g r=>signedCode D (integerCoordinate keep L i (fibreRep keep L i y) g r)
      (integer_coordinate_exact_D keep L i g _ r)
  have hi : Function.Injective f := by
    intro y z he
    apply Subtype.ext
    rw [←fibreRep_exact keep L i y,←fibreRep_exact keep L i z]
    funext g r
    rw [←integerCoordinate_cast,←integerCoordinate_cast]
    exact congrArg (fun u : ℤ=>(u:ℚ))
      (signedCode_inj D _ _ _ _ (congrFun (congrFun he g) r))
  have h := Fintype.card_le_of_injective f hi
  change Fintype.card (ActualY keep L i)≤(2*D+1)^(Fintype.card B*Fintype.card (NativeRows keep Copy I B))
  simpa only [Fintype.card_fun,Fintype.card_fin,←pow_mul,Nat.mul_comm] using h

#print axioms integer_coordinate_on_real_legs
#print axioms copy_incidence_limit
#print axioms real_leg_off_copy
#print axioms integer_coordinate_exact_D
#print axioms actualY_card_in_D_box
end P5MainBalance.M6
