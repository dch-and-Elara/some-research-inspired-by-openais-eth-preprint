import P5MainBalanceM6Rows
import P5MainBalanceM6LinearPatch
import P5MainBalanceNative

/-! Same physical rows at the original node and at t+z. This computes
the printed correction P_e(t+z)-P_e(t) on 1_U, with a genuinely
divisible outer z and no assumption that corrections are group-local. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Polynomial
open scoped BigOperators Classical

variable {E W F Copy I B V : Type*} [Fintype E] [Fintype W] [Fintype Copy]
  [Fintype I] [Fintype B] [LinearOrder B]

set_option maxHeartbeats 5000000 in
theorem physicalRow_add (L : SourceLayout E W F Copy I B) (t : I→ℚ)
    (M : Mix Copy I B) (e : E) (x y : W→ℚ) :
    physicalRow L t M e (x+y)=physicalRow L t M e x+physicalRow L t M e y := by
  simp only [physicalRow,rowChart,place,Matrix.mulVec_add,Pi.add_apply]
  rw [add_sub_add_comm,map_add]
  simp only [mul_add,map_add,add_mul,Finset.sum_add_distrib]
  abel

theorem physicalRow_sum {T : Type*} (L : SourceLayout E W F Copy I B) (t : I→ℚ)
    (M : Mix Copy I B) (e : E) (s : Finset T) (f : T→W→ℚ) :
    physicalRow L t M e (∑ a∈s,f a)=∑ a∈s,physicalRow L t M e (f a) := by
  induction s using Finset.induction_on with
  | empty => simp [physicalRow,rowChart,place]
  | insert a s ha ih =>
    simp only [Finset.sum_insert ha,physicalRow_add,ih]

noncomputable def bitUnit (w : W) (v : W) : ℚ := if v=w then 1 else 0

omit [Fintype W] in
theorem finite_bits_as_sum (U : Finset W) :
    (∑ w∈U,bitUnit w)=qbits (boolSet U) := by
  funext v
  rw [Finset.sum_apply]
  by_cases hv : v∈U
  · rw [Finset.sum_eq_single_of_mem v hv]
    · simp [bitUnit,qbits,boolSet,BooleanMeasurement.bit,hv]
    · intro w _ hw
      simp [bitUnit,Ne.symm hw]
  · rw [Finset.sum_eq_zero]
    · simp [qbits,boolSet,BooleanMeasurement.bit,hv]
    · intro w hw
      have h : v≠w := fun he=>hv (he ▸ hw)
      simp [bitUnit,h]

noncomputable def liftRow : ℚ[X]→+*Bivariate :=
  Polynomial.mapRingHom (C : ℚ→+*ℚ[X])

noncomputable def shiftNative (t : ℚ) : Bivariate→+*Bivariate :=
  Polynomial.eval₂RingHom C (X+C (C t))

theorem shiftNative_eq (t : ℚ) (p : Bivariate) : shiftNative t p=centerBivar t p := rfl

theorem shiftNative_C (t : ℚ) (p : ℚ[X]) : shiftNative t (C p)=C p := by simp [shiftNative]

theorem liftRow_comp (t : ℚ) (p : ℚ[X]) :
    shiftNative t (liftRow p)=liftRow (center t p) := by
  rw [shiftNative_eq]
  unfold centerBivar
  change (p.map (C : ℚ→+*ℚ[X])).comp (X+C (C t)) = (p.comp (X+C t)).map (C : ℚ→+*ℚ[X])
  rw [Polynomial.map_comp]
  simp

noncomputable def rowAt (t : ℚ) (p : ℚ[X]) : Bivariate :=
  C (C (p.eval t))

noncomputable def patchDifference (t : ℚ) (p : ℚ[X]) : Bivariate :=
  shiftNative t (liftRow p)-rowAt t p

theorem patchDifference_dvd (t : ℚ) (p : ℚ[X]) :
    (X:Bivariate)∣patchDifference t p := by
  rw [X_dvd_iff,patchDifference,liftRow_comp,coeff_sub,rowAt,coeff_C_zero]
  change ((p.comp (X+C t)).map (C : ℚ→+*ℚ[X])).coeff 0-C (p.eval t)=0
  rw [coeff_map,coeff_zero_eq_eval_zero,eval_comp]
  simp

noncomputable def patchQuotient (t : ℚ) (p : ℚ[X]) : Bivariate :=
  Classical.choose (patchDifference_dvd t p)

theorem patchQuotient_eq (t : ℚ) (p : ℚ[X]) :
    X*patchQuotient t p=patchDifference t p :=
  (Classical.choose_spec (patchDifference_dvd t p)).symm

theorem patchDifference_sum {T : Type*} (t : ℚ) (s : Finset T) (f : T→ℚ[X]) :
    patchDifference t (∑ a∈s,f a)=∑ a∈s,patchDifference t (f a) := by
  unfold patchDifference rowAt
  simp only [map_sum,eval_finset_sum,Finset.sum_sub_distrib]

noncomputable def originalInput (L : SourceLayout E W F Copy I B) (t : I→ℚ)
    (M : Mix Copy I B) (x : W→Bool) (e : E) : Bivariate :=
  liftRow (physicalRow L t M e (qbits x))

noncomputable def nativeInput (L : SourceLayout E W F Copy I B) (t : I→ℚ)
    (M : Mix Copy I B) (i : I) (x : W→Bool) (U : Finset W) (e : E) : Bivariate :=
  linearPatch (fun k => rowAt (t i) (physicalRow L t M k (qbits x)))
    (fun k w=> patchQuotient (t i) (physicalRow L t M k (bitUnit w))) U e

omit [Fintype W] in
theorem boolSet_trueBits (x : W→Bool) [Fintype W] :
    boolSet (Finset.univ.filter fun w=>x w) = x := by
  funext w
  cases h : x w <;> simp [boolSet,h]

set_option maxHeartbeats 8200000 in
theorem nativeInput_as_printed (L : SourceLayout E W F Copy I B) (t : I→ℚ)
    (M : Mix Copy I B) (i : I) (x : W→Bool) (U : Finset W) (e : E) :
    nativeInput L t M i x U e =
      rowAt (t i) (physicalRow L t M e (qbits x))+
        patchDifference (t i) (physicalRow L t M e (qbits (boolSet U))) := by
  unfold nativeInput linearPatch
  simp_rw [patchQuotient_eq]
  rw [←Finset.sum_filter]
  have hf : Finset.univ.filter (fun w=>w∈U)=U := by ext w; simp
  rw [hf,add_comm,←patchDifference_sum,←physicalRow_sum,finite_bits_as_sum]

theorem nativeInput_trueBits (L : SourceLayout E W F Copy I B) (t : I→ℚ)
    (M : Mix Copy I B) (i : I) (x : W→Bool) (e : E) :
    nativeInput L t M i x (Finset.univ.filter fun w=>x w) e =
      shiftNative (t i) (originalInput L t M x e) := by
  rw [nativeInput_as_printed,boolSet_trueBits,patchDifference,originalInput]
  abel

theorem nativeInput_actual_local (keep : ℕ→Prop) (L : SourceLayout E W F Copy I B)
    (t : I→ℚ) (M : Mix Copy I B) (hM : ActualBaseInvariant keep L M)
    (i : I) (hi : t i≠0) (e : E) (U : Finset W) (x y : W→Bool)
    (hy : sourceTuple keep L i x=sourceTuple keep L i y)
    (hx : ∀ w,L.a w i=L.d (L.factor e) i → x w=y w) :
    nativeInput L t M i x U e=nativeInput L t M i y U e := by
  rw [nativeInput_as_printed,nativeInput_as_printed]
  unfold rowAt
  rw [current_actual_row_local keep L t M hM i hi e x y hy hx]

#print axioms physicalRow_add
#print axioms physicalRow_sum
#print axioms finite_bits_as_sum
#print axioms liftRow_comp
#print axioms patchDifference_dvd
#print axioms patchQuotient_eq
#print axioms nativeInput_as_printed
#print axioms nativeInput_trueBits
#print axioms nativeInput_actual_local
end P5MainBalance.M6
