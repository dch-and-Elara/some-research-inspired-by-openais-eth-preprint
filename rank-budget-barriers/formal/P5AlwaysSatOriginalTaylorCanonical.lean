import P5AlwaysSatOriginalTaylorWords
import P5AlwaysSatOriginalTaylorChart
import P5AlwaysSatOriginalPhysicalSparsePoly

/-! Exact canonical 0/1 lift from the source F₂ violation polynomial.
Distinct actual variables in each occurrence clause prevent merging
selected words. The coefficient truth is derived, not hypothesized. -/
namespace Paper5.AlwaysSatOriginal.Physical.Taylor
open scoped BigOperators Classical
open P5MainBalance.M6.Sparse

section Generic
variable {A W R : Type*}

noncomputable def wordExponent (l : List A) (var : A→W)
    (pick : Choices l) : W→₀ℕ :=
  ∑ i : Fin l.length,if pick i then Finsupp.single (var (l.get i)) 1 else 0

theorem wordExponent_coordinate (l : List A) (var : A→W)
    (h : Function.Injective (fun i : Fin l.length=>var (l.get i)))
    (pick : Choices l) (i : Fin l.length) :
    wordExponent l var pick (var (l.get i))=if pick i then 1 else 0 := by
  classical
  rw [wordExponent,Finsupp.finset_sum_apply,Finset.sum_eq_single i]
  · cases pick i <;> simp
  · intro j _ hj
    have hv : var (l.get j)≠var (l.get i) := fun hh=>hj (h hh)
    cases pick j
    · rfl
    · exact Finsupp.single_eq_of_ne (Ne.symm hv)
  · simp

theorem wordExponent_injective (l : List A) (var : A→W)
    (h : Function.Injective (fun i : Fin l.length=>var (l.get i))) :
    Function.Injective (wordExponent l var) := by
  intro p q hpq
  funext i
  have hh := congrArg (fun z : W→₀ℕ=>z (var (l.get i))) hpq
  change wordExponent l var p (var (l.get i))=wordExponent l var q (var (l.get i)) at hh
  rw [wordExponent_coordinate l var h p i,wordExponent_coordinate l var h q i] at hh
  cases hp : p i <;> cases hq : q i <;> simp_all

theorem word_monomial [CommRing R] (l : List A) (var : A→W) (pick : Choices l) :
    (MvPolynomial.monomial (wordExponent l var pick) (1:R)) =
      letters (subword l pick) (fun p=>MvPolynomial.X (var p)) := by
  rw [wordExponent,MvPolynomial.monomial_sum_one,subword,letters_ofFn]
  apply Finset.prod_congr rfl
  intro i _
  cases pick i <;> simp [letters,MvPolynomial.X]

theorem support_weight_zero_one (l : List A) (sg : A→Bool) (p : Choices l) :
    (wordWeight l sg supportLetter p:ℤ)=0 ∨ (wordWeight l sg supportLetter p:ℤ)=1 := by
  classical
  by_cases h : ∀ i : Fin l.length,sg (l.get i) || p i
  · right
    exact Finset.prod_eq_one (fun i _=>if_pos (h i))
  · left
    obtain ⟨i,hi⟩ := not_forall.mp h
    exact Finset.prod_eq_zero (Finset.mem_univ i) (if_neg hi)

noncomputable def integralWordLift (l : List A) (var : A→W)
    (sg : A→Bool) : MvPolynomial W ℤ :=
  ∑ p : Choices l,MvPolynomial.monomial (wordExponent l var p)
    (wordWeight l sg supportLetter p)

theorem lift_coefficient_zero_one (l : List A) (var : A→W) (sg : A→Bool)
    (h : Function.Injective (fun i : Fin l.length=>var (l.get i))) (a : W→₀ℕ) :
    (integralWordLift l var sg).coeff a=0 ∨ (integralWordLift l var sg).coeff a=1 := by
  classical
  rw [integralWordLift,MvPolynomial.coeff_sum]
  by_cases ha : ∃ p : Choices l,wordExponent l var p=a
  · obtain ⟨p,rfl⟩ := ha
    rw [Finset.sum_eq_single p]
    · simpa only [MvPolynomial.coeff_monomial,if_pos rfl] using support_weight_zero_one l sg p
    · intro q _ hq
      rw [MvPolynomial.coeff_monomial,if_neg (fun hEq=>hq (wordExponent_injective l var h hEq))]
    · simp
  · left
    exact Finset.sum_eq_zero (fun p _=>by rw [MvPolynomial.coeff_monomial,
      if_neg (fun hEq=>ha ⟨p,hEq⟩)])

theorem lift_map_field (l : List A) (var : A→W) (sg : A→Bool) :
    MvPolynomial.map (Int.castRingHom (ZMod 2)) (integralWordLift l var sg) =
      violation (K:=ZMod 2) (l.map fun p=>(var p,sg p)) := by
  let ι : ℤ→+*MvPolynomial W (ZMod 2) := MvPolynomial.C.comp (Int.castRingHom (ZMod 2))
  rw [integralWordLift,map_sum]
  calc
    _ = ∑ p : Choices l,wordWeight l sg supportLetter p*
        letters (subword l p) (fun u=>MvPolynomial.X (var u)) := by
      apply Finset.sum_congr rfl
      intro p _
      rw [MvPolynomial.map_monomial,←mul_one ((Int.castRingHom (ZMod 2))
        (wordWeight l sg supportLetter p)),←MvPolynomial.C_mul_monomial,word_monomial]
      change ι (wordWeight l sg supportLetter p)*_=_
      rw [support_word_map]
    _ = _ := by
      rw [support_word_expansion]
      unfold violation letters
      rw [List.map_map]
      apply congrArg List.prod
      apply List.map_congr_left
      intro p _
      have h2 : (2:MvPolynomial W (ZMod 2))=0 := CharP.cast_eq_zero _ 2
      have hn : -(MvPolynomial.X (var p):MvPolynomial W (ZMod 2))=MvPolynomial.X (var p) := by
        apply (add_right_inj (MvPolynomial.X (var p))).mp
        rw [add_neg_cancel,←two_mul,h2,zero_mul]
      cases hs : sg p <;> simp [falseLiteral,hs,sub_eq_add_neg,hn]

theorem literal_canonical_lift (l : List A) (var : A→W) (sg : A→Bool)
    (h : Function.Injective (fun i : Fin l.length=>var (l.get i))) (a : W→₀ℕ) :
    (integralWordLift l var sg).coeff a =
      ((violation (K:=ZMod 2) (l.map fun p=>(var p,sg p))).coeff a).val := by
  have hh := congrArg (fun p : MvPolynomial W (ZMod 2)=>p.coeff a) (lift_map_field l var sg)
  change ((MvPolynomial.map (Int.castRingHom (ZMod 2))) (integralWordLift l var sg)).coeff a =
    (violation (K:=ZMod 2) (l.map fun p=>(var p,sg p))).coeff a at hh
  rw [MvPolynomial.coeff_map] at hh
  rw [←hh]
  rcases lift_coefficient_zero_one l var sg h a with h0|h0
  · rw [h0]; rfl
  · rw [h0]
    exact (by decide : (1:ℤ)=Int.ofNat ((1:ZMod 2).val))

theorem evaluate_our_lift (l : List A) (var : A→W) (sg : A→Bool) (x : W→ℤ) :
    MvPolynomial.eval x (integralWordLift l var sg) =
      ∑ p : Choices l,wordWeight l sg supportLetter p*letters (subword l p) (x ∘ var) := by
  rw [integralWordLift,map_sum]
  apply Finset.sum_congr rfl
  intro p _
  have hm : (MvPolynomial.monomial (wordExponent l var p) (wordWeight l sg supportLetter p):
      MvPolynomial W ℤ)=MvPolynomial.C (wordWeight l sg supportLetter p)*
        MvPolynomial.monomial (wordExponent l var p) 1 := by
    rw [MvPolynomial.C_mul_monomial,mul_one]
  rw [hm,word_monomial]
  unfold letters
  simp only [map_mul,map_list_prod,List.map_map,MvPolynomial.eval_C,
    Function.comp_def,MvPolynomial.eval_X]

end Generic

#print axioms wordExponent_coordinate
#print axioms wordExponent_injective
#print axioms word_monomial
#print axioms support_weight_zero_one
#print axioms lift_coefficient_zero_one
#print axioms lift_map_field
#print axioms literal_canonical_lift
#print axioms evaluate_our_lift
end Paper5.AlwaysSatOriginal.Physical.Taylor