import P5MainBalanceM6LinearPatch
import P5MainIteratorTrace

/-! The literal Taylor pair order of summation is valid for coefficients
over any commutative ring. Filtering by a Boolean patch predates the
measurement fibres and introduces no sign-dependent indices. -/
namespace P5MainBalance.M6
open P5MainBalance P5MainIterator Polynomial
open scoped BigOperators Classical

variable {W R : Type*} [Fintype W] [CommRing R]

theorem taylor_filter_exact (j : ℕ) (x : W→Bool) :
    ((Finset.univ.filter (fun w=>x w)).powerset.filter (fun S=>S.card≤j)).biUnion
      (fun S=>S.powerset.image (Prod.mk S)) =
        (TaylorList W j).filter (fun a=>∀ w∈a.1,x w=true) := by
  ext a
  rcases a with ⟨S,U⟩
  simp only [Finset.mem_biUnion,Finset.mem_filter,Finset.mem_powerset,Finset.mem_image,
    mem_taylorList,Prod.mk.injEq]
  constructor
  · rintro ⟨P,⟨hP,hJ⟩,T,hT,rfl,rfl⟩
    exact ⟨⟨hT,hJ⟩,fun w hw=>(Finset.mem_filter.mp (hP hw)).2⟩
  · rintro ⟨⟨hU,hJ⟩,hP⟩
    exact ⟨S,⟨fun w hw=>Finset.mem_filter.mpr ⟨Finset.mem_univ _,hP w hw⟩,hJ⟩,U,hU,rfl,rfl⟩

theorem one_window_as_terms (x : W→Bool) (j : ℕ) (f : Finset W→R) :
    window (Finset.univ.filter fun w=>x w) j f =
      ∑ a∈TaylorList W j,
        if ∀ w∈a.1,x w=true then (-1:R)^((a.1\a.2).card)*f a.2 else 0 := by
  rw [←Finset.sum_filter,←taylor_filter_exact,Finset.sum_biUnion]
  · unfold window
    refine Finset.sum_congr rfl fun S _=>?_
    rw [Finset.sum_image]
    exact fun i _ j _ h=>congrArg Prod.snd h
  · intro p _ q _ h
    change Disjoint (p.powerset.image (Prod.mk p)) (q.powerset.image (Prod.mk q))
    rw [Finset.disjoint_left]
    intro a ha hb
    obtain ⟨u,_,hu⟩ := Finset.mem_image.mp ha
    obtain ⟨v,_,hv⟩ := Finset.mem_image.mp hb
    exact h (congrArg Prod.fst (hu.trans hv.symm))

theorem assemble_taylor_pairs (j : ℕ) (F : (W→Bool)→Finset W→R) :
    (∑ x : W→Bool,window (Finset.univ.filter (fun w=>x w)) j (F x)) =
      ∑ a : TaylorList W j, (-1:R)^((a.val.1\a.val.2).card) *
        ∑ x : {x : W→Bool // ∀ w∈a.val.1,x w=true}, F x.val a.val.2 := by
  simp_rw [one_window_as_terms]
  rw [Finset.sum_comm,←Finset.sum_coe_sort]
  apply Finset.sum_congr rfl
  intro a _
  rw [←Finset.sum_filter]
  let p (x : W→Bool) := ∀ w∈a.val.1,x w=true
  have hw : ∀ x, x∈(Finset.univ : Finset (W→Bool)).filter p ↔ p x := by simp
  rw [Finset.sum_subtype _ hw,Finset.mul_sum]

section Fibres

variable {X Y : Type*} [Fintype X] [Fintype Y]

theorem sum_literal_fibres (get : X→Y) (gate : X→Prop) (f : X→R) :
    (∑ x : {x : X//gate x}, f x.val) =
      ∑ y : Y,∑ x : {x : X // get x=y ∧ gate x},f x.val := by
  let functor (x : {x : X//gate x}) := get x.val
  let e (y : Y) : {x : {x : X//gate x}//functor x=y} ≃ {x : X//get x=y ∧ gate x} :=
    ⟨fun x=>⟨x.val.val,x.property,x.val.property⟩,
     fun x=>⟨⟨x.val,x.property.2⟩,x.property.1⟩,fun _=>rfl,fun _=>rfl⟩
  calc
    _ = ∑ y : Y,∑ x : {x : {x : X//gate x}//functor x=y},f x.val.val :=
      (Fintype.sum_fiberwise functor (fun x=>f x.val)).symm
    _ = _ := Finset.sum_congr rfl (fun y _ =>((e y).sum_comp (fun x=>f x.val)))

end Fibres

#print axioms taylor_filter_exact
#print axioms one_window_as_terms
#print axioms assemble_taylor_pairs
#print axioms sum_literal_fibres
end P5MainBalance.M6
