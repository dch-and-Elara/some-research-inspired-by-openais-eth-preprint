import P5MainBalanceM6SparseCharts
import P5MainBalanceM6DirectOccurrences
import P5MainBalanceM6PrintedSchedule

/-! The degree caps govern the actual occurrence branch, not just the
number of monomials. Neutral factors have exactly one separate port. -/
namespace P5MainBalance.M6.Sparse
open P5MainBalance P5MainBalance.M6 P5MainIterator
open scoped BigOperators Classical

variable {V : Type*} [Fintype V] [DecidableEq V]

private def ownerSum {A B W : Type*} (a : A→W) (b : B→W) : A⊕B→W
  | .inl x => a x
  | .inr x => b x

private def fibreSumEquiv {A B W : Type*} (a : A→W) (b : B→W) (v : W) :
    {p : A⊕B // ownerSum a b p=v} ≃ ({x : A // a x=v}⊕{y : B // b y=v}) where
  toFun p := match p with
    | ⟨.inl a',h⟩ => .inl ⟨a',h⟩
    | ⟨.inr b',h⟩ => .inr ⟨b',h⟩
  invFun p := match p with
    | .inl ⟨a',h⟩ => ⟨.inl a',h⟩
    | .inr ⟨b',h⟩ => ⟨.inr b',h⟩
  left_inv p := by rcases p with ⟨a|b,h⟩ <;> rfl
  right_inv p := by rcases p with ⟨a,h⟩|⟨b,h⟩ <;> rfl

private theorem fibre_sum_card {A B W : Type*} [Fintype A] [Fintype B]
    (a : A→W) (b : B→W) (w : W) :
    Nat.card {p : A⊕B // ownerSum a b p=w} =
      Nat.card {p : A // a p=w}+Nat.card {p : B // b p=w} := by
  rw [Nat.card_congr (fibreSumEquiv a b w),Nat.card_sum]

private theorem fibre_id_card {W : Type*} (v : W) :
    Nat.card {p : W // id p=v}=1 := by
  let f : {p : W // id p=v} ≃ Unit :=
    ⟨fun _=>(),fun _=>⟨v,rfl⟩,fun x=>Subtype.ext x.property.symm,fun _=>rfl⟩
  rw [Nat.card_congr f,Nat.card_eq_fintype_card,Fintype.card_unit]

def endpointVertex (G : Finset (V×V)) : G×Bool→V :=
  fun p=>uOwnerOf G (.inl (.inr p))

omit [Fintype V] in
def localEndpoint (G : Finset (V×V)) (v : V) :
    {p : G×Bool // endpointVertex G p=v}→MainClonedCNF.EndpointSlot G v
  | ⟨(e,false),h⟩ => .inl ⟨e.val,Finset.mem_filter.mpr ⟨e.property,h⟩⟩
  | ⟨(e,true),h⟩ => .inr ⟨e.val,Finset.mem_filter.mpr ⟨e.property,h⟩⟩

omit [Fintype V] in
theorem localEndpoint_inj (G : Finset (V×V)) (v : V) : Function.Injective (localEndpoint G v) := by
  intro e f h
  have hd : ∀ x,Direct.decodeEndpoint G ⟨v,localEndpoint G v x⟩=x.val := by
    rintro ⟨⟨a,b⟩,h'⟩
    cases b <;> rfl
  apply Subtype.ext
  rw [←hd e,←hd f,h]

set_option maxHeartbeats 9500000 in
theorem uncloned_occurrences_at_most_five (G : Finset (V×V))
    (reg : ∀ v,GraphCutMoments.degree G v=3) (v : V) :
    Fintype.card {p : UPort G // uOwnerOf G p=v}≤5 := by
  have eqF : uOwnerOf G=ownerSum (ownerSum id (endpointVertex G)) id := by
    funext p
    rcases p with (w|⟨e,b⟩)|w
    · rfl
    · cases b <;> rfl
    · rfl
  have hE : Fintype.card {p : G×Bool // endpointVertex G p=v}≤3 := by
    have h := Fintype.card_le_of_injective (localEndpoint G v) (localEndpoint_inj G v)
    rwa [MainClonedCNF.endpoint_card G v,reg v] at h
  rw [←Nat.card_eq_fintype_card,eqF,fibre_sum_card,fibre_sum_card,fibre_id_card]
  rw [←Nat.card_eq_fintype_card] at hE
  omega

set_option maxHeartbeats 9500000 in
theorem cloned_occurrences_at_most_four (G : Finset (V×V))
    (reg : ∀ v,GraphCutMoments.degree G v=3) (w : V×Fin 4) :
    Fintype.card {p : CPort G //
        cOwnerOf G (MainClonedCNF.leftSlot G reg) (MainClonedCNF.rightSlot G reg) p=w}≤4 := by
  let a := Direct.ownerOf G (MainClonedCNF.leftSlot G reg) (MainClonedCNF.rightSlot G reg)
  have eqF : cOwnerOf G (MainClonedCNF.leftSlot G reg) (MainClonedCNF.rightSlot G reg)=ownerSum a id := by
    funext p
    cases p <;> rfl
  rw [←Nat.card_eq_fintype_card,eqF,fibre_sum_card,fibre_id_card]
  have h := Direct.printed_clone_scope_at_most_three G reg w
  change Fintype.card {p : MainClonedCNF.Port G // a p=w}≤3 at h
  rw [←Nat.card_eq_fintype_card] at h
  omega

theorem printed_no_heavy_from_occurrences (n : ℕ) (hLam : 1≤mainLambda n) (load : ℕ)
    (hc : load≤5) : load≤5*⌈Real.sqrt (mainLambda n:ℝ)⌉₊ := by
  have hLam' : (1:ℝ)≤mainLambda n := by exact_mod_cast hLam
  have hs := Real.sqrt_le_sqrt hLam'
  rw [Real.sqrt_one] at hs
  have hs' : (1:ℝ)≤(⌈Real.sqrt (mainLambda n:ℝ)⌉₊:ℝ) := hs.trans (Nat.le_ceil _)
  have hs'' : 1≤⌈Real.sqrt (mainLambda n:ℝ)⌉₊ := by exact_mod_cast hs'
  exact hc.trans (by nth_rw 1 [←Nat.mul_one 5]; exact Nat.mul_le_mul_left 5 hs'')

#print axioms uncloned_occurrences_at_most_five
#print axioms cloned_occurrences_at_most_four
#print axioms printed_no_heavy_from_occurrences
end P5MainBalance.M6.Sparse
