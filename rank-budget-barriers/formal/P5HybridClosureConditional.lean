import P5HybridClosureMain
import J6R11CollisionGreedy

/-! A correlated primitive assignment cannot use a product law on the
*words*. Conditional averaging is instead performed on the true
primitive addresses; a shared address occurs once in the support. -/
namespace Paper5.HybridClosure
open scoped BigOperators Classical
open GuardExpectation

section Block
variable {R C A : Type*} [Fintype R] [Fintype C] [Fintype A] [DecidableEq R] [DecidableEq C]

/-- Independent primitive addresses, not independently generated words. -/
theorem block_average (w : R⊕C→A→ℚ) (f : (R→A)→ℚ) (g : (C→A)→ℚ) :
    average w (fun z=>f (fun x=>z (.inl x))*g (fun y=>z (.inr y))) =
      average (fun r=>w (.inl r)) f * average (fun c=>w (.inr c)) g := by
  let chart := J6R11CollisionGreedy.splitSample (R:=R) (C:=C) (A:=A)
  let H := fun z : (R→A)×(C→A) =>
    (productMass (fun i=>w (.inl i)) z.1*f z.1)*
      (productMass (fun i=>w (.inr i)) z.2*g z.2)
  calc
    _ = ∑ z : R⊕C→A, H (chart z) := by
      unfold average H
      apply Finset.sum_congr rfl
      intro z _
      unfold productMass
      rw [Fintype.prod_sum_type]
      dsimp [chart,J6R11CollisionGreedy.splitSample]
      ring
    _ = ∑ z : (R→A)×(C→A),H z := Equiv.sum_comp chart H
    _ = _ := by unfold H average; rw [Fintype.sum_prod_type,Finset.sum_mul]; simp only [Finset.mul_sum]
end Block

section Support
variable {P A : Type*} [Fintype P] [DecidableEq P] [Fintype A]

theorem average_rename {Q : Type*} [Fintype Q] [DecidableEq Q] (e : Q≃P)
    (w : P→A→ℚ) (f : (P→A)→ℚ) :
    average w f=average (fun j=>w (e j)) (fun z=>f (z ∘ e.symm)) := by
  let chart := e.arrowCongr (Equiv.refl A)
  unfold average
  rw [←Equiv.sum_comp chart]
  apply Finset.sum_congr rfl
  intro z _
  unfold productMass
  change (∏ p,w p (z (e.symm p)))*f (z ∘ e.symm)=_
  congr 1
  rw [←Equiv.prod_comp e]
  simp

theorem average_on_support (s : Finset P) (w : P→A→ℚ)
    (hw : ∀ j,∑v,w j v=1) (f : (s→A)→ℚ) :
    average w (fun z=>f (fun i : s=> z i)) = average (fun i : s=>w i) f := by
  let e := Equiv.sumCompl (fun x : P=>x∈s)
  rw [average_rename e]
  have hf (z : (s⊕{i : P // i∉s})→A) :
      f (fun i : s => (z ∘ e.symm) i)=
        f (fun i : s => z (Sum.inl i))*1 := by
    rw [mul_one]
    congr 1
    funext i
    change z (e.symm i.1)=z (Sum.inl i)
    apply congrArg z
    apply e.injective
    rw [Equiv.apply_symm_apply]
    rfl
  simp_rw [hf]
  have hs := block_average (fun i=>w (e i)) f
    (fun _ : ({i : P // i∉s}→A) => (1:ℚ))
  change average (fun i=>w (e i)) (fun z=>f (fun i : s=>z (.inl i))*1) =
    average (fun i : s=>w i) f
  trans average (fun i : s => w (e (.inl i))) f *
    average (fun i : {i : P // i∉s} => w (e (.inr i))) (fun _ => 1)
  · exact hs
  · rw [average_const _ (fun i=>hw _) 1,mul_one]
    rfl
end Support

section ActualPair
open J1MainSourceLabels J1MainSourceCollision DiagonalAbundance
variable {V F B I S E : Type*} [Fintype V] [Fintype F] [Fintype B]
  [Fintype I] [DecidableEq I] [Fintype S]

def pairKeys (t : I) (tie : F→Option B) (var : E→V) (fac : E→F)
    (e₁ e₂ : E) : Bool×Bool×I→Primitive V F B I
  | (j,side,k) =>
    let e := if j then e₂ else e₁
    if side then .inr (factorKey t tie (fac e) k) else .inl (var e,k)

noncomputable def pairSupport (t : I) (tie : F→Option B) (var : E→V) (fac : E→F)
    (e₁ e₂ : E) : Finset (Primitive V F B I) :=
  Finset.univ.image (pairKeys t tie var fac e₁ e₂)

omit [Fintype V] [Fintype F] [Fintype B] in
theorem pairSupport_card (t : I) (tie : F→Option B) (var : E→V) (fac : E→F)
    (e₁ e₂ : E) : (pairSupport t tie var fac e₁ e₂).card≤4*Fintype.card I := by
  have h := Finset.card_image_le (s := (Finset.univ : Finset (Bool×Bool×I)))
    (f:=pairKeys t tie var fac e₁ e₂)
  simp only [Finset.card_univ,Fintype.card_prod,Fintype.card_bool] at h
  unfold pairSupport
  omega

noncomputable def pairProjection (t : I) (tie : F→Option B) (var : E→V) (fac : E→F)
    (e₁ e₂ : E) (z : pairSupport t tie var fac e₁ e₂→S) (j : Bool) : Draw I S :=
  (fun k=>z ⟨pairKeys t tie var fac e₁ e₂ (j,false,k),Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩,
   fun k=>z ⟨pairKeys t tie var fac e₁ e₂ (j,true,k),Finset.mem_image.mpr ⟨_,Finset.mem_univ _,rfl⟩⟩)

omit [Fintype V] [Fintype F] [Fintype B] [Fintype S] in
theorem pairProjection_restrict (t : I) (tie : F→Option B) (var : E→V) (fac : E→F)
    (e₁ e₂ : E) (z : Primitive V F B I→S) (j : Bool) :
    pairProjection t tie var fac e₁ e₂ (z ∘ Subtype.val) j =
      literalCell t tie var fac z (if j then e₂ else e₁) := by
  cases j <;> rfl

theorem conditional_actual_pair (t : I) (tie : F→Option B) (var : E→V) (fac : E→F)
    (e₁ e₂ : E) (w : Primitive V F B I→S→ℚ) (hw : ∀ i,∑x,w i x=1) :
    average w (fun z=>J1MainSourceCollision.indicator
      (literalCell t tie var fac z e₁=literalCell t tie var fac z e₂)) =
    average (fun i : pairSupport t tie var fac e₁ e₂=>w i)
      (fun z=>J1MainSourceCollision.indicator
        (pairProjection t tie var fac e₁ e₂ z false=pairProjection t tie var fac e₁ e₂ z true)) := by
  refine Eq.trans ?_ (average_on_support (pairSupport t tie var fac e₁ e₂) w hw _)
  rfl

omit [Fintype V] [Fintype F] [Fintype B] in
theorem conditional_pair_enumeration_size (t : I) (tie : F→Option B)
    (var : E→V) (fac : E→F) (e₁ e₂ : E) (hS : 0<Fintype.card S) :
    Fintype.card (pairSupport t tie var fac e₁ e₂→S)≤
      ((Fintype.card S)^(2*Fintype.card I))^2 := by
  rw [Fintype.card_fun,Fintype.card_coe,←pow_mul]
  have h := pairSupport_card t tie var fac e₁ e₂
  apply Nat.pow_le_pow_right hS
  omega
end ActualPair

#print axioms block_average
#print axioms average_rename
#print axioms average_on_support
#print axioms pairSupport_card
#print axioms pairProjection_restrict
#print axioms conditional_actual_pair
#print axioms conditional_pair_enumeration_size
end Paper5.HybridClosure