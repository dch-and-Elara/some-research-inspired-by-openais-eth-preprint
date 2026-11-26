import P5MainBalanceM6LinearPatch

/-! A literal factor is a finite monomial list. Its coefficients are
allowed to inspect only the signs marked in that factor, and its input
slots are typed occurrences of that factor. Both restrictions survive
monomial expansion, including the auxiliary V-lift. -/
namespace P5MainBalance.M6
open Polynomial
open scoped BigOperators Classical

variable {E F V R : Type*} [CommRing R]

structure Recipe (factor : E→F) (owner : V→F) (R : Type*) where
  count : F→ℕ
  degree : ∀ f,Fin (count f)→ℕ
  read : ∀ f k,Fin (degree f k)→{e : E // factor e=f}
  coeff : ∀ f,Fin (count f)→({v : V//owner v=f}→Bool)→R

variable {fowner : E→F} {sowner : V→F}

noncomputable def Recipe.factorScore (P : Recipe fowner sowner R) (f : F)
    (s : {v : V//sowner v=f}→Bool) (input : E→R[X]) : R[X] :=
  ∑ k,C (P.coeff f k s)*∏ j,input (P.read f k j).val

theorem Recipe.factorScore_congr (P : Recipe fowner sowner R) (f : F)
    (s s' : {v : V//sowner v=f}→Bool) (hσ : s=s')
    (input other : E→R[X]) (h : ∀ e,fowner e=f → input e=other e) :
    P.factorScore f s input=P.factorScore f s' other := by
  subst s'
  unfold Recipe.factorScore
  apply Finset.sum_congr rfl
  intro k _
  congr 1
  exact Finset.prod_congr rfl (fun j _=>h _ (P.read f k j).property)

variable [Fintype F]

noncomputable def Recipe.evaluate (P : Recipe fowner sowner R)
    (σ : V→Bool) (input : E→R[X]) : R[X] :=
  ∏ f,P.factorScore f (fun v=>σ v.val) input

theorem Recipe.expansion (P : Recipe fowner sowner R) (σ : V→Bool) (input : E→R[X]) :
    P.evaluate σ input =
      ∑ a : (∀ f,Fin (P.count f)),
        C (∏ f,P.coeff f (a f) (fun v=>σ v.val)) *
          ∏ e : (Σ f,Fin (P.degree f (a f))),input (P.read e.1 (a e.1) e.2).val := by
  unfold Recipe.evaluate Recipe.factorScore
  rw [Fintype.prod_sum]
  apply Finset.sum_congr rfl
  intro a _
  rw [Finset.prod_mul_distrib,←map_prod,Fintype.prod_sigma]

theorem Recipe.low_window {W : Type*} [Fintype W] [Nonempty W]
    (P : Recipe fowner sowner R) (σ : V→Bool) (base : E→R[X]) (δ : E→W→R[X])
    (x : Finset W) (j : ℕ) :
    (P.evaluate σ (linearPatch base δ x)).coeff j =
      window x j (fun U=>(P.evaluate σ (linearPatch base δ U)).coeff j) := by
  let T := (∀ f,Fin (P.count f))
  let D (a : T) := (Σ f,Fin (P.degree f (a f)))
  let e (a : T) := Fintype.equivFin (D a)
  let read (a : T) (n : Fin (Fintype.card (D a))) :=
    let i := (e a).symm n
    (P.read i.1 (a i.1) i.2).val
  have h (U : Finset W) :
      P.evaluate σ (linearPatch base δ U) =
        ∑ a:T,C (∏ f,P.coeff f (a f) (fun v=>σ v.val)) *
          ∏ k,linearPatch base δ U (read a k) := by
    rw [Recipe.expansion]
    apply Finset.sum_congr rfl
    intro a _
    congr 1
    exact ((e a).symm.prod_comp (fun i : D a => linearPatch base δ U
      (P.read i.1 (a i.1) i.2).val)).symm
  simp only [h]
  exact monomial_menu_has_small_window (fun a=>Fintype.card (D a)) read _ base δ x j

variable {B : Type*} [Fintype B] [DecidableEq B]


noncomputable def Recipe.groupScore (P : Recipe fowner sowner R)
    (d : F→B) (g : B)
    (s : {v : V // d (sowner v)=g}→Bool) (input : E→R[X]) : R[X] :=
  ∏ f : {f : F // d f=g},
    P.factorScore f.val (fun v=>s ⟨v.val,(congrArg d v.property).trans f.property⟩) input

omit [Fintype B] in
theorem Recipe.groupScore_congr (P : Recipe fowner sowner R) (d : F→B) (g : B)
    (s : {v : V//d (sowner v)=g}→Bool)
    (x y : E→R[X]) (h : ∀ e,d (fowner e)=g → x e=y e) :
    P.groupScore d g s x=P.groupScore d g s y := by
  unfold Recipe.groupScore
  apply Finset.prod_congr rfl
  intro f _
  exact P.factorScore_congr f.val _ _ rfl x y
    (fun e he=>h e ((congrArg d he).trans f.property))

theorem Recipe.regroup (P : Recipe fowner sowner R) (d : F→B) (σ : V→Bool)
    (x : E→R[X]) :
    (∏ g,P.groupScore d g (fun v=>σ v.val) x)=P.evaluate σ x := by
  unfold Recipe.groupScore Recipe.evaluate
  have h := Fintype.prod_fiberwise d (fun f=>P.factorScore f (fun v=>σ v.val) x)
  exact h

#print axioms Recipe.factorScore_congr
#print axioms Recipe.expansion
#print axioms Recipe.low_window
#print axioms Recipe.groupScore_congr
#print axioms Recipe.regroup
end P5MainBalance.M6
