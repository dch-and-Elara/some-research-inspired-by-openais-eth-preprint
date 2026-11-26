import P5GenericReadoutUni

/-! Ordinary two-dimensional interpolation on a full rectangular grid.
This is over unreduced K[X][Y]; no evaluation is applied to a
truncated algebra. -/
namespace Paper5.GenericReadout
open Polynomial
open scoped BigOperators Polynomial Classical

variable {K : Type*} [Field K]

noncomputable def specializeX (x : K) : K[X][X] →+* K[X] :=
  Polynomial.mapRingHom (Polynomial.evalRingHom x)

noncomputable def gridEval (x y : K) : K[X][X] →+* K :=
  (Polynomial.evalRingHom y).comp (specializeX x)

noncomputable def tensorBasis (p q : K[X]) : K[X][X] :=
  C p * q.map (C : K→+*K[X])

theorem tensor_scaled_coeff (a : K) (p q : K[X]) (n : ℕ) :
    (C (C a)*tensorBasis p q).coeff n=C (a*q.coeff n)*p := by
  simp only [tensorBasis,coeff_C_mul,Polynomial.coeff_map,map_mul]
  ring

set_option maxHeartbeats 12000000 in
theorem ordinary_interpolate_rectangle {dx dy : ℕ}
    (x : Fin (dx+1)→K) (y : Fin (dy+1)→K)
    (hx : Function.Injective x) (hy : Function.Injective y)
    (p : K[X][X]) (hX : ∀ n,(p.coeff n).natDegree≤dx) (hY : p.natDegree≤dy) :
    p=∑ i,∑ j,C (C (gridEval (x i) (y j) p))*tensorBasis (lagrange x i) (lagrange y j) := by
  apply Polynomial.ext
  intro n
  have hv (i : Fin (dx+1)) : (p.coeff n).eval (x i) =
      ∑ j,gridEval (x i) (y j) p * (lagrange y j).coeff n := by
    have hd : (specializeX (x i) p).natDegree≤dy :=
      Polynomial.natDegree_map_le.trans hY
    have he := congrArg (fun q : K[X]=>q.coeff n)
      (ordinary_interpolate y hy (specializeX (x i) p) hd)
    change ((p.map (Polynomial.evalRingHom (x i))).coeff n)=_ at he
    rw [Polynomial.coeff_map] at he
    simpa only [Polynomial.finset_sum_coeff,Polynomial.coeff_C_mul] using he
  calc
    p.coeff n = ∑ i,C ((p.coeff n).eval (x i))*lagrange x i :=
      ordinary_interpolate x hx _ (hX n)
    _ = _ := by
      rw [Polynomial.finset_sum_coeff]
      apply Finset.sum_congr rfl
      intro i _
      rw [hv i,map_sum,Finset.sum_mul,Polynomial.finset_sum_coeff]
      apply Finset.sum_congr rfl
      intro j _
      exact (tensor_scaled_coeff _ _ _ _).symm

theorem coeff_mul_inner_bound (p q : K[X][X]) (dx dx' : ℕ)
    (hP : ∀ i,(p.coeff i).natDegree≤dx) (hQ : ∀ i,(q.coeff i).natDegree≤dx')
    (n : ℕ) : ((p*q).coeff n).natDegree≤dx+dx' := by
  rw [Polynomial.coeff_mul]
  apply Polynomial.natDegree_sum_le_of_forall_le
  intro i _
  exact Polynomial.natDegree_mul_le.trans (Nat.add_le_add (hP i.1) (hQ i.2))

variable {G : Type*}

theorem inner_product_degree (p : G→K[X][X]) (s : Finset G) (dx : ℕ)
    (h : ∀g∈s,∀ n,((p g).coeff n).natDegree≤dx) :
    ∀ n,((∏g∈s,p g).coeff n).natDegree≤s.card*dx := by
  induction s using Finset.induction_on with
  | empty =>
    intro n
    simp only [Finset.prod_empty,Finset.card_empty,zero_mul,coeff_one]
    split <;> simp
  | @insert g s hg ih =>
    intro n
    rw [Finset.prod_insert hg,Finset.card_insert_of_notMem hg,Nat.add_mul,one_mul,add_comm]
    exact coeff_mul_inner_bound _ _ _ _ (h g (Finset.mem_insert_self _ _))
      (ih (fun a ha=>h a (Finset.mem_insert_of_mem ha))) n

variable [Fintype G]

theorem ordinary_product_rectangle_degree (p : G→K[X][X]) (dx dy : ℕ)
    (hX : ∀g n,((p g).coeff n).natDegree≤dx)
    (hY : ∀g,(p g).natDegree≤dy) :
    (∀ n,((∏g,p g).coeff n).natDegree≤Fintype.card G*dx) ∧
      (∏g,p g).natDegree≤Fintype.card G*dy := by
  constructor
  · simpa only [Finset.card_univ] using
      inner_product_degree p Finset.univ dx (fun g _=>hX g)
  · refine (Polynomial.natDegree_prod_le Finset.univ p).trans ?_
    calc
      _ ≤ ∑ _g : G,dy := Finset.sum_le_sum (fun g _=>hY g)
      _ = _ := by simp

#print axioms tensor_scaled_coeff
#print axioms ordinary_interpolate_rectangle
#print axioms coeff_mul_inner_bound
#print axioms inner_product_degree
#print axioms ordinary_product_rectangle_degree
end Paper5.GenericReadout
